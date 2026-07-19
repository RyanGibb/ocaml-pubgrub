let () = Memtrace.trace_if_requested ()
let () = if Sys.getenv_opt "BENCH_DEBUG" <> None then Pubgrub.set_debug true

module S = struct
  type t = string

  let compare = String.compare
  let pp = Format.pp_print_string
end

module Solver = Pubgrub.Make (S) (S)

(* Zero-padded so lexicographic comparison agrees with numeric order. *)
let v i = Printf.sprintf "%03d" i

let time f =
  let t0 = Unix.gettimeofday () in
  let result = f () in
  let t1 = Unix.gettimeofday () in
  (result, t1 -. t0)

let make_solver repo deps =
  let repo_tbl = Hashtbl.create 16 in
  List.iter (fun (n, v) -> Hashtbl.add repo_tbl n v) repo;
  let dep_tbl = Hashtbl.create 16 in
  List.iter (fun ((n, v), (dn, dvs)) -> Hashtbl.add dep_tbl (n, v) (dn, dvs)) deps;
  let versions n = Hashtbl.find_all repo_tbl n in
  let dependencies n v = Hashtbl.find_all dep_tbl (n, v) in
  (versions, dependencies)

let deep_chain n =
  let repo = List.init (n + 1) (fun i -> ("A" ^ v i, v 0)) in
  let deps =
    List.init n (fun i ->
        (("A" ^ v i, v 0), ("A" ^ v (i + 1), Solver.Ranges.singleton (v 0))))
  in
  let query = [ ("A" ^ v 0, Solver.Ranges.singleton (v 0)) ] in
  (make_solver repo deps, query)

let wide_fan n =
  let repo = List.init n (fun i -> ("P" ^ v i, v 0)) in
  let query = List.init n (fun i -> ("P" ^ v i, Solver.Ranges.singleton (v 0))) in
  (make_solver repo [], query)

let conflict_heavy n m =
  let repo =
    List.init n (fun i -> List.init m (fun j -> ("C" ^ v i, v j))) |> List.flatten
  in
  let deps =
    List.init (n - 1) (fun i ->
        List.init m (fun j ->
            let allowed =
              List.init m (fun k -> v k) |> List.filteri (fun k _ -> k <> j mod m)
            in
            (("C" ^ v i, v j), ("C" ^ v (i + 1), Solver.Ranges.of_list allowed))))
    |> List.flatten
  in
  let query = [ ("C" ^ v 0, Solver.Ranges.of_list (List.init m (fun j -> v j))) ] in
  (make_solver repo deps, query)

let diamond n m =
  let repo =
    List.init n (fun i -> ("D" ^ v i, v 0)) @ List.init m (fun j -> ("Z", v j))
  in
  let half = m / 2 in
  let deps =
    List.init n (fun i ->
        let start = i * half / n in
        let allowed = List.init half (fun k -> v ((start + k) mod m)) in
        (("D" ^ v i, v 0), ("Z", Solver.Ranges.of_list allowed)))
  in
  let query = List.init n (fun i -> ("D" ^ v i, Solver.Ranges.singleton (v 0))) in
  (make_solver repo deps, query)

(* Each pair (X i, Y i): X i 1 depends on Y i 1, which depends back on X i 0.
   Choosing X i 1 (the newest) always dead-ends, forcing one conflict
   resolution and backtrack per pair. *)
let backtrack_chain n =
  let repo =
    List.init n (fun i -> [ ("X" ^ v i, v 0); ("X" ^ v i, v 1); ("Y" ^ v i, v 1) ])
    |> List.flatten
  in
  let deps =
    List.init n (fun i ->
        [
          (("X" ^ v i, v 1), ("Y" ^ v i, Solver.Ranges.singleton (v 1)));
          (("Y" ^ v i, v 1), ("X" ^ v i, Solver.Ranges.singleton (v 0)));
        ])
    |> List.flatten
  in
  let query = List.init n (fun i -> ("X" ^ v i, Solver.Ranges.of_list [ v 0; v 1 ])) in
  (make_solver repo deps, query)

(* Chain A0 -> A1 -> ... -> An of exact version requirements, but the final
   package only ships a version outside the required range, so solving fails
   after propagating the whole chain. *)
let unsat_chain n =
  let repo = List.init (n + 1) (fun i -> ("A" ^ v i, v (if i = n then 1 else 0))) in
  let deps =
    List.init n (fun i ->
        (("A" ^ v i, v 0), ("A" ^ v (i + 1), Solver.Ranges.singleton (v 0))))
  in
  let query = [ ("A" ^ v 0, Solver.Ranges.singleton (v 0)) ] in
  (make_solver repo deps, query)

(* Random graph with power-law popularity and geometric version/dep counts. *)
let realistic n =
  let rng = Random.State.make [| 42 |] in
  let geom p =
    let rec go k =
      if Random.State.float rng 1.0 < p then k else go (k + 1)
    in
    go 0
  in
  (* Pick an index in [0, max_idx) biased toward lower values. *)
  let popular_under max_idx =
    let r = Random.State.float rng 1.0 in
    int_of_float (Float.of_int max_idx *. r *. r)
  in
  let n_versions = Array.init n (fun _ -> 1 + geom 0.3) in
  let pkg i = "P" ^ v i in
  let repo =
    List.init n (fun i ->
        List.init n_versions.(i) (fun j -> (pkg i, v j)))
    |> List.flatten
  in
  let deps = ref [] in
  for i = 1 to n - 1 do
    for j = 0 to n_versions.(i) - 1 do
      let chosen = Hashtbl.create 4 in
      for _ = 1 to geom 0.4 do
        let target = popular_under i in
        if not (Hashtbl.mem chosen target) then begin
          Hashtbl.add chosen target ();
          let target_nv = n_versions.(target) in
          let lower = Random.State.int rng ((target_nv + 1) / 2) in
          let allowed =
            List.init (target_nv - lower) (fun k -> v (lower + k))
          in
          deps :=
            ((pkg i, v j), (pkg target, Solver.Ranges.of_list allowed))
            :: !deps
        end
      done
    done
  done;
  let n_query = max 1 (n / 20) in
  let query =
    List.init n_query (fun k ->
        let i = n - 1 - k in
        let nv = n_versions.(i) in
        (pkg i, Solver.Ranges.of_list (List.init nv (fun j -> v j))))
  in
  (make_solver repo !deps, query)

(* Every query constraint and every decided package's dependencies must be
   satisfied by the returned solution. *)
let validate ~dependencies query solution =
  let find n = List.find_opt (fun (n', _) -> String.equal n n') solution in
  let satisfied (n, r) =
    match find n with Some (_, ver) -> Solver.Ranges.contains ver r | None -> false
  in
  List.for_all satisfied query
  && List.for_all
       (fun (n, ver) -> List.for_all satisfied (dependencies n ver))
       solution

let run shape n reps =
  let (versions, dependencies), query =
    match shape with
    | "deep_chain" -> deep_chain n
    | "wide_fan" -> wide_fan n
    | "conflict_heavy" -> conflict_heavy n 5
    | "diamond" -> diamond n 20
    | "backtrack_chain" -> backtrack_chain n
    | "unsat_chain" -> unsat_chain n
    | "realistic" -> realistic n
    | _ -> failwith (Printf.sprintf "unknown shape: %s" shape)
  in
  let runs =
    List.init reps (fun _ -> time (fun () -> Solver.solve ~versions ~dependencies query))
  in
  let status =
    match fst (List.hd runs) with
    | Ok solution -> if validate ~dependencies query solution then "ok" else "INVALID"
    | Error _ -> "error"
  in
  let times = List.map snd runs in
  let mn = List.fold_left min infinity times in
  let mean = List.fold_left ( +. ) 0. times /. float_of_int reps in
  Printf.printf "%s n=%d %s min=%.4fs mean=%.4fs reps=%d\n" shape n status mn mean reps;
  status <> "INVALID"

let all_shapes =
  [
    ("deep_chain", 500);
    ("wide_fan", 1000);
    ("conflict_heavy", 100);
    ("diamond", 200);
    ("backtrack_chain", 200);
    ("unsat_chain", 500);
    ("realistic", 1000);
  ]

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let ok =
    match args with
    | [ "all" ] -> List.for_all (fun (shape, n) -> run shape n 3) all_shapes
    | [ shape; n_str ] -> run shape (int_of_string n_str) 1
    | [ shape; n_str; reps_str ] ->
        run shape (int_of_string n_str) (int_of_string reps_str)
    | _ ->
        Printf.eprintf "usage: bench <shape> <n> [reps] | bench all\n";
        Printf.eprintf
          "shapes: deep_chain, wide_fan, conflict_heavy, diamond, backtrack_chain, \
           unsat_chain, realistic\n";
        exit 1
  in
  if not ok then exit 1
