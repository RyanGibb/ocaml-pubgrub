let () = Memtrace.trace_if_requested ()

module S = struct
  type t = string

  let compare = String.compare
  let pp = Format.pp_print_string
end

module Solver = Pubgrub.Make (S) (S)

let v i = string_of_int i

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
  let query = [ ("A0", Solver.Ranges.singleton (v 0)) ] in
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
  let query = [ ("C0", Solver.Ranges.of_list (List.init m (fun j -> v j))) ] in
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

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  match args with
  | [ shape; n_str ] ->
      let n = int_of_string n_str in
      let (versions, dependencies), query =
        match shape with
        | "deep_chain" -> deep_chain n
        | "wide_fan" -> wide_fan n
        | "conflict_heavy" -> conflict_heavy n 5
        | "diamond" -> diamond n 20
        | "realistic" -> realistic n
        | _ -> failwith (Printf.sprintf "unknown shape: %s" shape)
      in
      let result, elapsed = time (fun () -> Solver.solve ~versions ~dependencies query) in
      let status = match result with Ok _ -> "ok" | Error _ -> "error" in
      Printf.printf "%s n=%d %s %.4fs\n" shape n status elapsed
  | _ ->
      Printf.eprintf "usage: bench <shape> <n>\n";
      Printf.eprintf "shapes: deep_chain, wide_fan, conflict_heavy, diamond, realistic\n";
      exit 1
