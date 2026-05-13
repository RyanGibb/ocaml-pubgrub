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
        | _ -> failwith (Printf.sprintf "unknown shape: %s" shape)
      in
      let result, elapsed = time (fun () -> Solver.solve ~versions ~dependencies query) in
      let status = match result with Ok _ -> "ok" | Error _ -> "error" in
      Printf.printf "%s n=%d %s %.4fs\n" shape n status elapsed
  | _ ->
      Printf.eprintf "usage: bench <shape> <n>\n";
      Printf.eprintf "shapes: deep_chain, wide_fan, conflict_heavy, diamond\n";
      exit 1
