let () = Pubgrub.set_debug true

module StringOrd = struct
  type t = string

  let compare = String.compare
  let pp = Format.pp_print_string
end

module Solver = Pubgrub.Make (StringOrd) (StringOrd)

let pp_result fmt = function
  | Ok resolution ->
      Format.(
        pp_print_list
          ~pp_sep:(fun fmt () -> pp_print_string fmt ", ")
          (fun fmt (n, v) -> fprintf fmt "%s %s" n v))
        fmt resolution
  | Error incomp -> Solver.explain_incompatibility fmt incomp

let solve_ranges repo deps query =
  let repo_tbl = Hashtbl.create 16 in
  List.iter (fun (n, v) -> Hashtbl.add repo_tbl n v) repo;
  let dep_tbl = Hashtbl.create 16 in
  List.iter (fun (pkg, dep) -> Hashtbl.add dep_tbl pkg dep) deps;
  let vers n = Hashtbl.find_all repo_tbl n in
  let deps n v = Hashtbl.find_all dep_tbl (n, v) in
  let result = Solver.solve ~vers ~deps query in
  Format.printf "%a\n" pp_result result

(* Ranges given as version lists, which is all most tests need. *)
let solve repo deps query =
  solve_ranges repo
    (List.map (fun (pkg, (dn, dvs)) -> (pkg, (dn, Solver.Ranges.of_list dvs))) deps)
    (List.map (fun (n, vs) -> (n, Solver.Ranges.of_list vs)) query)

let%expect_test "example - diamond dependency" =
  solve
    [ ("A", "1"); ("B", "1"); ("C", "1"); ("D", "1"); ("D", "2"); ("D", "3") ]
    [
      (("A", "1"), ("B", [ "1" ]));
      (("A", "1"), ("C", [ "1" ]));
      (("B", "1"), ("D", [ "1"; "2" ]));
      (("C", "1"), ("D", [ "2"; "3" ]));
    ]
    [ ("A", [ "1" ]) ];
  [%expect
    {|
    initial incompatibilities
    (terms: {Root *, not A 1}, cause: dependency root -> A 1)
    unit propagation on: Root
    new assignment on level 0: Derivation A 1 due to incompatibility (terms: {Root *, not A 1}, cause: dependency root -> A 1)
    unit propagation on: A
    deciding on A: 1
    trying version 1
    dependency incompatibilities
    (terms: {A 1, not C 1}, cause: dependency A 1 -> C 1)
    (terms: {A 1, not B 1}, cause: dependency A 1 -> B 1)
    assignment on level 1: Decision A 1
    unit propagation on: A
    new assignment on level 1: Derivation B 1 due to incompatibility (terms: {A 1, not B 1}, cause: dependency A 1 -> B 1)
    new assignment on level 1: Derivation C 1 due to incompatibility (terms: {A 1, not C 1}, cause: dependency A 1 -> C 1)
    unit propagation on: C
    unit propagation on: B
    deciding on B: 1
    trying version 1
    dependency incompatibilities
    (terms: {B 1, not D 1 ∪ 2}, cause: dependency B 1 -> D 1 ∪ 2)
    assignment on level 2: Decision B 1
    unit propagation on: B
    new assignment on level 2: Derivation D 1 ∪ 2 due to incompatibility (terms: {B 1, not D 1 ∪ 2}, cause: dependency B 1 -> D 1 ∪ 2)
    unit propagation on: D
    deciding on C: 1
    trying version 1
    dependency incompatibilities
    (terms: {C 1, not D 2 ∪ 3}, cause: dependency C 1 -> D 2 ∪ 3)
    assignment on level 3: Decision C 1
    unit propagation on: C
    new assignment on level 3: Derivation D 2 ∪ 3 due to incompatibility (terms: {C 1, not D 2 ∪ 3}, cause: dependency C 1 -> D 2 ∪ 3)
    unit propagation on: D
    deciding on D: 2
    trying version 2
    assignment on level 4: Decision D 2
    unit propagation on: D
    D 2, C 1, B 1, A 1
    |}]

let%expect_test "simple" =
  solve
    [ ("foo", "1.0.0"); ("bar", "1.0.0"); ("bar", "2.0.0") ]
    [ (("foo", "1.0.0"), ("bar", [ "1.0.0"; "2.0.0" ])) ]
    [ ("foo", [ "1.0.0" ]) ];
  [%expect
    {|
    initial incompatibilities
    (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)
    unit propagation on: Root
    new assignment on level 0: Derivation foo 1.0.0 due to incompatibility (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)
    unit propagation on: foo
    deciding on foo: 1.0.0
    trying version 1.0.0
    dependency incompatibilities
    (terms: {foo 1.0.0, not bar 1.0.0 ∪ 2.0.0}, cause: dependency foo 1.0.0 -> bar 1.0.0 ∪ 2.0.0)
    assignment on level 1: Decision foo 1.0.0
    unit propagation on: foo
    new assignment on level 1: Derivation bar 1.0.0 ∪ 2.0.0 due to incompatibility (terms: {foo 1.0.0, not bar 1.0.0 ∪ 2.0.0}, cause: dependency foo 1.0.0 -> bar 1.0.0 ∪ 2.0.0)
    unit propagation on: bar
    deciding on bar: 1.0.0 ∪ 2.0.0
    trying version 2.0.0
    assignment on level 2: Decision bar 2.0.0
    unit propagation on: bar
    bar 2.0.0, foo 1.0.0
    |}]

let%expect_test "conflict avoidance" =
  solve
    [
      ("foo", "1.1.0");
      ("foo", "1.0.0");
      ("bar", "2.0.0");
      ("bar", "1.1.0");
      ("bar", "1.0.0");
    ]
    [ (("foo", "1.1.0"), ("bar", [ "2" ])) ]
    [ ("foo", [ "1.0.0"; "1.1.0" ]); ("bar", [ "1.0.0"; "1.1.0" ]) ];
  [%expect
    {|
    initial incompatibilities
    (terms: {Root *, not foo 1.0.0 ∪ 1.1.0}, cause: dependency root -> foo 1.0.0 ∪ 1.1.0)
    (terms: {Root *, not bar 1.0.0 ∪ 1.1.0}, cause: dependency root -> bar 1.0.0 ∪ 1.1.0)
    unit propagation on: Root
    new assignment on level 0: Derivation bar 1.0.0 ∪ 1.1.0 due to incompatibility (terms: {Root *, not bar 1.0.0 ∪ 1.1.0}, cause: dependency root -> bar 1.0.0 ∪ 1.1.0)
    new assignment on level 0: Derivation foo 1.0.0 ∪ 1.1.0 due to incompatibility (terms: {Root *, not foo 1.0.0 ∪ 1.1.0}, cause: dependency root -> foo 1.0.0 ∪ 1.1.0)
    unit propagation on: foo
    unit propagation on: bar
    deciding on bar: 1.0.0 ∪ 1.1.0
    trying version 1.1.0
    assignment on level 1: Decision bar 1.1.0
    unit propagation on: bar
    deciding on foo: 1.0.0 ∪ 1.1.0
    trying version 1.1.0
    dependency incompatibilities
    (terms: {foo 1.1.0, not bar 2}, cause: dependency foo 1.1.0 -> bar 2)
    not adding decision due to conflict
    unit propagation on: foo
    new assignment on level 1: Derivation not foo 1.1.0 due to incompatibility (terms: {foo 1.1.0, not bar 2}, cause: dependency foo 1.1.0 -> bar 2)
    unit propagation on: foo
    deciding on foo: 1.0.0
    trying version 1.0.0
    assignment on level 2: Decision foo 1.0.0
    unit propagation on: foo
    foo 1.0.0, bar 1.1.0
    |}]

let%expect_test "conflict - circular dependency" =
  solve
    [ ("foo", "2.0.0"); ("foo", "1.0.0"); ("bar", "1.0.0") ]
    [ (("foo", "2.0.0"), ("bar", [ "1.0.0" ])); (("bar", "1.0.0"), ("foo", [ "1.0.0" ])) ]
    [ ("foo", [ "1.0.0"; "2.0.0" ]) ];
  [%expect
    {|
    initial incompatibilities
    (terms: {Root *, not foo 1.0.0 ∪ 2.0.0}, cause: dependency root -> foo 1.0.0 ∪ 2.0.0)
    unit propagation on: Root
    new assignment on level 0: Derivation foo 1.0.0 ∪ 2.0.0 due to incompatibility (terms: {Root *, not foo 1.0.0 ∪ 2.0.0}, cause: dependency root -> foo 1.0.0 ∪ 2.0.0)
    unit propagation on: foo
    deciding on foo: 1.0.0 ∪ 2.0.0
    trying version 2.0.0
    dependency incompatibilities
    (terms: {foo 2.0.0, not bar 1.0.0}, cause: dependency foo 2.0.0 -> bar 1.0.0)
    assignment on level 1: Decision foo 2.0.0
    unit propagation on: foo
    new assignment on level 1: Derivation bar 1.0.0 due to incompatibility (terms: {foo 2.0.0, not bar 1.0.0}, cause: dependency foo 2.0.0 -> bar 1.0.0)
    unit propagation on: bar
    deciding on bar: 1.0.0
    trying version 1.0.0
    dependency incompatibilities
    (terms: {bar 1.0.0, not foo 1.0.0}, cause: dependency bar 1.0.0 -> foo 1.0.0)
    not adding decision due to conflict
    unit propagation on: bar
    conflict resolution on: (terms: {bar 1.0.0, not foo 1.0.0}, cause: dependency bar 1.0.0 -> foo 1.0.0)
    satisfiying assignment on level 1: Derivation bar 1.0.0 due to incompatibility (terms: {foo 2.0.0, not bar 1.0.0}, cause: dependency foo 2.0.0 -> bar 1.0.0)
    prior cause (terms: {foo 2.0.0}, cause: ((terms: {bar 1.0.0, not foo 1.0.0}, cause: dependency bar 1.0.0 -> foo 1.0.0) and (terms: {foo 2.0.0, not bar 1.0.0}, cause: dependency foo 2.0.0 -> bar 1.0.0)))
    conflict resolution on: (terms: {foo 2.0.0}, cause: ((terms: {bar 1.0.0, not foo 1.0.0}, cause: dependency bar 1.0.0 -> foo 1.0.0) and (terms: {foo 2.0.0, not bar 1.0.0}, cause: dependency foo 2.0.0 -> bar 1.0.0)))
    satisfiying assignment on level 1: Decision foo 2.0.0
    backtracking to level 0
    solution: (0: Derivation foo 1.0.0 ∪ 2.0.0 due to incompatibility (terms: {Root *, not foo 1.0.0 ∪ 2.0.0}, cause: dependency root -> foo 1.0.0 ∪ 2.0.0)), (0: Decision root)
    new incompatibility (terms: {foo 2.0.0}, cause: ((terms: {bar 1.0.0, not foo 1.0.0}, cause: dependency bar 1.0.0 -> foo 1.0.0) and (terms: {foo 2.0.0, not bar 1.0.0}, cause: dependency foo 2.0.0 -> bar 1.0.0)))
    new assignment on level 0: Derivation not foo 2.0.0 due to incompatibility (terms: {foo 2.0.0}, cause: ((terms: {bar 1.0.0, not foo 1.0.0}, cause: dependency bar 1.0.0 -> foo 1.0.0) and (terms: {foo 2.0.0, not bar 1.0.0}, cause: dependency foo 2.0.0 -> bar 1.0.0)))
    unit propagation on: foo
    deciding on foo: 1.0.0
    trying version 1.0.0
    assignment on level 1: Decision foo 1.0.0
    unit propagation on: foo
    foo 1.0.0
    |}]

let%expect_test "conflict - partial satisfier" =
  solve
    [
      ("foo", "1.1.0");
      ("foo", "1.0.0");
      ("left", "1.0.0");
      ("right", "1.0.0");
      ("shared", "2.0.0");
      ("shared", "1.0.0");
      ("target", "2.0.0");
      ("target", "1.0.0");
    ]
    [
      (("foo", "1.1.0"), ("left", [ "1.0.0" ]));
      (("foo", "1.1.0"), ("right", [ "1.0.0" ]));
      (("left", "1.0.0"), ("shared", [ "1.0.0"; "2.0.0" ]));
      (("right", "1.0.0"), ("shared", [ "1.0.0" ]));
      (("shared", "1.0.0"), ("target", [ "1.0.0" ]));
    ]
    [ ("foo", [ "1.0.0"; "1.1.0" ]); ("target", [ "2.0.0" ]) ];
  [%expect
    {|
    initial incompatibilities
    (terms: {Root *, not foo 1.0.0 ∪ 1.1.0}, cause: dependency root -> foo 1.0.0 ∪ 1.1.0)
    (terms: {Root *, not target 2.0.0}, cause: dependency root -> target 2.0.0)
    unit propagation on: Root
    new assignment on level 0: Derivation target 2.0.0 due to incompatibility (terms: {Root *, not target 2.0.0}, cause: dependency root -> target 2.0.0)
    new assignment on level 0: Derivation foo 1.0.0 ∪ 1.1.0 due to incompatibility (terms: {Root *, not foo 1.0.0 ∪ 1.1.0}, cause: dependency root -> foo 1.0.0 ∪ 1.1.0)
    unit propagation on: foo
    unit propagation on: target
    deciding on target: 2.0.0
    trying version 2.0.0
    assignment on level 1: Decision target 2.0.0
    unit propagation on: target
    deciding on foo: 1.0.0 ∪ 1.1.0
    trying version 1.1.0
    dependency incompatibilities
    (terms: {foo 1.1.0, not right 1.0.0}, cause: dependency foo 1.1.0 -> right 1.0.0)
    (terms: {foo 1.1.0, not left 1.0.0}, cause: dependency foo 1.1.0 -> left 1.0.0)
    assignment on level 2: Decision foo 1.1.0
    unit propagation on: foo
    new assignment on level 2: Derivation left 1.0.0 due to incompatibility (terms: {foo 1.1.0, not left 1.0.0}, cause: dependency foo 1.1.0 -> left 1.0.0)
    new assignment on level 2: Derivation right 1.0.0 due to incompatibility (terms: {foo 1.1.0, not right 1.0.0}, cause: dependency foo 1.1.0 -> right 1.0.0)
    unit propagation on: right
    unit propagation on: left
    deciding on left: 1.0.0
    trying version 1.0.0
    dependency incompatibilities
    (terms: {left 1.0.0, not shared 1.0.0 ∪ 2.0.0}, cause: dependency left 1.0.0 -> shared 1.0.0 ∪ 2.0.0)
    assignment on level 3: Decision left 1.0.0
    unit propagation on: left
    new assignment on level 3: Derivation shared 1.0.0 ∪ 2.0.0 due to incompatibility (terms: {left 1.0.0, not shared 1.0.0 ∪ 2.0.0}, cause: dependency left 1.0.0 -> shared 1.0.0 ∪ 2.0.0)
    unit propagation on: shared
    deciding on right: 1.0.0
    trying version 1.0.0
    dependency incompatibilities
    (terms: {right 1.0.0, not shared 1.0.0}, cause: dependency right 1.0.0 -> shared 1.0.0)
    assignment on level 4: Decision right 1.0.0
    unit propagation on: right
    new assignment on level 4: Derivation shared 1.0.0 due to incompatibility (terms: {right 1.0.0, not shared 1.0.0}, cause: dependency right 1.0.0 -> shared 1.0.0)
    unit propagation on: shared
    deciding on shared: 1.0.0
    trying version 1.0.0
    dependency incompatibilities
    (terms: {shared 1.0.0, not target 1.0.0}, cause: dependency shared 1.0.0 -> target 1.0.0)
    not adding decision due to conflict
    unit propagation on: shared
    conflict resolution on: (terms: {shared 1.0.0, not target 1.0.0}, cause: dependency shared 1.0.0 -> target 1.0.0)
    satisfiying assignment on level 4: Derivation shared 1.0.0 due to incompatibility (terms: {right 1.0.0, not shared 1.0.0}, cause: dependency right 1.0.0 -> shared 1.0.0)
    backtracking to level 0
    solution: (0: Derivation foo 1.0.0 ∪ 1.1.0 due to incompatibility (terms: {Root *, not foo 1.0.0 ∪ 1.1.0}, cause: dependency root -> foo 1.0.0 ∪ 1.1.0)), (0: Derivation target 2.0.0 due to incompatibility (terms: {Root *, not target 2.0.0}, cause: dependency root -> target 2.0.0)), (0: Decision root)
    new assignment on level 0: Derivation not shared 1.0.0 due to incompatibility (terms: {shared 1.0.0, not target 1.0.0}, cause: dependency shared 1.0.0 -> target 1.0.0)
    unit propagation on: shared
    deciding on target: 2.0.0
    trying version 2.0.0
    assignment on level 1: Decision target 2.0.0
    unit propagation on: target
    deciding on foo: 1.0.0 ∪ 1.1.0
    trying version 1.1.0
    assignment on level 2: Decision foo 1.1.0
    unit propagation on: foo
    new assignment on level 2: Derivation left 1.0.0 due to incompatibility (terms: {foo 1.1.0, not left 1.0.0}, cause: dependency foo 1.1.0 -> left 1.0.0)
    new assignment on level 2: Derivation right 1.0.0 due to incompatibility (terms: {foo 1.1.0, not right 1.0.0}, cause: dependency foo 1.1.0 -> right 1.0.0)
    unit propagation on: right
    conflict resolution on: (terms: {right 1.0.0, not shared 1.0.0}, cause: dependency right 1.0.0 -> shared 1.0.0)
    satisfiying assignment on level 2: Derivation right 1.0.0 due to incompatibility (terms: {foo 1.1.0, not right 1.0.0}, cause: dependency foo 1.1.0 -> right 1.0.0)
    backtracking to level 0
    solution: (0: Derivation not shared 1.0.0 due to incompatibility (terms: {shared 1.0.0, not target 1.0.0}, cause: dependency shared 1.0.0 -> target 1.0.0)), (0: Derivation foo 1.0.0 ∪ 1.1.0 due to incompatibility (terms: {Root *, not foo 1.0.0 ∪ 1.1.0}, cause: dependency root -> foo 1.0.0 ∪ 1.1.0)), (0: Derivation target 2.0.0 due to incompatibility (terms: {Root *, not target 2.0.0}, cause: dependency root -> target 2.0.0)), (0: Decision root)
    new assignment on level 0: Derivation not right 1.0.0 due to incompatibility (terms: {right 1.0.0, not shared 1.0.0}, cause: dependency right 1.0.0 -> shared 1.0.0)
    unit propagation on: right
    new assignment on level 0: Derivation not foo 1.1.0 due to incompatibility (terms: {foo 1.1.0, not right 1.0.0}, cause: dependency foo 1.1.0 -> right 1.0.0)
    unit propagation on: foo
    deciding on foo: 1.0.0
    trying version 1.0.0
    assignment on level 1: Decision foo 1.0.0
    unit propagation on: foo
    deciding on target: 2.0.0
    trying version 2.0.0
    assignment on level 2: Decision target 2.0.0
    unit propagation on: target
    target 2.0.0, foo 1.0.0
    |}]

let%expect_test "linear error" =
  solve
    [ ("foo", "1.0.0"); ("bar", "2.0.0"); ("baz", "1.0.0"); ("baz", "3.0.0") ]
    [ (("foo", "1.0.0"), ("bar", [ "2.0.0" ])); (("bar", "2.0.0"), ("baz", [ "3.0.0" ])) ]
    [ ("foo", [ "1.0.0" ]); ("baz", [ "1.0.0" ]) ];
  [%expect
    {|
    initial incompatibilities
    (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)
    (terms: {Root *, not baz 1.0.0}, cause: dependency root -> baz 1.0.0)
    unit propagation on: Root
    new assignment on level 0: Derivation baz 1.0.0 due to incompatibility (terms: {Root *, not baz 1.0.0}, cause: dependency root -> baz 1.0.0)
    new assignment on level 0: Derivation foo 1.0.0 due to incompatibility (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)
    unit propagation on: foo
    unit propagation on: baz
    deciding on baz: 1.0.0
    trying version 1.0.0
    assignment on level 1: Decision baz 1.0.0
    unit propagation on: baz
    deciding on foo: 1.0.0
    trying version 1.0.0
    dependency incompatibilities
    (terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0)
    assignment on level 2: Decision foo 1.0.0
    unit propagation on: foo
    new assignment on level 2: Derivation bar 2.0.0 due to incompatibility (terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0)
    unit propagation on: bar
    deciding on bar: 2.0.0
    trying version 2.0.0
    dependency incompatibilities
    (terms: {bar 2.0.0, not baz 3.0.0}, cause: dependency bar 2.0.0 -> baz 3.0.0)
    not adding decision due to conflict
    unit propagation on: bar
    conflict resolution on: (terms: {bar 2.0.0, not baz 3.0.0}, cause: dependency bar 2.0.0 -> baz 3.0.0)
    satisfiying assignment on level 2: Derivation bar 2.0.0 due to incompatibility (terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0)
    backtracking to level 0
    solution: (0: Derivation foo 1.0.0 due to incompatibility (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)), (0: Derivation baz 1.0.0 due to incompatibility (terms: {Root *, not baz 1.0.0}, cause: dependency root -> baz 1.0.0)), (0: Decision root)
    new assignment on level 0: Derivation not bar 2.0.0 due to incompatibility (terms: {bar 2.0.0, not baz 3.0.0}, cause: dependency bar 2.0.0 -> baz 3.0.0)
    unit propagation on: bar
    conflict resolution on: (terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0)
    satisfiying assignment on level 0: Derivation not bar 2.0.0 due to incompatibility (terms: {bar 2.0.0, not baz 3.0.0}, cause: dependency bar 2.0.0 -> baz 3.0.0)
    prior cause (terms: {not baz 3.0.0, foo 1.0.0}, cause: ((terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0) and (terms: {bar 2.0.0, not baz 3.0.0}, cause: dependency bar 2.0.0 -> baz 3.0.0)))
    conflict resolution on: (terms: {not baz 3.0.0, foo 1.0.0}, cause: ((terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0) and (terms: {bar 2.0.0, not baz 3.0.0}, cause: dependency bar 2.0.0 -> baz 3.0.0)))
    satisfiying assignment on level 0: Derivation foo 1.0.0 due to incompatibility (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)
    prior cause (terms: {not baz 3.0.0}, cause: ((terms: {not baz 3.0.0, foo 1.0.0}, cause: ((terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0) and (terms: {bar 2.0.0, not baz 3.0.0}, cause: dependency bar 2.0.0 -> baz 3.0.0))) and (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)))
    conflict resolution on: (terms: {not baz 3.0.0}, cause: ((terms: {not baz 3.0.0, foo 1.0.0}, cause: ((terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0) and (terms: {bar 2.0.0, not baz 3.0.0}, cause: dependency bar 2.0.0 -> baz 3.0.0))) and (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)))
    satisfiying assignment on level 0: Derivation baz 1.0.0 due to incompatibility (terms: {Root *, not baz 1.0.0}, cause: dependency root -> baz 1.0.0)
    prior cause (terms: {Root *}, cause: ((terms: {not baz 3.0.0}, cause: ((terms: {not baz 3.0.0, foo 1.0.0}, cause: ((terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0) and (terms: {bar 2.0.0, not baz 3.0.0}, cause: dependency bar 2.0.0 -> baz 3.0.0))) and (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0))) and (terms: {Root *, not baz 1.0.0}, cause: dependency root -> baz 1.0.0)))
    conflict resolution on: (terms: {Root *}, cause: ((terms: {not baz 3.0.0}, cause: ((terms: {not baz 3.0.0, foo 1.0.0}, cause: ((terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0) and (terms: {bar 2.0.0, not baz 3.0.0}, cause: dependency bar 2.0.0 -> baz 3.0.0))) and (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0))) and (terms: {Root *, not baz 1.0.0}, cause: dependency root -> baz 1.0.0)))
    Because foo 1.0.0 -> bar 2.0.0 and bar 2.0.0 -> baz 3.0.0, foo 1.0.0 requires baz 3.0.0.
    And because root -> foo 1.0.0 and root -> baz 1.0.0, version solving failed.
    |}]

let%expect_test "branching error" =
  solve
    [
      ("foo", "1.0.0");
      ("foo", "1.1.0");
      ("a", "1.0.0");
      ("b", "1.0.0");
      ("b", "2.0.0");
      ("x", "1.0.0");
      ("y", "1.0.0");
      ("y", "2.0.0");
    ]
    [
      (("foo", "1.0.0"), ("a", [ "1.0.0" ]));
      (("foo", "1.0.0"), ("b", [ "1.0.0" ]));
      (("foo", "1.1.0"), ("x", [ "1.0.0" ]));
      (("foo", "1.1.0"), ("y", [ "1.0.0" ]));
      (("a", "1.0.0"), ("b", [ "2.0.0" ]));
      (("x", "1.0.0"), ("y", [ "2.0.0" ]));
    ]
    [ ("foo", [ "1.0.0" ]) ];
  [%expect
    {|
    initial incompatibilities
    (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)
    unit propagation on: Root
    new assignment on level 0: Derivation foo 1.0.0 due to incompatibility (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)
    unit propagation on: foo
    deciding on foo: 1.0.0
    trying version 1.0.0
    dependency incompatibilities
    (terms: {foo 1.0.0, not b 1.0.0}, cause: dependency foo 1.0.0 -> b 1.0.0)
    (terms: {foo 1.0.0, not a 1.0.0}, cause: dependency foo 1.0.0 -> a 1.0.0)
    assignment on level 1: Decision foo 1.0.0
    unit propagation on: foo
    new assignment on level 1: Derivation a 1.0.0 due to incompatibility (terms: {foo 1.0.0, not a 1.0.0}, cause: dependency foo 1.0.0 -> a 1.0.0)
    new assignment on level 1: Derivation b 1.0.0 due to incompatibility (terms: {foo 1.0.0, not b 1.0.0}, cause: dependency foo 1.0.0 -> b 1.0.0)
    unit propagation on: b
    unit propagation on: a
    deciding on a: 1.0.0
    trying version 1.0.0
    dependency incompatibilities
    (terms: {a 1.0.0, not b 2.0.0}, cause: dependency a 1.0.0 -> b 2.0.0)
    not adding decision due to conflict
    unit propagation on: a
    conflict resolution on: (terms: {a 1.0.0, not b 2.0.0}, cause: dependency a 1.0.0 -> b 2.0.0)
    satisfiying assignment on level 1: Derivation b 1.0.0 due to incompatibility (terms: {foo 1.0.0, not b 1.0.0}, cause: dependency foo 1.0.0 -> b 1.0.0)
    prior cause (terms: {foo 1.0.0, a 1.0.0}, cause: ((terms: {a 1.0.0, not b 2.0.0}, cause: dependency a 1.0.0 -> b 2.0.0) and (terms: {foo 1.0.0, not b 1.0.0}, cause: dependency foo 1.0.0 -> b 1.0.0)))
    conflict resolution on: (terms: {foo 1.0.0, a 1.0.0}, cause: ((terms: {a 1.0.0, not b 2.0.0}, cause: dependency a 1.0.0 -> b 2.0.0) and (terms: {foo 1.0.0, not b 1.0.0}, cause: dependency foo 1.0.0 -> b 1.0.0)))
    satisfiying assignment on level 1: Derivation a 1.0.0 due to incompatibility (terms: {foo 1.0.0, not a 1.0.0}, cause: dependency foo 1.0.0 -> a 1.0.0)
    backtracking to level 0
    solution: (0: Derivation foo 1.0.0 due to incompatibility (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)), (0: Decision root)
    new incompatibility (terms: {foo 1.0.0, a 1.0.0}, cause: ((terms: {a 1.0.0, not b 2.0.0}, cause: dependency a 1.0.0 -> b 2.0.0) and (terms: {foo 1.0.0, not b 1.0.0}, cause: dependency foo 1.0.0 -> b 1.0.0)))
    new assignment on level 0: Derivation not a 1.0.0 due to incompatibility (terms: {foo 1.0.0, a 1.0.0}, cause: ((terms: {a 1.0.0, not b 2.0.0}, cause: dependency a 1.0.0 -> b 2.0.0) and (terms: {foo 1.0.0, not b 1.0.0}, cause: dependency foo 1.0.0 -> b 1.0.0)))
    unit propagation on: a
    conflict resolution on: (terms: {foo 1.0.0, not a 1.0.0}, cause: dependency foo 1.0.0 -> a 1.0.0)
    satisfiying assignment on level 0: Derivation not a 1.0.0 due to incompatibility (terms: {foo 1.0.0, a 1.0.0}, cause: ((terms: {a 1.0.0, not b 2.0.0}, cause: dependency a 1.0.0 -> b 2.0.0) and (terms: {foo 1.0.0, not b 1.0.0}, cause: dependency foo 1.0.0 -> b 1.0.0)))
    prior cause (terms: {foo 1.0.0}, cause: ((terms: {foo 1.0.0, not a 1.0.0}, cause: dependency foo 1.0.0 -> a 1.0.0) and (terms: {foo 1.0.0, a 1.0.0}, cause: ((terms: {a 1.0.0, not b 2.0.0}, cause: dependency a 1.0.0 -> b 2.0.0) and (terms: {foo 1.0.0, not b 1.0.0}, cause: dependency foo 1.0.0 -> b 1.0.0)))))
    conflict resolution on: (terms: {foo 1.0.0}, cause: ((terms: {foo 1.0.0, not a 1.0.0}, cause: dependency foo 1.0.0 -> a 1.0.0) and (terms: {foo 1.0.0, a 1.0.0}, cause: ((terms: {a 1.0.0, not b 2.0.0}, cause: dependency a 1.0.0 -> b 2.0.0) and (terms: {foo 1.0.0, not b 1.0.0}, cause: dependency foo 1.0.0 -> b 1.0.0)))))
    satisfiying assignment on level 0: Derivation foo 1.0.0 due to incompatibility (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)
    prior cause (terms: {Root *}, cause: ((terms: {foo 1.0.0}, cause: ((terms: {foo 1.0.0, not a 1.0.0}, cause: dependency foo 1.0.0 -> a 1.0.0) and (terms: {foo 1.0.0, a 1.0.0}, cause: ((terms: {a 1.0.0, not b 2.0.0}, cause: dependency a 1.0.0 -> b 2.0.0) and (terms: {foo 1.0.0, not b 1.0.0}, cause: dependency foo 1.0.0 -> b 1.0.0))))) and (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)))
    conflict resolution on: (terms: {Root *}, cause: ((terms: {foo 1.0.0}, cause: ((terms: {foo 1.0.0, not a 1.0.0}, cause: dependency foo 1.0.0 -> a 1.0.0) and (terms: {foo 1.0.0, a 1.0.0}, cause: ((terms: {a 1.0.0, not b 2.0.0}, cause: dependency a 1.0.0 -> b 2.0.0) and (terms: {foo 1.0.0, not b 1.0.0}, cause: dependency foo 1.0.0 -> b 1.0.0))))) and (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)))
    Because a 1.0.0 -> b 2.0.0 and foo 1.0.0 -> b 1.0.0, foo 1.0.0 or a 1.0.0 is forbidden.
    And because foo 1.0.0 -> a 1.0.0 and root -> foo 1.0.0, version solving failed.
    |}]

let%expect_test "partial satisfier - joint constraints" =
  solve
    [
      ("a", "2");
      ("a", "1");
      ("z", "1");
      ("z", "2");
      ("z", "3");
      ("z", "4");
      ("b", "1");
      ("b", "2");
      ("c", "1");
      ("c", "2");
    ]
    [
      (("a", "2"), ("z", [ "1"; "2"; "3" ]));
      (("a", "2"), ("z", [ "2"; "3"; "4" ]));
      (("z", "2"), ("b", [ "2" ]));
      (("z", "3"), ("c", [ "2" ]));
    ]
    [ ("a", [ "1"; "2" ]); ("b", [ "1" ]); ("c", [ "1" ]) ];
  [%expect
    {|
    initial incompatibilities
    (terms: {Root *, not a 1 ∪ 2}, cause: dependency root -> a 1 ∪ 2)
    (terms: {Root *, not b 1}, cause: dependency root -> b 1)
    (terms: {Root *, not c 1}, cause: dependency root -> c 1)
    unit propagation on: Root
    new assignment on level 0: Derivation c 1 due to incompatibility (terms: {Root *, not c 1}, cause: dependency root -> c 1)
    new assignment on level 0: Derivation b 1 due to incompatibility (terms: {Root *, not b 1}, cause: dependency root -> b 1)
    new assignment on level 0: Derivation a 1 ∪ 2 due to incompatibility (terms: {Root *, not a 1 ∪ 2}, cause: dependency root -> a 1 ∪ 2)
    unit propagation on: a
    unit propagation on: b
    unit propagation on: c
    deciding on b: 1
    trying version 1
    assignment on level 1: Decision b 1
    unit propagation on: b
    deciding on c: 1
    trying version 1
    assignment on level 2: Decision c 1
    unit propagation on: c
    deciding on a: 1 ∪ 2
    trying version 2
    dependency incompatibilities
    (terms: {a 2, not z 2 ∪ 3 ∪ 4}, cause: dependency a 2 -> z 2 ∪ 3 ∪ 4)
    (terms: {a 2, not z 1 ∪ 2 ∪ 3}, cause: dependency a 2 -> z 1 ∪ 2 ∪ 3)
    assignment on level 3: Decision a 2
    unit propagation on: a
    new assignment on level 3: Derivation z 1 ∪ 2 ∪ 3 due to incompatibility (terms: {a 2, not z 1 ∪ 2 ∪ 3}, cause: dependency a 2 -> z 1 ∪ 2 ∪ 3)
    new assignment on level 3: Derivation z 2 ∪ 3 ∪ 4 due to incompatibility (terms: {a 2, not z 2 ∪ 3 ∪ 4}, cause: dependency a 2 -> z 2 ∪ 3 ∪ 4)
    unit propagation on: z
    unit propagation on: z
    deciding on z: 2 ∪ 3
    trying version 3
    dependency incompatibilities
    (terms: {z 3, not c 2}, cause: dependency z 3 -> c 2)
    not adding decision due to conflict
    unit propagation on: z
    new assignment on level 3: Derivation not z 3 due to incompatibility (terms: {z 3, not c 2}, cause: dependency z 3 -> c 2)
    unit propagation on: z
    deciding on z: 2
    trying version 2
    dependency incompatibilities
    (terms: {z 2, not b 2}, cause: dependency z 2 -> b 2)
    not adding decision due to conflict
    unit propagation on: z
    conflict resolution on: (terms: {z 2, not b 2}, cause: dependency z 2 -> b 2)
    satisfiying assignment on level 3: Derivation not z 3 due to incompatibility (terms: {z 3, not c 2}, cause: dependency z 3 -> c 2)
    prior cause (terms: {z 2 ∪ 3, not b 2, not c 2}, cause: ((terms: {z 2, not b 2}, cause: dependency z 2 -> b 2) and (terms: {z 3, not c 2}, cause: dependency z 3 -> c 2)))
    conflict resolution on: (terms: {z 2 ∪ 3, not b 2, not c 2}, cause: ((terms: {z 2, not b 2}, cause: dependency z 2 -> b 2) and (terms: {z 3, not c 2}, cause: dependency z 3 -> c 2)))
    satisfiying assignment on level 3: Derivation z 2 ∪ 3 ∪ 4 due to incompatibility (terms: {a 2, not z 2 ∪ 3 ∪ 4}, cause: dependency a 2 -> z 2 ∪ 3 ∪ 4)
    prior cause (terms: {not z 4, not b 2, not c 2, a 2}, cause: ((terms: {z 2 ∪ 3, not b 2, not c 2}, cause: ((terms: {z 2, not b 2}, cause: dependency z 2 -> b 2) and (terms: {z 3, not c 2}, cause: dependency z 3 -> c 2))) and (terms: {a 2, not z 2 ∪ 3 ∪ 4}, cause: dependency a 2 -> z 2 ∪ 3 ∪ 4)))
    conflict resolution on: (terms: {not z 4, not b 2, not c 2, a 2}, cause: ((terms: {z 2 ∪ 3, not b 2, not c 2}, cause: ((terms: {z 2, not b 2}, cause: dependency z 2 -> b 2) and (terms: {z 3, not c 2}, cause: dependency z 3 -> c 2))) and (terms: {a 2, not z 2 ∪ 3 ∪ 4}, cause: dependency a 2 -> z 2 ∪ 3 ∪ 4)))
    satisfiying assignment on level 3: Derivation z 1 ∪ 2 ∪ 3 due to incompatibility (terms: {a 2, not z 1 ∪ 2 ∪ 3}, cause: dependency a 2 -> z 1 ∪ 2 ∪ 3)
    prior cause (terms: {not b 2, not c 2, a 2}, cause: ((terms: {not z 4, not b 2, not c 2, a 2}, cause: ((terms: {z 2 ∪ 3, not b 2, not c 2}, cause: ((terms: {z 2, not b 2}, cause: dependency z 2 -> b 2) and (terms: {z 3, not c 2}, cause: dependency z 3 -> c 2))) and (terms: {a 2, not z 2 ∪ 3 ∪ 4}, cause: dependency a 2 -> z 2 ∪ 3 ∪ 4))) and (terms: {a 2, not z 1 ∪ 2 ∪ 3}, cause: dependency a 2 -> z 1 ∪ 2 ∪ 3)))
    conflict resolution on: (terms: {not b 2, not c 2, a 2}, cause: ((terms: {not z 4, not b 2, not c 2, a 2}, cause: ((terms: {z 2 ∪ 3, not b 2, not c 2}, cause: ((terms: {z 2, not b 2}, cause: dependency z 2 -> b 2) and (terms: {z 3, not c 2}, cause: dependency z 3 -> c 2))) and (terms: {a 2, not z 2 ∪ 3 ∪ 4}, cause: dependency a 2 -> z 2 ∪ 3 ∪ 4))) and (terms: {a 2, not z 1 ∪ 2 ∪ 3}, cause: dependency a 2 -> z 1 ∪ 2 ∪ 3)))
    satisfiying assignment on level 3: Decision a 2
    backtracking to level 0
    solution: (0: Derivation a 1 ∪ 2 due to incompatibility (terms: {Root *, not a 1 ∪ 2}, cause: dependency root -> a 1 ∪ 2)), (0: Derivation b 1 due to incompatibility (terms: {Root *, not b 1}, cause: dependency root -> b 1)), (0: Derivation c 1 due to incompatibility (terms: {Root *, not c 1}, cause: dependency root -> c 1)), (0: Decision root)
    new incompatibility (terms: {not b 2, not c 2, a 2}, cause: ((terms: {not z 4, not b 2, not c 2, a 2}, cause: ((terms: {z 2 ∪ 3, not b 2, not c 2}, cause: ((terms: {z 2, not b 2}, cause: dependency z 2 -> b 2) and (terms: {z 3, not c 2}, cause: dependency z 3 -> c 2))) and (terms: {a 2, not z 2 ∪ 3 ∪ 4}, cause: dependency a 2 -> z 2 ∪ 3 ∪ 4))) and (terms: {a 2, not z 1 ∪ 2 ∪ 3}, cause: dependency a 2 -> z 1 ∪ 2 ∪ 3)))
    new assignment on level 0: Derivation not a 2 due to incompatibility (terms: {not b 2, not c 2, a 2}, cause: ((terms: {not z 4, not b 2, not c 2, a 2}, cause: ((terms: {z 2 ∪ 3, not b 2, not c 2}, cause: ((terms: {z 2, not b 2}, cause: dependency z 2 -> b 2) and (terms: {z 3, not c 2}, cause: dependency z 3 -> c 2))) and (terms: {a 2, not z 2 ∪ 3 ∪ 4}, cause: dependency a 2 -> z 2 ∪ 3 ∪ 4))) and (terms: {a 2, not z 1 ∪ 2 ∪ 3}, cause: dependency a 2 -> z 1 ∪ 2 ∪ 3)))
    unit propagation on: a
    deciding on a: 1
    trying version 1
    assignment on level 1: Decision a 1
    unit propagation on: a
    deciding on b: 1
    trying version 1
    assignment on level 2: Decision b 1
    unit propagation on: b
    deciding on c: 1
    trying version 1
    assignment on level 3: Decision c 1
    unit propagation on: c
    c 1, b 1, a 1
    |}]

let%expect_test "shared dependency - collapsing" =
  solve
    [ ("a", "2"); ("a", "1"); ("b", "1") ]
    [ (("a", "2"), ("b", [ "1" ])); (("a", "1"), ("b", [ "1" ])) ]
    [ ("a", [ "1"; "2" ]) ];
  [%expect
    {|
    initial incompatibilities
    (terms: {Root *, not a 1 ∪ 2}, cause: dependency root -> a 1 ∪ 2)
    unit propagation on: Root
    new assignment on level 0: Derivation a 1 ∪ 2 due to incompatibility (terms: {Root *, not a 1 ∪ 2}, cause: dependency root -> a 1 ∪ 2)
    unit propagation on: a
    deciding on a: 1 ∪ 2
    trying version 2
    dependency incompatibilities
    (terms: {a 1 ∪ 2, not b 1}, cause: dependency a 2 -> b 1)
    assignment on level 1: Decision a 2
    unit propagation on: a
    new assignment on level 1: Derivation b 1 due to incompatibility (terms: {a 1 ∪ 2, not b 1}, cause: dependency a 2 -> b 1)
    unit propagation on: b
    deciding on b: 1
    trying version 1
    assignment on level 2: Decision b 1
    unit propagation on: b
    b 1, a 2
    |}]

(* An empty dependency range is unsatisfiable, so foo cannot be selected. *)
let%expect_test "unsatisfiable dependency - empty range" =
  solve
    [ ("foo", "1.0.0"); ("bar", "1.0.0") ]
    [ (("foo", "1.0.0"), ("bar", [])) ]
    [ ("foo", [ "1.0.0" ]) ];
  [%expect
    {|
    initial incompatibilities
    (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)
    unit propagation on: Root
    new assignment on level 0: Derivation foo 1.0.0 due to incompatibility (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)
    unit propagation on: foo
    deciding on foo: 1.0.0
    trying version 1.0.0
    dependency incompatibilities
    (terms: {foo 1.0.0}, cause: dependency foo 1.0.0 -> bar ∅)
    not adding decision due to conflict
    unit propagation on: foo
    conflict resolution on: (terms: {foo 1.0.0}, cause: dependency foo 1.0.0 -> bar ∅)
    satisfiying assignment on level 0: Derivation foo 1.0.0 due to incompatibility (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)
    prior cause (terms: {Root *}, cause: ((terms: {foo 1.0.0}, cause: dependency foo 1.0.0 -> bar ∅) and (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)))
    conflict resolution on: (terms: {Root *}, cause: ((terms: {foo 1.0.0}, cause: dependency foo 1.0.0 -> bar ∅) and (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)))
    Because foo 1.0.0 -> bar ∅ and root -> foo 1.0.0, version solving failed.
    |}]

(* Likewise for an empty range in the query itself. *)
let%expect_test "unsatisfiable root dependency - empty range" =
  solve [ ("foo", "1.0.0") ] [] [ ("foo", []) ];
  [%expect
    {|
    initial incompatibilities
    (terms: {Root *}, cause: dependency root -> foo ∅)
    unit propagation on: Root
    conflict resolution on: (terms: {Root *}, cause: dependency root -> foo ∅)
    root -> foo ∅
    |}]

let%expect_test "no versions - missing dependency version" =
  solve
    [ ("foo", "1.0.0"); ("bar", "1.0.0") ]
    [ (("foo", "1.0.0"), ("bar", [ "2.0.0" ])) ]
    [ ("foo", [ "1.0.0" ]) ];
  [%expect
    {|
    initial incompatibilities
    (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)
    unit propagation on: Root
    new assignment on level 0: Derivation foo 1.0.0 due to incompatibility (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)
    unit propagation on: foo
    deciding on foo: 1.0.0
    trying version 1.0.0
    dependency incompatibilities
    (terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0)
    assignment on level 1: Decision foo 1.0.0
    unit propagation on: foo
    new assignment on level 1: Derivation bar 2.0.0 due to incompatibility (terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0)
    unit propagation on: bar
    deciding on bar: 2.0.0
    no versions found, adding incompatiblity (terms: {bar 2.0.0}, cause: no versions)
    unit propagation on: bar
    conflict resolution on: (terms: {bar 2.0.0}, cause: no versions)
    satisfiying assignment on level 1: Derivation bar 2.0.0 due to incompatibility (terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0)
    backtracking to level 0
    solution: (0: Derivation foo 1.0.0 due to incompatibility (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)), (0: Decision root)
    new assignment on level 0: Derivation not bar 2.0.0 due to incompatibility (terms: {bar 2.0.0}, cause: no versions)
    unit propagation on: bar
    conflict resolution on: (terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0)
    satisfiying assignment on level 0: Derivation not bar 2.0.0 due to incompatibility (terms: {bar 2.0.0}, cause: no versions)
    prior cause (terms: {foo 1.0.0}, cause: ((terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0) and (terms: {bar 2.0.0}, cause: no versions)))
    conflict resolution on: (terms: {foo 1.0.0}, cause: ((terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0) and (terms: {bar 2.0.0}, cause: no versions)))
    satisfiying assignment on level 0: Derivation foo 1.0.0 due to incompatibility (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)
    prior cause (terms: {Root *}, cause: ((terms: {foo 1.0.0}, cause: ((terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0) and (terms: {bar 2.0.0}, cause: no versions))) and (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)))
    conflict resolution on: (terms: {Root *}, cause: ((terms: {foo 1.0.0}, cause: ((terms: {foo 1.0.0, not bar 2.0.0}, cause: dependency foo 1.0.0 -> bar 2.0.0) and (terms: {bar 2.0.0}, cause: no versions))) and (terms: {Root *, not foo 1.0.0}, cause: dependency root -> foo 1.0.0)))
    Because foo 1.0.0 -> bar 2.0.0 and no versions of bar match 2.0.0, foo 1.0.0 is forbidden.
    And because root -> foo 1.0.0, version solving failed.
    |}]

(* [opt] is only required by foo 2, and both its versions dead-end. Ruling out
   opt 2 derives "not opt [2, +∞)", which then satisfies "opt (-∞, 2)" only
   partially; generalising opt away loses the foo 1 solution. *)
let%expect_test "conflict - negative satisfier of a positive term" =
  solve
    [
      ("foo", "1");
      ("foo", "2");
      ("opt", "1");
      ("opt", "2");
      ("mid", "1");
      ("bar", "1");
      ("bar", "2");
      ("baz", "1");
      ("baz", "2");
    ]
    [
      (("foo", "2"), ("opt", [ "1"; "2" ]));
      (("opt", "2"), ("bar", [ "1" ]));
      (("opt", "1"), ("mid", [ "1" ]));
      (("mid", "1"), ("baz", [ "2" ]));
    ]
    [ ("foo", [ "1"; "2" ]); ("baz", [ "1" ]); ("bar", [ "2" ]) ];
  [%expect
    {|
    initial incompatibilities
    (terms: {Root *, not foo 1 ∪ 2}, cause: dependency root -> foo 1 ∪ 2)
    (terms: {Root *, not baz 1}, cause: dependency root -> baz 1)
    (terms: {Root *, not bar 2}, cause: dependency root -> bar 2)
    unit propagation on: Root
    new assignment on level 0: Derivation bar 2 due to incompatibility (terms: {Root *, not bar 2}, cause: dependency root -> bar 2)
    new assignment on level 0: Derivation baz 1 due to incompatibility (terms: {Root *, not baz 1}, cause: dependency root -> baz 1)
    new assignment on level 0: Derivation foo 1 ∪ 2 due to incompatibility (terms: {Root *, not foo 1 ∪ 2}, cause: dependency root -> foo 1 ∪ 2)
    unit propagation on: foo
    unit propagation on: baz
    unit propagation on: bar
    deciding on bar: 2
    trying version 2
    assignment on level 1: Decision bar 2
    unit propagation on: bar
    deciding on baz: 1
    trying version 1
    assignment on level 2: Decision baz 1
    unit propagation on: baz
    deciding on foo: 1 ∪ 2
    trying version 2
    dependency incompatibilities
    (terms: {foo 2, not opt 1 ∪ 2}, cause: dependency foo 2 -> opt 1 ∪ 2)
    assignment on level 3: Decision foo 2
    unit propagation on: foo
    new assignment on level 3: Derivation opt 1 ∪ 2 due to incompatibility (terms: {foo 2, not opt 1 ∪ 2}, cause: dependency foo 2 -> opt 1 ∪ 2)
    unit propagation on: opt
    deciding on opt: 1 ∪ 2
    trying version 2
    dependency incompatibilities
    (terms: {opt 2, not bar 1}, cause: dependency opt 2 -> bar 1)
    not adding decision due to conflict
    unit propagation on: opt
    new assignment on level 3: Derivation not opt 2 due to incompatibility (terms: {opt 2, not bar 1}, cause: dependency opt 2 -> bar 1)
    unit propagation on: opt
    deciding on opt: 1
    trying version 1
    dependency incompatibilities
    (terms: {opt 1, not mid 1}, cause: dependency opt 1 -> mid 1)
    assignment on level 4: Decision opt 1
    unit propagation on: opt
    new assignment on level 4: Derivation mid 1 due to incompatibility (terms: {opt 1, not mid 1}, cause: dependency opt 1 -> mid 1)
    unit propagation on: mid
    deciding on mid: 1
    trying version 1
    dependency incompatibilities
    (terms: {mid 1, not baz 2}, cause: dependency mid 1 -> baz 2)
    not adding decision due to conflict
    unit propagation on: mid
    conflict resolution on: (terms: {mid 1, not baz 2}, cause: dependency mid 1 -> baz 2)
    satisfiying assignment on level 4: Derivation mid 1 due to incompatibility (terms: {opt 1, not mid 1}, cause: dependency opt 1 -> mid 1)
    backtracking to level 0
    solution: (0: Derivation foo 1 ∪ 2 due to incompatibility (terms: {Root *, not foo 1 ∪ 2}, cause: dependency root -> foo 1 ∪ 2)), (0: Derivation baz 1 due to incompatibility (terms: {Root *, not baz 1}, cause: dependency root -> baz 1)), (0: Derivation bar 2 due to incompatibility (terms: {Root *, not bar 2}, cause: dependency root -> bar 2)), (0: Decision root)
    new assignment on level 0: Derivation not mid 1 due to incompatibility (terms: {mid 1, not baz 2}, cause: dependency mid 1 -> baz 2)
    unit propagation on: mid
    deciding on bar: 2
    trying version 2
    assignment on level 1: Decision bar 2
    unit propagation on: bar
    deciding on baz: 1
    trying version 1
    assignment on level 2: Decision baz 1
    unit propagation on: baz
    deciding on foo: 1 ∪ 2
    trying version 2
    assignment on level 3: Decision foo 2
    unit propagation on: foo
    new assignment on level 3: Derivation opt 1 ∪ 2 due to incompatibility (terms: {foo 2, not opt 1 ∪ 2}, cause: dependency foo 2 -> opt 1 ∪ 2)
    unit propagation on: opt
    new assignment on level 3: Derivation not opt 1 due to incompatibility (terms: {opt 1, not mid 1}, cause: dependency opt 1 -> mid 1)
    conflict resolution on: (terms: {opt 2, not bar 1}, cause: dependency opt 2 -> bar 1)
    satisfiying assignment on level 3: Derivation not opt 1 due to incompatibility (terms: {opt 1, not mid 1}, cause: dependency opt 1 -> mid 1)
    prior cause (terms: {not bar 1, not mid 1, opt 1 ∪ 2}, cause: ((terms: {opt 2, not bar 1}, cause: dependency opt 2 -> bar 1) and (terms: {opt 1, not mid 1}, cause: dependency opt 1 -> mid 1)))
    conflict resolution on: (terms: {not bar 1, not mid 1, opt 1 ∪ 2}, cause: ((terms: {opt 2, not bar 1}, cause: dependency opt 2 -> bar 1) and (terms: {opt 1, not mid 1}, cause: dependency opt 1 -> mid 1)))
    satisfiying assignment on level 3: Derivation opt 1 ∪ 2 due to incompatibility (terms: {foo 2, not opt 1 ∪ 2}, cause: dependency foo 2 -> opt 1 ∪ 2)
    backtracking to level 0
    solution: (0: Derivation not mid 1 due to incompatibility (terms: {mid 1, not baz 2}, cause: dependency mid 1 -> baz 2)), (0: Derivation foo 1 ∪ 2 due to incompatibility (terms: {Root *, not foo 1 ∪ 2}, cause: dependency root -> foo 1 ∪ 2)), (0: Derivation baz 1 due to incompatibility (terms: {Root *, not baz 1}, cause: dependency root -> baz 1)), (0: Derivation bar 2 due to incompatibility (terms: {Root *, not bar 2}, cause: dependency root -> bar 2)), (0: Decision root)
    new incompatibility (terms: {not bar 1, not mid 1, opt 1 ∪ 2}, cause: ((terms: {opt 2, not bar 1}, cause: dependency opt 2 -> bar 1) and (terms: {opt 1, not mid 1}, cause: dependency opt 1 -> mid 1)))
    new assignment on level 0: Derivation not opt 1 ∪ 2 due to incompatibility (terms: {not bar 1, not mid 1, opt 1 ∪ 2}, cause: ((terms: {opt 2, not bar 1}, cause: dependency opt 2 -> bar 1) and (terms: {opt 1, not mid 1}, cause: dependency opt 1 -> mid 1)))
    unit propagation on: opt
    new assignment on level 0: Derivation not foo 2 due to incompatibility (terms: {foo 2, not opt 1 ∪ 2}, cause: dependency foo 2 -> opt 1 ∪ 2)
    unit propagation on: foo
    deciding on bar: 2
    trying version 2
    assignment on level 1: Decision bar 2
    unit propagation on: bar
    deciding on baz: 1
    trying version 1
    assignment on level 2: Decision baz 1
    unit propagation on: baz
    deciding on foo: 1
    trying version 1
    assignment on level 3: Decision foo 1
    unit propagation on: foo
    foo 1, baz 1, bar 2
    |}]

(* Reading {Root *, not foo *} as contradicted before anything is assigned
   leaves nothing to propagate, and solving returns the empty solution. *)
let%expect_test "unconstrained root dependency" =
  solve_ranges [ ("foo", "1"); ("foo", "2") ] [] [ ("foo", Solver.Ranges.full) ];
  [%expect
    {|
    initial incompatibilities
    (terms: {Root *, not foo *}, cause: dependency root -> foo *)
    unit propagation on: Root
    new assignment on level 0: Derivation foo * due to incompatibility (terms: {Root *, not foo *}, cause: dependency root -> foo *)
    unit propagation on: foo
    deciding on foo: *
    trying version 2
    assignment on level 1: Decision foo 2
    unit propagation on: foo
    foo 2
    |}]

(* Same defect one level down: bar is still required, whatever its version. *)
let%expect_test "unconstrained dependency" =
  solve_ranges
    [ ("foo", "1"); ("bar", "1"); ("bar", "2") ]
    [ (("foo", "1"), ("bar", Solver.Ranges.full)) ]
    [ ("foo", Solver.Ranges.of_list [ "1" ]) ];
  [%expect
    {|
    initial incompatibilities
    (terms: {Root *, not foo 1}, cause: dependency root -> foo 1)
    unit propagation on: Root
    new assignment on level 0: Derivation foo 1 due to incompatibility (terms: {Root *, not foo 1}, cause: dependency root -> foo 1)
    unit propagation on: foo
    deciding on foo: 1
    trying version 1
    dependency incompatibilities
    (terms: {foo 1, not bar *}, cause: dependency foo 1 -> bar *)
    assignment on level 1: Decision foo 1
    unit propagation on: foo
    new assignment on level 1: Derivation bar * due to incompatibility (terms: {foo 1, not bar *}, cause: dependency foo 1 -> bar *)
    unit propagation on: bar
    deciding on bar: *
    trying version 2
    assignment on level 2: Decision bar 2
    unit propagation on: bar
    bar 2, foo 1
    |}]

(* Debug output is off here: these are about which candidate comes back, not
   the trace that got there. *)
let solve_choose ~choose repo deps query =
  Pubgrub.set_debug false;
  let repo_tbl = Hashtbl.create 16 in
  List.iter (fun (n, v) -> Hashtbl.add repo_tbl n v) repo;
  let dep_tbl = Hashtbl.create 16 in
  List.iter (fun (pkg, dep) -> Hashtbl.add dep_tbl pkg dep) deps;
  let vers n = Hashtbl.find_all repo_tbl n in
  let deps n v =
    List.map
      (fun (dn, dvs) -> (dn, Solver.Ranges.of_list dvs))
      (Hashtbl.find_all dep_tbl (n, v))
  in
  let query = List.map (fun (n, vs) -> (n, Solver.Ranges.of_list vs)) query in
  let result = Solver.solve ?choose ~vers ~deps query in
  Format.printf "%a\n" pp_result result;
  Pubgrub.set_debug true

let repo = [ ("root", "1"); ("sel", "a"); ("sel", "b"); ("a", "1"); ("b", "1") ]

let deps =
  [
    (("root", "1"), ("sel", [ "a"; "b" ]));
    (("root", "1"), ("a", [ "1" ]));
    (("sel", "a"), ("a", [ "1" ]));
    (("sel", "b"), ("b", [ "1" ]));
  ]

let query = [ ("root", [ "1" ]) ]

let%expect_test "choose omitted" =
  solve_choose ~choose:None repo deps query;
  [%expect {| b 1, sel b, a 1, root 1 |}]

let%expect_test "choose prefers an already-selected target" =
  let target = function "a" -> "a" | _ -> "b" in
  let choose ~assigned n cands =
    if n <> "sel" then List.hd (List.sort (fun x y -> compare y x) cands)
    else
      match List.find_opt (fun c -> assigned (target c) <> Solver.Unselected) cands with
      | Some c -> c
      | None -> List.hd cands
  in
  solve_choose ~choose:(Some choose) repo deps query;
  [%expect {| sel a, a 1, root 1 |}]

let%expect_test "choose outside the candidates falls back" =
  let choose ~assigned:_ _ _ = "no-such-version" in
  solve_choose ~choose:(Some choose) repo deps query;
  [%expect {| b 1, sel b, a 1, root 1 |}]

(* Debug output is off here too: these are about which name gets decided
   first, which the order of the printed assignments already shows. *)
let solve_next ~next repo deps query =
  Pubgrub.set_debug false;
  let repo_tbl = Hashtbl.create 16 in
  List.iter (fun (n, v) -> Hashtbl.add repo_tbl n v) repo;
  let dep_tbl = Hashtbl.create 16 in
  List.iter (fun (pkg, dep) -> Hashtbl.add dep_tbl pkg dep) deps;
  let vers n = Hashtbl.find_all repo_tbl n in
  let deps n v =
    List.map
      (fun (dn, dvs) -> (dn, Solver.Ranges.of_list dvs))
      (Hashtbl.find_all dep_tbl (n, v))
  in
  let query = List.map (fun (n, vs) -> (n, Solver.Ranges.of_list vs)) query in
  let result = Solver.solve ?next ~vers ~deps query in
  Format.printf "%a\n" pp_result result;
  Pubgrub.set_debug true

let%expect_test "next omitted" =
  solve_next ~next:None repo deps query;
  [%expect {| b 1, sel b, a 1, root 1 |}]

let%expect_test "next takes the most-constrained name last" =
  let next ~assigned:_ open_names = fst (List.hd (List.rev open_names)) in
  solve_next ~next:(Some next) repo deps query;
  [%expect {| a 1, b 1, sel b, root 1 |}]

let%expect_test "next outside the open names falls back" =
  let next ~assigned:_ _ = "no-such-name" in
  solve_next ~next:(Some next) repo deps query;
  [%expect {| b 1, sel b, a 1, root 1 |}]

(* A loading driver lists a version only once a manifest declaring it has
   loaded. [late] holds each such version with the name whose dependencies,
   once asked, list it. The solve over the growing lists is printed above the
   solve over the final ones, and the two must agree. *)
let solve_grow repo late deps query =
  Pubgrub.set_debug false;
  let asked = Hashtbl.create 16 in
  let listed (n, v) =
    match List.assoc_opt (n, v) late with Some by -> Hashtbl.mem asked by | None -> true
  in
  let deps_of n v =
    Hashtbl.replace asked n ();
    List.filter_map (fun (pkg, dep) -> if pkg = (n, v) then Some dep else None) deps
  in
  let vers listed n =
    List.filter_map (fun (m, v) -> if m = n && listed (m, v) then Some v else None) repo
  in
  let grown = Solver.solve ~vers:(vers listed) ~deps:deps_of query in
  let final = Solver.solve ~vers:(vers (fun _ -> true)) ~deps:deps_of query in
  Format.printf "%a\n%a\n" pp_result grown pp_result final;
  Pubgrub.set_debug true

let pts = Solver.Ranges.of_list

(* l is a links class: each declarer depends on the class at its own version.
   b 2 declares l after l was asked and decided for a. *)
let%expect_test "growth - a declarer arrives after the class was asked" =
  solve_grow
    [ ("a", "1"); ("b", "1"); ("b", "2"); ("l", "a1"); ("l", "b2") ]
    [ (("l", "a1"), "a"); (("l", "b2"), "b") ]
    [ (("a", "1"), ("l", pts [ "a1" ])); (("b", "2"), ("l", pts [ "b2" ])) ]
    [ ("a", pts [ "1" ]); ("b", pts [ "1"; "2" ]) ];
  [%expect {|
    b 1, l a1, a 1
    b 1, l a1, a 1
    |}]

(* Review 5's B2: k 2 is ruled out while key k holds only k 2; q then aliases
   zz 1 into k. What was learnt of k 2 must not rule out zz 1. *)
let%expect_test "growth - a key gains a package after a location was decided" =
  solve_grow
    [
      ("a", "1"); ("a", "2"); ("q", "1"); ("q", "2"); ("q", "3"); ("k", "k2"); ("k", "zz1");
    ]
    [ (("k", "zz1"), "q") ]
    [
      (("a", "2"), ("k", pts [ "k2" ]));
      (("k", "k2"), ("d", pts []));
      (("q", "1"), ("k", pts [ "zz1" ]));
      (("q", "2"), ("k", pts [ "zz1" ]));
      (("q", "3"), ("k", pts [ "zz1" ]));
    ]
    [ ("a", pts [ "1"; "2" ]); ("q", pts [ "1"; "2"; "3" ]) ];
  [%expect {|
    k zz1, q 3, a 1
    k zz1, q 3, a 1
    |}]

(* Review 5's B1: p takes w at a 1 or c 1, handed over while w lists only
   those; r's load then lists b 1 between them. When c 1 fails, p must get
   a 1, never b 1. *)
let%expect_test "growth - a key gains a package inside an edge's range" =
  solve_grow
    [ ("p", "1"); ("r", "1"); ("w", "a1"); ("w", "b1"); ("w", "c1") ]
    [ (("w", "b1"), "r") ]
    [
      (("p", "1"), ("w", pts [ "a1"; "c1" ]));
      (("p", "1"), ("r", pts [ "1" ]));
      (("w", "c1"), ("x", pts []));
    ]
    [ ("p", pts [ "1" ]) ];
  [%expect {|
    w a1, r 1, p 1
    w a1, r 1, p 1
    |}]

(* 1 lacks the dependency; nothing can be listed between 2 and 4. *)
let%expect_test "contiguous - points, or intervals where dense" =
  let has_dep v = v <> "1" in
  let vs = [ "1"; "2"; "3"; "4"; "5" ] in
  let dense a b = a >= "2" && b <= "4" in
  Format.printf "%a\n%a\n" Solver.Ranges.pp
    (Solver.Ranges.contiguous "3" vs has_dep)
    Solver.Ranges.pp
    (Solver.Ranges.contiguous ~dense "3" vs has_dep);
  [%expect {|
    2 ∪ 3 ∪ 4 ∪ 5
    [2, 4] ∪ 5
    |}]

(* 1 and 5 lack the dependency; with dense, the block runs up to 5. *)
let%expect_test "contiguous - a dense block runs up to the next listed version" =
  let has_dep v = v <> "1" && v <> "5" in
  let vs = [ "1"; "2"; "3"; "4"; "5" ] in
  let pp = Solver.Ranges.pp in
  let all _ _ = true in
  let inner a b = a >= "2" && b <= "4" in
  Format.printf "%a\n%a\n%a\n" pp
    (Solver.Ranges.contiguous "3" vs has_dep)
    pp
    (Solver.Ranges.contiguous ~dense:inner "3" vs has_dep)
    pp
    (Solver.Ranges.contiguous ~dense:all "3" vs has_dep);
  [%expect {|
    2 ∪ 3 ∪ 4
    [2, 4]
    [2, 5)
    |}]
