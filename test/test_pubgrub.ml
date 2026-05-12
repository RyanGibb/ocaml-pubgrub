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

let solve repo deps query =
  let repo_tbl = Hashtbl.create 16 in
  List.iter (fun (n, v) -> Hashtbl.add repo_tbl n v) repo;
  let dep_tbl = Hashtbl.create 16 in
  List.iter
    (fun ((n, v), (dn, dvs)) ->
      Hashtbl.add dep_tbl (n, v) (dn, Solver.Ranges.of_list dvs))
    deps;
  let versions n = Hashtbl.find_all repo_tbl n in
  let dependencies n v = Hashtbl.find_all dep_tbl (n, v) in
  let query = List.map (fun (n, vs) -> (n, Solver.Ranges.of_list vs)) query in
  let result = Solver.resolve ~versions ~dependencies query in
  Format.printf "%a\n" pp_result result

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
  [%expect {| D 2, C 1, B 1, A 1 |}]

let%expect_test "simple" =
  solve
    [ ("foo", "1.0.0"); ("bar", "1.0.0"); ("bar", "2.0.0") ]
    [ (("foo", "1.0.0"), ("bar", [ "1.0.0"; "2.0.0" ])) ]
    [ ("foo", [ "1.0.0" ]) ];
  [%expect {| bar 2.0.0, foo 1.0.0 |}]

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
  [%expect {| foo 1.0.0, bar 1.1.0 |}]

let%expect_test "conflict - circular dependency" =
  solve
    [ ("foo", "2.0.0"); ("foo", "1.0.0"); ("bar", "1.0.0") ]
    [ (("foo", "2.0.0"), ("bar", [ "1.0.0" ])); (("bar", "1.0.0"), ("foo", [ "1.0.0" ])) ]
    [ ("foo", [ "1.0.0"; "2.0.0" ]) ];
  [%expect {| foo 1.0.0 |}]

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
  [%expect {| foo 1.0.0, target 2.0.0 |}]

let%expect_test "linear error" =
  solve
    [ ("foo", "1.0.0"); ("bar", "2.0.0"); ("baz", "1.0.0"); ("baz", "3.0.0") ]
    [ (("foo", "1.0.0"), ("bar", [ "2.0.0" ])); (("bar", "2.0.0"), ("baz", [ "3.0.0" ])) ]
    [ ("foo", [ "1.0.0" ]); ("baz", [ "1.0.0" ]) ];
  [%expect
    {|
    Because foo 1.0.0 -> bar 2.0.0 and bar 2.0.0 -> baz 3.0.0, foo * requires baz 3.0.0.
    And because root -> baz 1.0.0 and root -> foo 1.0.0, version solving failed.
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
    Because a 1.0.0 -> b 2.0.0 and foo 1.0.0 -> a 1.0.0, foo (-∞, 1.1.0) requires b 2.0.0.
    And because foo 1.0.0 -> b 1.0.0 and root -> foo 1.0.0, version solving failed.
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
  [%expect {| a 1, b 1, c 1 |}]

let%expect_test "shared dependency - collapsing" =
  solve
    [ ("a", "2"); ("a", "1"); ("b", "1") ]
    [ (("a", "2"), ("b", [ "1" ])); (("a", "1"), ("b", [ "1" ])) ]
    [ ("a", [ "1"; "2" ]) ];
  [%expect {| b 1, a 2 |}]
