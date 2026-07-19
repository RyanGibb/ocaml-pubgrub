module type NAME = sig
  type t

  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module type VERSION = sig
  type t

  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module Make (N : NAME) (V : VERSION) = struct
  module Ranges = Ranges.Make (V)

  type name = Root | Name of N.t
  type package = N.t * V.t

  let compare_name a b =
    match (a, b) with
    | Root, Root -> 0
    | Root, _ -> -1
    | _, Root -> 1
    | Name a, Name b -> N.compare a b

  let pp_name fmt = function
    | Root -> Format.pp_print_string fmt "Root"
    | Name n -> N.pp fmt n

  let pp_package fmt (n, v) = Format.fprintf fmt "%a %a" N.pp n V.pp v

  type polarity = Pos | Neg
  type term = polarity * name * Ranges.t

  type cause =
    | NoVersions
    | Dependency of package * (name * Ranges.t)
    | RootDependency of (name * Ranges.t)
    | Derived of incompatibility * incompatibility

  and incompatibility = { terms : term list; cause : cause }

  type decision_level = int
  type term_status = Satisfied | Contradicted | Undetermined

  type incomp_status =
    | All_satisfied
    | Some_contradicted
    | Almost_satisfied of term
    | Incomp_undetermined

  let pp_polarity fmt = function Pos -> () | Neg -> Format.pp_print_string fmt "not "

  let pp_term fmt (p, n, vs) =
    Format.fprintf fmt "%a%a %a" pp_polarity p pp_name n Ranges.pp vs

  let pp_terms fmt terms =
    Format.fprintf fmt "{%a}"
      Format.(
        pp_print_list
          ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ")
          (fun fmt t -> fprintf fmt "%a" pp_term t))
      terms

  let rec pp_cause fmt = function
    | NoVersions -> Format.pp_print_string fmt "no versions"
    | Dependency (pkg, (n, r)) ->
        Format.fprintf fmt "dependency %a -> %a %a" pp_package pkg pp_name n Ranges.pp r
    | RootDependency (n, r) ->
        Format.fprintf fmt "dependency root -> %a %a" pp_name n Ranges.pp r
    | Derived (i1, i2) ->
        Format.fprintf fmt "(%a and %a)" pp_incompatibility i1 pp_incompatibility i2

  and pp_incompatibility fmt { terms; cause } =
    Format.fprintf fmt "(terms: %a, cause: %a)" pp_terms terms pp_cause cause

  let pp_incompatibilities fmt incomps =
    Format.fprintf fmt "%a"
      Format.(
        pp_print_list
          ~pp_sep:(fun fmt () -> Format.pp_print_string fmt "\n\t")
          (fun fmt i -> fprintf fmt "%a" pp_incompatibility i))
      incomps

  let term_name = function _, name, _ -> name

  let equal_term (p1, n1, r1) (p2, n2, r2) =
    p1 = p2 && compare_name n1 n2 = 0 && Ranges.equal r1 r2

  let equal_terms a b = List.length a = List.length b && List.for_all2 equal_term a b

  let negate_term = function
    | Pos, name, r -> (Neg, name, r)
    | Neg, name, r -> (Pos, name, r)

  let term_satisfies (sp, _, sr) (tp, _, tr) =
    match (sp, tp) with
    | Pos, Pos -> Ranges.subset_of sr tr
    | Neg, Neg -> Ranges.subset_of tr sr
    | Pos, Neg -> Ranges.is_disjoint sr tr
    | Neg, Pos -> Ranges.subset_of (Ranges.complement sr) tr

  let term_not_difference (sp, sn, sr) (tp, _, tr) =
    match (sp, tp) with
    | Pos, Pos -> (Neg, sn, Ranges.difference sr tr)
    | Neg, Pos -> (Pos, sn, Ranges.union sr tr)
    | Pos, Neg -> (Neg, sn, Ranges.intersection sr tr)
    | Neg, Neg -> (Neg, sn, Ranges.difference tr sr)

  let normalise_terms terms =
    let tbl = Hashtbl.create (List.length terms) in
    List.iter
      (fun (pol, name, r) ->
        let key =
          List.find_opt
            (fun k -> compare_name k name = 0)
            (List.of_seq (Hashtbl.to_seq_keys tbl))
        in
        let key = match key with Some k -> k | None -> name in
        let replace = Hashtbl.replace tbl key in
        match Hashtbl.find_opt tbl key with
        | None -> replace (pol, r)
        | Some (pol', r') -> (
            match (pol, pol') with
            | Pos, Pos -> replace (Pos, Ranges.intersection r r')
            | Neg, Neg -> replace (Neg, Ranges.union r r')
            | Pos, Neg -> replace (Pos, Ranges.difference r r')
            | Neg, Pos -> replace (Pos, Ranges.difference r' r)))
      terms;
    let result = Hashtbl.fold (fun name (pol, r) acc -> (pol, name, r) :: acc) tbl [] in
    (* a negative term over the empty range is a tautology: drop it *)
    let result =
      List.filter (function Neg, _, r -> not (Ranges.is_empty r) | _ -> true) result
    in
    match result with
    | _ :: _ :: _ -> List.filter (function Pos, Root, _ -> false | _ -> true) result
    | _ -> result
end
