module Make (N : Types.NAME) (V : Types.VERSION) = struct
  include Types.Make (N) (V)
  module NameMap = Map.Make (N)
  module NameSet = Set.Make (N)

  type assignment =
    | Decision of package
    | RootDecision
    | Derivation of term * incompatibility

  type t = {
    assignments : (assignment * decision_level) list;
    name_ranges : (bool * Ranges.t) NameMap.t;
    decided_names : NameSet.t;
    undecided_pos_names : NameSet.t;
    root_selected : bool;
  }

  let empty =
    {
      assignments = [];
      name_ranges = NameMap.empty;
      decided_names = NameSet.empty;
      undecided_pos_names = NameSet.empty;
      root_selected = false;
    }

  let lookup_range n nr =
    Option.value (NameMap.find_opt n nr) ~default:(false, Ranges.full)

  let update_name_ranges nr = function
    | Decision (n, v) -> NameMap.add n (true, Ranges.singleton v) nr
    | Derivation ((Pos, Name n, r), _) ->
        let _, old_r = lookup_range n nr in
        NameMap.add n (true, Ranges.intersection r old_r) nr
    | Derivation ((Neg, Name n, r), _) ->
        let old_pos, old_r = lookup_range n nr in
        NameMap.add n (old_pos, Ranges.intersection (Ranges.complement r) old_r) nr
    | _ -> nr

  let update_decided_names ds = function Decision (n, _) -> NameSet.add n ds | _ -> ds

  let update_undecided_pos_names ups ~decided = function
    | Decision (n, _) -> NameSet.remove n ups
    | Derivation ((Pos, Name n, _), _) ->
        if NameSet.mem n decided then ups else NameSet.add n ups
    | _ -> ups

  let update_root_selected rs = function RootDecision -> true | _ -> rs

  let add ps lvl a =
    {
      assignments = (a, lvl) :: ps.assignments;
      name_ranges = update_name_ranges ps.name_ranges a;
      decided_names = update_decided_names ps.decided_names a;
      undecided_pos_names =
        update_undecided_pos_names ps.undecided_pos_names ~decided:ps.decided_names a;
      root_selected = update_root_selected ps.root_selected a;
    }

  let backtrack ps level =
    let filtered = List.filter (fun (_, lvl) -> lvl <= level) ps.assignments in
    let name_ranges, decided_names, undecided_pos_names, root_selected =
      List.fold_left
        (fun (nr, ds, ups, rs) (a, _) ->
          ( update_name_ranges nr a,
            update_decided_names ds a,
            update_undecided_pos_names ups ~decided:ds a,
            update_root_selected rs a ))
        (NameMap.empty, NameSet.empty, NameSet.empty, false)
        (List.rev filtered)
    in
    {
      assignments = filtered;
      name_ranges;
      decided_names;
      undecided_pos_names;
      root_selected;
    }

  let assignments ps = ps.assignments
  let name_range ps n = lookup_range n ps.name_ranges
  let is_decided ps n = NameSet.mem n ps.decided_names
  let root_selected ps = ps.root_selected
  let undecided_pos_names ps = ps.undecided_pos_names

  let term_status ps (pol, name, vs) =
    match name with
    | Root -> (
        match (root_selected ps, pol) with
        | true, Pos -> Satisfied
        | true, Neg -> Contradicted
        | false, Pos -> Undetermined
        | false, Neg -> Satisfied)
    | Name n -> (
        let has_positive, sr = name_range ps n in
        match (has_positive, pol) with
        | false, Pos -> Contradicted
        | false, Neg ->
            if Ranges.is_disjoint sr vs then Satisfied
            else if Ranges.subset_of sr vs then Contradicted
            else Undetermined
        | true, _ ->
            if Ranges.subset_of sr vs then
              match pol with Pos -> Satisfied | Neg -> Contradicted
            else if Ranges.is_disjoint sr vs then
              match pol with Pos -> Contradicted | Neg -> Satisfied
            else Undetermined)

  let incompatibility_status ps incomp : incomp_status =
    let rec aux s = function
      | [] -> s
      | t :: ts -> (
          match (s, term_status ps t) with
          | All_satisfied, Satisfied -> aux All_satisfied ts
          | All_satisfied, Undetermined -> aux (Almost_satisfied t) ts
          | Almost_satisfied t, Satisfied -> aux (Almost_satisfied t) ts
          | Almost_satisfied _, Undetermined -> aux Incomp_undetermined ts
          | Some_contradicted, _ -> Some_contradicted
          | _, Contradicted -> Some_contradicted
          | Incomp_undetermined, _ -> aux Incomp_undetermined ts)
    in
    aux All_satisfied incomp.terms

  let find_earliest_satisfier ps incomp =
    let oldest_first = List.rev ps.assignments in
    let rec aux acc = function
      | [] -> None
      | (a, lvl) :: rest ->
          let acc' = add acc lvl a in
          if incompatibility_status acc' incomp = All_satisfied then Some ((a, lvl), acc)
          else aux acc' rest
    in
    aux empty oldest_first

  let find_previous_satisfier_level ps_before (sat_a, sat_lvl) incomp =
    let oldest_first = List.rev ps_before.assignments in
    let rec aux acc = function
      | [] -> None
      | (a, lvl) :: rest ->
          let acc' = add acc lvl a in
          let with_sat = add acc' sat_lvl sat_a in
          if incompatibility_status with_sat incomp = All_satisfied then Some lvl
          else aux acc' rest
    in
    match aux empty oldest_first with Some lvl -> lvl | None -> 0

  let pp_assignment fmt = function
    | Decision package -> Format.fprintf fmt "Decision %a" pp_package package
    | RootDecision -> Format.fprintf fmt "Decision root"
    | Derivation (term, cause) ->
        Format.fprintf fmt "Derivation %a due to incompatibility %a" pp_term term
          pp_incompatibility cause

  let pp_assignments fmt =
    Format.(
      pp_print_list
        ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ")
        (fun fmt (a, d) -> fprintf fmt "(%d: %a)" d pp_assignment a))
      fmt

  let assignment_name = function
    | Decision (n, _) -> Name n
    | RootDecision -> Root
    | Derivation ((_, name, _), _) -> name
end
