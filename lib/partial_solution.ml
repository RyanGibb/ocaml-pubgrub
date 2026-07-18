module Make (N : Types.NAME) (V : Types.VERSION) = struct
  include Types.Make (N) (V)
  module NameSet = Set.Make (N)

  type assignment =
    | Decision of package
    | RootDecision
    | Derivation of term * incompatibility

  type t = (assignment * decision_level) list

  let empty = []
  let add ps lvl a = (a, lvl) :: ps
  let backtrack ps level = List.filter (fun (_, lvl) -> lvl <= level) ps
  let assignments ps = ps

  (* Compute the effective range for a name from the assignments, and whether
     there's any positive derivation for it. *)
  let name_range ps n =
    let rec aux has_pos = function
      | [] -> (has_pos, Ranges.full)
      | (Decision (n', v), _) :: _ when N.compare n' n = 0 -> (true, Ranges.singleton v)
      | (Derivation ((Pos, Name n', r), _), _) :: rest when N.compare n' n = 0 ->
          let _, sr = aux true rest in
          (true, Ranges.intersection r sr)
      | (Derivation ((Neg, Name n', r), _), _) :: rest when N.compare n' n = 0 ->
          let has_pos, sr = aux has_pos rest in
          (has_pos, Ranges.intersection (Ranges.complement r) sr)
      | _ :: rest -> aux has_pos rest
    in
    aux false ps

  let is_decided ps n =
    List.exists
      (fun (a, _) -> match a with Decision (n', _) -> N.compare n' n = 0 | _ -> false)
      ps

  let root_selected ps =
    List.exists (fun (a, _) -> match a with RootDecision -> true | _ -> false) ps

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
    let rec aux = function
      | [] -> None
      | sat :: rest -> (
          match aux rest with
          | None ->
              if incompatibility_status (sat :: rest) incomp = All_satisfied then
                Some (sat, rest)
              else None
          | some -> some)
    in
    aux ps

  let find_previous_satisfier_level ps_before satisfier incomp =
    let rec aux = function
      | [] -> None
      | sat :: rest -> (
          match aux rest with
          | None ->
              if incompatibility_status (satisfier :: sat :: rest) incomp = All_satisfied
              then Some (snd sat)
              else None
          | some -> some)
    in
    match aux ps_before with Some lvl -> lvl | None -> 0

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
