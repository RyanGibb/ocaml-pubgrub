module Make (N : Types.NAME) (V : Types.VERSION) = struct
  include Types.Make (N) (V)
  module NameMap = Map.Make (N)
  module NameSet = Set.Make (N)

  type assignment =
    | Decision of package
    | RootDecision
    | Derivation of term * incompatibility

  (* One assignment touching a name, with the cumulative constraint state for
     that name after applying it. *)
  type entry = {
    level : decision_level;
    state : bool * Ranges.t; (* (has_positive, range) after this assignment *)
    decided : bool; (* some assignment up to this one is a Decision *)
  }

  (* Assignment levels are non-decreasing in chronological order (backtracking
     truncates to a prefix and resumes at the target level), so dropping
     assignments above a level always removes a newest-first prefix. *)
  type t = {
    assignments : (assignment * decision_level) list; (* newest first *)
    by_name : entry list NameMap.t; (* newest first *)
    trail : (decision_level * N.t) list; (* newest first *)
    root_selected : bool;
    decided_names : NameSet.t;
    undecided_pos_names : NameSet.t;
  }

  let empty =
    {
      assignments = [];
      by_name = NameMap.empty;
      trail = [];
      root_selected = false;
      decided_names = NameSet.empty;
      undecided_pos_names = NameSet.empty;
    }

  let initial_state = (false, Ranges.full)

  let apply_assignment (has_pos, sr) = function
    | Decision (_, v) -> (true, Ranges.singleton v)
    | Derivation ((Pos, _, r), _) -> (true, Ranges.intersection r sr)
    | Derivation ((Neg, _, r), _) ->
        (has_pos, Ranges.intersection (Ranges.complement r) sr)
    | RootDecision -> (has_pos, sr)

  let add ps lvl a =
    let ps = { ps with assignments = (a, lvl) :: ps.assignments } in
    match a with
    | RootDecision -> { ps with root_selected = true }
    | Derivation ((_, Root, _), _) -> ps
    | Decision (n, _) | Derivation ((_, Name n, _), _) ->
        let entries = Option.value (NameMap.find_opt n ps.by_name) ~default:[] in
        let prev_state, prev_decided =
          match entries with
          | e :: _ -> (e.state, e.decided)
          | [] -> (initial_state, false)
        in
        let entry =
          {
            level = lvl;
            state = apply_assignment prev_state a;
            decided = (prev_decided || match a with Decision _ -> true | _ -> false);
          }
        in
        let decided_names =
          match a with
          | Decision _ -> NameSet.add n ps.decided_names
          | _ -> ps.decided_names
        in
        let undecided_pos_names =
          match a with
          | Decision _ -> NameSet.remove n ps.undecided_pos_names
          | Derivation ((Pos, _, _), _) ->
              if NameSet.mem n ps.decided_names then ps.undecided_pos_names
              else NameSet.add n ps.undecided_pos_names
          | _ -> ps.undecided_pos_names
        in
        {
          ps with
          by_name = NameMap.add n (entry :: entries) ps.by_name;
          trail = (lvl, n) :: ps.trail;
          decided_names;
          undecided_pos_names;
        }

  let backtrack ps level =
    let rec drop_assignments = function
      | (_, lvl) :: rest when lvl > level -> drop_assignments rest
      | assignments -> assignments
    in
    let rec split_trail touched = function
      | (lvl, n) :: rest when lvl > level -> split_trail (NameSet.add n touched) rest
      | trail -> (touched, trail)
    in
    let touched, trail = split_trail NameSet.empty ps.trail in
    let by_name, decided_names, undecided_pos_names =
      NameSet.fold
        (fun n (by_name, decided, undecided) ->
          let rec drop_entries = function
            | e :: rest when e.level > level -> drop_entries rest
            | entries -> entries
          in
          let entries =
            drop_entries (Option.value (NameMap.find_opt n by_name) ~default:[])
          in
          match entries with
          | [] ->
              ( NameMap.remove n by_name,
                NameSet.remove n decided,
                NameSet.remove n undecided )
          | e :: _ ->
              let decided =
                if e.decided then NameSet.add n decided else NameSet.remove n decided
              in
              let undecided =
                if fst e.state && not e.decided then NameSet.add n undecided
                else NameSet.remove n undecided
              in
              (NameMap.add n entries by_name, decided, undecided))
        touched
        (ps.by_name, ps.decided_names, ps.undecided_pos_names)
    in
    {
      ps with
      assignments = drop_assignments ps.assignments;
      by_name;
      trail;
      decided_names;
      undecided_pos_names;
    }

  let assignments ps = ps.assignments

  let name_range ps n =
    match NameMap.find_opt n ps.by_name with
    | Some (e :: _) -> e.state
    | _ -> initial_state

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
