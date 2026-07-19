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
    index : int; (* global chronological sequence number *)
    level : decision_level;
    assignment : assignment;
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
    root : (int * decision_level) option;
    decided_names : NameSet.t;
    undecided_pos_names : NameSet.t;
    next_index : int;
  }

  let empty =
    {
      assignments = [];
      by_name = NameMap.empty;
      trail = [];
      root = None;
      decided_names = NameSet.empty;
      undecided_pos_names = NameSet.empty;
      next_index = 0;
    }

  let initial_state = (false, Ranges.full)

  let apply_assignment (has_pos, sr) = function
    | Decision (_, v) -> (true, Ranges.singleton v)
    | Derivation ((Pos, _, r), _) -> (true, Ranges.intersection r sr)
    | Derivation ((Neg, _, r), _) ->
        (has_pos, Ranges.intersection (Ranges.complement r) sr)
    | RootDecision -> (has_pos, sr)

  let add ps lvl a =
    let index = ps.next_index in
    let ps =
      { ps with assignments = (a, lvl) :: ps.assignments; next_index = index + 1 }
    in
    match a with
    | RootDecision -> { ps with root = Some (index, lvl) }
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
            index;
            level = lvl;
            assignment = a;
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
    ( {
        ps with
        assignments = drop_assignments ps.assignments;
        by_name;
        trail;
        decided_names;
        undecided_pos_names;
      },
      NameSet.elements touched )

  let assignments ps = ps.assignments

  let name_range ps n =
    match NameMap.find_opt n ps.by_name with
    | Some (e :: _) -> e.state
    | _ -> initial_state

  let is_decided ps n = NameSet.mem n ps.decided_names
  let root_selected ps = ps.root <> None
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

  (* Term satisfaction is monotone: constraint states only narrow as
     assignments accumulate, so once a term is satisfied it stays satisfied.
     An incompatibility thus becomes All_satisfied exactly when its last term
     does, letting us search per term instead of replaying all assignments. *)
  let state_satisfies (pol, _, vs) (has_pos, sr) =
    match pol with
    | Pos -> has_pos && Ranges.subset_of sr vs
    | Neg -> Ranges.is_disjoint sr vs

  let entries_for ps n =
    Option.value (NameMap.find_opt n ps.by_name) ~default:[]

  (* Earliest chronological point at which [term] becomes satisfied:
     (index, level, satisfying assignment), with index -1 when no assignment
     is needed. None if it never becomes satisfied. *)
  let term_satisfaction ps ((pol, name, _) as term) =
    match name with
    | Root -> (
        match (ps.root, pol) with
        | Some (index, level), Pos -> Some (index, level, RootDecision)
        | Some _, Neg -> None
        | None, Pos -> None
        | None, Neg -> Some (-1, 0, RootDecision))
    | Name n ->
        if state_satisfies term initial_state then Some (-1, 0, RootDecision)
        else
          List.find_map
            (fun e ->
              if state_satisfies term e.state then Some (e.index, e.level, e.assignment)
              else None)
            (List.rev (entries_for ps n))

  let find_satisfier ps incomp =
    let rec satisfactions acc = function
      | [] -> Some (List.rev acc)
      | t :: ts -> (
          match term_satisfaction ps t with
          | None -> None
          | Some s -> satisfactions ((t, s) :: acc) ts)
    in
    match satisfactions [] incomp.terms with
    | None | Some [] -> None
    | Some (first :: rest) ->
        let sat_term, (sat_index, sat_level, sat_assignment) =
          List.fold_left
            (fun ((_, (best_index, _, _)) as best) ((_, (index, _, _)) as cur) ->
              if index > best_index then cur else best)
            first rest
        in
        if sat_index < 0 then
          (* Degenerate: satisfied with no assignments at all; mirror the
             replay-based behavior of reporting the oldest assignment. *)
          match List.rev ps.assignments with
          | [] -> None
          | (a, lvl) :: _ -> Some ((a, lvl), lvl)
        else
          (* The previous satisfier: the latest point at which every term
             except the satisfier's own contribution is satisfied, i.e. the
             level [incomp] would still be satisfied at were the satisfier
             the only assignment above it. *)
          let others_prev =
            List.fold_left
              (fun (best_index, best_level) (t, (index, level, _)) ->
                if t == sat_term || index <= best_index then (best_index, best_level)
                else (index, level))
              (-1, 0) (first :: rest)
          in
          let own_prev =
            match sat_term with
            | _, Root, _ -> (-1, 0)
            | _, Name n, _ ->
                let satisfied_with s =
                  state_satisfies sat_term (apply_assignment s sat_assignment)
                in
                if satisfied_with initial_state then (-1, 0)
                else
                  let rec walk = function
                    | [] -> (-1, 0)
                    | e :: _ when e.index >= sat_index -> (-1, 0)
                    | e :: rest ->
                        if satisfied_with e.state then (e.index, e.level) else walk rest
                  in
                  walk (List.rev (entries_for ps n))
          in
          let prev_index, prev_level =
            if fst own_prev > fst others_prev then own_prev else others_prev
          in
          let previous_level = if prev_index >= 0 then prev_level else 0 in
          Some ((sat_assignment, sat_level), previous_level)

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
