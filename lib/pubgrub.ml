let ( let* ) = Option.bind

module type NAME = Types.NAME
module type VERSION = Types.VERSION

let debug_enabled = ref false

let debug_printf fmt =
  if !debug_enabled then
    Format.kfprintf
      (fun _ -> Format.pp_print_flush Format.std_formatter ())
      Format.std_formatter fmt
  else Format.ifprintf Format.std_formatter fmt

let set_debug enabled = debug_enabled := enabled

module Make (N : NAME) (V : VERSION) = struct
  include Types.Make (N) (V)
  module PS = Partial_solution.Make (N) (V)
  module Incomp = Incompatibilities.Make (N) (V)
  module PQ = Priority_queue.Make (N)

  type state = {
    incomps : Incomp.t;
    decision_level : decision_level;
    partial_solution : PS.t;
    (* Candidates for the next decision, prioritised by the number of
       available versions remaining under the current constraints. *)
    candidates : PQ.t;
  }

  let add_incomp state incomp = { state with incomps = Incomp.add incomp state.incomps }
  let add_incomps state incomps = List.fold_left add_incomp state incomps

  (* Count of available versions for [n] in the current partial solution. *)
  let count_for ~versions state n =
    let _, sr = PS.name_range state.partial_solution n in
    List.length (List.filter (fun v -> Ranges.contains v sr) (versions n))

  (* Push an assignment onto the partial solution at the current decision
     level and refresh the candidates priority queue. *)
  let add_assignment ~versions state assignment =
    let partial_solution =
      PS.add state.partial_solution state.decision_level assignment
    in
    let state = { state with partial_solution } in
    let set_count n = PQ.update state.candidates n (count_for ~versions state n) in
    let candidates =
      match assignment with
      | PS.Decision (n, _) -> PQ.remove state.candidates n
      | PS.Derivation ((Pos, Name n, _), _) ->
          if PS.is_decided state.partial_solution n then state.candidates else set_count n
      | PS.Derivation ((Neg, Name n, _), _) ->
          if PS.NameSet.mem n (PS.undecided_pos_names state.partial_solution) then
            set_count n
          else state.candidates
      | _ -> state.candidates
    in
    { state with candidates }

  (* Rebuild the priority queue from scratch from the current partial solution.
     Used after backtrack. *)
  let rebuild_candidates ~versions state =
    let state = { state with candidates = PQ.empty } in
    PS.NameSet.fold
      (fun n s ->
        { s with candidates = PQ.insert s.candidates n (count_for ~versions s n) })
      (PS.undecided_pos_names state.partial_solution)
      state

  let rec conflict_resolution ~versions state original_incomp incomp :
      (state * incompatibility * term, incompatibility) Result.t =
    debug_printf "conflict resolution on: %a\n" pp_incompatibility incomp;
    match incomp.terms with
    | [] -> Error incomp
    | [ (Pos, Root, _) ] -> Error incomp
    | _ -> (
        match PS.find_satisfier state.partial_solution incomp with
        | None -> failwith "Incompatibility not satisfied"
        | Some ((satisfier, satisfier_decision_level), previous_satisfier_level) -> (
            debug_printf "satisfiying assignment on level %d: %a\n"
              satisfier_decision_level PS.pp_assignment satisfier;
            let term =
              let name = PS.assignment_name satisfier in
              List.find (fun t -> compare_name (term_name t) name = 0) incomp.terms
            in
            match (satisfier, satisfier_decision_level != previous_satisfier_level) with
            | PS.Decision _, _ | PS.RootDecision, _ | _, true ->
                debug_printf "backtracking to level %d\n" previous_satisfier_level;
                let partial_solution =
                  PS.backtrack state.partial_solution previous_satisfier_level
                in
                debug_printf "solution: %a\n" PS.pp_assignments
                  (PS.assignments partial_solution);
                let state =
                  {
                    state with
                    partial_solution;
                    decision_level = previous_satisfier_level;
                  }
                in
                let state = rebuild_candidates ~versions state in
                let state =
                  if incomp != original_incomp then (
                    debug_printf "new incompatibility %a\n" pp_incompatibility incomp;
                    add_incomp state incomp)
                  else state
                in
                Ok (state, incomp, term)
            | PS.Derivation (satisfier_term, cause), _ ->
                let base_terms =
                  incomp.terms @ cause.terms
                  |> List.filter (fun t ->
                      compare_name (term_name t) (term_name term) <> 0)
                in
                let partial_satisfier_term =
                  if term_satisfies satisfier_term term then []
                  else [ term_not_difference satisfier_term term ]
                in
                let prior_cause =
                  {
                    terms = normalise_terms (base_terms @ partial_satisfier_term);
                    cause = Derived (incomp, cause);
                  }
                in
                debug_printf "prior cause %a\n" pp_incompatibility prior_cause;
                conflict_resolution ~versions state original_incomp prior_cause))

  let rec unit_propagation ~versions state changed : (state, incompatibility) Result.t =
    match changed with
    | [] -> Ok state
    | name :: changed ->
        debug_printf "unit propagation on: %a\n" pp_name name;
        let incomps = Incomp.find_for_name name state.incomps in
        incompat_propagation ~versions state changed incomps

  and incompat_propagation ~versions state changed = function
    | [] -> unit_propagation ~versions state changed
    | incomp :: incomps -> (
        match PS.incompatibility_status state.partial_solution incomp with
        | All_satisfied -> (
            match conflict_resolution ~versions state incomp incomp with
            | Ok (state, incomp, term) ->
                let assignment = PS.Derivation (negate_term term, incomp) in
                let _, name, _ = term in
                debug_printf "new assignment on level %d: %a\n" state.decision_level
                  PS.pp_assignment assignment;
                let state = add_assignment ~versions state assignment in
                unit_propagation ~versions state [ name ]
            | Error incomp -> Error incomp)
        | Almost_satisfied term ->
            let assignment = PS.Derivation (negate_term term, incomp) in
            debug_printf "new assignment on level %d: %a\n" state.decision_level
              PS.pp_assignment assignment;
            let state = add_assignment ~versions state assignment in
            let _, name, _ = term in
            incompat_propagation ~versions state (name :: changed) incomps
        | _ -> incompat_propagation ~versions state changed incomps)

  (* a negative term over the empty range can never be violated: drop it *)
  let drop_tautologies =
    List.filter (function Neg, _, r -> not (Ranges.is_empty r) | _ -> true)

  let dependency_incomps ~versions ~dependencies n version =
    let all_versions = versions n in
    List.map
      (fun (dep_name, dep_range) ->
        let has_dep v =
          List.exists
            (fun (dn, dr) -> N.compare dn dep_name = 0 && Ranges.equal dr dep_range)
            (dependencies n v)
        in
        let depender_range = Ranges.contiguous version all_versions has_dep in
        {
          terms =
            drop_tautologies
              [ (Pos, Name n, depender_range); (Neg, Name dep_name, dep_range) ];
          cause = Dependency ((n, version), (Name dep_name, dep_range));
        })
      (dependencies n version)

  let make_decision ~versions ~dependencies state =
    let find_undecided_term () =
      match PQ.min_elt state.candidates with
      | None -> None
      | Some (_, n) ->
          let _, sr = PS.name_range state.partial_solution n in
          let real_vs = List.filter (fun v -> Ranges.contains v sr) (versions n) in
          Some (n, real_vs)
    in
    let* n, real_vs = find_undecided_term () in
    let _, sr = PS.name_range state.partial_solution n in
    debug_printf "deciding on %a: %a\n" N.pp n Ranges.pp sr;
    let decision_level = state.decision_level + 1 in
    match real_vs with
    | [] ->
        let incomp = { terms = [ (Pos, Name n, sr) ]; cause = NoVersions } in
        debug_printf "no versions found, adding incompatiblity %a\n" pp_incompatibility
          incomp;
        let state = add_incomp state incomp in
        Some (Name n, state)
    | _ ->
        let version = List.hd (List.sort (fun a b -> V.compare b a) real_vs) in
        debug_printf "trying version %a\n" V.pp version;
        let dep_incomps =
          dependency_incomps ~versions ~dependencies n version
          |> List.filter (fun i -> not (Incomp.mem i state.incomps))
        in
        if List.length dep_incomps > 0 then
          debug_printf "dependency incompatibilities\n\t%a\n" pp_incompatibilities
            dep_incomps;
        let state = add_incomps state dep_incomps in
        let trial_state =
          add_assignment ~versions { state with decision_level }
            (PS.Decision (n, version))
        in
        let conflicts =
          List.exists
            (fun i ->
              match PS.incompatibility_status trial_state.partial_solution i with
              | All_satisfied -> true
              | _ -> false)
            dep_incomps
        in
        if conflicts then (
          debug_printf "not adding decision due to conflict\n";
          Some (Name n, state))
        else (
          debug_printf "assignment on level %d: %a\n" decision_level PS.pp_assignment
            (PS.Decision (n, version));
          Some (Name n, trial_state))

  let extract_resolution state =
    List.filter_map
      (function PS.Decision pkg, _ -> Some pkg | _ -> None)
      (PS.assignments state.partial_solution)

  let init_incomps query =
    List.map
      (fun ((dep_name, dep_range) as dep) ->
        {
          terms = drop_tautologies [ (Pos, Root, Ranges.full); (Neg, dep_name, dep_range) ];
          cause = RootDependency dep;
        })
      query

  type query = (N.t * Ranges.t) list

  let solve ~versions ~dependencies (query : query) :
      ((N.t * V.t) list, incompatibility) Result.t =
    let root_deps = List.map (fun (name, range) -> (Name name, range)) query in
    let rec solve_loop state next =
      match unit_propagation ~versions state [ next ] with
      | Error incomp -> Error incomp
      | Ok state -> (
          match make_decision ~versions ~dependencies state with
          | None -> Ok (extract_resolution state)
          | Some (next, state) -> solve_loop state next)
    in
    let incomps = init_incomps root_deps in
    debug_printf "initial incompatibilities\n\t%a\n" pp_incompatibilities incomps;
    let partial_solution = PS.add PS.empty 0 PS.RootDecision in
    let initial_state =
      add_incomps
        {
          incomps = Incomp.empty;
          decision_level = 0;
          partial_solution;
          candidates = PQ.empty;
        }
        incomps
    in
    solve_loop initial_state Root

  let explain_terms fmt = function
    | [ (Pos, n, vs); (Neg, m, us) ] | [ (Neg, m, us); (Pos, n, vs) ] ->
        Format.fprintf fmt "%a %a requires %a %a" pp_name n Ranges.pp vs pp_name m
          Ranges.pp us
    | [] | [ (Pos, Root, _) ] -> Format.fprintf fmt "version solving failed."
    | terms ->
        Format.fprintf fmt "%a is forbidden."
          Format.(
            pp_print_list
              ~pp_sep:(fun fmt () -> Format.pp_print_string fmt " or ")
              (fun fmt t -> fprintf fmt "%a" pp_term t))
          terms

  let explain_incompatibility fmt root =
    let line_numbers = Hashtbl.create 16 in
    let line_number = ref 0 in
    let set_line_number cause =
      incr line_number;
      Hashtbl.add line_numbers cause !line_number;
      !line_number
    in
    let is_external incomp = match incomp.cause with Derived _ -> false | _ -> true in
    let rec count_caused incomp = function
      | Derived (c1, c2) ->
          (if c1 == incomp then 1 else 0)
          + (if c2 == incomp then 1 else 0)
          + count_caused incomp c1.cause + count_caused incomp c2.cause
      | _ -> 0
    in
    let rec explain_incomp fmt incomp =
      match incomp.cause with
      | NoVersions -> Format.fprintf fmt "%a not available" explain_terms incomp.terms
      | Dependency (pkg, (n, r)) ->
          Format.fprintf fmt "%a -> %a %a" pp_package pkg pp_name n Ranges.pp r
      | RootDependency (n, r) -> Format.fprintf fmt "root -> %a %a" pp_name n Ranges.pp r
      | Derived (cause1, cause2) ->
          (match (is_external cause1, is_external cause2) with
          | false, false -> (
              match
                ( Hashtbl.find_opt line_numbers cause1,
                  Hashtbl.find_opt line_numbers cause2 )
              with
              | Some line1, Some line2 ->
                  Format.fprintf fmt "Because %a (%d) and %a (%d), %a." explain_terms
                    cause1.terms line1 explain_terms cause2.terms line2 explain_terms
                    incomp.terms
              | Some line1, None ->
                  Format.fprintf fmt "%a\nAnd because %a (%d), %a." explain_incomp cause2
                    explain_terms cause1.terms line1 explain_terms incomp.terms
              | None, Some line2 ->
                  Format.fprintf fmt "%a\nAnd because %a (%d), %a." explain_incomp cause1
                    explain_terms cause2.terms line2 explain_terms incomp.terms
              | None, None -> (
                  let is_simple incomp =
                    match incomp.cause with
                    | Derived (c1, c2) -> is_external c1 && is_external c2
                    | _ -> true
                  in
                  match
                    match (is_simple cause1, is_simple cause2) with
                    | true, _ -> Some (cause1, cause2)
                    | false, true -> Some (cause2, cause1)
                    | false, false -> None
                  with
                  | Some (simple, complex) ->
                      Format.fprintf fmt "%a\n%a\nThus, %a" explain_incomp complex
                        explain_incomp simple explain_terms incomp.terms
                  | None ->
                      let line1 = set_line_number cause1 in
                      let line2 = set_line_number cause2 in
                      Format.fprintf fmt "%a (%d)\n\n%a (%d)\nThus, %a" explain_incomp
                        cause1 line1 explain_incomp cause2 line2 explain_terms
                        incomp.terms))
          | false, _ | _, false -> (
              let derived, ext =
                if is_external cause1 then (cause2, cause1) else (cause1, cause2)
              in
              match Hashtbl.find_opt line_numbers derived with
              | Some line ->
                  Format.fprintf fmt "Because %a and %a (%d), %a" explain_incomp ext
                    explain_terms derived.terms line explain_terms incomp.terms
              | None -> (
                  match
                    match derived.cause with
                    | Derived (c1, c2) -> (
                        let* derived, ext =
                          match (is_external c1, is_external c2) with
                          | true, false -> Some (c2, c1)
                          | false, true -> Some (c1, c2)
                          | _ -> None
                        in
                        match Hashtbl.find_opt line_numbers derived with
                        | None -> Some (derived, ext)
                        | _ -> None)
                    | _ -> None
                  with
                  | Some (prior_derived, prior_external) ->
                      Format.fprintf fmt "%a\nAnd because %a and %a, %a" explain_incomp
                        prior_derived explain_incomp prior_external explain_incomp ext
                        explain_terms incomp.terms
                  | _ ->
                      Format.fprintf fmt "%a\nAnd because %a, %a" explain_incomp derived
                        explain_incomp ext explain_terms incomp.terms))
          | true, true ->
              Format.fprintf fmt "Because %a and %a, %a." explain_incomp cause1
                explain_incomp cause2 explain_terms incomp.terms);
          if count_caused incomp root.cause > 1 then
            Format.fprintf fmt " (%d)" (set_line_number incomp)
          else ()
    in
    explain_incomp fmt root
end
