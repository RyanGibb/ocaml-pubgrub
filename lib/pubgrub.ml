let ( let* ) = Option.bind

module type NameType = Types.NameType
module type VersionType = Types.VersionType

let debug_enabled = ref false

let debug_printf fmt =
  if !debug_enabled then
    Format.kfprintf
      (fun _ -> Format.pp_print_flush Format.std_formatter ())
      Format.std_formatter fmt
  else Format.ifprintf Format.std_formatter fmt

let set_debug enabled = debug_enabled := enabled

module Make (N : NameType) (V : VersionType) = struct
  include Types.Make (N) (V)
  module PS = Partial_solution.Make (N) (V)
  module Incomp = Incompatibilities.Make (N) (V)
  module PQ = Priority_queue.Make (N)

  module DepMap = Map.Make (struct
    type t = N.t * N.t

    let compare (a, b) (c, d) =
      let x = N.compare a c in
      if x <> 0 then x else N.compare b d
  end)

  type state = {
    incomps : Incomp.t;
    (* the dependency incompatibilities in [incomps], by depender and dependency *)
    dep_incomps : incompatibility list DepMap.t;
    decision_level : decision_level;
    partial_solution : PS.t;
    (* Candidates for the next decision, prioritised by the number of
       available versions remaining under the current constraints. *)
    candidates : PQ.t;
  }

  let add_incomp state incomp = { state with incomps = Incomp.add incomp state.incomps }
  let add_incomps state incomps = List.fold_left add_incomp state incomps

  (* Count of available versions for [n] in the current partial solution. *)
  let count_for ~vers state n =
    let _, sr = PS.name_range state.partial_solution n in
    List.length (List.filter (fun v -> Ranges.contains v sr) (vers n))

  (* Push an assignment onto the partial solution at the current decision
     level and refresh the candidates priority queue. *)
  let add_assignment ~vers state assignment =
    let partial_solution =
      PS.add state.partial_solution state.decision_level assignment
    in
    let state = { state with partial_solution } in
    let set_count n = PQ.update state.candidates n (count_for ~vers state n) in
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

  (* Refresh the priority queue for the names whose constraints a backtrack
     changed; all other names keep their counts. *)
  let refresh_candidates ~vers state touched =
    List.fold_left
      (fun s n ->
        let candidates =
          if PS.NameSet.mem n (PS.undecided_pos_names s.partial_solution) then
            PQ.update s.candidates n (count_for ~vers s n)
          else PQ.remove s.candidates n
        in
        { s with candidates })
      state touched

  let rec conflict_resolution ~vers state original_incomp incomp :
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
                let partial_solution, touched =
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
                let state = refresh_candidates ~vers state touched in
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
                conflict_resolution ~vers state original_incomp prior_cause))

  let rec unit_propagation ~vers state changed : (state, incompatibility) Result.t =
    match changed with
    | [] -> Ok state
    | name :: changed ->
        debug_printf "unit propagation on: %a\n" pp_name name;
        let incomps = Incomp.find_for_name name state.incomps in
        incompat_propagation ~vers state changed incomps

  and incompat_propagation ~vers state changed = function
    | [] -> unit_propagation ~vers state changed
    | incomp :: incomps -> (
        match PS.incompatibility_status state.partial_solution incomp with
        | All_satisfied -> (
            match conflict_resolution ~vers state incomp incomp with
            | Ok (state, incomp, term) ->
                let assignment = PS.Derivation (negate_term term, incomp) in
                let _, name, _ = term in
                debug_printf "new assignment on level %d: %a\n" state.decision_level
                  PS.pp_assignment assignment;
                let state = add_assignment ~vers state assignment in
                unit_propagation ~vers state [ name ]
            | Error incomp -> Error incomp)
        | Almost_satisfied term ->
            let assignment = PS.Derivation (negate_term term, incomp) in
            debug_printf "new assignment on level %d: %a\n" state.decision_level
              PS.pp_assignment assignment;
            let state = add_assignment ~vers state assignment in
            let _, name, _ = term in
            incompat_propagation ~vers state (name :: changed) incomps
        | _ -> incompat_propagation ~vers state changed incomps)

  (* a negative term over the empty range can never be violated: drop it *)
  let drop_tautologies =
    List.filter (function Neg, _, r -> not (Ranges.is_empty r) | _ -> true)

  (* A dependency incompatibility names only versions whose dependencies were
     asked, as a version listed later need not share the dependency. A version
     with the same dependency range as others joins their incompatibility, as
     pubgrub-rs's merge_dependents does, and replaces it in the pool; [dense]
     then lets the union span, or run up to, versions nothing can be listed
     between. [None] when the incompatibility already names [version]. *)
  let add_dependency ?dense ~vers state n version (dep_name, dep_range) =
    let key = (n, dep_name) in
    let held = Option.value ~default:[] (DepMap.find_opt key state.dep_incomps) in
    let old, old_range =
      match
        List.find_map
          (fun i ->
            match i.cause with
            | Dependency ((_, r), (_, dr)) when Ranges.equal dr dep_range -> Some (i, r)
            | _ -> None)
          held
      with
      | Some (i, r) -> (Some i, r)
      | None -> (None, Ranges.empty)
    in
    if Ranges.contains version old_range then (state, None)
    else
      let block =
        match dense with
        | None -> Ranges.singleton version
        | Some dense ->
            let named v = V.compare v version = 0 || Ranges.contains v old_range in
            Ranges.contiguous ~dense:(dense n) version (vers n) named
      in
      let range = Ranges.union old_range block in
      let incomp =
        {
          terms =
            drop_tautologies [ (Pos, Name n, range); (Neg, Name dep_name, dep_range) ];
          cause = Dependency ((n, range), (Name dep_name, dep_range));
        }
      in
      let incomps, held =
        match old with
        | None -> (state.incomps, held)
        | Some o -> (Incomp.remove o state.incomps, List.filter (fun i -> i != o) held)
      in
      ( {
          state with
          incomps = Incomp.add incomp incomps;
          dep_incomps = DepMap.add key (incomp :: held) state.dep_incomps;
        },
        Some incomp )

  let greatest vs = List.hd (List.sort (fun a b -> V.compare b a) vs)

  let make_decision ?dense ~vers ~deps ?next ?choose state =
    let find_undecided_term () =
      match PQ.min_elt state.candidates with
      | None -> None
      | Some (_, dflt) ->
          let n =
            match next with
            | None -> dflt
            | Some pick ->
                (* which undecided name is decided first is a heuristic, so any
                   name still in the queue is a sound answer; one outside it is
                   not, and leaves the queue's own choice standing *)
                let open_names =
                  List.map (fun (c, n) -> (n, c)) (PQ.to_list state.candidates)
                in
                let assigned n = PS.selection state.partial_solution n in
                let n = pick ~assigned open_names in
                let matches (m, _) = m == n || N.compare m n = 0 in
                Option.fold ~none:dflt ~some:fst (List.find_opt matches open_names)
          in
          let _, sr = PS.name_range state.partial_solution n in
          let real_vs = List.filter (fun v -> Ranges.contains v sr) (vers n) in
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
        let version =
          match choose with
          | None -> greatest real_vs
          | Some pick ->
              (* a pick from outside [real_vs] would decide a version the
                 current constraints exclude, so it is discarded *)
              let assigned n = PS.selection state.partial_solution n in
              let v = pick ~assigned n real_vs in
              let matches c = c == v || V.compare c v = 0 in
              Option.value (List.find_opt matches real_vs) ~default:(greatest real_vs)
        in
        debug_printf "trying version %a\n" V.pp version;
        let state, dep_incomps =
          List.fold_left
            (fun (state, added) dep ->
              match add_dependency ?dense ~vers state n version dep with
              | state, Some i -> (state, i :: added)
              | state, None -> (state, added))
            (state, []) (deps n version)
        in
        let dep_incomps = List.rev dep_incomps in
        if List.length dep_incomps > 0 then
          debug_printf "dependency incompatibilities\n\t%a\n" pp_incompatibilities
            dep_incomps;
        let trial_state =
          add_assignment ~vers { state with decision_level } (PS.Decision (n, version))
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
          terms =
            drop_tautologies [ (Pos, Root, Ranges.full); (Neg, dep_name, dep_range) ];
          cause = RootDependency dep;
        })
      query

  type query = (N.t * Ranges.t) list

  let solve ?next ?choose ?dense ~vers ~deps (query : query) :
      ((N.t * V.t) list, incompatibility) Result.t =
    let root_deps = List.map (fun (name, range) -> (Name name, range)) query in
    let rec solve_loop state decided =
      match unit_propagation ~vers state [ decided ] with
      | Error incomp -> Error incomp
      | Ok state -> (
          match make_decision ?dense ~vers ~deps ?next ?choose state with
          | None -> Ok (extract_resolution state)
          | Some (decided, state) -> solve_loop state decided)
    in
    let incomps = init_incomps root_deps in
    debug_printf "initial incompatibilities\n\t%a\n" pp_incompatibilities incomps;
    let partial_solution = PS.add PS.empty 0 PS.RootDecision in
    let initial_state =
      add_incomps
        {
          incomps = Incomp.empty;
          dep_incomps = DepMap.empty;
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
    | [] | [ (Pos, Root, _) ] -> Format.fprintf fmt "version solving failed"
    | terms ->
        Format.fprintf fmt "%a is forbidden"
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
      | NoVersions -> (
          match incomp.terms with
          | [ (Pos, n, vs) ] ->
              Format.fprintf fmt "no versions of %a match %a" pp_name n Ranges.pp vs
          | terms -> explain_terms fmt terms)
      | Dependency ((d, dr), (n, r)) ->
          Format.fprintf fmt "%a %a -> %a %a" N.pp d Ranges.pp dr pp_name n Ranges.pp r
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
                      Format.fprintf fmt "%a\n%a\nThus, %a." explain_incomp complex
                        explain_incomp simple explain_terms incomp.terms
                  | None ->
                      let line1 = set_line_number cause1 in
                      let line2 = set_line_number cause2 in
                      Format.fprintf fmt "%a (%d)\n\n%a (%d)\nThus, %a." explain_incomp
                        cause1 line1 explain_incomp cause2 line2 explain_terms
                        incomp.terms))
          | false, _ | _, false -> (
              let derived, ext =
                if is_external cause1 then (cause2, cause1) else (cause1, cause2)
              in
              match Hashtbl.find_opt line_numbers derived with
              | Some line ->
                  Format.fprintf fmt "Because %a and %a (%d), %a." explain_incomp ext
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
                      Format.fprintf fmt "%a\nAnd because %a and %a, %a." explain_incomp
                        prior_derived explain_incomp prior_external explain_incomp ext
                        explain_terms incomp.terms
                  | _ ->
                      Format.fprintf fmt "%a\nAnd because %a, %a." explain_incomp derived
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
