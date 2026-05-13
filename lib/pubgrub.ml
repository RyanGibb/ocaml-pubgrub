let ( let* ) = Option.bind

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

let debug_enabled = ref false

let debug_printf fmt =
  if !debug_enabled then
    Format.kfprintf
      (fun _ -> Format.pp_print_flush Format.std_formatter ())
      Format.std_formatter fmt
  else Format.ifprintf Format.std_formatter fmt

let set_debug enabled = debug_enabled := enabled

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

  type assignment =
    | Decision of package
    | RootDecision
    | Derivation of term * incompatibility

  type solution = (assignment * decision_level) list

  type state = {
    incomps : incompatibility list;
    solution : solution;
    decision_level : decision_level;
  }

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

  let pp_assignment fmt = function
    | Decision package -> Format.fprintf fmt "Decision %a" pp_package package
    | RootDecision -> Format.fprintf fmt "Decision root"
    | Derivation (term, cause) ->
        Format.fprintf fmt "Derivation %a due to incompatibility %a" pp_term term
          pp_incompatibility cause

  let pp_solution fmt =
    Format.(
      pp_print_list
        ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ")
        (fun fmt (a, d) -> fprintf fmt "(%d: %a)" d pp_assignment a))
      fmt

  type term_status = Satisfied | Contradicted | Undetermined

  type incomp_status =
    | All_satisfied
    | Some_contradicted
    | Almost_satisfied of term
    | Incomp_undetermined

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

  let assignment_name = function
    | Decision (n, _) -> Name n
    | RootDecision -> Root
    | Derivation ((_, name, _), _) -> name

  (* Compute the effective range for a name from the solution, and whether
     there's any positive derivation for it. *)
  let solution_range n solution =
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
    aux false solution

  let root_selected solution =
    List.exists (fun (a, _) -> match a with RootDecision -> true | _ -> false) solution

  let term_status solution (pol, name, vs) =
    match name with
    | Root -> (
        let selected = root_selected solution in
        match (selected, pol) with
        | true, Pos -> Satisfied
        | true, Neg -> Contradicted
        | false, Pos -> Undetermined
        | false, Neg -> Satisfied)
    | Name n -> (
        let has_positive, sr = solution_range n solution in
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

  let incompatibility_status solution incomp : incomp_status =
    let rec aux s = function
      | [] -> s
      | t :: ts -> (
          match (s, term_status solution t) with
          | All_satisfied, Satisfied -> aux All_satisfied ts
          | All_satisfied, Undetermined -> aux (Almost_satisfied t) ts
          | Almost_satisfied t, Satisfied -> aux (Almost_satisfied t) ts
          | Almost_satisfied _, Undetermined -> aux Incomp_undetermined ts
          | Some_contradicted, _ -> Some_contradicted
          | _, Contradicted -> Some_contradicted
          | Incomp_undetermined, _ -> aux Incomp_undetermined ts)
    in
    aux All_satisfied incomp.terms

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
    match result with
    | _ :: _ :: _ -> List.filter (function Pos, Root, _ -> false | _ -> true) result
    | _ -> result

  let rec conflict_resolution state original_incomp incomp :
      (state * incompatibility * term, incompatibility) Result.t =
    debug_printf "conflict resolution on: %a\n" pp_incompatibility incomp;
    let rec find_earliest_satisfier incomp = function
      | [] -> []
      | assignment :: assignments -> (
          match find_earliest_satisfier incomp assignments with
          | [] -> (
              match incompatibility_status (assignment :: assignments) incomp with
              | All_satisfied -> assignment :: assignments
              | _ -> [])
          | solution -> solution)
    in
    let rec find_previous_satisfier satisfier incomp = function
      | [] -> []
      | assignment :: assignments -> (
          match find_previous_satisfier satisfier incomp assignments with
          | [] -> (
              match
                incompatibility_status (satisfier :: assignment :: assignments) incomp
              with
              | All_satisfied -> assignment :: assignments
              | _ -> [])
          | solution -> solution)
    in
    match incomp.terms with
    | [] -> Error incomp
    | [ (Pos, Root, _) ] -> Error incomp
    | _ -> (
        let (satisfier, satisfier_decision_level), assignments =
          match find_earliest_satisfier incomp state.solution with
          | assignment :: assignments -> (assignment, assignments)
          | _ -> failwith "Incompatibility not satisfied"
        in
        debug_printf "satisfiying assignment on level %d: %a\n" satisfier_decision_level
          pp_assignment satisfier;
        let term =
          let name = assignment_name satisfier in
          List.find (fun t -> compare_name (term_name t) name = 0) incomp.terms
        in
        let previous_satisfier_level =
          match
            find_previous_satisfier
              (satisfier, satisfier_decision_level)
              incomp assignments
          with
          | (_, decision_level) :: _ -> decision_level
          | _ -> 0
        in
        match (satisfier, satisfier_decision_level != previous_satisfier_level) with
        | Decision _, _ | RootDecision, _ | _, true ->
            debug_printf "backtracking to level %d\n" previous_satisfier_level;
            let solution =
              List.filter
                (fun (_assignment, decision_level) ->
                  decision_level <= previous_satisfier_level)
                state.solution
            in
            debug_printf "solution: %a\n" pp_solution solution;
            let incomps =
              if incomp != original_incomp then (
                debug_printf "new incompatibility %a\n" pp_incompatibility incomp;
                incomp :: state.incomps)
              else state.incomps
            in
            let state =
              { incomps; solution; decision_level = previous_satisfier_level }
            in
            Ok (state, incomp, term)
        | Derivation (satisfier_term, cause), _ ->
            let base_terms =
              incomp.terms @ cause.terms
              |> List.filter (fun t -> compare_name (term_name t) (term_name term) <> 0)
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
            conflict_resolution state original_incomp prior_cause)

  let rec unit_propagation state changed : (state, incompatibility) Result.t =
    match changed with
    | [] -> Ok state
    | name :: changed ->
        debug_printf "unit propagation on: %a\n" pp_name name;
        let incomps =
          List.filter
            (fun incomp ->
              List.exists (fun t -> compare_name (term_name t) name = 0) incomp.terms)
            state.incomps
        in
        incompat_propagation state changed incomps

  and incompat_propagation state changed = function
    | [] -> unit_propagation state changed
    | incomp :: incomps -> (
        match incompatibility_status state.solution incomp with
        | All_satisfied -> (
            match conflict_resolution state incomp incomp with
            | Ok (state, incomp, term) ->
                let assignment = Derivation (negate_term term, incomp) in
                let _, name, _ = term in
                debug_printf "new assignment on level %d: %a\n" state.decision_level
                  pp_assignment assignment;
                let state =
                  {
                    state with
                    solution = (assignment, state.decision_level) :: state.solution;
                  }
                in
                unit_propagation state [ name ]
            | Error incomp -> Error incomp)
        | Almost_satisfied term ->
            let assignment = Derivation (negate_term term, incomp) in
            debug_printf "new assignment on level %d: %a\n" state.decision_level
              pp_assignment assignment;
            let solution = (assignment, state.decision_level) :: state.solution in
            let state = { state with solution } in
            let _, name, _ = term in
            incompat_propagation state (name :: changed) incomps
        | _ -> incompat_propagation state changed incomps)

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
          terms = [ (Pos, Name n, depender_range); (Neg, Name dep_name, dep_range) ];
          cause = Dependency ((n, version), (Name dep_name, dep_range));
        })
      (dependencies n version)

  let make_decision ~versions ~dependencies state =
    let find_undecided_term () =
      let rec aux best = function
        | [] -> best
        | (Derivation ((Pos, Name n, _), _), _) :: solution ->
            let _, sr = solution_range n state.solution in
            let real_vs = List.filter (fun v -> Ranges.contains v sr) (versions n) in
            let decided =
              List.exists
                (fun (a, _) ->
                  match a with Decision (n', _) -> N.compare n' n = 0 | _ -> false)
                state.solution
            in
            if decided then aux best solution
            else
              let count = List.length real_vs in
              let best =
                match best with
                | Some (_, _, c) when c <= count -> best
                | _ -> Some (n, real_vs, count)
              in
              aux best solution
        | _ :: solution -> aux best solution
      in
      aux None state.solution |> Option.map (fun (n, vs, _) -> (n, vs))
    in
    let* n, real_vs = find_undecided_term () in
    let _, sr = solution_range n state.solution in
    debug_printf "deciding on %a: %a\n" N.pp n Ranges.pp sr;
    let decision_level = state.decision_level + 1 in
    match real_vs with
    | [] ->
        let incomp = { terms = [ (Pos, Name n, sr) ]; cause = NoVersions } in
        debug_printf "no versions found, adding incompatiblity %a\n" pp_incompatibility
          incomp;
        let state = { state with incomps = incomp :: state.incomps } in
        Some (Name n, state)
    | _ ->
        let version = List.hd (List.sort (fun a b -> V.compare b a) real_vs) in
        debug_printf "trying version %a\n" V.pp version;
        let dep_incomps =
          dependency_incomps ~versions ~dependencies n version
          |> List.filter (fun i ->
              not (List.exists (fun i' -> equal_terms i'.terms i.terms) state.incomps))
        in
        if List.length dep_incomps > 0 then
          debug_printf "dependency incompatibilities\n\t%a\n" pp_incompatibilities
            dep_incomps;
        let incomps = dep_incomps @ state.incomps in
        let state = { state with incomps } in
        let conflicts =
          List.exists
            (fun i ->
              let solution = (Decision (n, version), decision_level) :: state.solution in
              match incompatibility_status solution i with
              | All_satisfied -> true
              | _ -> false)
            dep_incomps
        in
        if conflicts then (
          debug_printf "not adding decision due to conflict\n";
          Some (Name n, state))
        else
          let assignment = Decision (n, version) in
          debug_printf "assignment on level %d: %a\n" decision_level pp_assignment
            assignment;
          let solution = (assignment, decision_level) :: state.solution in
          let state = { incomps; solution; decision_level } in
          Some (Name n, state)

  let extract_resolution state =
    List.filter_map (function Decision pkg, _ -> Some pkg | _ -> None) state.solution

  let init_incomps query =
    List.map
      (fun ((dep_name, dep_range) as dep) ->
        {
          terms = [ (Pos, Root, Ranges.full); (Neg, dep_name, dep_range) ];
          cause = RootDependency dep;
        })
      query

  type query = (N.t * Ranges.t) list

  let solve ~versions ~dependencies (query : query) :
      ((N.t * V.t) list, incompatibility) Result.t =
    let root_deps = List.map (fun (name, range) -> (Name name, range)) query in
    let rec solve_loop state next =
      match unit_propagation state [ next ] with
      | Error incomp -> Error incomp
      | Ok state -> (
          match make_decision ~versions ~dependencies state with
          | None -> Ok (extract_resolution state)
          | Some (next, state) -> solve_loop state next)
    in
    let incomps = init_incomps root_deps in
    debug_printf "initial incompatibilities\n\t%a\n" pp_incompatibilities incomps;
    (* Root is pre-seeded as RootDecision rather than derived from a
       {not Root any} incomp via unit propagation. Sits at decision level 0
       per the spec's example tables. *)
    let root_assignment = (RootDecision, 0) in
    solve_loop { incomps; solution = [ root_assignment ]; decision_level = 0 } Root

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
