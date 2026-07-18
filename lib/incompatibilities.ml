module Make (N : Types.NAME) (V : Types.VERSION) = struct
  include Types.Make (N) (V)

  module NameMap = Map.Make (struct
    type t = name

    let compare = compare_name
  end)

  type t = incompatibility list NameMap.t

  let empty = NameMap.empty

  (* Unique names mentioned by an incompatibility's terms. *)
  let incomp_names incomp =
    List.fold_left
      (fun acc t ->
        let n = term_name t in
        if List.exists (fun n' -> compare_name n' n = 0) acc then acc else n :: acc)
      [] incomp.terms

  let add incomp t =
    List.fold_left
      (fun m n ->
        let existing = NameMap.find_opt n m |> Option.value ~default:[] in
        NameMap.add n (incomp :: existing) m)
      t (incomp_names incomp)

  let find_for_name n t = NameMap.find_opt n t |> Option.value ~default:[]

  let mem incomp t =
    match incomp_names incomp with
    | [] -> false
    | first :: _ ->
        List.exists (fun i' -> equal_terms i'.terms incomp.terms) (find_for_name first t)
end
