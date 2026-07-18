module Make (N : Types.NAME) (V : Types.VERSION) = struct
  include Types.Make (N) (V)

  type t = incompatibility list

  let empty = []
  let add incomp t = incomp :: t

  let find_for_name n t =
    List.filter
      (fun incomp ->
        List.exists (fun tm -> compare_name (term_name tm) n = 0) incomp.terms)
      t

  let mem incomp t = List.exists (fun i' -> equal_terms i'.terms incomp.terms) t
end
