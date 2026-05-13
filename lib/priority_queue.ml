module Make (N : Types.NAME) = struct
  module NMap = Map.Make (N)

  module Entry = struct
    type t = int * N.t

    let compare (p1, n1) (p2, n2) =
      let c = Int.compare p1 p2 in
      if c <> 0 then c else N.compare n1 n2
  end

  module EntrySet = Set.Make (Entry)

  type t = { priority : int NMap.t; by_priority : EntrySet.t }

  let empty = { priority = NMap.empty; by_priority = EntrySet.empty }

  let insert pq n p =
    {
      priority = NMap.add n p pq.priority;
      by_priority = EntrySet.add (p, n) pq.by_priority;
    }

  let remove pq n =
    match NMap.find_opt n pq.priority with
    | None -> pq
    | Some p ->
        {
          priority = NMap.remove n pq.priority;
          by_priority = EntrySet.remove (p, n) pq.by_priority;
        }

  let update pq n p = insert (remove pq n) n p
  let min_elt pq = EntrySet.min_elt_opt pq.by_priority
end
