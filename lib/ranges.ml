module type OrderedType = sig
  type t

  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module Make (V : OrderedType) = struct
  type bound = Unbounded | Included of V.t | Excluded of V.t
  type segment = bound * bound

  (* Sorted, non-overlapping (lower, upper) segments, in an array so that
     [contains] can search them. *)
  type t = segment array

  let of_segments l = Array.of_list l
  let segments = Array.to_list
  let empty = [||]
  let full = [| (Unbounded, Unbounded) |]

  let equal_bound a b =
    match (a, b) with
    | Unbounded, Unbounded -> true
    | Included a, Included b | Excluded a, Excluded b -> V.compare a b = 0
    | _ -> false

  let equal a b =
    Array.length a = Array.length b
    && Array.for_all2
         (fun (lo1, hi1) (lo2, hi2) -> equal_bound lo1 lo2 && equal_bound hi1 hi2)
         a b

  let is_empty a = Array.length a = 0
  let singleton v = [| (Included v, Included v) |]
  let higher_than v = [| (Included v, Unbounded) |]
  let strictly_higher_than v = [| (Excluded v, Unbounded) |]
  let lower_than v = [| (Unbounded, Included v) |]
  let strictly_lower_than v = [| (Unbounded, Excluded v) |]

  let between lo hi =
    if V.compare lo hi >= 0 then empty else [| (Included lo, Excluded hi) |]

  (* The block of [pred]-satisfying versions of [sorted] around [current]
     names no version outside [sorted]: one listed later need not satisfy
     [pred], and an incompatibility recorded over it would outlive the list.
     [dense a b] says nothing can ever be listed strictly between the adjacent
     [a] and [b], so the block may span them with one interval, and its top
     may run up to, excluding, the listed version above it, which lets the
     ranges of neighbouring blocks merge.
     Precondition: pred current = true. *)
  let contiguous ?(dense = fun _ _ -> false) current sorted pred =
    let sorted = List.sort_uniq V.compare sorted in
    let below = List.rev (List.filter (fun v -> V.compare v current < 0) sorted) in
    let above = List.filter (fun v -> V.compare v current > 0) sorted in
    let rec take = function
      | v :: rest when pred v ->
          let block, after = take rest in
          (v :: block, after)
      | rest -> ([], rest)
    in
    let lower, _ = take below in
    let upper, after = take above in
    let top hi =
      match after with next :: _ when dense hi next -> Excluded next | _ -> Included hi
    in
    let rec runs = function
      | [] -> []
      | lo :: rest -> (
          let rec extend hi = function
            | v :: rest when dense hi v -> extend v rest
            | rest -> (hi, rest)
          in
          match extend lo rest with
          | hi, [] -> [ (Included lo, top hi) ]
          | hi, rest -> (Included lo, Included hi) :: runs rest)
    in
    of_segments (runs (List.rev_append lower (current :: upper)))

  let of_list vs =
    List.sort_uniq V.compare vs
    |> List.map (fun v -> (Included v, Included v))
    |> of_segments

  let flip = function
    | Unbounded -> Unbounded
    | Included v -> Excluded v
    | Excluded v -> Included v

  (* Is lo <= hi, i.e. does this segment contain at least one point? *)
  let valid lo hi =
    match (lo, hi) with
    | Unbounded, _ | _, Unbounded -> true
    | Included a, Included b -> V.compare a b <= 0
    | Included a, Excluded b | Excluded a, Included b | Excluded a, Excluded b ->
        V.compare a b < 0

  (* Compare two lower bounds. Smaller = further left. *)
  let cmp_lo a b =
    match (a, b) with
    | Unbounded, Unbounded -> 0
    | Unbounded, _ -> -1
    | _, Unbounded -> 1
    | Included a, Included b | Excluded a, Excluded b -> V.compare a b
    | Included a, Excluded b ->
        let c = V.compare a b in
        if c = 0 then -1 (* Included is tighter *) else c
    | Excluded a, Included b ->
        let c = V.compare a b in
        if c = 0 then 1 else c

  (* Compare two upper bounds. Larger = further right. *)
  let cmp_hi a b =
    match (a, b) with
    | Unbounded, Unbounded -> 0
    | Unbounded, _ -> 1
    | _, Unbounded -> -1
    | Included a, Included b | Excluded a, Excluded b -> V.compare a b
    | Included a, Excluded b ->
        let c = V.compare a b in
        if c = 0 then 1 (* Included extends further *) else c
    | Excluded a, Included b ->
        let c = V.compare a b in
        if c = 0 then -1 else c

  (* Can these two segments be merged? i.e. is there no gap between
     upper bound hi and lower bound lo? *)
  let adjacent_or_overlapping hi lo =
    match (hi, lo) with
    | Unbounded, _ | _, Unbounded -> true
    | Included _, Included _ | Included _, Excluded _ | Excluded _, Included _ ->
        (* At the same point, Included+Included overlap, and
           Included+Excluded or Excluded+Included are adjacent *)
        V.compare
          (match hi with Included v | Excluded v -> v | Unbounded -> assert false)
          (match lo with Included v | Excluded v -> v | Unbounded -> assert false)
        >= 0
    | Excluded a, Excluded b ->
        (* Two excluded bounds at the same point leave a gap *)
        V.compare a b > 0

  let complement a =
    let rec aux lo = function
      | [] -> ( match lo with Unbounded -> [] | _ -> [ (lo, Unbounded) ])
      | (seg_lo, seg_hi) :: rest ->
          let seg =
            match seg_lo with
            | Unbounded -> []
            | _ ->
                let hi = flip seg_lo in
                if valid lo hi then [ (lo, hi) ] else []
          in
          seg @ aux (flip seg_hi) rest
    in
    match segments a with [] -> full | segments -> of_segments (aux Unbounded segments)

  (* the segments of a list built newest first *)
  let of_rev = function
    | [] -> empty
    | first :: _ as l ->
        let n = List.length l in
        let a = Array.make n first in
        List.iteri (fun i seg -> a.(n - 1 - i) <- seg) l;
        a

  let union a b =
    (* Merge the two segment arrays by lower bound, collapsing each segment
       into the last one taken where there is no gap between them *)
    let na = Array.length a and nb = Array.length b in
    let take ((s2, e2) as seg) = function
      | (s1, e1) :: rest when adjacent_or_overlapping e1 s2 ->
          (s1, if cmp_hi e1 e2 >= 0 then e1 else e2) :: rest
      | acc -> seg :: acc
    in
    let rec aux i j acc =
      if i < na && (j >= nb || cmp_lo (fst a.(i)) (fst b.(j)) <= 0) then
        aux (i + 1) j (take a.(i) acc)
      else if j < nb then aux i (j + 1) (take b.(j) acc)
      else acc
    in
    of_rev (aux 0 0 [])

  let intersection a b =
    (* Two-pointer walk: at each step, clip the current segments against
       each other and advance whichever ends first. *)
    let na = Array.length a and nb = Array.length b in
    let rec aux i j acc =
      if i >= na || j >= nb then acc
      else
        let ls, le = a.(i) and rs, re = b.(j) in
        let lo = if cmp_lo ls rs >= 0 then ls else rs in
        let advance_left = cmp_hi le re <= 0 in
        let hi = if advance_left then le else re in
        let acc = if valid lo hi then (lo, hi) :: acc else acc in
        if advance_left then aux (i + 1) j acc else aux i (j + 1) acc
    in
    of_rev (aux 0 0 [])

  (* [intersection]'s walk, stopping at the first segment it would keep *)
  let is_disjoint a b =
    let na = Array.length a and nb = Array.length b in
    let rec aux i j =
      i >= na || j >= nb
      ||
      let ls, le = a.(i) and rs, re = b.(j) in
      let lo = if cmp_lo ls rs >= 0 then ls else rs in
      let advance_left = cmp_hi le re <= 0 in
      let hi = if advance_left then le else re in
      (not (valid lo hi)) && if advance_left then aux (i + 1) j else aux i (j + 1)
    in
    aux 0 0

  let difference a b = intersection a (complement b)

  (* The segments' lower bounds ascend, so those at or below [v] are a prefix,
     and only the last of them can hold [v]. *)
  let contains v a =
    let lo_le = function
      | Unbounded -> true
      | Included l -> V.compare l v <= 0
      | Excluded l -> V.compare l v < 0
    in
    let le_hi = function
      | Unbounded -> true
      | Included h -> V.compare v h <= 0
      | Excluded h -> V.compare v h < 0
    in
    (* the first segment in [lo, hi) whose lower bound is above [v] *)
    let rec search lo hi =
      if lo >= hi then lo
      else
        let mid = (lo + hi) / 2 in
        if lo_le (fst a.(mid)) then search (mid + 1) hi else search lo mid
    in
    let i = search 0 (Array.length a) in
    i > 0 && le_hi (snd a.(i - 1))

  let subset_of a b =
    (* Every segment in a must be fully contained in some segment in b *)
    let na = Array.length a and nb = Array.length b in
    let rec aux i j =
      if i >= na then true
      else if j >= nb then false
      else
        let ss, se = a.(i) and cs, ce = b.(j) in
        if cmp_lo cs ss <= 0 && cmp_hi se ce <= 0 then
          (* subset segment fits in containing segment *)
          aux (i + 1) j
        else if not (valid ss ce) then
          (* containing segment ends before subset segment starts, advance *)
          aux i (j + 1)
        else false
    in
    aux 0 0

  let pp fmt a =
    match segments a with
    | [] -> Format.pp_print_string fmt "∅"
    | [ (Unbounded, Unbounded) ] -> Format.pp_print_string fmt "*"
    | segments ->
        Format.pp_print_list
          ~pp_sep:(fun fmt () -> Format.pp_print_string fmt " ∪ ")
          (fun fmt (lo, hi) ->
            match (lo, hi) with
            | Included a, Included b when V.compare a b = 0 ->
                Format.fprintf fmt "%a" V.pp a
            | _ -> (
                (match lo with
                | Unbounded -> Format.pp_print_string fmt "(-∞"
                | Included v -> Format.fprintf fmt "[%a" V.pp v
                | Excluded v -> Format.fprintf fmt "(%a" V.pp v);
                Format.pp_print_string fmt ", ";
                match hi with
                | Unbounded -> Format.pp_print_string fmt "+∞)"
                | Included v -> Format.fprintf fmt "%a]" V.pp v
                | Excluded v -> Format.fprintf fmt "%a)" V.pp v))
          fmt segments
end
