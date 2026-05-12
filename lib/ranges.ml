module type ORDERED = sig
  type t

  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module Make (V : ORDERED) = struct
  type bound = Unbounded | Included of V.t | Excluded of V.t
  type segment = bound * bound

  (* A sorted list of non-overlapping (lower, upper) segments. *)
  type t = segment list

  let empty = []
  let full = [ (Unbounded, Unbounded) ]

  let equal_bound a b =
    match (a, b) with
    | Unbounded, Unbounded -> true
    | Included a, Included b | Excluded a, Excluded b -> V.compare a b = 0
    | _ -> false

  let equal a b =
    List.length a = List.length b
    && List.for_all2
         (fun (lo1, hi1) (lo2, hi2) -> equal_bound lo1 lo2 && equal_bound hi1 hi2)
         a b

  let is_empty = function [] -> true | _ -> false
  let singleton v = [ (Included v, Included v) ]
  let higher_than v = [ (Included v, Unbounded) ]
  let strictly_higher_than v = [ (Excluded v, Unbounded) ]
  let lower_than v = [ (Unbounded, Included v) ]
  let strictly_lower_than v = [ (Unbounded, Excluded v) ]

  let between lo hi =
    if V.compare lo hi >= 0 then empty else [ (Included lo, Excluded hi) ]

  (* Find the contiguous block of pred-satisfying versions containing current
     and produce a range covering it. Extends to -∞/+∞ when the block reaches
     the edges of [sorted]. Precondition: pred current = true. *)
  let contiguous current sorted pred =
    let sorted = List.sort_uniq V.compare sorted in
    let below = List.filter (fun v -> V.compare v current < 0) sorted in
    let above = List.filter (fun v -> V.compare v current > 0) sorted in
    let rec walk_up = function
      | [] -> None
      | v :: _ when not (pred v) -> Some v
      | _ :: rest -> walk_up rest
    in
    let rec walk_down lo = function
      | [] -> (lo, false)
      | v :: _ when not (pred v) -> (lo, true)
      | v :: rest -> walk_down v rest
    in
    let upper = walk_up above in
    let lo, has_lower = walk_down current (List.rev below) in
    match (has_lower, upper) with
    | false, None -> full
    | false, Some u -> strictly_lower_than u
    | true, None -> higher_than lo
    | true, Some u -> between lo u

  let of_list vs =
    List.sort_uniq V.compare vs |> List.map (fun v -> (Included v, Included v))

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

  let complement segments =
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
    match segments with [] -> [ (Unbounded, Unbounded) ] | _ -> aux Unbounded segments

  let union a b =
    (* Merge two sorted segment lists, combining overlapping/adjacent segments *)
    let rec merge la lb =
      match (la, lb) with
      | [], r | r, [] -> r
      | (ls, le) :: la', (rs, re) :: lb' ->
          if cmp_lo ls rs <= 0 then (ls, le) :: merge la' lb else (rs, re) :: merge la lb'
    in
    let sorted = merge a b in
    (* Now collapse overlapping/adjacent segments *)
    let rec collapse = function
      | [] -> []
      | [ seg ] -> [ seg ]
      | (s1, e1) :: (s2, e2) :: rest ->
          if adjacent_or_overlapping e1 s2 then
            collapse ((s1, if cmp_hi e1 e2 >= 0 then e1 else e2) :: rest)
          else (s1, e1) :: collapse ((s2, e2) :: rest)
    in
    collapse sorted

  let intersection a b =
    (* Two-pointer walk: at each step, clip the current segments against
       each other and advance whichever ends first. *)
    let rec aux la lb =
      match (la, lb) with
      | [], _ | _, [] -> []
      | (ls, le) :: la', (rs, re) :: rb' ->
          let lo = if cmp_lo ls rs >= 0 then ls else rs in
          let advance_left = cmp_hi le re <= 0 in
          let hi = if advance_left then le else re in
          let seg = if valid lo hi then [ (lo, hi) ] else [] in
          let rest = if advance_left then aux la' lb else aux la rb' in
          seg @ rest
    in
    aux a b

  let difference a b = intersection a (complement b)

  let contains v segments =
    List.exists
      (fun (lo, hi) ->
        (match lo with
          | Unbounded -> true
          | Included l -> V.compare l v <= 0
          | Excluded l -> V.compare l v < 0)
        &&
        match hi with
        | Unbounded -> true
        | Included h -> V.compare v h <= 0
        | Excluded h -> V.compare v h < 0)
      segments

  let subset_of a b =
    (* Every segment in a must be fully contained in some segment in b *)
    let rec aux la lb =
      match (la, lb) with
      | [], _ -> true
      | _, [] -> false
      | (ss, se) :: la', (cs, ce) :: cb' ->
          if cmp_lo cs ss <= 0 && cmp_hi se ce <= 0 then
            (* subset segment fits in containing segment *)
            aux la' lb
          else if not (valid ss ce) then
            (* containing segment ends before subset segment starts, advance *)
            aux la cb'
          else false
    in
    aux a b

  let is_disjoint a b = is_empty (intersection a b)

  let pp fmt = function
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
