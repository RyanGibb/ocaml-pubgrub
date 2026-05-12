module type ORDERED = sig
  type t

  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module Make (V : ORDERED) : sig
  type t

  val empty : t
  val full : t
  val singleton : V.t -> t
  val of_list : V.t list -> t
  val higher_than : V.t -> t
  val strictly_higher_than : V.t -> t
  val lower_than : V.t -> t
  val strictly_lower_than : V.t -> t
  val between : V.t -> V.t -> t
  val contiguous : V.t -> V.t list -> (V.t -> bool) -> t
  val union : t -> t -> t
  val intersection : t -> t -> t
  val complement : t -> t
  val difference : t -> t -> t
  val equal : t -> t -> bool
  val is_empty : t -> bool
  val contains : V.t -> t -> bool
  val subset_of : t -> t -> bool
  val is_disjoint : t -> t -> bool
  val pp : Format.formatter -> t -> unit
end
