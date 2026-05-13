(** Min priority queue keyed on a name with an integer priority. Ties broken by the name's
    own [compare]. All operations are O(log n). *)

module Make (N : Types.NAME) : sig
  type t

  val empty : t

  val insert : t -> N.t -> int -> t
  (** [insert pq n p]: associate name [n] with priority [p]. *)

  val remove : t -> N.t -> t
  (** [remove pq n]: drop [n] from the queue if present. *)

  val update : t -> N.t -> int -> t
  (** [update pq n p]: set [n]'s priority to [p], replacing any existing entry. *)

  val min_elt : t -> (int * N.t) option
  (** [min_elt pq]: the smallest [(priority, name)] pair, or [None] when empty. *)
end
