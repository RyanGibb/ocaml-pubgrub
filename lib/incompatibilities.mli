(** Pool of incompatibilities accumulated during version solving.*)

module Make (N : Types.NAME) (V : Types.VERSION) : sig
  include module type of Types.Make (N) (V)

  type t

  val empty : t

  val add : incompatibility -> t -> t
  (** [add i t]: register [i] in the pool. *)

  val find_for_name : name -> t -> incompatibility list
  (** [find_for_name n t]: incompatibilities that mention [n]. *)

  val mem : incompatibility -> t -> bool
  (** [mem i t]: is some incompatibility already in [t] with the same terms as [i]? *)
end
