(** Pool of incompatibilities accumulated during version solving.*)

module Make (N : Types.NameType) (V : Types.VersionType) : sig
  include module type of Types.Make (N) (V)

  type t

  val empty : t

  val add : incompatibility -> t -> t
  (** [add i t]: register [i] in the pool. *)

  val find_for_name : name -> t -> incompatibility list
  (** [find_for_name n t]: incompatibilities that mention [n]. *)

  val remove : incompatibility -> t -> t
  (** [remove i t]: drop [i] itself, compared physically, from the pool. *)
end
