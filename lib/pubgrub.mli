module type NameType = sig
  type t

  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module type VersionType = sig
  type t

  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

val set_debug : bool -> unit

module Make (N : NameType) (V : VersionType) : sig
  module Ranges : module type of Ranges.Make (V)

  type incompatibility
  type query = (N.t * Ranges.t) list

  val solve :
    versions:(N.t -> V.t list) ->
    dependencies:(N.t -> V.t -> (N.t * Ranges.t) list) ->
    query ->
    ((N.t * V.t) list, incompatibility) Result.t

  val explain_incompatibility : Format.formatter -> incompatibility -> unit
end
