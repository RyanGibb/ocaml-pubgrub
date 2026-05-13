(** Shared types and basic operations used by the PubGrub solver. *)

module type NAME = sig
  type t

  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module type VERSION = sig
  type t

  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module Make (N : NAME) (V : VERSION) : sig
  module Ranges : module type of Ranges.Make (V)

  type name = Root | Name of N.t
  type package = N.t * V.t
  type polarity = Pos | Neg
  type term = polarity * name * Ranges.t

  type cause =
    | NoVersions
    | Dependency of package * (name * Ranges.t)
    | RootDependency of (name * Ranges.t)
    | Derived of incompatibility * incompatibility

  and incompatibility = { terms : term list; cause : cause }

  type decision_level = int
  type term_status = Satisfied | Contradicted | Undetermined

  type incomp_status =
    | All_satisfied
    | Some_contradicted
    | Almost_satisfied of term
    | Incomp_undetermined

  val compare_name : name -> name -> int
  val pp_name : Format.formatter -> name -> unit
  val pp_package : Format.formatter -> package -> unit
  val pp_polarity : Format.formatter -> polarity -> unit
  val pp_term : Format.formatter -> term -> unit
  val pp_terms : Format.formatter -> term list -> unit
  val pp_cause : Format.formatter -> cause -> unit
  val pp_incompatibility : Format.formatter -> incompatibility -> unit
  val pp_incompatibilities : Format.formatter -> incompatibility list -> unit
  val term_name : term -> name
  val equal_term : term -> term -> bool
  val equal_terms : term list -> term list -> bool

  val negate_term : term -> term
  (** Flip the polarity of a term. *)

  val term_satisfies : term -> term -> bool
  (** [term_satisfies s t]: does the assignment described by [s] force [t]? *)

  val term_not_difference : term -> term -> term
  (** [term_not_difference s t]: the negation of [s] restricted to outside [t]. Used
      during conflict resolution to build prior causes. *)

  val normalise_terms : term list -> term list
  (** Combine terms in a list that refer to the same name. Positive terms with the same
      name intersect, negative terms with the same name union, and mixed-polarity
      collisions take the difference. *)
end
