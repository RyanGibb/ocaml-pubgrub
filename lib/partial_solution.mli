(** The partial solution: the assignments the solver has accumulated so far. *)

module Make (N : Types.NAME) (V : Types.VERSION) : sig
  include module type of Types.Make (N) (V)
  module NameSet : Set.S with type elt = N.t

  type assignment =
    | Decision of package
    | RootDecision
    | Derivation of term * incompatibility

  type t

  val empty : t

  val add : t -> decision_level -> assignment -> t
  (** [add ps lvl a]: push [a] at decision level [lvl] onto [ps]. *)

  val backtrack : t -> decision_level -> t
  (** [backtrack ps level]: drop every assignment whose decision level exceeds [level]. *)

  val assignments : t -> (assignment * decision_level) list
  (** The assignments, newest first. *)

  val name_range : t -> N.t -> bool * Ranges.t
  (** [name_range ps n]: [(has_pos, r)] where [r] is the intersection of all constraints
      on [n] and [has_pos] is true iff some assignment forces [n] to be selected. *)

  val is_decided : t -> N.t -> bool
  val root_selected : t -> bool
  val term_status : t -> term -> term_status
  val incompatibility_status : t -> incompatibility -> incomp_status

  val find_earliest_satisfier :
    t -> incompatibility -> ((assignment * decision_level) * t) option
  (** Find the earliest assignment in [ps] (oldest-first) whose inclusion first makes
      [incomp] All_satisfied. Returns the satisfier and the partial solution as it was
      BEFORE the satisfier was added. *)

  val find_previous_satisfier_level :
    t -> assignment * decision_level -> incompatibility -> decision_level
  (** [find_previous_satisfier_level ps_before satisfier incomp]: the decision level at
      which (some prefix of [ps_before] + [satisfier]) first becomes All_satisfied.
      Returns 0 if no prefix helps. *)

  val pp_assignment : Format.formatter -> assignment -> unit
  val pp_assignments : Format.formatter -> (assignment * decision_level) list -> unit
  val assignment_name : assignment -> name
end
