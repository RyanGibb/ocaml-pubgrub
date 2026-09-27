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

  (** What the partial solution says about a name. [Entailed r] is already forced into the
      solution, with [r] the versions still open to it; it will be decided before solving
      ends, so it counts as selected alongside [Decided]. *)
  type selection = Unselected | Entailed of Ranges.t | Decided of V.t

  val solve :
    ?next:(assigned:(N.t -> selection) -> (N.t * int) list -> N.t) ->
    ?choose:(assigned:(N.t -> selection) -> N.t -> V.t list -> V.t) ->
    ?dense:(N.t -> V.t -> V.t -> bool) ->
    vers:(N.t -> V.t list) ->
    deps:(N.t -> V.t -> (N.t * Ranges.t) list) ->
    query ->
    ((N.t * V.t) list, incompatibility) Result.t
  (** [next ~assigned open_names] picks which name to decide next. [open_names] is the
      non-empty list of names still awaiting a decision, each with how many versions the
      accumulated constraints still allow it, ordered by the solver's own preference
      (fewest first). Which one is taken is only ever a heuristic -- every open name is a
      sound answer -- so the hook is free to impose any order it likes; a result outside
      the list is discarded and the solver's own choice stands.

      [choose ~assigned n candidates] then picks which of [candidates] to try for [n].
      [candidates] is non-empty and holds the versions of [n] the accumulated constraints
      still allow; a result outside it is discarded, so the hook can reorder but never
      widen the search. Omitted, the solver takes the greatest candidate by [V.compare].

      Both hooks receive [assigned], what the partial solution currently says about any
      name. Omitting them leaves the solver's behaviour exactly as it was.

      The lookups may be those of an instance still being loaded, provided that:
      - [vers n] may grow between calls, and only grow;
      - [deps n v] is the same at every call;
      - every range in [deps] and in the query names only versions [vers] lists when the
        range is handed over, and no interval in it can later take in a version listed
        after it.

      Every range the solver records then names only listed versions, so it never records
      that some range of a name has no versions, and the outcome is that of the final
      lists: a solution is one of theirs, and a failure proves they have none.

      A dependency incompatibility names its depender's versions as points, as one listed
      later need not share the dependency. [dense n a b] says no version of [n] can ever
      be listed strictly between the adjacent listed [a] and [b], so it may span them with
      one interval, or run up to [b], excluding it, when [b] lacks the dependency. *)

  val explain_incompatibility : Format.formatter -> incompatibility -> unit
end
