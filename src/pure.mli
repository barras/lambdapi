(** Interface to PLOF. *)

type command = Parser.p_cmd Pos.loc
type state

type result =
  | OK    of state
  | Error of Pos.popt option * string

val initial_state : state

val handle_command : state -> command -> result
