open Base

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm

open Mformula

open Etc

module MState : sig

  type t = { mf: IFormula.t
           ; tp_cur: timepoint
           ; tp_out: timepoint
           ; ts_waiting: timestamp Queue.t
           ; tsdbs: (timestamp * Db.t) Queue.t
           ; tpts: (timepoint, timestamp) Hashtbl.t
           ; lets: (string * IFormula.t) list }

  val tp_cur: t -> timepoint

  val tsdbs: t -> (timestamp * Db.t) Queue.t

  val init: MFormula.t -> t

  val to_string: string -> t -> string

end

module Memo : sig

  type 'a t
  
  val find : 'a t -> IFormula.t -> Polarity.t -> 'a option
  val add_event : 'a t -> string -> 'a t
  val add_obligation : 'a t -> int -> 'a t
  val empty : 'a t

end

type res = Expl.t TS.t list * Expl.t * IFormula.t

val monitor_steps: int ref

val mstep: ?force_evaluate_lets:bool -> timestamp -> Db.t -> bool -> MState.t -> FObligations.t ->
           res Memo.t -> res Memo.t * (((timepoint * timestamp) * Expl.t) list * Expl.t * MState.t)


