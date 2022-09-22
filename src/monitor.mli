(*******************************************************************)
(*    This is part of Explanator2, it is distributed under the     *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Mtl
open Expl
open Util
open Interval
open Checker.VerifiedExplanator2

module Deque = Core_kernel.Deque

type mbuf2 = expl Deque.t * expl Deque.t

module Once : sig
  type moaux = {
      ts_zero: timestamp option
    ; ts_tp_in: (timestamp * timepoint) Deque.t
    ; ts_tp_out: (timestamp * timepoint) Deque.t
    ; s_alphas_in: (timestamp * expl) Deque.t
    ; s_alphas_out: (timestamp * expl) Deque.t
    ; v_alphas_in: (timestamp * vexpl) Deque.t
    ; v_alphas_out: (timestamp * vexpl) Deque.t
    ; }
end

module Historically : sig
  type mhaux = {
      ts_zero: timestamp option
    ; ts_tp_in: (timestamp * timepoint) Deque.t
    ; ts_tp_out: (timestamp * timepoint) Deque.t
    ; s_alphas_in: (timestamp * sexpl) Deque.t
    ; s_alphas_out: (timestamp * sexpl) Deque.t
    ; v_alphas_in: (timestamp * expl) Deque.t
    ; v_alphas_out: (timestamp * expl) Deque.t
    ; }
end

module Eventually : sig
  type meaux = {
      ts_tp_out: (timestamp * timepoint) Deque.t
    ; ts_tp_in: (timestamp * timepoint) Deque.t
    ; s_alphas_in: (timestamp * expl) Deque.t
    ; v_alphas_in: (timestamp * vexpl) Deque.t
    ; optimal_proofs: (timestamp * expl) Deque.t
    ; }
end

module Always : sig
  type maaux = {
      ts_tp_out: (timestamp * timepoint) Deque.t
    ; ts_tp_in: (timestamp * timepoint) Deque.t
    ; v_alphas_in: (timestamp * expl) Deque.t
    ; s_alphas_in: (timestamp * sexpl) Deque.t
    ; optimal_proofs: (timestamp * expl) Deque.t
    ; }
end

module Since : sig
  type msaux = {
      ts_zero: timestamp option
    ; ts_tp_in: (timestamp * timepoint) Deque.t
    ; ts_tp_out: (timestamp * timepoint) Deque.t

    (* sorted deque of S^+ beta [alphas] *)
    ; s_beta_alphas_in: (timestamp * expl) Deque.t
    (* deque of S^+ beta [alphas] outside of the interval *)
    ; s_beta_alphas_out: (timestamp * expl) Deque.t

    (* sorted deque of S^- alpha [betas] *)
    ; v_alpha_betas_in: (timestamp * expl) Deque.t
    (* sorted deque of alpha proofs *)
    ; v_alphas_out: (timestamp * expl) Deque.t
    (* list of beta violations inside the interval *)
    ; v_betas_in: (timestamp * vexpl) Deque.t
    (* list of alpha/beta violations *)
    ; v_alphas_betas_out: (timestamp * vexpl option * vexpl option) Deque.t
    ; }
end

module Until : sig
  type muaux = {
      ts_tp_in: (timestamp * timepoint) Deque.t
    ; ts_tp_out: (timestamp * timepoint) Deque.t
    (* deque of sorted deques of U^+ beta [alphas] proofs where
     * ts corresponds to the timestamp of the beta proof *)
    ; alphas_beta: ((timestamp * expl) Deque.t) Deque.t
    (* most recent sequence of alpha satisfactions w/o holes *)
    ; alphas_suffix: (timestamp * sexpl) Deque.t
    (* deque of sorted deques of U^- ~alpha [~betas] proofs where
     * ts corresponds to the timestamp of the ~alpha proof *)
    ; betas_alpha: ((timestamp * expl) Deque.t) Deque.t
    (* sorted deque of alpha proofs outside the interval *)
    ; v_alphas_out: (timestamp * expl) Deque.t
    (* deque of alpha violations inside the interval *)
    ; alphas_in: (timestamp * expl) Deque.t
    (* deque of beta violations inside the interval *)
    ; betas_suffix_in: (timestamp * vexpl) Deque.t
    ; optimal_proofs: (timestamp * expl) Deque.t
    ; }
end

type mformula =
  | MTT
  | MFF
  | MP of string
  | MNeg of mformula
  | MConj of mformula * mformula * mbuf2
  | MDisj of mformula * mformula * mbuf2
  | MImp of mformula * mformula * mbuf2
  | MIff of mformula * mformula * mbuf2
  | MPrev of interval * mformula * bool * expl Deque.t * timestamp Deque.t
  | MNext of interval * mformula * bool * timestamp Deque.t
  | MOnce of interval * mformula * (timestamp * timepoint) Deque.t * Once.moaux
  | MHistorically of interval * mformula * (timestamp * timepoint) Deque.t * Historically.mhaux
  | MEventually of interval * mformula * expl Deque.t * (timestamp * timepoint) Deque.t * Eventually.meaux
  | MAlways of interval * mformula * expl Deque.t * (timestamp * timepoint) Deque.t * Always.maaux
  | MSince of interval * mformula * mformula * mbuf2 * (timestamp * timepoint) Deque.t * Since.msaux
  | MUntil of interval * mformula * mformula * mbuf2 * (timestamp * timepoint) Deque.t * Until.muaux

type state =
  { tp: timepoint
  ; mf: mformula
  ; events: (Util.SS.t * timestamp) list
  ; tp_ts: (timepoint, timestamp) Hashtbl.t
  }

val monitor_cli: in_channel -> out_channel -> mode -> out_mode -> bool -> (expl -> expl -> bool) ->
                 (string trace -> nat -> string mtl -> (string sproof, string vproof) sum -> bool) -> formula ->
             out_channel
val monitor_vis: (mformula * state) option -> string -> (expl -> expl -> bool) -> formula ->
                 (mformula * state) option * string
