(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Util

type sexpl =
  | STT of int
  | SAtom of int * string
  | SNeg of vexpl
  | SDisjL of sexpl
  | SDisjR of sexpl
  | SConj of sexpl * sexpl
  | SImplL of vexpl
  | SImplR of sexpl
  | SIffS of sexpl * sexpl
  | SIffV of vexpl * vexpl
  | SPrev of sexpl
  | SOnce of int * sexpl
  | SHistorically of sexpl list
  | SNext of sexpl
  | SEventually of int * sexpl
  | SAlways of sexpl list
  | SSince of sexpl * sexpl list
  | SUntil of sexpl * sexpl list
and vexpl =
  | VFF of int
  | VAtom of int * string
  | VNeg of sexpl
  | VDisj of vexpl * vexpl
  | VConjL of vexpl
  | VConjR of vexpl
  | VImpl of sexpl * vexpl
  | VIffL of sexpl * vexpl
  | VIffR of vexpl * sexpl
  | VPrev0
  | VPrevOutL of int
  | VPrevOutR of int
  | VPrev of vexpl
  | VOnce of vexpl list
  | VHistorically of int * vexpl
  | VNextOutL of int
  | VNextOutR of int
  | VNext of vexpl
  | VEventually of vexpl list
  | VAlways of int * vexpl
  | VSince of int * vexpl * vexpl list
  | VSinceInf of int * int * vexpl list
  | VSinceOutL of int
  | VUntil of int * vexpl * vexpl list
  | VUntilInf of int * int * vexpl list

type expl = S of sexpl | V of vexpl

exception VEXPL
exception SEXPL

let unS = function S p -> p | _ -> raise VEXPL
let unV = function V p -> p | _ -> raise SEXPL

let expl_to_bool = function
  | S _ -> true
  | V _ -> false

let sappend sp sp1 = match sp with
  | SSince (sp2, sp1s) -> SSince (sp2, List.append sp1s [sp1])
  | SUntil (sp2, sp1s) -> SUntil (sp2, sp1 :: sp1s)
  | _ -> failwith "Bad arguments for sappend"

let vappend vp vp2 = match vp with
  | VSince (i, vp1, vp2s) -> VSince (i,  vp1, List.append vp2s [vp2])
  | VSinceInf (i, etp, vp2s) -> VSinceInf (i, etp, List.append vp2s [vp2])
  | VUntil (i, vp1, vp2s) -> VUntil (i, vp1, vp2 :: vp2s)
  | VUntilInf (i, ltp, vp2s) -> VUntilInf (i, ltp, vp2 :: vp2s)
  | _ -> failwith "Bad arguments for vappend"

let sdrop sp = match sp with
  | SUntil (sp2, sp1s) -> SUntil (sp2, drop_front sp1s)
  | _ -> failwith "Bad arguments for sdrop"

let vdrop vp = match vp with
  | VUntil (i, vp1, vp2s) -> VUntil (i, vp1, drop_front vp2s)
  | VUntilInf (i, ltp, vp2s) -> VUntilInf (i, ltp, drop_front vp2s)
  | _ -> failwith "Bad arguments for vdrop"

let slift = function
  | SOnce (i, sp) -> SOnce (i + 1, sp)
  | SEventually (i, sp) -> SEventually (i - 1, sp)
  | _ -> failwith "Bad arguments for slift"

let vlift = function
  | VHistorically (i, vp) -> VHistorically (i + 1, vp)
  | VAlways (i, vp) -> VAlways (i - 1, vp)
  | _ -> failwith "Bad arguments for vlift"

let rec s_at = function
  | STT i -> i
  | SAtom (i, _) -> i
  | SNeg vphi -> v_at vphi
  | SDisjL sphi -> s_at sphi
  | SDisjR spsi -> s_at spsi
  | SConj (sphi, spsi) -> s_at sphi
  | SImplL vphi -> v_at vphi
  | SImplR spsi -> s_at spsi
  | SIffS (sphi, spsi) -> s_at sphi
  | SIffV (vphi, vspi) -> v_at vphi
  | SPrev sphi -> s_at sphi + 1
  | SOnce (i, _) -> i
  | SHistorically sphis -> s_at (last sphis)
  | SNext sphi -> s_at sphi - 1
  | SEventually (i, _) -> i
  | SAlways sphis -> s_at (List.hd sphis)
  | SSince (spsi, sphis) -> (match sphis with
      | [] -> s_at spsi
      | _ -> s_at (last sphis))
  | SUntil (spsi, sphis) -> (match sphis with
      | [] -> s_at spsi
      | x::xs -> s_at x)
and v_at = function
  | VFF i -> i
  | VAtom (i, _) -> i
  | VNeg sphi -> s_at sphi
  | VDisj (vphi, vpsi) -> v_at vphi
  | VConjL vphi -> v_at vphi
  | VConjR vpsi -> v_at vpsi
  | VImpl (sphi, vpsi) -> s_at sphi
  | VIffL (sphi, vpsi) -> s_at sphi
  | VIffR (vphi, sspi) -> v_at vphi
  | VPrev0 -> 0
  | VPrevOutL i -> i
  | VPrevOutR i -> i
  | VPrev vphi -> v_at vphi + 1
  | VOnce vphis -> v_at (last vphis)
  | VHistorically (i, _) -> i
  | VNextOutL i -> i
  | VNextOutR i -> i
  | VNext vphi -> v_at vphi - 1
  | VEventually vphis -> v_at (List.hd vphis)
  | VAlways (i, _) -> i
  | VSince (i, _, _) -> i
  | VSinceInf (i, _, _) -> i
  | VSinceOutL i -> i
  | VUntil (i, _, _) -> i
  | VUntilInf (i, _, _) -> i

let p_at = function
| S s_p -> s_at s_p
| V v_p -> v_at v_p

(***********************************
 *                                 *
 * Measure: size                   *
 *                                 *
 ***********************************)
let rec s_size = function
  | STT _ -> 1
  | SAtom (_, _) -> 1
  | SNeg expl -> 1 + v_size expl
  | SDisjL sphi -> 1 + s_size sphi
  | SDisjR spsi -> 1 + s_size spsi
  | SConj (sphi, spsi) -> 1 + s_size sphi + s_size spsi
  | SImplL vphi -> 1 + v_size vphi
  | SImplR spsi -> 1 + s_size spsi
  | SIffS (sphi, spsi) -> 1 + s_size sphi + s_size spsi
  | SIffV (vphi, vpsi) -> 1 + v_size vphi + v_size vpsi
  | SPrev expl -> 1 + s_size expl
  | SOnce (i, expl) -> 1 + s_size expl
  | SHistorically expls -> 1 + sum s_size expls
  | SNext expl -> 1 + s_size expl
  | SEventually (i, expl) -> 1 + s_size expl
  | SAlways expls -> 1 + sum s_size expls
  | SSince (spsi, sphis) -> 1 + s_size spsi + sum s_size sphis
  | SUntil (spsi, sphis) -> 1 + s_size spsi + sum s_size sphis
and v_size = function
  | VFF _ -> 1
  | VAtom (_, _) -> 1
  | VNeg sphi -> 1 + s_size sphi
  | VDisj (vphi, vpsi) -> 1 + v_size vphi + v_size vpsi
  | VConjL vphi -> 1 + v_size vphi
  | VConjR vpsi -> 1 + v_size vpsi
  | VImpl (sphi, vpsi) -> 1 + s_size sphi + v_size vpsi
  | VIffL (sphi, vpsi) -> 1 + s_size sphi + v_size vpsi
  | VIffR (vphi, spsi) -> 1 + v_size vphi + s_size spsi
  | VPrev0 -> 1
  | VPrevOutL _ -> 1
  | VPrevOutR _ -> 1
  | VPrev vphi -> 1 + v_size vphi
  | VOnce expls -> 1 + sum v_size expls
  | VHistorically (i, expl) -> 1 + v_size expl
  | VNextOutL _ -> 1
  | VNextOutR _ -> 1
  | VNext vphi -> 1 + v_size vphi
  | VEventually expls -> 1 + sum v_size expls
  | VAlways (_, expl) -> 1 + v_size expl
  | VSince (_, vphi, vpsis) -> 1 + v_size vphi + sum v_size vpsis
  | VSinceInf (i, _, vpsis) -> 1 + sum v_size vpsis
  | VSinceOutL _ -> 1
  | VUntil (i, vphi, vpsis) -> 1 + v_size vphi + sum v_size vpsis
  | VUntilInf (i, _, vpsis) -> 1 + sum v_size vpsis

let size = function
  | S s_p -> s_size s_p
  | V v_p -> v_size v_p

let size_le = mk_le size

let minsize a b = if size a <= size b then a else b
let minsize_list = function
  | [] -> failwith "empty list for minsize_list"
  | x::xs -> List.fold_left minsize x xs

(***********************************
 *                                 *
 * Measure: width                  *
 *                                 *
 ***********************************)
let rec s_high = function
  | STT i -> i
  | SAtom (i, _) -> i
  | SNeg vphi -> v_high vphi
  | SDisjL sphi -> s_high sphi
  | SDisjR spsi -> s_high spsi
  | SConj (sphi, spsi) -> max (s_high sphi) (s_high spsi)
  | SImplL vphi -> v_high vphi
  | SImplR spsi -> s_high spsi
  | SIffS (sphi, spsi) -> max (s_high sphi) (s_high spsi)
  | SIffV (vphi, vpsi) -> max (v_high vphi) (v_high vpsi)
  | SPrev sphi -> max (s_at (SPrev sphi)) (s_high sphi)
  | SOnce (i, sphi) -> max i (s_high sphi)
  | SHistorically sphis -> max_list (List.map s_high sphis)
  | SNext sphi -> max (s_at (SNext sphi)) (s_high sphi)
  | SEventually (i, sphi) -> max i (s_high sphi)
  | SAlways sphis -> max_list (List.map s_high sphis)
  | SSince (spsi, sphis) -> max (s_high spsi) (max_list (List.map s_high sphis))
  | SUntil (spsi, sphis) -> max (s_high spsi) (max_list (List.map s_high sphis))
and v_high p = match p with
  | VFF i -> i
  | VAtom (i, _) -> i
  | VNeg sphi -> s_high sphi
  | VDisj (vphi, vpsi) -> max (v_high vphi) (v_high vpsi)
  | VConjL vphi -> v_high vphi
  | VConjR vpsi -> v_high vpsi
  | VImpl (sphi, vpsi) -> max (s_high sphi) (v_high vpsi)
  | VIffL (sphi, vpsi) -> max (s_high sphi) (v_high vpsi)
  | VIffR (vphi, spsi) -> max (v_high vphi) (s_high spsi)
  | VPrev0 -> 0
  | VPrevOutL i -> i
  | VPrevOutR i -> i
  | VPrev vphi -> max (v_at (VPrev vphi)) (v_high vphi)
  | VOnce vphis -> max_list (List.map v_high vphis)
  | VHistorically (i, vphi) -> max i (v_high vphi)
  | VNextOutL i -> i
  | VNextOutR i -> i
  | VNext vphi -> max (v_at (VNext vphi)) (v_high vphi)
  | VEventually vphis -> max_list (List.map v_high vphis)
  | VAlways (i, vphi) -> max i (v_high vphi)
  (* TODO: Check if we should consider i here *)
  | VSince (_, vphi, vpsis) -> max (v_high vphi) (max_list (List.map v_high vpsis))
  | VSinceInf (_, _, vpsis) -> max_list (List.map v_high vpsis)
  | VSinceOutL i -> i
  | VUntil (_, vphi, vpsis) -> max (v_high vphi) (max_list (List.map v_high vpsis))
  | VUntilInf (_, _, vpsis) -> max_list (List.map v_high vpsis)

let rec s_low = function
  | STT i -> i
  | SAtom (i, _) -> i
  | SNeg vphi -> v_low vphi
  | SDisjL sphi -> s_low sphi
  | SDisjR spsi -> s_low spsi
  | SConj (sphi, spsi) -> min (s_low sphi) (s_low spsi)
  | SImplL vphi -> v_low vphi
  | SImplR spsi -> s_low spsi
  | SIffS (sphi, spsi) -> min (s_low sphi) (s_low spsi)
  | SIffV (vphi, vpsi) -> min (v_low vphi) (v_low vpsi)
  | SPrev sphi -> min (s_at (SPrev sphi)) (s_low sphi)
  | SOnce (i, sphi) -> min i (s_low sphi)
  | SHistorically sphis -> min_list (List.map s_low sphis)
  | SNext sphi -> min (s_at (SNext sphi)) (s_low sphi)
  | SEventually (i, sphi) -> min i (s_low sphi)
  | SAlways sphis -> min_list (List.map s_low sphis)
  | SSince (spsi, sphis) -> min (s_low spsi) (min_list (List.map s_low sphis))
  | SUntil (spsi, sphis) -> min (s_low spsi) (min_list (List.map s_low sphis))
and v_low p = match p with
  | VFF i -> i
  | VAtom (i, _) -> i
  | VNeg sphi -> s_low sphi
  | VDisj (vphi, vpsi) -> min (v_low vphi) (v_low vpsi)
  | VConjL vphi -> v_low vphi
  | VConjR vpsi -> v_low vpsi
  | VImpl (sphi, vpsi) -> min (s_low sphi) (v_low vpsi)
  | VIffL (sphi, vpsi) -> min (s_low sphi) (v_low vpsi)
  | VIffR (vphi, spsi) -> min (v_low vphi) (s_low spsi)
  | VPrev0 -> 0
  | VPrevOutL i -> i
  | VPrevOutR i -> i
  | VPrev vphi -> min (v_at (VPrev vphi)) (v_low vphi)
  | VOnce vphis -> min_list (List.map v_low vphis)
  | VHistorically (i, vphi) -> min i (v_low vphi)
  | VNextOutL i -> i
  | VNextOutR i -> i
  | VNext vphi -> min (v_at (VNext vphi)) (v_low vphi)
  | VEventually vphis -> min_list (List.map v_low vphis)
  | VAlways (i, vphi) -> min i (v_low vphi)
  (* TODO: Check if we should consider i here *)
  | VSince (_, vphi, vpsis) -> min (v_low vphi) (min_list (List.map v_low vpsis))
  | VSinceInf (_, _, vpsis) -> min_list (List.map v_low vpsis)
  | VSinceOutL i -> i
  | VUntil (_, vphi, vpsis) -> min (v_low vphi) (min_list (List.map v_low vpsis))
  | VUntilInf (_, _, vpsis) -> min_list (List.map v_low vpsis)

let high p = match p with
  | S s_p -> s_high s_p
  | V v_p -> v_high v_p

let low p = match p with
  | S s_p -> s_low s_p
  | V v_p -> v_low v_p

(* let width p = high p - low p *)

let high_le = mk_le high
let low_le = mk_le (fun p -> - low p)

(***********************************
 *                                 *
 * Measure: pred                   *
 *                                 *
 ***********************************)
let rec s_pred = function
  | STT i -> 0
  | SAtom (i, _) -> 1
  | SNeg expl -> v_pred expl
  | SDisjL sphi -> s_pred sphi
  | SDisjR spsi -> s_pred spsi
  | SConj (sphi, spsi) -> s_pred sphi + s_pred spsi
  | SImplL vphi -> v_pred vphi
  | SImplR spsi -> s_pred spsi
  | SIffS (sphi, spsi) -> s_pred sphi + s_pred spsi
  | SIffV (vphi, vpsi) -> v_pred vphi + v_pred vpsi
  | SPrev expl -> s_pred expl
  | SOnce (i, expl) -> s_pred expl
  | SHistorically expls -> sum s_pred expls
  | SNext expl -> s_pred expl
  | SEventually (i, expl) -> s_pred expl
  | SAlways expls -> sum s_pred expls
  | SSince (spsi, sphis) -> s_pred spsi + sum s_pred sphis
  | SUntil (spsi, sphis) -> s_pred spsi + sum s_pred sphis
and v_pred = function
  | VFF i -> 0
  | VAtom (i, _) -> 1
  | VNeg sphi -> s_pred sphi
  | VDisj (vphi, vpsi) -> v_pred vphi + v_pred vpsi
  | VConjL vphi -> v_pred vphi
  | VConjR vpsi -> v_pred vpsi
  | VImpl (sphi, vpsi) -> s_pred sphi + v_pred vpsi
  | VIffL (sphi, vpsi) -> s_pred sphi + v_pred vpsi
  | VIffR (vphi, spsi) -> v_pred vphi + s_pred spsi
  | VPrev0 -> 0
  | VPrevOutL _ -> 0
  | VPrevOutR _ -> 0
  | VPrev vphi -> v_pred vphi
  | VOnce expls -> sum v_pred expls
  | VHistorically (i, expl) -> v_pred expl
  | VNextOutL _ -> 0
  | VNextOutR _ -> 0
  | VNext vphi -> v_pred vphi
  | VEventually expls -> sum v_pred expls
  | VAlways (i, expl) -> v_pred expl
  | VSince (_, vphi, vpsis) -> v_pred vphi + sum v_pred vpsis
  | VSinceInf (_, _, vpsis) -> sum v_pred vpsis
  | VSinceOutL _ -> 0
  | VUntil (_, vphi, vpsis) -> v_pred vphi + sum v_pred vpsis
  | VUntilInf (_, _, vpsis) -> sum v_pred vpsis

let predicates = function
  | S s_p -> s_pred s_p
  | V v_p -> v_pred v_p

let predicates_le = mk_le predicates

(* Printing functions*)
let rec s_to_string indent p =
  let indent' = "\t" ^ indent in
  match p with
  | STT i -> Printf.sprintf "%strue{%d}" indent i
  | SAtom (i, a) -> Printf.sprintf "%s%s{%d}" indent a i
  | SNeg vphi -> Printf.sprintf "%sSNeg{%d}\n%s" indent (s_at p) (v_to_string indent' vphi)
  | SDisjL sphi -> Printf.sprintf "%sSDisjL{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SDisjR spsi -> Printf.sprintf "%sSDisjR{%d}\n%s" indent (s_at p) (s_to_string indent' spsi)
  | SConj (sphi, spsi) -> Printf.sprintf "%sSConj{%d}\n%s\n%s)" indent (s_at p) (s_to_string indent' sphi) (s_to_string indent' spsi)
  | SImplL vphi -> Printf.sprintf "%sSImplL{%d}\n%s" indent (s_at p) (v_to_string indent' vphi)
  | SImplR spsi -> Printf.sprintf "%sSImplR{%d}\n%s" indent (s_at p) (s_to_string indent' spsi)
  | SIffS (sphi, spsi) -> Printf.sprintf "%sSIffS{%d}\n%s\n%s)" indent (s_at p) (s_to_string indent' sphi) (s_to_string indent' spsi)
  | SIffV (vphi, vpsi) -> Printf.sprintf "%sSIffV{%d}\n%s\n%s)" indent (s_at p) (v_to_string indent' vphi) (v_to_string indent' vpsi)
  | SPrev sphi -> Printf.sprintf "%sSPrev{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SOnce (_, sphi) -> Printf.sprintf "%sSOnce{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SHistorically sphis -> Printf.sprintf "%sSHistorically{%d}\n%s" indent (s_at p) (list_to_string indent' s_to_string sphis)
  | SNext sphi -> Printf.sprintf "%sSNext{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SEventually (_, sphi) -> Printf.sprintf "%sSEventually{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SAlways sphis -> Printf.sprintf "%sSAlways{%d}\n%s" indent (s_at p) (list_to_string indent' s_to_string sphis)
  | SSince (spsi, sphis) ->
      Printf.sprintf "%sSSince{%d}\n%s\n%s" indent (s_at p) (s_to_string indent' spsi) (list_to_string indent' s_to_string sphis)
  | SUntil (spsi, sphis) ->
      Printf.sprintf "%sSUntil{%d}\n%s\n%s" indent (s_at p) (list_to_string indent' s_to_string sphis) (s_to_string indent' spsi)
and v_to_string indent p =
  let indent' = "\t" ^ indent in
  match p with
  | VFF i -> Printf.sprintf "%sfalse{%d}" indent i
  | VAtom (i, a) -> Printf.sprintf "%s!%s{%d}" indent a i
  | VNeg sphi -> Printf.sprintf "%sVNeg{%d}\n%s" indent (v_at p) (s_to_string indent' sphi)
  | VDisj (vphi, vpsi) -> Printf.sprintf "%sVDisj{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vphi) (v_to_string indent' vpsi)
  | VConjL vphi -> Printf.sprintf "%sVConjL{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VConjR vpsi -> Printf.sprintf "%sVConjR{%d}\n%s" indent (v_at p) (v_to_string indent' vpsi)
  | VImpl (sphi, vpsi) -> Printf.sprintf "%sVImpl{%d}\n%s\n%s)" indent (v_at p) (s_to_string indent' sphi) (v_to_string indent' vpsi)
  | VIffL (sphi, vpsi) -> Printf.sprintf "%sVIffL{%d}\n%s\n%s)" indent (v_at p) (s_to_string indent' sphi) (v_to_string indent' vpsi)
  | VIffR (vphi, spsi) -> Printf.sprintf "%sVIffR{%d}\n%s\n%s)" indent (v_at p) (v_to_string indent' vphi) (s_to_string indent' spsi)
  | VPrev0 -> Printf.sprintf "%sVPrev{0}" indent'
  | VPrevOutL i -> Printf.sprintf "%sVPrevOutL{%d}" indent' i
  | VPrevOutR i -> Printf.sprintf "%sVPrevOutR{%d}" indent' i
  | VPrev vphi -> Printf.sprintf "%sVPrev{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VOnce vphis -> Printf.sprintf "%sVOnce{%d}\n%s" indent (v_at p) (list_to_string indent' v_to_string vphis)
  | VHistorically (_, vphi) -> Printf.sprintf "%sVHistorically{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VNextOutL i -> Printf.sprintf "%sVNextOutL{%d}" indent' i
  | VNextOutR i -> Printf.sprintf "%sVNextOutR{%d}" indent' i
  | VNext vphi -> Printf.sprintf "%sVNext{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VEventually vphis -> Printf.sprintf "%sVEventually{%d}\n%s" indent (v_at p) (list_to_string indent' v_to_string vphis)
  | VAlways (_, vphi) -> Printf.sprintf "%sVAlways{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VSince (_, vphi, vpsis) ->
     Printf.sprintf "%sVSince{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vphi) (list_to_string indent' v_to_string vpsis)
  | VSinceInf (_, _, vpsis) ->
     Printf.sprintf "%sVSinceInf{%d}\n%s" indent (v_at p) (list_to_string indent' v_to_string vpsis)
  | VSinceOutL i -> Printf.sprintf "%sVSinceOutL{%d}" indent' i
  | VUntil (_, vphi, vpsis) ->
      Printf.sprintf "%sVUntil{%d}\n%s\n%s" indent (v_at p) (list_to_string indent' v_to_string vpsis) (v_to_string indent' vphi)
  | VUntilInf (_, _, vpsis) ->
     Printf.sprintf "%sVUntilInf{%d}\n%s" indent (v_at p) (list_to_string indent' v_to_string vpsis)

let expl_to_string = function
  | S p -> s_to_string "" p
  | V p -> v_to_string "" p
