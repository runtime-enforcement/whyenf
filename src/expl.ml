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
  | SPrev of sexpl
  | SNext of sexpl
  | SSince of sexpl * sexpl list
  | SUntil of sexpl * sexpl list
and vexpl =
  | VFF of int
  | VAtom of int * string
  | VNeg of sexpl
  | VDisj of vexpl * vexpl
  | VConjL of vexpl
  | VConjR of vexpl
  | VPrev0
  | VPrevOutL of int
  | VPrevOutR of int
  | VPrev of vexpl
  | VNextOutL of int
  | VNextOutR of int
  | VNext of vexpl
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
  | VSince (tp, vp1, vp2s) -> VSince (tp,  vp1, List.append vp2s [vp2])
  | VSinceInf (tp, etp, vp2s) -> VSinceInf (tp, etp, List.append vp2s [vp2])
  | VUntil (tp, vp1, vp2s) -> VUntil (tp, vp1, vp2 :: vp2s)
  | VUntilInf (tp, ltp, vp2s) -> VUntilInf (tp, ltp, vp2 :: vp2s)
  | _ -> failwith "Bad arguments for vappend"

let sdrop sp = match sp with
  | SUntil (_, []) -> None
  | SUntil (sp2, sp1s) -> Some (SUntil (sp2, drop_front sp1s))
  | _ -> failwith "Bad arguments for sdrop"

let vdrop vp = match vp with
  | VUntil (_, _, _::[]) -> None
  | VUntil (tp, vp1, vp2s) -> Some (VUntil (tp, vp1, drop_front vp2s))
  | VUntilInf (_, _, []) -> None
  | VUntilInf (tp, ltp, vp2s) -> Some (VUntilInf (tp, ltp, drop_front vp2s))
  | _ -> failwith "Bad arguments for vdrop"

let rec s_at = function
  | STT i -> i
  | SAtom (i, _) -> i
  | SNeg vphi -> v_at vphi
  | SDisjL sphi -> s_at sphi
  | SDisjR spsi -> s_at spsi
  | SConj (sphi, _) -> s_at sphi
  | SPrev sphi -> s_at sphi + 1
  | SNext sphi -> s_at sphi - 1
  | SSince (spsi, sphis) -> (match sphis with
      | [] -> s_at spsi
      | _ -> s_at (last sphis))
  | SUntil (spsi, sphis) -> (match sphis with
      | [] -> s_at spsi
      | x :: _ -> s_at x)
and v_at = function
  | VFF i -> i
  | VAtom (i, _) -> i
  | VNeg sphi -> s_at sphi
  | VDisj (vphi, _) -> v_at vphi
  | VConjL vphi -> v_at vphi
  | VConjR vpsi -> v_at vpsi
  | VPrev0 -> 0
  | VPrevOutL i -> i
  | VPrevOutR i -> i
  | VPrev vphi -> v_at vphi + 1
  | VNextOutL i -> i
  | VNextOutR i -> i
  | VNext vphi -> v_at vphi - 1
  | VSince (i, _, _) -> i
  | VSinceInf (i, _, _) -> i
  | VSinceOutL i -> i
  | VUntil (i, _, _) -> i
  | VUntilInf (i, _, _) -> i

let s_ltp sp = match sp with
  | SUntil (sp2, _) -> s_at sp2
  | _ -> failwith "Bad arguments for s_ltp"

let v_etp vp = match vp with
  | VUntil (i, _, []) -> i
  | VUntil (_, _, vp2::_) -> v_at vp2
  | _ -> failwith "Bad arguments for v_etp"

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
  | SPrev expl -> 1 + s_size expl
  | SNext expl -> 1 + s_size expl
  | SSince (spsi, sphis) -> 1 + s_size spsi + sum s_size sphis
  | SUntil (spsi, sphis) -> 1 + s_size spsi + sum s_size sphis
and v_size = function
  | VFF _ -> 1
  | VAtom (_, _) -> 1
  | VNeg sphi -> 1 + s_size sphi
  | VDisj (vphi, vpsi) -> 1 + v_size vphi + v_size vpsi
  | VConjL vphi -> 1 + v_size vphi
  | VConjR vpsi -> 1 + v_size vpsi
  | VPrev0 -> 1
  | VPrevOutL _ -> 1
  | VPrevOutR _ -> 1
  | VPrev vphi -> 1 + v_size vphi
  | VNextOutL _ -> 1
  | VNextOutR _ -> 1
  | VNext vphi -> 1 + v_size vphi
  | VSince (_, vphi, vpsis) -> 1 + v_size vphi + sum v_size vpsis
  | VSinceInf (_, _, vpsis) -> 1 + sum v_size vpsis
  | VSinceOutL _ -> 1
  | VUntil (_, vphi, vpsis) -> 1 + v_size vphi + sum v_size vpsis
  | VUntilInf (_, _, vpsis) -> 1 + sum v_size vpsis

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
  | SPrev sphi -> max (s_at (SPrev sphi)) (s_high sphi)
  | SNext sphi -> max (s_at (SNext sphi)) (s_high sphi)
  | SSince (spsi, sphis) -> max (s_high spsi) (max_list (List.map s_high sphis))
  | SUntil (spsi, sphis) -> max (s_high spsi) (max_list (List.map s_high sphis))
and v_high p = match p with
  | VFF i -> i
  | VAtom (i, _) -> i
  | VNeg sphi -> s_high sphi
  | VDisj (vphi, vpsi) -> max (v_high vphi) (v_high vpsi)
  | VConjL vphi -> v_high vphi
  | VConjR vpsi -> v_high vpsi
  | VPrev0 -> 0
  | VPrevOutL i -> i
  | VPrevOutR i -> i
  | VPrev vphi -> max (v_at (VPrev vphi)) (v_high vphi)
  | VNextOutL i -> i
  | VNextOutR i -> i
  | VNext vphi -> max (v_at (VNext vphi)) (v_high vphi)
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
  | SPrev sphi -> min (s_at (SPrev sphi)) (s_low sphi)
  | SNext sphi -> min (s_at (SNext sphi)) (s_low sphi)
  | SSince (spsi, sphis) -> min (s_low spsi) (min_list (List.map s_low sphis))
  | SUntil (spsi, sphis) -> min (s_low spsi) (min_list (List.map s_low sphis))
and v_low p = match p with
  | VFF i -> i
  | VAtom (i, _) -> i
  | VNeg sphi -> s_low sphi
  | VDisj (vphi, vpsi) -> min (v_low vphi) (v_low vpsi)
  | VConjL vphi -> v_low vphi
  | VConjR vpsi -> v_low vpsi
  | VPrev0 -> 0
  | VPrevOutL i -> i
  | VPrevOutR i -> i
  | VPrev vphi -> min (v_at (VPrev vphi)) (v_low vphi)
  | VNextOutL i -> i
  | VNextOutR i -> i
  | VNext vphi -> min (v_at (VNext vphi)) (v_low vphi)
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
  | STT _ -> 0
  | SAtom (_, _) -> 1
  | SNeg expl -> v_pred expl
  | SDisjL sphi -> s_pred sphi
  | SDisjR spsi -> s_pred spsi
  | SConj (sphi, spsi) -> s_pred sphi + s_pred spsi
  | SPrev expl -> s_pred expl
  | SNext expl -> s_pred expl
  | SSince (spsi, sphis) -> s_pred spsi + sum s_pred sphis
  | SUntil (spsi, sphis) -> s_pred spsi + sum s_pred sphis
and v_pred = function
  | VFF _ -> 0
  | VAtom (_, _) -> 1
  | VNeg sphi -> s_pred sphi
  | VDisj (vphi, vpsi) -> v_pred vphi + v_pred vpsi
  | VConjL vphi -> v_pred vphi
  | VConjR vpsi -> v_pred vpsi
  | VPrev0 -> 0
  | VPrevOutL _ -> 0
  | VPrevOutR _ -> 0
  | VPrev vphi -> v_pred vphi
  | VNextOutL _ -> 0
  | VNextOutR _ -> 0
  | VNext vphi -> v_pred vphi
  | VSince (_, vphi, vpsis) -> v_pred vphi + sum v_pred vpsis
  | VSinceInf (_, _, vpsis) -> sum v_pred vpsis
  | VSinceOutL _ -> 0
  | VUntil (_, vphi, vpsis) -> v_pred vphi + sum v_pred vpsis
  | VUntilInf (_, _, vpsis) -> sum v_pred vpsis

let predicates = function
  | S s_p -> s_pred s_p
  | V v_p -> v_pred v_p

let predicates_le = mk_le predicates

(* Printing functions *)
let rec s_to_string indent p =
  let indent' = "\t" ^ indent in
  match p with
  | STT i -> Printf.sprintf "%strue{%d}" indent i
  | SAtom (i, a) -> Printf.sprintf "%s%s{%d}" indent a i
  | SNeg vphi -> Printf.sprintf "%sSNeg{%d}\n%s" indent (s_at p) (v_to_string indent' vphi)
  | SDisjL sphi -> Printf.sprintf "%sSDisjL{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SDisjR spsi -> Printf.sprintf "%sSDisjR{%d}\n%s" indent (s_at p) (s_to_string indent' spsi)
  | SConj (sphi, spsi) -> Printf.sprintf "%sSConj{%d}\n%s\n%s)" indent (s_at p) (s_to_string indent' sphi) (s_to_string indent' spsi)
  | SPrev sphi -> Printf.sprintf "%sSPrev{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SNext sphi -> Printf.sprintf "%sSNext{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
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
  | VPrev0 -> Printf.sprintf "%sVPrev0{0}" indent'
  | VPrevOutL i -> Printf.sprintf "%sVPrevOutL{%d}" indent' i
  | VPrevOutR i -> Printf.sprintf "%sVPrevOutR{%d}" indent' i
  | VPrev vphi -> Printf.sprintf "%sVPrev{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VNextOutL i -> Printf.sprintf "%sVNextOutL{%d}" indent' i
  | VNextOutR i -> Printf.sprintf "%sVNextOutR{%d}" indent' i
  | VNext vphi -> Printf.sprintf "%sVNext{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
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
