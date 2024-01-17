(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Pred

module Fdeque = Core.Fdeque

module Part = struct

  type sub = (Dom.t, Dom.comparator_witness) Setc.t

  type 'a t = (sub * 'a) list

  let random_empty_set = Set.empty (module String)

  let trivial p = [(Setc.univ (module Dom), p)]

  let hd part = snd (List.hd_exn part)

  let length part = List.length part

  let map part f = List.map part ~f:(fun (s, p) -> (s, f p))

  let map2 part f = List.map part ~f:(fun (s, p) -> f (s, p))

  let fold_left part init f = List.fold_left part ~init:init ~f:(fun acc (_, p) -> f acc p)

  let filter part f = List.filter part ~f:(fun (_, p) -> f p)

  let exists part f = List.exists part ~f:(fun (_, p) -> f p)

  let for_all part f = List.for_all part ~f:(fun (_, p) -> f p)

  let values part = List.map part ~f:(fun (_, p) -> p)

  let find part x = snd (List.find_exn part ~f:(fun (s, p) -> Setc.mem s x))

  let find2 part f = List.find_exn part ~f:(fun (s, p) -> f p)

  let rec tabulate ds f z =
    (Setc.Complement ds, z) ::
      (Set.fold ds ~init:[] ~f:(fun acc d -> (Setc.Finite (Set.of_list (module Dom) [d]), f d) :: acc))

  let rec merge2 f part1 part2 = match part1, part2 with
    | [], _ -> []
    | (sub1, v1) :: part1, part2 ->
       let part12 = List.filter_map part2
                      ~f:(fun (sub2, v2) ->
                        (if not (Setc.is_empty (Setc.inter sub1 sub2))
                         then Some (Setc.inter sub1 sub2, f v1 v2) else None)) in
       let part2not1 = List.filter_map part2
                         ~f:(fun (sub2, v2) ->
                           (if not (Setc.is_empty (Setc.diff sub2 sub1))
                            then Some (Setc.diff sub2 sub1, v2) else None)) in
       part12 @ (merge2 f part1 part2not1)

  let merge3 f part1 part2 part3 = match part1, part2, part3 with
    | [], _ , _
      | _ , [], _
      | _ , _ , [] -> raise (Invalid_argument "one of the partitions is empty")
    | part1, part2, part3 ->
       merge2 (fun pt3 f' -> f' pt3) part3 (merge2 f part1 part2)

  let split_prod part = (map part fst, map part snd)

  let split_list part =
    let subs = List.map part ~f:fst in
    let vs = List.map part ~f:snd in
    List.map (Option.value_exn (List.transpose vs)) ~f:(List.zip_exn subs)

  let rec el_to_string indent var f (sub, v) =
    Printf.sprintf "%s%s ∈ %s\n\n%s" indent (Term.value_to_string var) (Setc.to_string sub)
      (f (indent ^ (String.make 4 ' ')) v)

  let to_string indent var f = function
    | [] -> indent ^ "❮ · ❯"
    | [x] -> indent ^ "❮\n\n" ^ (el_to_string indent var f x) ^ "\n" ^ indent ^ "❯\n"
    | xs -> List.fold_left xs ~init:(indent ^ "❮\n\n")
              ~f:(fun s el -> s ^ (el_to_string indent var f el) ^ "\n") ^ indent ^ "❯\n"

  (* dedup related *)
  let dedup p_eq part =
    let rec aux acc (s,v) =
      match acc with
      | [] -> [(s,v)]
      | (t,u) :: acc -> if p_eq u v then (Setc.union s t, u) :: acc
                        else (t,u) :: aux acc (s,v) in
    let rec dedup_rec part acc =
      match part with
      | [] -> acc
      | (s,v) :: part -> let acc' = aux acc (s,v) in
                         dedup_rec part acc' in
    dedup_rec part []

  let map_dedup p_eq part f = dedup p_eq (map part f)

  let map2_dedup p_eq part f = dedup p_eq (map2 part f)

  let tabulate_dedup p_eq ds f z = dedup p_eq (tabulate ds f z)

  let merge2_dedup p_eq f part1 part2 = dedup p_eq (merge2 f part1 part2)

  let merge3_dedup p_eq f part1 part2 part3 = dedup p_eq (merge3 f part1 part2 part3)

  let split_prod_dedup p_eq part =
    let part1, part2 = split_prod part in
    (dedup p_eq part1, dedup p_eq part2)

  let split_list_dedup p_eq part = List.map (split_list part) ~f:(dedup p_eq)

end


module Proof = struct

  type sp =
    | STT of int
    | SEqConst of int * string * Dom.t
    | SPred of int * string * Term.t list
    | SNeg of vp
    | SOrL of sp
    | SOrR of sp
    | SAnd of sp * sp
    | SImpL of vp
    | SImpR of sp
    | SIffSS of sp * sp
    | SIffVV of vp * vp
    | SExists of string * Dom.t * sp
    | SForall of string * (sp Part.t)
    | SPrev of sp
    | SNext of sp
    | SNextAssm of int
    | SOnce of int * sp
    | SEventually of int * sp
    | SEventuallyAssm of int * Interval.t
    | SEventuallyNow of sp * Interval.t
    | SHistorically of int * int * sp Fdeque.t
    | SHistoricallyOut of int
    | SAlways of int * int * sp Fdeque.t
    | SAlwaysAssm of int * sp option * Interval.t
    | SSince of sp * sp Fdeque.t
    | SUntil of sp * sp Fdeque.t
    | SUntilAssm of int * sp * Interval.t
    | SUntilNow of sp * Interval.t
  and vp =
    | VFF of int
    | VEqConst of int * string * Dom.t
    | VPred of int * string * Term.t list
    | VNeg of sp
    | VOr of vp * vp
    | VAndL of vp
    | VAndR of vp
    | VImp of sp * vp
    | VIffSV of sp * vp
    | VIffVS of vp * sp
    | VExists of string * (vp Part.t)
    | VForall of string * Dom.t * vp
    | VPrev of vp
    | VPrev0
    | VPrevOutL of int
    | VPrevOutR of int
    | VNext of vp
    | VNextOutL of int
    | VNextOutR of int
    | VNextAssm of int * Interval.t
    | VOnceOut of int
    | VOnce of int * int * vp Fdeque.t
    | VEventually of int * int * vp Fdeque.t
    | VEventuallyAssm of int * vp option * Interval.t
    | VHistorically of int * vp
    | VAlways of int * vp
    | VAlwaysAssm of int * Interval.t
    | VAlwaysNow of vp * Interval.t
    | VSinceOut of int
    | VSince of int * vp * vp Fdeque.t
    | VSinceInf of int * int * vp Fdeque.t
    | VUntil of int * vp * vp Fdeque.t
    | VUntilInf of int * int * vp Fdeque.t
    | VUntilAssm of int * vp * Interval.t
    | VUntilNow of vp * Interval.t

  type t = S of sp | V of vp

  let rec s_equal x y = match x, y with
    | STT tp, STT tp' -> Int.equal tp tp'
    | SEqConst (tp, x, c), SEqConst (tp', x', c') -> Int.equal tp tp' && String.equal x x' && Dom.equal c c'
    | SPred (tp, r, terms), SPred (tp', r', terms') -> Int.equal tp tp' && String.equal r r' &&
                                                         Int.equal (List.length terms) (List.length terms') &&
                                                           List.for_all2_exn terms terms' ~f:(fun t1 t2 -> Term.equal t1 t2)
    | SNeg vp, SNeg vp'
      | SImpL vp, SImpL vp' -> v_equal vp vp'
    | SImpR sp, SImpR sp'
      | SOrL sp, SOrL sp'
      | SOrR sp, SOrR sp'
      | SPrev sp, SPrev sp'
      | SNext sp, SNext sp' -> s_equal sp sp'
    | SNextAssm tp, SNextAssm tp' -> Int.equal tp tp'
    | SAnd (sp1, sp2), SAnd (sp1', sp2')
      | SIffSS (sp1, sp2), SIffSS (sp1', sp2') -> s_equal sp1 sp1' && s_equal sp2 sp2'
    | SIffVV (vp1, vp2), SIffVV (vp1', vp2') -> v_equal vp1 vp1' && v_equal vp2 vp2'
    | SExists (x, d, sp), SExists (x', d', sp') -> String.equal x x' && Dom.equal d d' && s_equal sp sp'
    | SForall (x, part), SForall (x', part') -> String.equal x x' && Int.equal (Part.length part) (Part.length part') &&
                                                  List.for_all2_exn part part' ~f:(fun (s, p) (s', p') ->
                                                      Setc.equal s s' && s_equal p p')
    | SOnce (tp, sp), SOnce (tp', sp')
      | SEventually (tp, sp), SEventually (tp', sp') -> Int.equal tp tp' && s_equal sp sp'
    | SEventuallyAssm (tp, i), SEventuallyAssm (tp', i') -> Int.equal tp tp' && Interval.equal i i'
    | SEventuallyNow (sp, i), SEventuallyNow (sp', i') -> s_equal sp sp' && Interval.equal i i'
    | SHistoricallyOut tp, SHistoricallyOut tp' -> Int.equal tp tp'
    | SHistorically (tp, ltp, sps), SHistorically (tp', li', sps') -> Int.equal tp tp' && Int.equal ltp li' &&
                                                                        Int.equal (Fdeque.length sps) (Fdeque.length sps') &&
                                                                          Etc.fdeque_for_all2_exn sps sps' ~f:(fun sp sp' -> s_equal sp sp')
    | SAlways (tp, htp, sps), SAlways (tp', hi', sps') -> Int.equal tp tp' && Int.equal htp hi' &&
                                                            Int.equal (Fdeque.length sps) (Fdeque.length sps') &&
                                                              Etc.fdeque_for_all2_exn sps sps' ~f:(fun sp sp' -> s_equal sp sp')
    | SAlwaysAssm (tp, Some sp, i), SAlwaysAssm (tp', Some sp', i') -> Int.equal tp tp' && s_equal sp sp' && Interval.equal i i'
    | SAlwaysAssm (tp, None, i), SAlwaysAssm (tp', None, i') -> Int.equal tp tp' && Interval.equal i i'
    | SSince (sp2, sp1s), SSince (sp2', sp1s')
      | SUntil (sp2, sp1s), SUntil (sp2', sp1s') -> s_equal sp2 sp2' && Int.equal (Fdeque.length sp1s) (Fdeque.length sp1s') &&
                                                      Etc.fdeque_for_all2_exn sp1s sp1s' ~f:(fun sp1 sp1' -> s_equal sp1 sp1')
    | SUntilAssm (tp, sp, i), SUntilAssm (tp', sp', i') ->  Int.equal tp tp' && s_equal sp sp' && Interval.equal i i'
    | SUntilNow (sp, i), SUntilNow (sp', i') -> s_equal sp sp' && Interval.equal i i'
    | _ -> false
  and v_equal x y = match x, y with
    | VFF tp, VFF tp' -> Int.equal tp tp'
    | VEqConst (tp, x, c), VEqConst (tp', x', c') -> Int.equal tp tp' && String.equal x x' && Dom.equal c c'
    | VPred (tp, r, terms), VPred (tp', r', terms') -> Int.equal tp tp' && String.equal r r' &&
                                                         Int.equal (List.length terms) (List.length terms') &&
                                                           List.for_all2_exn terms terms' ~f:(fun t1 t2 -> Term.equal t1 t2)
    | VNeg sp, VNeg sp' -> s_equal sp sp'
    | VAndL vp, VAndL vp'
      | VAndR vp, VAndR vp'
      | VPrev vp, VPrev vp'
      | VNext vp, VNext vp' -> v_equal vp vp'
    | VOr (vp1, vp2), VOr (vp1', vp2') -> v_equal vp1 vp1' && v_equal vp2 vp2'
    | VImp (sp1, vp2), VImp (sp1', vp2')
      | VIffSV (sp1, vp2), VIffSV (sp1', vp2') -> s_equal sp1 sp1' && v_equal vp2 vp2'
    | VIffVS (vp1, sp2), VIffVS (vp1', sp2') -> v_equal vp1 vp1' && s_equal sp2 sp2'
    | VExists (x, part), VExists (x', part') -> String.equal x x' && Int.equal (Part.length part) (Part.length part') &&
                                                  List.for_all2_exn part part' ~f:(fun (s, p) (s', p') ->
                                                      Setc.equal s s' && v_equal p p')
    | VForall (x, d, vp), VForall (x', d', vp') -> String.equal x x' && Dom.equal d d' && v_equal vp vp'
    | VPrev0, VPrev0 -> true
    | VPrevOutL tp, VPrevOutL tp'
      | VPrevOutR tp, VPrevOutR tp'
      | VNextOutL tp, VNextOutL tp'
      | VNextOutR tp, VNextOutR tp'
      | VOnceOut tp, VOnceOut tp'
      | VSinceOut tp, VSinceOut tp' -> Int.equal tp tp'
    | VNextAssm (tp, i), VNextAssm (tp', i') -> Int.equal tp tp' && Interval.equal i i'
    | VOnce (tp, ltp, vps), VOnce (tp', li', vps') -> Int.equal tp tp' && Int.equal ltp li' &&
                                                        Int.equal (Fdeque.length vps) (Fdeque.length vps') &&
                                                          Etc.fdeque_for_all2_exn vps vps' ~f:(fun vp vp' -> v_equal vp vp')
    | VEventually (tp, htp, vps), VEventually (tp', hi', vps') -> Int.equal tp tp' && Int.equal htp hi' &&
                                                                    Int.equal (Fdeque.length vps) (Fdeque.length vps') &&
                                                                      Etc.fdeque_for_all2_exn vps vps' ~f:(fun vp vp' -> v_equal vp vp')
    | VEventuallyAssm (tp, Some vp, i), VEventuallyAssm (tp', Some vp', i') -> Int.equal tp tp' && v_equal vp vp' && Interval.equal i i'
    | VEventuallyAssm (tp, None, i), VEventuallyAssm (tp', None, i') -> Int.equal tp tp' && Interval.equal i i'
    | VHistorically (tp, vp), VHistorically (tp', vp')
      | VAlways (tp, vp), VAlways (tp', vp') -> Int.equal tp tp'
    | VAlwaysAssm (tp, i), VAlwaysAssm (tp', i') -> Int.equal tp tp' && Interval.equal i i'
    | VAlwaysNow (vp, i), VAlwaysNow (vp', i') -> v_equal vp vp' && Interval.equal i i'
    | VSince (tp, vp1, vp2s), VSince (tp', vp1', vp2s')
      | VUntil (tp, vp1, vp2s), VUntil (tp', vp1', vp2s') -> Int.equal tp tp' && v_equal vp1 vp1' &&
                                                               Int.equal (Fdeque.length vp2s) (Fdeque.length vp2s') &&
                                                                 Etc.fdeque_for_all2_exn vp2s vp2s' ~f:(fun vp2 vp2' -> v_equal vp2 vp2')
    | VSinceInf (tp, ltp, vp2s), VSinceInf (tp', li', vp2s') -> Int.equal tp tp' && Int.equal ltp li' &&
                                                                  Int.equal (Fdeque.length vp2s) (Fdeque.length vp2s') &&
                                                                    Etc.fdeque_for_all2_exn vp2s vp2s' ~f:(fun vp2 vp2' -> v_equal vp2 vp2')

    | VUntilInf (tp, htp, vp2s), VUntilInf (tp', hi', vp2s') -> Int.equal tp tp' && Int.equal htp hi' &&
                                                                  Int.equal (Fdeque.length vp2s) (Fdeque.length vp2s') &&
                                                                    Etc.fdeque_for_all2_exn vp2s vp2s' ~f:(fun vp2 vp2' -> v_equal vp2 vp2')
    | VUntilAssm (tp, vp, i), VUntilAssm (tp', vp', i') -> Int.equal tp tp' && v_equal vp vp' && Interval.equal i i'
    | VUntilNow (vp, i), VUntilNow (vp', i') -> v_equal vp vp' && Interval.equal i i'
    | _ -> false


  let equal x y = match x, y with
    | S sp, S sp' -> s_equal sp sp'
    | V vp, V vp' -> v_equal vp vp'
    | _ -> false

  let unS = function
    | S sp -> sp
    | _ -> raise (Invalid_argument "unS is not defined for V proofs")

  let unV = function
    | V vp -> vp
    | _ -> raise (Invalid_argument "unV is not defined for S proofs")

  let isS = function
    | S _ -> true
    | V _ -> false

  let isV = function
    | S _ -> false
    | V _ -> true

  let s_append sp sp1 = match sp with
    | SSince (sp2, sp1s) -> SSince (sp2, Fdeque.enqueue_back sp1s sp1)
    | SUntil (sp2, sp1s) -> SUntil (sp2, Fdeque.enqueue_back sp1s sp1)
    | _ -> raise (Invalid_argument "sappend is not defined for this sp")

  let v_append vp vp2 = match vp with
    | VSince (tp, vp1, vp2s) -> VSince (tp,  vp1, Fdeque.enqueue_back vp2s vp2)
    | VSinceInf (tp, etp, vp2s) -> VSinceInf (tp, etp, Fdeque.enqueue_back vp2s vp2)
    | VUntil (tp, vp1, vp2s) -> VUntil (tp, vp1, Fdeque.enqueue_back vp2s vp2)
    | VUntilInf (tp, ltp, vp2s) -> VUntilInf (tp, ltp, Fdeque.enqueue_back vp2s vp2)
    | _ -> raise (Invalid_argument "vappend is not defined for this vp")

  let s_drop = function
    | SUntil (sp2, sp1s) -> (match Fdeque.drop_front sp1s with
                             | None -> None
                             | Some(sp1s') -> Some (SUntil (sp2, sp1s')))
    | _ -> raise (Invalid_argument "sdrop is not defined for this sp")

  let v_drop = function
    | VUntil (tp, vp1, vp2s) -> (match Fdeque.drop_front vp2s with
                                 | None -> None
                                 | Some(vp2s') -> Some (VUntil (tp, vp1, vp2s')))
    | VUntilInf (tp, ltp, vp2s) -> (match Fdeque.drop_front vp2s with
                                    | None -> None
                                    | Some(vp2s') -> Some (VUntilInf (tp, ltp, vp2s)))
    | _ -> raise (Invalid_argument "vdrop is not defined for this vp")

  let rec s_at = function
    | STT tp -> tp
    | SEqConst (tp, _, _) -> tp
    | SPred (tp, _, _) -> tp
    | SNeg vp -> v_at vp
    | SOrL sp1 -> s_at sp1
    | SOrR sp2 -> s_at sp2
    | SAnd (sp1, _) -> s_at sp1
    | SImpL vp1 -> v_at vp1
    | SImpR sp2 -> s_at sp2
    | SIffSS (sp1, _) -> s_at sp1
    | SIffVV (vp1, _) -> v_at vp1
    | SExists (_, _, sp) -> s_at sp
    | SForall (_, part) -> s_at (Part.hd part)
    | SPrev sp -> s_at sp + 1
    | SNext sp -> s_at sp - 1
    | SNextAssm tp -> tp
    | SOnce (tp, _) -> tp
    | SEventually (tp, _) -> tp
    | SEventuallyAssm (tp, _) -> tp
    | SEventuallyNow (sp, _) -> s_at sp
    | SHistorically (tp, _, _) -> tp
    | SHistoricallyOut tp -> tp
    | SAlways (tp, _, _) -> tp
    | SAlwaysAssm (tp, _, _) -> tp
    | SSince (sp2, sp1s) -> if Fdeque.is_empty sp1s then s_at sp2
                            else s_at (Fdeque.peek_back_exn sp1s)
    | SUntil (sp2, sp1s) -> if Fdeque.is_empty sp1s then s_at sp2
                            else s_at (Fdeque.peek_front_exn sp1s)
    | SUntilAssm (tp, _, _) -> tp
    | SUntilNow (sp, _) -> s_at sp
  and v_at = function
    | VFF tp -> tp
    | VEqConst (tp, _, _) -> tp
    | VPred (tp, _, _) -> tp
    | VNeg sp -> s_at sp
    | VOr (vp1, _) -> v_at vp1
    | VAndL vp1 -> v_at vp1
    | VAndR vp2 -> v_at vp2
    | VImp (sp1, _) -> s_at sp1
    | VIffSV (sp1, _) -> s_at sp1
    | VIffVS (vp1, _) -> v_at vp1
    | VExists (_, part) -> v_at (Part.hd part)
    | VForall (_, _, vp) -> v_at vp
    | VPrev vp -> v_at vp + 1
    | VPrev0 -> 0
    | VPrevOutL tp -> tp
    | VPrevOutR tp -> tp
    | VNext vp -> v_at vp - 1
    | VNextOutL tp -> tp
    | VNextOutR tp -> tp
    | VNextAssm (tp, _) -> tp
    | VOnceOut tp -> tp
    | VOnce (tp, _, _) -> tp
    | VEventually (tp, _, _) -> tp
    | VEventuallyAssm (tp, _, _) -> tp
    | VHistorically (tp, _) -> tp
    | VAlways (tp, _) -> tp
    | VAlwaysAssm (tp, _) -> tp
    | VAlwaysNow (vp, _) -> v_at vp
    | VSinceOut tp -> tp
    | VSince (tp, _, _) -> tp
    | VSinceInf (tp, _, _) -> tp
    | VUntil (tp, _, _) -> tp
    | VUntilInf (tp, _, _) -> tp
    | VUntilAssm (tp, _, _) -> tp
    | VUntilNow (vp, _) -> v_at vp

  let p_at = function
    | S s_p -> s_at s_p
    | V v_p -> v_at v_p

  let s_ltp = function
    | SUntil (sp2, _) -> s_at sp2
    | _ -> raise (Invalid_argument "s_ltp is not defined for this sp")

  let v_etp = function
    | VUntil (tp, _, vp2s) -> if Fdeque.is_empty vp2s then tp
                              else v_at (Fdeque.peek_front_exn vp2s)
    | _ -> raise (Invalid_argument "v_etp is not defined for this vp")

  let cmp f p1 p2 = f p1 <= f p2

  let rec s_to_string indent p =
    let indent' = "\t" ^ indent in
    match p with
    | STT i -> Printf.sprintf "%strue{%d}" indent i
    | SEqConst (tp, x, c) -> Printf.sprintf "%sSEqConst(%d, %s, %s)" indent tp x (Dom.to_string c)
    | SPred (tp, r, trms) -> Printf.sprintf "%sSPred(%d, %s, %s)" indent tp r (Term.list_to_string trms)
    | SNeg vp -> Printf.sprintf "%sSNeg{%d}\n%s" indent (s_at p) (v_to_string indent' vp)
    | SOrL sp1 -> Printf.sprintf "%sSOrL{%d}\n%s" indent (s_at p) (s_to_string indent' sp1)
    | SOrR sp2 -> Printf.sprintf "%sSOrR{%d}\n%s" indent (s_at p) (s_to_string indent' sp2)
    | SAnd (sp1, sp2) -> Printf.sprintf "%sSAnd{%d}\n%s\n%s" indent (s_at p)
                           (s_to_string indent' sp1) (s_to_string indent' sp2)
    | SImpL vp1 -> Printf.sprintf "%sSImpL{%d}\n%s" indent (s_at p) (v_to_string indent' vp1)
    | SImpR sp2 -> Printf.sprintf "%sSImpR{%d}\n%s" indent (s_at p) (s_to_string indent' sp2)
    | SIffSS (sp1, sp2) -> Printf.sprintf "%sSIffSS{%d}\n%s\n%s" indent (s_at p)
                             (s_to_string indent' sp1) (s_to_string indent' sp2)
    | SIffVV (vp1, vp2) -> Printf.sprintf "%sSIffVV{%d}\n%s\n%s" indent (s_at p)
                             (v_to_string indent' vp1) (v_to_string indent' vp2)
    | SExists (x, d, sp) -> Printf.sprintf "%sSExists{%d}{%s=%s}\n%s\n" indent (s_at p)
                              x (Dom.to_string d) (s_to_string indent' sp)
    | SForall (x, part) -> Printf.sprintf "%sSForall{%d}{%s}\n%s\n" indent (s_at (SForall (x, part)))
                             x (Part.to_string indent' (Var x) s_to_string part)
    | SPrev sp -> Printf.sprintf "%sSPrev{%d}\n%s" indent (s_at p) (s_to_string indent' sp)
    | SNext sp -> Printf.sprintf "%sSNext{%d}\n%s" indent (s_at p) (s_to_string indent' sp)
    | SNextAssm tp -> Printf.sprintf "%sSNextAssm{%d}\n" indent tp
    | SOnce (_, sp) -> Printf.sprintf "%sSOnce{%d}\n%s" indent (s_at p) (s_to_string indent' sp)
    | SEventually (_, sp) -> Printf.sprintf "%sSEventually{%d}\n%s" indent (s_at p)
                               (s_to_string indent' sp)
    | SEventuallyAssm (tp, i) -> Printf.sprintf "%sSEventuallyAssm{%d}\n%s" indent tp
                                   (Interval.to_string i)
    | SEventuallyNow (sp, i) -> Printf.sprintf "%sSEventuallyNow\n%s\n%s" indent
                                  (Interval.to_string i) (s_to_string indent' sp)
    | SHistorically (_, _, sps) -> Printf.sprintf "%sSHistorically{%d}\n%s" indent (s_at p)
                                     (Etc.deque_to_string indent' s_to_string sps)
    | SHistoricallyOut i -> Printf.sprintf "%sSHistoricallyOut{%d}" indent' i
    | SAlways (_, _, sps) -> Printf.sprintf "%sSAlways{%d}\n%s" indent (s_at p)
                               (Etc.deque_to_string indent' s_to_string sps)
    | SAlwaysAssm (tp, Some sp, i) -> Printf.sprintf "%sSAlwaysAssm{%d}{%s}\n%s" indent tp
                                        (s_to_string indent' sp) (Interval.to_string i)
    | SAlwaysAssm (tp, None, i) -> Printf.sprintf "%sSAlwaysAssm{%d}\n%s" indent tp
                                     (Interval.to_string i)
    | SSince (sp2, sp1s) -> Printf.sprintf "%sSSince{%d}\n%s\n%s" indent (s_at p) (s_to_string indent' sp2)
                              (Etc.deque_to_string indent' s_to_string sp1s)
    | SUntil (sp2, sp1s) -> Printf.sprintf "%sSUntil{%d}\n%s\n%s" indent (s_at p)
                              (Etc.deque_to_string indent' s_to_string sp1s) (s_to_string indent' sp2)
    | SUntilAssm (tp, sp, i) -> Printf.sprintf "%sSUntilAssm{%d}{%s}\n%s" indent tp
                                  (s_to_string indent' sp) (Interval.to_string i)
    | SUntilNow (sp, i) -> Printf.sprintf "%sSUntilNow\n%s\n%s" indent
                             (Interval.to_string i) (s_to_string indent' sp)
  and v_to_string indent p =
    let indent' = "\t" ^ indent in
    match p with
    | VFF i -> Printf.sprintf "%sfalse{%d}" indent i
    | VEqConst (tp, x, c) -> Printf.sprintf "%sVEqConst(%d, %s, %s)" indent tp x (Dom.to_string c)
    | VPred (tp, r, trms) -> Printf.sprintf "%sVPred(%d, %s, %s)" indent tp r (Term.list_to_string trms)
    | VNeg sp -> Printf.sprintf "%sVNeg{%d}\n%s" indent (v_at p) (s_to_string indent' sp)
    | VOr (vp1, vp2) -> Printf.sprintf "%sVOr{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vp1) (v_to_string indent' vp2)
    | VAndL vp1 -> Printf.sprintf "%sVAndL{%d}\n%s" indent (v_at p) (v_to_string indent' vp1)
    | VAndR vp2 -> Printf.sprintf "%sVAndR{%d}\n%s" indent (v_at p) (v_to_string indent' vp2)
    | VImp (sp1, vp2) -> Printf.sprintf "%sVImp{%d}\n%s\n%s" indent (v_at p) (s_to_string indent' sp1) (v_to_string indent' vp2)
    | VIffSV (sp1, vp2) -> Printf.sprintf "%sVIffSV{%d}\n%s\n%s" indent (v_at p) (s_to_string indent' sp1) (v_to_string indent' vp2)
    | VIffVS (vp1, sp2) -> Printf.sprintf "%sVIffVS{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vp1) (s_to_string indent' sp2)
    | VExists (x, part) -> Printf.sprintf "%sVExists{%d}{%s}\n%s\n" indent (v_at (VExists (x, part)))
                             x (Part.to_string indent' (Var x) v_to_string part)
    | VForall (x, d, vp) -> Printf.sprintf "%sVForall{%d}{%s=%s}\n%s\n" indent (v_at p)
                              x (Dom.to_string d) (v_to_string indent' vp)
    | VPrev vp -> Printf.sprintf "%sVPrev{%d}\n%s" indent (v_at p) (v_to_string indent' vp)
    | VPrev0 -> Printf.sprintf "%sVPrev0{0}" indent'
    | VPrevOutL tp -> Printf.sprintf "%sVPrevOutL{%d}" indent' tp
    | VPrevOutR tp -> Printf.sprintf "%sVPrevOutR{%d}" indent' tp
    | VNext vp -> Printf.sprintf "%sVNext{%d}\n%s" indent (v_at p) (v_to_string indent' vp)
    | VNextAssm (tp, i) -> Printf.sprintf "%sVNextAssm{%d}{%s}" indent' tp (Interval.to_string i)
    | VNextOutL i -> Printf.sprintf "%sVNextOutL{%d}" indent' i
    | VNextOutR i -> Printf.sprintf "%sVNextOutR{%d}" indent' i
    | VOnceOut i -> Printf.sprintf "%sVOnceOut{%d}" indent' i
    | VOnce (_, _, vps) -> Printf.sprintf "%sVOnce{%d}\n%s" indent (v_at p)
                             (Etc.deque_to_string indent' v_to_string vps)
    | VEventually (_, _, vps) -> Printf.sprintf "%sVEventually{%d}\n%s" indent (v_at p)
                                   (Etc.deque_to_string indent' v_to_string vps)
    | VEventuallyAssm (tp, Some vp, i) -> Printf.sprintf "%sVEventuallyAssm{%d}{%s}\n%s" indent' tp
                                            (Interval.to_string i) (v_to_string indent' vp)
    | VEventuallyAssm (tp, None, i) -> Printf.sprintf "%sVEventuallyAssm{%d}\n%s" indent' tp
                                       (Interval.to_string i)
    | VHistorically (_, vp) -> Printf.sprintf "%sVHistorically{%d}\n%s" indent (v_at p) (v_to_string indent' vp)
    | VAlways (_, vp) -> Printf.sprintf "%sVAlways{%d}\n%s" indent (v_at p) (v_to_string indent' vp)
    | VAlwaysAssm (tp, i) -> Printf.sprintf "%sVAlwaysAssm{%d}\n%s" indent' tp
                               (Interval.to_string i)
    | VAlwaysNow (vp, i) -> Printf.sprintf "%sVAlwaysNow\n%s\n%s" indent
                              (Interval.to_string i) (v_to_string indent' vp)
    | VSinceOut i -> Printf.sprintf "%sVSinceOut{%d}" indent' i
    | VSince (_, vp1, vp2s) -> Printf.sprintf "%sVSince{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vp1)
                                 (Etc.deque_to_string indent' v_to_string vp2s)
    | VSinceInf (_, _, vp2s) -> Printf.sprintf "%sVSinceInf{%d}\n%s" indent (v_at p)
                                  (Etc.deque_to_string indent' v_to_string vp2s)
    | VUntil (_, vp1, vp2s) -> Printf.sprintf "%sVUntil{%d}\n%s\n%s" indent (v_at p)
                                 (Etc.deque_to_string indent' v_to_string vp2s) (v_to_string indent' vp1)
    | VUntilInf (_, _, vp2s) -> Printf.sprintf "%sVUntilInf{%d}\n%s" indent (v_at p)
                                  (Etc.deque_to_string indent' v_to_string vp2s)
    | VUntilAssm (tp, vp, i) -> Printf.sprintf "%sVUntilAssm{%d}{%s}\n%s" indent tp
                                  (Interval.to_string i) (v_to_string indent' vp)
    | VUntilNow (vp, i) -> Printf.sprintf "%sVUntilNow\n%s\n%s" indent
                             (Interval.to_string i) (v_to_string indent' vp)

  let to_string indent = function
    | S p -> s_to_string indent p
    | V p -> v_to_string indent p

  let val_changes_to_latex v =
    if List.is_empty v then "v"
    else "v[" ^ Etc.string_list_to_string (List.map v ~f:(fun (x, d) -> Printf.sprintf "%s \\mapsto %s" x d)) ^ "]"

  let rec s_to_latex indent v idx p (h: Formula.t) =
    let indent' = "\t" ^ indent in
    match p, h with
    | STT tp, TT  ->
       Printf.sprintf "\\infer[\\top]{%s, %d \\pvd true}{}\n" (val_changes_to_latex v) tp
    | SEqConst (tp, x, c), EqConst (_, _) ->
       Printf.sprintf "\\infer[\\Seqconst]{%s, %d \\pvd %s = %s}{%s \\approx %s}\n"
         (val_changes_to_latex v) tp (Etc.escape_underscores x) (Dom.to_string c)
         (Etc.escape_underscores x) (Dom.to_string c)
    | SPred (tp, r, trms), Predicate (_, _) ->
       Printf.sprintf "\\infer[\\Spred]{%s, %d \\pvd %s\\,(%s)}{(%s,[%s]) \\in\\Gamma_{%d}}\n"
         (val_changes_to_latex v) tp (Etc.escape_underscores r) (Term.list_to_string trms)
         (Etc.escape_underscores r) (Term.list_to_string trms) tp
    | SNeg vp, Neg f ->
       Printf.sprintf "\\infer[\\Sneg]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (v_to_latex indent' v idx vp f)
    | SOrL sp1, Or (_, f, g) ->
       Printf.sprintf "\\infer[\\Sdisjl]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (s_to_latex indent' v idx sp1 f)
    | SOrR sp2, Or (_, f, g) ->
       Printf.sprintf "\\infer[\\Sdisjr]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (s_to_latex indent' v idx sp2 g)
    | SAnd (sp1, sp2), And (_, f, g) ->
       Printf.sprintf "\\infer[\\Sconj]{%s, %d \\pvd %s}\n%s{{%s} & {%s}}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h)
         indent (s_to_latex indent' v idx sp1 f) (s_to_latex indent' v idx sp2 g)
    | SImpL vp1, Imp (_, f, g) ->
       Printf.sprintf "\\infer[\\SimpL]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (v_to_latex indent' v idx vp1 f)
    | SImpR sp2, Imp (_, f, g) ->
       Printf.sprintf "\\infer[\\SimpR]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (s_to_latex indent' v idx sp2 g)
    | SIffSS (sp1, sp2), Iff (_, _, f, g) ->
       Printf.sprintf "\\infer[\\SiffSS]{%s, %d \\pvd %s}\n%s{{%s} & {%s}}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h)
         indent (s_to_latex indent' v idx sp1 f) (s_to_latex indent' v idx sp2 g)
    | SIffVV (vp1, vp2), Iff (_, _, f, g) ->
       Printf.sprintf "\\infer[\\SiffVV]{%s, %d \\pvd %s}\n%s{{%s} & {%s}}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h)
         indent (v_to_latex indent' v idx vp1 f) (v_to_latex indent' v idx vp2 g)
    | SExists (x, d, sp), Exists (_, _, f) ->
       let v' = v @ [(x, Dom.to_string d)] in
       Printf.sprintf "\\infer[\\Sexists]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (s_to_latex indent' v' idx sp f)
    | SForall (x, part), Forall (_, _, f) ->
       Printf.sprintf "\\infer[\\Sforall]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent
         (String.concat ~sep:"&" (List.map part ~f:(fun (sub, sp) ->
                                      let idx' = idx + 1 in
                                      let v' = v @ [(x, "d_" ^ (Int.to_string idx') ^ " \\in " ^ (Setc.to_latex sub))] in
                                      "{" ^ (s_to_latex indent' v' idx' sp f) ^ "}")))
    | SPrev sp, Prev (i, f) ->
       Printf.sprintf "\\infer[\\Sprev{}]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (s_to_latex indent' v idx sp f)
    | SNext sp, Next (i, f) ->
       Printf.sprintf "\\infer[\\Snext{}]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (s_to_latex indent' v idx sp f)
    | SOnce (tp, sp), Once (i, f) ->
       Printf.sprintf "\\infer[\\Sonce{}]{%s, %d \\pvd %s}\n%s{{%d \\leq %d} & {\\tau_%d - \\tau_%d \\in %s} & {%s}}\n"
         (val_changes_to_latex v) tp (Formula.to_latex h) indent
         (s_at sp) tp tp (s_at sp) (Interval.to_latex i) (s_to_latex indent' v idx sp f)
    | SEventually (tp, sp), Eventually (i, f) ->
       Printf.sprintf "\\infer[\\Seventually{}]{%s, %d \\pvd %s}\n%s{{%d \\geq %d} & {\\tau_%d - \\tau_%d \\in %s} & {%s}}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent
         (s_at sp) tp (s_at sp) tp (Interval.to_latex i) (s_to_latex indent' v idx sp f)
    | SHistorically (tp, _, sps), Historically (i, f) ->
       Printf.sprintf "\\infer[\\Shistorically{}]{%s, %d \\pvd %s}\n%s{{\\tau_%d - \\tau_0 \\geq %d} & %s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent tp (Interval.left i)
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map sps ~f:(fun sp -> "{" ^ (s_to_latex indent' v idx sp f) ^ "}"))))
    | SHistoricallyOut _, Historically (i, f) ->
       Printf.sprintf "\\infer[\\ShistoricallyL{}]{%s, %d \\pvd %s}\n%s{\\tau_%d - \\tau_0 < %d}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (s_at p) (Interval.left i)
    | SAlways (_, _, sps), Always (i, f) ->
       Printf.sprintf "\\infer[\\Salways{}]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map sps ~f:(fun sp -> "{" ^ (s_to_latex indent' v idx sp f) ^ "}"))))
    | SSince (sp2, sp1s), Since (_, i, f, g) ->
       Printf.sprintf "\\infer[\\Ssince{}]{%s, %d \\pvd %s}\n%s{{%d \\leq %d} & {\\tau_%d - \\tau_%d \\in %s} & {%s} & %s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent
         (s_at sp2) (s_at p) (s_at p) (s_at sp2) (Interval.to_latex i) (s_to_latex indent' v idx sp2 g)
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map sp1s ~f:(fun sp -> "{" ^ (s_to_latex indent' v idx sp f) ^ "}"))))
    | SUntil (sp2, sp1s), Until (_, i, f, g) ->
       Printf.sprintf "\\infer[\\Suntil{}]{%s, %d \\pvd %s}\n%s{{%d \\leq %d} & {\\tau_%d - \\tau_%d \\in %s} & %s & {%s}}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent
         (s_at p) (s_at sp2) (s_at sp2) (s_at p) (Interval.to_latex i)
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map sp1s ~f:(fun sp -> "{" ^ (s_to_latex indent' v idx sp f) ^ "}"))))
         (s_to_latex indent' v idx sp2 g)
    | _ -> ""
  and v_to_latex indent v idx p (h: Formula.t) =
    let indent' = "\t" ^ indent in
    match p, h with
    | VFF tp, FF ->
       Printf.sprintf "\\infer[\\bot]{%s, %d \\nvd false}{}\n" (val_changes_to_latex v) tp
    | VEqConst (tp, x, c), EqConst (_, _) ->
       Printf.sprintf "\\infer[\\Veqconst]{%s, %d \\nvd %s = %s}{%s \\not\\approx %s}\n"
         (val_changes_to_latex v) tp (Etc.escape_underscores x) (Dom.to_string c)
         (Etc.escape_underscores x) (Dom.to_string c)
    | VPred (tp, r, trms), Predicate (_, _) ->
       Printf.sprintf "\\infer[\\Vpred]{%s, %d \\nvd %s\\,(%s)}{(%s,[%s]) \\notin\\Gamma_{%d}}\n"
         (val_changes_to_latex v) tp (Etc.escape_underscores r) (Term.list_to_string trms)
         (Etc.escape_underscores r) (Term.list_to_string trms) tp
    | VNeg sp, Neg f ->
       Printf.sprintf "\\infer[\\Vneg]{%s, %d \\nvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent (s_to_latex indent' v idx sp f)
    | VOr (vp1, vp2), Or (_, f, g) ->
       Printf.sprintf "\\infer[\\Vdisj]{%s, %d \\nvd %s}\n%s{{%s} & {%s}}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h)
         indent (v_to_latex indent' v idx vp1 f) (v_to_latex indent' v idx vp2 g)
    | VAndL vp1, And (_, f, _) ->
       Printf.sprintf "\\infer[\\Vconjl]{%s, %d \\nvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent (v_to_latex indent' v idx vp1 f)
    | VAndR vp2, And (_, _, g) ->
       Printf.sprintf "\\infer[\\Vconjr]{%s, %d \\nvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent (v_to_latex indent' v idx vp2 g)
    | VImp (sp1, vp2), Imp (_, f, g) ->
       Printf.sprintf "\\infer[\\Vimp]{%s, %d \\nvd %s}\n%s{{%s} & {%s}}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h)
         indent (s_to_latex indent' v idx sp1 f) (v_to_latex indent' v idx vp2 g)
    | VIffSV (sp1, vp2), Iff (_, _, f, g) ->
       Printf.sprintf "\\infer[\\ViffSV]{%s, %d \\nvd %s}\n%s{{%s} & {%s}}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h)
         indent (s_to_latex indent' v idx sp1 f) (v_to_latex indent' v idx vp2 g)
    | VIffVS (vp1, sp2), Iff (_, _, f, g) ->
       Printf.sprintf "\\infer[\\ViffSV]{%s, %d \\nvd %s}\n%s{{%s} & {%s}}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h)
         indent (v_to_latex indent' v idx vp1 f) (s_to_latex indent' v idx sp2 g)
    | VExists (x, part), Exists (_, _, f) ->
       Printf.sprintf "\\infer[\\Vexists]{%s, %d \\nvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent
         (String.concat ~sep:"&" (List.map part ~f:(fun (sub, vp) ->
                                      let idx' = idx + 1 in
                                      let v' = v @ [(x, "d_" ^ (Int.to_string idx') ^ " \\in " ^ (Setc.to_latex sub))] in
                                      "{" ^ (v_to_latex indent' v' idx' vp f) ^ "}")))
    | VForall (x, d, vp), Forall (_, _, f) ->
       let v' = v @ [(x, Dom.to_string d)] in
       Printf.sprintf "\\infer[\\Vforall]{%s, %d \\nvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent (v_to_latex indent' v' idx vp f)
    | VPrev vp, Prev (i, f) ->
       Printf.sprintf "\\infer[\\Vprev{}]{%s, %d \\nvd %s}\n%s{{%d > 0} & {%s}}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent (v_at p) (v_to_latex indent' v idx vp f)
    | VPrev0, Prev (i, f) ->
       Printf.sprintf "\\infer[\\Vprevz]{%s, %d \\nvd %s}{}\n" (val_changes_to_latex v) (v_at p) (Formula.to_latex h)
    | VPrevOutL tp, Prev (i, f) ->
       Printf.sprintf "\\infer[\\Vprevl]{%s, %d \\nvd %s}\n%s{{%d > 0} & {\\tau_%d - \\tau_%d < %d}}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent (v_at p) (v_at p) ((v_at p)-1) (Interval.left i)
    | VPrevOutR tp, Prev (i, f) ->
       Printf.sprintf "\\infer[\\Vprevr]{%s, %d \\nvd %s}\n%s{{%d > 0} & {\\tau_%d - \\tau_%d > %d}}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent (v_at p) (v_at p) ((v_at p)-1) (Option.value_exn (Interval.right i))
    | VNext vp, Next (i, f) ->
       Printf.sprintf "\\infer[\\Vnext{}]{%s, %d \\nvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent (v_to_latex indent' v idx vp f)
    | VNextOutL tp, Next (i, f) ->
       Printf.sprintf "\\infer[\\Vnextl]{%s, %d \\nvd %s}{\\tau_%d - \\tau_%d < %d}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) ((v_at p)+1) (v_at p) (Interval.left i)
    | VNextOutR tp, Next (i, f) ->
       Printf.sprintf "\\infer[\\Vnextr]{%s, %d \\nvd %s}{\\tau_%d - \\tau_%d > %d}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) ((v_at p)+1) (v_at p) (Option.value_exn (Interval.right i))
    | VOnceOut tp, Once (i, f) ->
       Printf.sprintf "\\infer[\\Voncel{}]{%s, %d \\nvd %s}\n%s{\\tau_%d - \\tau_0 < %d}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent (v_at p) (Interval.left i)
    | VOnce (_, _, vps), Once (i, f) ->
       Printf.sprintf "\\infer[\\Vonce{}]{%s, %d \\nvd %s}\n%s{{\\tau_%d - \\tau_0 \\geq %d} & %s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent (v_at p) (Interval.left i)
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map vps ~f:(fun vp -> "{" ^ (v_to_latex indent' v idx vp f) ^ "}"))))
    | VEventually (_, _, vps), Eventually (i, f) ->
       Printf.sprintf "\\infer[\\Veventually{}]{%s, %d \\nvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map vps ~f:(fun vp -> "{" ^ (v_to_latex indent' v idx vp f) ^ "}"))))
    | VHistorically (tp, vp), Historically (i, f) ->
       Printf.sprintf "\\infer[\\Vhistorically{}]{%s, %d \\nvd %s}\n%s{{%d \\leq %d} & {\\tau_%d - \\tau_%d \\in %s} & {%s}}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent
         (v_at vp) tp tp (v_at vp) (Interval.to_latex i) (v_to_latex indent' v idx vp f)
    | VAlways (tp, vp), Always (i, f) ->
       Printf.sprintf "\\infer[\\Valways{}]{%s, %d \\nvd %s}\n%s{{%d \\geq %d} & {\\tau_%d - \\tau_%d \\in %s} & {%s}}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent
         (v_at vp) tp (v_at vp) tp (Interval.to_latex i) (v_to_latex indent' v idx vp f)
    | VSinceOut tp, Since (_, i, f, g) ->
       Printf.sprintf "\\infer[\\Vsincel{}]{%s, %d \\nvd %s}\n%s{\\tau_%d - \\tau_0 < %d}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent (v_at p) (Interval.left i)
    | VSince (tp, vp1, vp2s), Since (_, i, f, g) ->
       Printf.sprintf "\\infer[\\Vsince{}]{%s, %d \\nvd %s}\n%s{{%d \\leq %d} & {\\tau_%d - \\tau_0 \\geq %d} & {%s} & %s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent
         (v_at vp1) tp tp (Interval.left i) (v_to_latex indent' v idx vp1 f)
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map vp2s ~f:(fun vp -> "{" ^ (v_to_latex indent' v idx vp g) ^ "}"))))
    | VSinceInf (tp, _, vp2s), Since (_, i, f, g) ->
       Printf.sprintf "\\infer[\\Vsinceinf{}]{%s, %d \\nvd %s}\n%s{{\\tau_%d - \\tau_0 \\geq %d} & %s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent tp (Interval.left i)
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map vp2s ~f:(fun vp -> "{" ^ (v_to_latex indent' v idx vp g) ^ "}"))))
    | VUntil (tp, vp1, vp2s), Until (_, i, f, g) ->
       Printf.sprintf "\\infer[\\Vuntil{}]{%s, %d \\nvd %s}\n%s{{%d \\leq %d} & %s & {%s}}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent tp (v_at vp1)
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map vp2s ~f:(fun vp -> "{" ^ (v_to_latex indent' v idx vp g) ^ "}"))))
         (v_to_latex indent' v idx vp1 f)
    | VUntilInf (_, _, vp2s), Until (_, i, f, g) ->
       Printf.sprintf "\\infer[\\Vuntil{}]{%s, %d \\nvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map vp2s ~f:(fun vp -> "{" ^ (v_to_latex indent' v idx vp g) ^ "}"))))
    | _ -> ""

  let to_latex indent fmla = function
    | S p -> s_to_latex indent [] 0 p fmla
    | V p -> v_to_latex indent [] 0 p fmla

  let to_bool indent = function
    | S _ -> "true\n"
    | V _ -> "false\n"

  module Size = struct

    let sum f d = Fdeque.fold d ~init:0 ~f:(fun acc p -> acc + f p)

    let rec s = function
      | STT _ -> 1
      | SEqConst _ -> 1
      | SPred _ -> 1
      | SNeg vp -> 1 + v vp
      | SOrL sp1 -> 1 + s sp1
      | SOrR sp2 -> 1 + s sp2
      | SAnd (sp1, sp2) -> 1 + s sp1 + s sp2
      | SImpL vp1 -> 1 + v vp1
      | SImpR sp2 -> 1 + s sp2
      | SIffSS (sp1, sp2) -> 1 + s sp1 + s sp2
      | SIffVV (vp1, vp2) -> 1 + v vp1 + v vp2
      | SExists (_, _, sp) -> 1 + s sp
      | SForall (_, part) -> 1 + (Part.fold_left part 0 (fun a sp -> a + s sp))
      | SPrev sp -> 1 + s sp
      | SNext sp -> 1 + s sp
      | SNextAssm _ -> 1
      | SOnce (_, sp) -> 1 + s sp
      | SEventually (_, sp) -> 1 + s sp
      | SEventuallyAssm _ -> 1
      | SEventuallyNow (sp, _) -> 1 + s sp
      | SHistorically (_, _, sps) -> 1 + sum s sps
      | SHistoricallyOut _ -> 1
      | SAlways (_, _, sps) -> 1 + sum s sps
      | SAlwaysAssm _ -> 1
      | SSince (sp2, sp1s) -> 1 + s sp2 + sum s sp1s
      | SUntil (sp2, sp1s) -> 1 + s sp2 + sum s sp1s
      | SUntilAssm _ -> 1
      | SUntilNow (sp, _) -> 1 + s sp
    and v = function
      | VFF _ -> 1
      | VEqConst _ -> 1
      | VPred _ -> 1
      | VNeg sp -> 1 + s sp
      | VOr (vp1, vp2) -> 1 + v vp1 + v vp2
      | VAndL vp1 -> 1 + v vp1
      | VAndR vp2 -> 1 + v vp2
      | VImp (sp1, vp2) -> 1 + s sp1 + v vp2
      | VIffSV (sp1, vp2) -> 1 + s sp1 + v vp2
      | VIffVS (vp1, sp2) -> 1 + v vp1 + s sp2
      | VExists (_, part) -> 1 + (Part.fold_left part 0 (fun a vp -> a + v vp))
      | VForall (_, _, vp) -> 1 + v vp
      | VPrev vp -> 1 + v vp
      | VPrev0 -> 1
      | VPrevOutL _ -> 1
      | VPrevOutR _ -> 1
      | VNext vp -> 1 + v vp
      | VNextOutL _ -> 1
      | VNextOutR _ -> 1
      | VNextAssm _ -> 1
      | VOnceOut _ -> 1
      | VOnce (_, _, vp1s) -> 1 + sum v vp1s
      | VEventually (_, _, vp1s) -> 1 + sum v vp1s
      | VEventuallyAssm _ -> 1
      | VHistorically (_, vp1) -> 1 + v vp1
      | VAlways (_, vp1) -> 1 + v vp1
      | VAlwaysAssm _ -> 1
      | VAlwaysNow (vp, _) -> 1 + v vp
      | VSinceOut _ -> 1
      | VSince (_, vp1, vp2s) -> 1 + v vp1 + sum v vp2s
      | VSinceInf (_, _, vp2s) -> 1 + sum v vp2s
      | VUntil (_, vp1, vp2s) -> 1 + v vp1 + sum v vp2s
      | VUntilInf (_, _, vp2s) -> 1 + sum v vp2s
      | VUntilAssm _ -> 1
      | VUntilNow (vp, _) -> 1 + v vp

    let p = function
      | S s_p -> s s_p
      | V v_p -> v v_p

    let minp_bool = cmp p

    let minp x y = if p x <= p y then x else y

    let minp_list = function
      | [] -> raise (Invalid_argument "function not defined for empty lists")
      | x :: xs -> List.fold_left xs ~init:x ~f:minp

  end

end

module Pdt = struct

  type 'a t = Leaf of 'a | Node of string * ('a t) Part.t

  let rec apply1 vars f pdt = match vars, pdt with
    | _ , Leaf l -> Leaf (f l)
    | z :: vars, Node (x, part) ->
       if String.equal x z then
         Node (x, Part.map part (apply1 vars f))
       else apply1 vars f (Node (x, part))
    | _ -> raise (Invalid_argument "variable list is empty")

  let rec apply2 vars f pdt1 pdt2 = match vars, pdt1, pdt2 with
    | _ , Leaf l1, Leaf l2 -> Leaf (f l1 l2)
    | _ , Leaf l1, Node (x, part2) -> Node (x, Part.map part2 (apply1 vars (f l1)))
    | _ , Node (x, part1), Leaf l2 -> Node (x, Part.map part1 (apply1 vars (fun l1 -> f l1 l2)))
    | z :: vars, Node (x, part1), Node (y, part2) ->
       if String.equal x z && String.equal y z then
         Node (z, Part.merge2 (apply2 vars f) part1 part2)
       else (if String.equal x z then
               Node (x, Part.map part1 (fun pdt1 -> apply2 vars f pdt1 (Node (y, part2))))
             else (if String.equal y z then
                     Node (y, Part.map part2 (apply2 vars f (Node (x, part1))))
                   else apply2 vars f (Node (x, part1)) (Node (y, part2))))
    | _ -> raise (Invalid_argument "variable list is empty")

  let rec apply3 vars f pdt1 pdt2 pdt3 = match vars, pdt1, pdt2, pdt3 with
    | _ , Leaf l1, Leaf l2, Leaf l3 -> Leaf (f l1 l2 l3)
    | _ , Leaf l1, Leaf l2, Node (x, part3) ->
       Node (x, Part.map part3 (apply1 vars (fun l3 -> f l1 l2 l3)))
    | _ , Leaf l1, Node (x, part2), Leaf l3 ->
       Node (x, Part.map part2 (apply1 vars (fun l2 -> f l1 l2 l3)))
    | _ , Node (x, part1), Leaf l2, Leaf l3 ->
       Node (x, Part.map part1 (apply1 vars (fun l1 -> f l1 l2 l3)))
    | w :: vars, Leaf l1, Node (y, part2), Node (z, part3) ->
       if String.equal y w && String.equal z w then
         Node (w, Part.merge2 (apply2 vars (f l1)) part2 part3)
       else (if String.equal y w then
               Node (y, Part.map part2 (fun pdt2 -> apply2 vars (f l1) pdt2 (Node (z, part3))))
             else (if String.equal z w then
                     Node (z, Part.map part3 (fun pdt3 -> apply2 vars (f l1) (Node (y, part2)) pdt3))
                   else apply3 vars f (Leaf l1) (Node (y, part2)) (Node(z, part3))))
    | w :: vars, Node (x, part1), Node (y, part2), Leaf l3 ->
       if String.equal x w && String.equal y w then
         Node (w, Part.merge2 (apply2 vars (fun l1 l2 -> f l1 l2 l3)) part1 part2)
       else (if String.equal x w then
               Node (x, Part.map part1 (fun pdt1 -> apply2 vars (fun pt1 pt2 -> f pt1 pt2 l3) pdt1 (Node (y, part2))))
             else (if String.equal y w then
                     Node (y, Part.map part2 (fun pdt2 -> apply2 vars (fun l1 l2 -> f l1 l2 l3) (Node (x, part1)) pdt2))
                   else apply3 vars f (Node (x, part1)) (Node (y, part2)) (Leaf l3)))
    | w :: vars, Node (x, part1), Leaf l2, Node (z, part3) ->
       if String.equal x w && String.equal z w then
         Node (w, Part.merge2 (apply2 vars (fun l1 -> f l1 l2)) part1 part3)
       else (if String.equal x w then
               Node (x, Part.map part1 (fun pdt1 -> apply2 vars (fun l1 -> f l1 l2) pdt1 (Node (z, part3))))
             else (if String.equal z w then
                     Node (z, Part.map part3 (fun pdt3 -> apply2 vars (fun l1 -> f l1 l2) (Node (x, part1)) pdt3))
                   else apply3 vars f (Node (x, part1)) (Leaf l2) (Node (z, part3))))
    | w :: vars, Node (x, part1), Node (y, part2), Node (z, part3) ->
       if String.equal x w && String.equal y w && String.equal z w then
         Node (z, Part.merge3 (apply3 vars f) part1 part2 part3)
       else (if String.equal x w && String.equal y w then
               Node (w, Part.merge2 (fun pdt1 pdt2 -> apply3 vars f pdt1 pdt2 (Node (z, part3))) part1 part2)
             else (if String.equal x w && String.equal z w then
                     Node (w, Part.merge2 (fun pdt1 pdt3 -> apply3 vars f pdt1 (Node (y, part2)) pdt3) part1 part3)
                   else (if String.equal y w && String.equal z w then
                           Node (w, Part.merge2 (apply3 vars (fun l1 -> f l1) (Node (x, part1))) part2 part3)
                         else (if String.equal x w then
                                 Node (x, Part.map part1 (fun pdt1 -> apply3 vars f pdt1 (Node (y, part2)) (Node (z, part3))))
                               else (if String.equal y w then
                                       Node (y, Part.map part2 (fun pdt2 -> apply3 vars f (Node (x, part1)) pdt2 (Node (z, part3))))
                                     else (if String.equal z w then
                                             Node (z, Part.map part3 (fun pdt3 -> apply3 vars f (Node (x, part1)) (Node (y, part2)) pdt3))
                                           else apply3 vars f (Node (x, part1)) (Node (y, part2)) (Node (z, part3))))))))
    | _ -> raise (Invalid_argument "variable list is empty")

  let rec split_prod = function
    | Leaf (l1, l2) -> (Leaf l1, Leaf l2)
    | Node (x, part) -> let (part1, part2) = Part.split_prod (Part.map part split_prod) in
                        (Node (x, part1), Node (x, part2))

  let rec split_list = function
    | Leaf l -> List.map l ~f:(fun el -> Leaf el)
    | Node (x, part) -> List.map (Part.split_list (Part.map part split_list)) ~f:(fun el -> Node (x, el))

  let rec to_string f indent = function
    | Leaf pt -> Printf.sprintf "%s%s\n" indent (f pt)
    | Node (x, part) -> (Part.to_string indent (Var x) (to_string f) part)

  let rec to_latex f indent = function
    | Leaf pt -> Printf.sprintf "%s%s\n" indent (f pt)
    | Node (x, part) -> (Part.to_string indent (Var x) (to_latex f) part)

  let rec to_light_string f indent = function
    | Leaf pt -> Printf.sprintf "%s%s\n" indent (f pt)
    | Node (x, part) -> (Part.to_string indent (Var x) (to_light_string f) part)

  let unleaf = function
    | Leaf l -> l
    | _ -> raise (Invalid_argument "function not defined for nodes")

  let rec hide vars f_leaf f_node pdt = match vars, pdt with
    |  _ , Leaf l -> Leaf (f_leaf l)
    | [x], Node (y, part) -> Leaf (f_node (Part.map part unleaf))
    | x :: vars, Node (y, part) -> if String.equal x y then
                                     Node (y, Part.map part (hide vars f_leaf f_node))
                                   else hide vars f_leaf f_node (Node (y, part))
    | _ -> raise (Invalid_argument "function not defined for other cases")

  (* reduce related *)
  let rec eq p_eq pdt1 pdt2 =
    match pdt1, pdt2 with
    | Leaf l1, Leaf l2 -> p_eq l1 l2
    | Node (x, part), Node (x', part') -> String.equal x x' && Int.equal (Part.length part) (Part.length part') &&
                                            List.for_all2_exn part part' ~f:(fun (s, v) (s', v') ->
                                                Setc.equal s s' && eq p_eq v v')
    | _ -> false

  let rec reduce p_eq = function
    | Leaf l -> Leaf l
    | Node (x, part) -> Node (x, Part.dedup (eq p_eq) (Part.map part (reduce p_eq)))

  let rec apply1_reduce p_eq vars f pdt = match vars, pdt with
    | _ , Leaf l -> Leaf (f l)
    | z :: vars, Node (x, part) ->
       if String.equal x z then
         Node (x, Part.map_dedup (eq p_eq) part (apply1_reduce p_eq vars f))
       else apply1_reduce p_eq vars f (Node (x, part))
    | _ -> raise (Invalid_argument "variable list is empty")

  let rec apply2_reduce p_eq vars f pdt1 pdt2 = match vars, pdt1, pdt2 with
    | _ , Leaf l1, Leaf l2 -> Leaf (f l1 l2)
    | _ , Leaf l1, Node (x, part2) -> Node (x, Part.map_dedup (eq p_eq) part2 (apply1_reduce p_eq vars (f l1)))
    | _ , Node (x, part1), Leaf l2 -> Node (x, Part.map_dedup (eq p_eq) part1 (apply1_reduce p_eq vars (fun l1 -> f l1 l2)))
    | z :: vars, Node (x, part1), Node (y, part2) ->
       if String.equal x z && String.equal y z then
         Node (z, Part.merge2_dedup (eq p_eq) (apply2_reduce p_eq vars f) part1 part2)
       else (if String.equal x z then
               Node (x, Part.map_dedup (eq p_eq) part1 (fun pdt1 -> apply2_reduce p_eq vars f pdt1 (Node (y, part2))))
             else (if String.equal y z then
                     Node (y, Part.map_dedup (eq p_eq) part2 (apply2_reduce p_eq vars f (Node (x, part1))))
                   else apply2_reduce p_eq vars f (Node (x, part1)) (Node (y, part2))))
    | _ -> raise (Invalid_argument "variable list is empty")

  let apply3_reduce p_eq vars f pdt1 pdt2 pdt3 =
    let p_eq2 (a, b) (a', b') = a == a' && b == b' in
    let pdt12 = apply2_reduce p_eq2 vars (fun a b -> (a, b)) pdt1 pdt2 in
    apply2_reduce p_eq vars (fun (a, b) c -> f a b c) pdt12 pdt3

  let rec split_prod_reduce p_eq = function
    | Leaf (l1, l2) -> (Leaf l1, Leaf l2)
    | Node (x, part) -> let (part1, part2) = Part.split_prod_dedup (eq p_eq) (Part.map part (split_prod_reduce p_eq)) in
                        (Node (x, part1), Node (x, part2))

  let rec split_list_reduce p_eq = function
    | Leaf l -> List.map l ~f:(fun el -> Leaf el)
    | Node (x, part) -> List.map (Part.split_list_dedup (eq p_eq) (Part.map part (split_list_reduce p_eq))) ~f:(fun el -> Node (x, el))

  let rec hide_reduce p_eq vars f_leaf f_node pdt = match vars, pdt with
    |  _ , Leaf l -> Leaf (f_leaf l)
    | [x], Node (y, part) -> Leaf (f_node (Part.map part unleaf))
    | x :: vars, Node (y, part) -> if String.equal x y then
                                     Node (y, Part.map_dedup (eq p_eq) part (hide_reduce p_eq vars f_leaf f_node))
                                   else hide_reduce p_eq vars f_leaf f_node (Node (y, part))
    | _ -> raise (Invalid_argument "function not defined for other cases")

  let rec replace_leaf v l = function
    | Leaf _ -> Leaf l
    | Node (x, part) -> Node (x, Part.map2 part (fun (s, expl) ->
                                     if Setc.mem s (Map.find_exn v x) then
                                       (s, replace_leaf v l expl)
                                     else
                                       (s, expl)))

  let rec specialize v = function
    | Leaf l -> l
    | Node (x, part) -> specialize v (Part.find part (Map.find_exn v x))

  let rec specialize_partial v = function
    | Leaf l -> Leaf l
    | Node (x, part) when Map.mem v x -> specialize_partial v (Part.find part (Map.find_exn v x))
    | Node (x, part) -> Node (x, Part.map part (specialize_partial v))

  let rec collect f v x = function
    | Leaf l when f l -> Setc.univ (module Dom)
    | Leaf l -> Setc.empty (module Dom)
    | Node (x', part) when String.equal x x' ->
       List.fold_left (Part.map2 part (fun (s, p) -> Setc.inter s (collect f v x p)))
         ~init:(Setc.empty (module Dom)) ~f:Setc.union
    | Node (x', part) ->
       collect f v x (Part.find part (Map.find_exn v x'))

  let rec from_valuation vars v p p' =
    match vars with
    | [] -> Leaf p
    | var::vars when not (Map.mem v var) -> from_valuation vars v p p'
    | var::vars -> let d = Map.find_exn v var in
                   let rest = from_valuation vars v p p' in
                   let part = Part.tabulate (Set.singleton (module Dom) d) (fun _ -> rest) (Leaf p') in
                   Node (var, part)

end

type t = Proof.t Pdt.t

let rec is_violated = function
  | Pdt.Leaf l -> (match l with
                   | Proof.S _ -> false
                   | V _ -> true)
  | Node (x, part) -> Part.exists part is_violated

let rec is_satisfied = function
  | Pdt.Leaf l -> (match l with
                   | Proof.S _ -> true
                   | V _ -> false)
  | Node (x, part) -> Part.exists part is_satisfied

(*let rec get_violation v = function
  | Pdt.Leaf l -> (v, l)
  | Node (x, part) -> let (s, p) = Part.find2 part is_violated in
                      let elt = Setc.some_elt (Dom.tt_of_domain (Setc.min_elt_exn s)) s in
                      get_violation (Map.add_exn ~key:x ~data:elt) p*)

let rec at = function
  | Pdt.Leaf pt -> Proof.p_at pt
  | Node (_, part) -> at (Part.hd part)

let to_string expl = Pdt.to_string (Proof.to_string "") "" expl

let to_latex fmla expl = Pdt.to_latex (Proof.to_latex "" fmla) "" expl

let to_light_string expl = Pdt.to_light_string (Proof.to_bool "") "" expl
