(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base


module Part = struct

  type 'a t = Abs_part of ((Domain.t, Domain.comparator_witness) Coset.t * 'a) list

  let the = function Abs_part part -> part

  let hd part = snd (List.hd_exn (the part))

  let map part f = Abs_part (List.map (the part) (fun (s, p) -> (s, f p)))

  let fold_left part init f = List.fold_left (the part) ~init:init ~f:(fun acc (_, p) -> f acc p)

  let rec merge2 f part1 part2 = match part1, part2 with
    | Abs_part [], Abs_part [] -> Abs_part []
    | Abs_part ((sub1, v1) :: part1), Abs_part part2 ->
       let part12 = List.filter_map part2
                      (fun (sub2, v2) ->
                        (if not (Coset.is_empty (Coset.inter sub1 sub2))
                         then Some (Coset.inter sub1 sub2, f v1 v2) else None)) in
       let part2not1 = List.filter_map part2
                         (fun (sub2, v2) ->
                           (if not (Coset.is_empty (Coset.diff sub2 sub1))
                            then Some (Coset.diff sub2 sub1, v2) else None)) in
       Abs_part (part12 @ (the (merge2 f (Abs_part part1) (Abs_part part2not1))))

end


module Proof = struct

  type sp =
    | STT of int
    | SPred of int * string * Pred.Term.t list
    | SNeg of vp
    | SOrL of sp
    | SOrR of sp
    | SAnd of sp * sp
    | SImpL of vp
    | SImpR of sp
    | SIffSS of sp * sp
    | SIffVV of vp * vp
    | SExists of string * Domain.t * sp
    | SForall of string * (sp Part.t)
    | SPrev of sp
    | SNext of sp
    | SOnce of int * sp
    | SEventually of int * sp
    | SHistorically of int * int * sp Fdeque.t
    | SHistoricallyOutL of int
    | SAlways of int * int * sp Fdeque.t
    | SSince of sp * sp Fdeque.t
    | SUntil of sp * sp Fdeque.t
  and vp =
    | VFF of int
    | VPred of int * string * Pred.Term.t list
    | VNeg of sp
    | VOr of vp * vp
    | VAndL of vp
    | VAndR of vp
    | VImp of sp * vp
    | VIffSV of sp * vp
    | VIffVS of vp * sp
    | VExists of string * (vp Part.t)
    | VForall of string * Domain.t * vp
    | VPrev of vp
    | VPrev0
    | VPrevOutL of int
    | VPrevOutR of int
    | VNext of vp
    | VNextOutL of int
    | VNextOutR of int
    | VOnceOut of int
    | VOnce of int * int * vp Fdeque.t
    | VEventually of int * int * vp Fdeque.t
    | VHistorically of int * vp
    | VAlways of int * vp
    | VSinceOut of int
    | VSince of int * vp * vp Fdeque.t
    | VSinceInf of int * int * vp Fdeque.t
    | VUntil of int * vp * vp Fdeque.t
    | VUntilInf of int * int * vp Fdeque.t

  type t = S of sp | V of vp

  let s_append sp sp1 = match sp with
    | SSince (sp2, sp1s) -> SSince (sp2, Fdeque.enqueue_back sp1s sp1)
    | SUntil (sp2, sp1s) -> SUntil (sp2, Fdeque.enqueue_front sp1s sp1)
    | _ -> raise (Invalid_argument "sappend is not defined for this sp")

  let v_append vp vp2 = match vp with
    | VSince (tp, vp1, vp2s) -> VSince (tp,  vp1, Fdeque.enqueue_back vp2s vp2)
    | VSinceInf (tp, etp, vp2s) -> VSinceInf (tp, etp, Fdeque.enqueue_back vp2s vp2)
    | VUntil (tp, vp1, vp2s) -> VUntil (tp, vp1, Fdeque.enqueue_front vp2s vp2)
    | VUntilInf (tp, ltp, vp2s) -> VUntilInf (tp, ltp, Fdeque.enqueue_front vp2s vp2)
    | _ -> raise (Invalid_argument "vappend is not defined for this vp")

  let s_drop = function
    | SUntil (sp2, sp1s) -> if Fdeque.is_empty sp1s then None
                            else Some (SUntil (sp2, Fdeque.drop_front sp1s))
    | _ -> raise (Invalid_argument "sdrop is not defined for this sp")

  let v_drop = function
    | VUntil (tp, vp1, vp2s) -> if Fdeque.is_empty vp2s then None
                                else Some (VUntil (tp, vp1, Fdeque.drop_front vp2s))
    | VUntilInf (tp, ltp, vp2s) -> if Fdeque.is_empty vp2s then None
                                   else Some (VUntilInf (tp, ltp, Fdeque.drop_front vp2s))
    | _ -> raise (Invalid_argument "vdrop is not defined for this vp")

  let rec s_at = function
    | STT tp -> tp
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
    | SOnce (tp, _) -> tp
    | SEventually (tp, _) -> tp
    | SHistorically (tp, _, _) -> tp
    | SHistoricallyOutL tp -> tp
    | SAlways (tp, _, _) -> tp
    | SSince (sp2, sp1s) -> if Fdeque.is_empty sp1s then s_at sp2
                            else s_at (Fdeque.peek_back_exn sp1s)
    | SUntil (sp2, sp1s) -> if Fdeque.is_empty sp1s then s_at sp2
                            else s_at (Fdeque.peek_front_exn sp1s)
  and v_at = function
    | VFF tp -> tp
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
    | VOnceOut tp -> tp
    | VOnce (tp, _, _) -> tp
    | VEventually (tp, _, _) -> tp
    | VHistorically (tp, _) -> tp
    | VAlways (tp, _) -> tp
    | VSinceOut tp -> tp
    | VSince (tp, _, _) -> tp
    | VSinceInf (tp, _, _) -> tp
    | VUntil (tp, _, _) -> tp
    | VUntilInf (tp, _, _) -> tp

  let s_ltp = function
    | SUntil (sp2, _) -> s_at sp2
    | _ -> raise (Invalid_argument "s_ltp is not defined for this sp")

  let v_etp = function
    | VUntil (tp, _, vp2s) -> if Fdeque.is_empty vp2s then tp
                              else v_at (Fdeque.peek_front_exn vp2s)
    | _ -> raise (Invalid_argument "v_etp is not defined for this vp")

  let p_at = function
    | S s_p -> s_at s_p
    | V v_p -> v_at v_p

  let cmp f p1 p2 = f p1 <= f p2

  module Size = struct

    let sum f d = Fdeque.fold d ~init:0 ~f:(fun acc p -> acc + f p)

    let rec s = function
      | STT _ -> 1
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
      | SOnce (_, sp) -> 1 + s sp
      | SEventually (_, sp) -> 1 + s sp
      | SHistorically (_, _, sps) -> 1 + sum s sps
      | SHistoricallyOutL _ -> 1
      | SAlways (_, _, sps) -> 1 + sum s sps
      | SSince (sp2, sp1s) -> 1 + s sp2 + sum s sp1s
      | SUntil (sp2, sp1s) -> 1 + s sp2 + sum s sp1s
    and v = function
      | VFF _ -> 1
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
      | VOnceOut _ -> 1
      | VOnce (_, _, vp1s) -> 1 + sum v vp1s
      | VEventually (_, _, vp1s) -> 1 + sum v vp1s
      | VHistorically (_, vp1) -> 1 + v vp1
      | VAlways (_, vp1) -> 1 + v vp1
      | VSinceOut _ -> 1
      | VSince (_, vp1, vp2s) -> 1 + v vp1 + sum v vp2s
      | VSinceInf (_, _, vp2s) -> 1 + sum v vp2s
      | VUntil (_, vp1, vp2s) -> 1 + v vp1 + sum v vp2s
      | VUntilInf (_, _, vp2s) -> 1 + sum v vp2s

    let p = function
      | S s_p -> s s_p
      | V v_p -> v v_p

    let le = cmp p

    let minsize x y = if p x <= p y then x else y

    let minsize_list = function
      | [] -> raise (Invalid_argument "minsize_list is not defined for empty lists")
      | x :: xs -> List.fold_left xs x minsize

  end

end


type 'a pdt = Leaf of 'a | Node of string * ('a pdt) Part.t

type t = Proof.t pdt

let rec apply1 vars f expl = match vars, expl with
  | vars, Leaf pt -> Leaf (f pt)
  | z :: vars, Node (x, part) ->
     if String.equal x z then
       Node (x, Part.map part (apply1 vars f))
     else apply1 vars f (Node (x, part))
  | _ -> raise (Invalid_argument "variable list is empty")

let rec apply2 vars f expl1 expl2 = match vars, expl1, expl2 with
  | vars, Leaf pt1, Leaf pt2 -> Leaf (f pt1 pt2)
  | vars, Leaf pt1, Node (x, part2) ->
     Node (x, Part.map part2 (apply1 vars (f pt1)))
  | vars, Node (x, part1), Leaf pt2 ->
     Node (x, Part.map part1 (apply1 vars (fun pt1 -> f pt1 pt2)))
  | z :: vars, Node (x, part1), Node (y, part2) ->
     if String.equal x z && String.equal y z then
       Node (z, Part.merge2 (apply2 vars f) part1 part2)
     else (if String.equal x z then
             Node (x, Part.map part1 (fun e1 -> apply2 vars f e1 (Node (y, part2))))
           else (if String.equal y z then
                   Node (y, Part.map part2 (apply2 vars f (Node (x, part1))))
                 else apply2 vars f (Node (x, part1)) (Node (y, part2))))
  | _ -> raise (Invalid_argument "variable list is empty")
