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
open Pred

module Deque = Core_kernel.Deque

module Part = struct

  type 'a t = Abs_part of ((Domain.t, Domain.comparator_witness) Coset.t * 'a) list

  let random_empty_set = Set.empty (module String)

  let trivial p = Abs_part ([(Coset.univ (module Domain), p)])

  let the = function Abs_part part -> part

  let hd part = snd (List.hd_exn (the part))

  let map part f = Abs_part (List.map (the part) (fun (s, p) -> (s, f p)))

  let fold_left_snd part init f = List.fold_left (the part) ~init:init ~f:(fun acc (_, p) -> f acc p)

  let rec tabulate ds f z =
    let rec distinct = function
      | [] -> true
      | x :: xs -> not (List.mem xs x ~equal:Domain.equal) && distinct xs in
    Abs_part (if not (distinct ds) then
                (Complement (Set.of_list (module Domain) ds), z) ::
                  (List.map ~f:(fun d -> (Coset.Finite (Set.of_list (module Domain) [d]), f d)) ds)
              else [(Coset.univ (module Domain), z)])

  let rec merge2 f part1 part2 = match part1, part2 with
    | Abs_part [], _ -> Abs_part []
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

  let merge3 f part1 part2 part3 = match part1, part2, part3 with
    | Abs_part [], _ , _
      | _ , Abs_part [], _
      | _ , _ , Abs_part [] -> raise (Invalid_argument "one of the partitions is empty")
    | Abs_part part1, Abs_part part2, Abs_part part3 ->
       merge2 (fun pt3 f' -> f' pt3) (Abs_part part3) (merge2 f (Abs_part part1) (Abs_part part2))

  let rec el_to_string indent f (sub, v) =
    Printf.sprintf "%scoset = {%s}\n%s%s" indent (Coset.to_string sub) indent (f indent v)

  let to_string indent f part = match the part with
    | [] -> indent ^ "[]"
    | [x] -> indent ^ Etc.eat "[" ((el_to_string indent f x) ^ "]")
    | x :: xs ->
       List.fold_left ~f:(fun s el -> Etc.eat (s ^ "\n" ^ indent ^ "; ") (el_to_string indent f el))
         ~init:(indent ^ Etc.eat "[ " (el_to_string indent f x)) xs ^ " ]"

end


module Proof = struct

  type sp =
    | STT of int
    | SPred of int * string * Term.t list
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
    | SHistorically of int * int * sp Deque.t
    | SHistoricallyOut of int
    | SAlways of int * int * sp Deque.t
    | SSince of sp * sp Deque.t
    | SUntil of sp * sp Deque.t
  and vp =
    | VFF of int
    | VPred of int * string * Term.t list
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
    | VOnce of int * int * vp Deque.t
    | VEventually of int * int * vp Deque.t
    | VHistorically of int * vp
    | VAlways of int * vp
    | VSinceOut of int
    | VSince of int * vp * vp Deque.t
    | VSinceInf of int * int * vp Deque.t
    | VUntil of int * vp * vp Deque.t
    | VUntilInf of int * int * vp Deque.t

  type t = S of sp | V of vp

  let unS = function
    | S sp -> sp
    | _ -> raise (Invalid_argument "unS is not defined for V proofs")

  let unV = function
    | V vp -> vp
    | _ -> raise (Invalid_argument "unV is not defined for S proofs")

  let s_append sp sp1 = match sp with
    | SSince (sp2, sp1s) -> Deque.enqueue_back sp1s sp1; SSince (sp2, sp1s)
    | SUntil (sp2, sp1s) -> Deque.enqueue_back sp1s sp1; SUntil (sp2, sp1s)
    | _ -> raise (Invalid_argument "sappend is not defined for this sp")

  let v_append vp vp2 = match vp with
    | VSince (tp, vp1, vp2s) -> Deque.enqueue_back vp2s vp2; VSince (tp,  vp1, vp2s)
    | VSinceInf (tp, etp, vp2s) -> Deque.enqueue_back vp2s vp2; VSinceInf (tp, etp, vp2s)
    | VUntil (tp, vp1, vp2s) -> Deque.enqueue_back vp2s vp2; VUntil (tp, vp1, vp2s)
    | VUntilInf (tp, ltp, vp2s) -> Deque.enqueue_back vp2s vp2; VUntilInf (tp, ltp, vp2s)
    | _ -> raise (Invalid_argument "vappend is not defined for this vp")

  let s_drop = function
    | SUntil (sp2, sp1s) -> if Deque.is_empty sp1s then None
                            else (Deque.drop_front sp1s; Some (SUntil (sp2, sp1s)))
    | _ -> raise (Invalid_argument "sdrop is not defined for this sp")

  let v_drop = function
    | VUntil (tp, vp1, vp2s) -> if Deque.is_empty vp2s then None
                                else (Deque.drop_front vp2s; Some (VUntil (tp, vp1, vp2s)))
    | VUntilInf (tp, ltp, vp2s) -> if Deque.is_empty vp2s then None
                                   else (Deque.drop_front vp2s; Some (VUntilInf (tp, ltp, vp2s)))
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
    | SHistoricallyOut tp -> tp
    | SAlways (tp, _, _) -> tp
    | SSince (sp2, sp1s) -> if Deque.is_empty sp1s then s_at sp2
                            else s_at (Deque.peek_back_exn sp1s)
    | SUntil (sp2, sp1s) -> if Deque.is_empty sp1s then s_at sp2
                            else s_at (Deque.peek_front_exn sp1s)
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

  let p_at = function
    | S s_p -> s_at s_p
    | V v_p -> v_at v_p

  let s_ltp = function
    | SUntil (sp2, _) -> s_at sp2
    | _ -> raise (Invalid_argument "s_ltp is not defined for this sp")

  let v_etp = function
    | VUntil (tp, _, vp2s) -> if Deque.is_empty vp2s then tp
                              else v_at (Deque.peek_front_exn vp2s)
    | _ -> raise (Invalid_argument "v_etp is not defined for this vp")

  let cmp f p1 p2 = f p1 <= f p2

  let rec s_to_string indent p =
    let indent' = "\t" ^ indent in
    match p with
    | STT i -> Printf.sprintf "%strue{%d}" indent i
    | SPred (tp, r, trms) -> Printf.sprintf "%s%s{%d}{%s}" indent r tp (Term.list_to_string trms)
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
                              x (Domain.to_string d) (s_to_string indent' sp)
    | SForall (x, part) -> Printf.sprintf "%sSForall{%d}{%s}\n%s\n" indent (s_at (SForall (x, part)))
                             x (Part.to_string indent' s_to_string part)
    | SPrev sp -> Printf.sprintf "%sSPrev{%d}\n%s" indent (s_at p) (s_to_string indent' sp)
    | SNext sp -> Printf.sprintf "%sSNext{%d}\n%s" indent (s_at p) (s_to_string indent' sp)
    | SOnce (_, sp) -> Printf.sprintf "%sSOnce{%d}\n%s" indent (s_at p) (s_to_string indent' sp)
    | SEventually (_, sp) -> Printf.sprintf "%sSEventually{%d}\n%s" indent (s_at p)
                               (s_to_string indent' sp)
    | SHistorically (_, _, sps) -> Printf.sprintf "%sSHistorically{%d}\n%s" indent (s_at p)
                                     (Etc.deque_to_string indent' s_to_string sps)
    | SHistoricallyOut i -> Printf.sprintf "%sSHistoricallyOut{%d}" indent' i
    | SAlways (_, _, sps) -> Printf.sprintf "%sSAlways{%d}\n%s" indent (s_at p)
                               (Etc.deque_to_string indent' s_to_string sps)
    | SSince (sp2, sp1s) -> Printf.sprintf "%sSSince{%d}\n%s\n%s" indent (s_at p) (s_to_string indent' sp2)
                              (Etc.deque_to_string indent' s_to_string sp1s)
    | SUntil (sp2, sp1s) -> Printf.sprintf "%sSUntil{%d}\n%s\n%s" indent (s_at p)
                              (Etc.deque_to_string indent' s_to_string sp1s) (s_to_string indent' sp2)
  and v_to_string indent p =
    let indent' = "\t" ^ indent in
    match p with
    | VFF i -> Printf.sprintf "%sfalse{%d}" indent i
    | VPred (tp, r, trms) ->  Printf.sprintf "%s!%s{%d}{%s}" indent r tp (Term.list_to_string trms)
    | VNeg sp -> Printf.sprintf "%sVNeg{%d}\n%s" indent (v_at p) (s_to_string indent' sp)
    | VOr (vp1, vp2) -> Printf.sprintf "%sVOr{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vp1) (v_to_string indent' vp2)
    | VAndL vp1 -> Printf.sprintf "%sVAndL{%d}\n%s" indent (v_at p) (v_to_string indent' vp1)
    | VAndR vp2 -> Printf.sprintf "%sVAndR{%d}\n%s" indent (v_at p) (v_to_string indent' vp2)
    | VImp (sp1, vp2) -> Printf.sprintf "%sVImp{%d}\n%s\n%s" indent (v_at p) (s_to_string indent' sp1) (v_to_string indent' vp2)
    | VIffSV (sp1, vp2) -> Printf.sprintf "%sVIffSV{%d}\n%s\n%s" indent (v_at p) (s_to_string indent' sp1) (v_to_string indent' vp2)
    | VIffVS (vp1, sp2) -> Printf.sprintf "%sVIffVS{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vp1) (s_to_string indent' sp2)
    | VExists (x, part) -> Printf.sprintf "%sVExists{%d}{%s}\n%s\n" indent (v_at (VExists (x, part)))
                             x (Part.to_string indent' v_to_string part)
    | VForall (x, d, vp) -> Printf.sprintf "%sSExists{%d}{%s=%s}\n%s\n" indent (v_at p)
                              x (Domain.to_string d) (v_to_string indent' vp)
    | VPrev vp -> Printf.sprintf "%sVPrev{%d}\n%s" indent (v_at p) (v_to_string indent' vp)
    | VPrev0 -> Printf.sprintf "%sVPrev0{0}" indent'
    | VPrevOutL i -> Printf.sprintf "%sVPrevOutL{%d}" indent' i
    | VPrevOutR i -> Printf.sprintf "%sVPrevOutR{%d}" indent' i
    | VNext vp -> Printf.sprintf "%sVNext{%d}\n%s" indent (v_at p) (v_to_string indent' vp)
    | VNextOutL i -> Printf.sprintf "%sVNextOutL{%d}" indent' i
    | VNextOutR i -> Printf.sprintf "%sVNextOutR{%d}" indent' i
    | VOnceOut i -> Printf.sprintf "%sVOnceOut{%d}" indent' i
    | VOnce (_, _, vps) -> Printf.sprintf "%sVOnce{%d}\n%s" indent (v_at p)
                             (Etc.deque_to_string indent' v_to_string vps)
    | VEventually (_, _, vps) -> Printf.sprintf "%sVEventually{%d}\n%s" indent (v_at p)
                                   (Etc.deque_to_string indent' v_to_string vps)
    | VHistorically (_, vp) -> Printf.sprintf "%sVHistorically{%d}\n%s" indent (v_at p) (v_to_string indent' vp)
    | VAlways (_, vp) -> Printf.sprintf "%sVAlways{%d}\n%s" indent (v_at p) (v_to_string indent' vp)
    | VSinceOut i -> Printf.sprintf "%sVSinceOut{%d}" indent' i
    | VSince (_, vp1, vp2s) -> Printf.sprintf "%sVSince{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vp1)
                                 (Etc.deque_to_string indent' v_to_string vp2s)
    | VSinceInf (_, _, vp2s) -> Printf.sprintf "%sVSinceInf{%d}\n%s" indent (v_at p)
                                  (Etc.deque_to_string indent' v_to_string vp2s)
    | VUntil (_, vp1, vp2s) -> Printf.sprintf "%sVUntil{%d}\n%s\n%s" indent (v_at p)
                                 (Etc.deque_to_string indent' v_to_string vp2s) (v_to_string indent' vp1)
    | VUntilInf (_, _, vp2s) -> Printf.sprintf "%sVUntilInf{%d}\n%s" indent (v_at p)
                                  (Etc.deque_to_string indent' v_to_string vp2s)

  let to_string indent = function
    | S p -> s_to_string indent p
    | V p -> v_to_string indent p

  module Size = struct

    let sum f d = Deque.fold d ~init:0 ~f:(fun acc p -> acc + f p)

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
      | SForall (_, part) -> 1 + (Part.fold_left_snd part 0 (fun a sp -> a + s sp))
      | SPrev sp -> 1 + s sp
      | SNext sp -> 1 + s sp
      | SOnce (_, sp) -> 1 + s sp
      | SEventually (_, sp) -> 1 + s sp
      | SHistorically (_, _, sps) -> 1 + sum s sps
      | SHistoricallyOut _ -> 1
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
      | VExists (_, part) -> 1 + (Part.fold_left_snd part 0 (fun a vp -> a + v vp))
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

    let minp_bool = cmp p

    let minp x y = if p x <= p y then x else y

    let minp_list = function
      | [] -> raise (Invalid_argument "function not defined for empty lists")
      | x :: xs -> List.fold_left xs ~init:x ~f:minp

  end

end


type 'a pdt = Leaf of 'a | Node of Term.t * ('a pdt) Part.t

type t = Proof.t pdt

let rec at = function
  | Leaf pt -> Proof.p_at pt
  | Node (_, part) -> at (Part.hd part)

let rec apply1 vars f expl = match vars, expl with
  | _ , Leaf pt -> Leaf (f pt)
  | z :: vars, Node (x, part) ->
     if Term.equal x z then
       Node (x, Part.map part (apply1 vars f))
     else apply1 vars f (Node (x, part))
  | _ -> raise (Invalid_argument "variable list is empty")

let rec apply2 vars f expl1 expl2 = match vars, expl1, expl2 with
  | _ , Leaf pt1, Leaf pt2 -> Leaf (f pt1 pt2)
  | _ , Leaf pt1, Node (x, part2) -> Node (x, Part.map part2 (apply1 vars (f pt1)))
  | _ , Node (x, part1), Leaf pt2 -> Node (x, Part.map part1 (apply1 vars (fun pt1 -> f pt1 pt2)))
  | z :: vars, Node (x, part1), Node (y, part2) ->
     if Term.equal x z && Term.equal y z then
       Node (z, Part.merge2 (apply2 vars f) part1 part2)
     else (if Term.equal x z then
             Node (x, Part.map part1 (fun e1 -> apply2 vars f e1 (Node (y, part2))))
           else (if Term.equal y z then
                   Node (y, Part.map part2 (apply2 vars f (Node (x, part1))))
                 else apply2 vars f (Node (x, part1)) (Node (y, part2))))
  | _ -> raise (Invalid_argument "variable list is empty")

let rec apply3 vars f expl1 expl2 expl3 = match vars, expl1, expl2, expl3 with
  | _ , Leaf pt1, Leaf pt2, Leaf pt3 -> Leaf (f pt1 pt2 pt3)
  | _ , Leaf pt1, Leaf pt2, Node (x, part3) ->
     Node (x, Part.map part3 (apply2 vars (f pt1) (Leaf pt2)))
  | _ , Leaf pt1, Node (x, part2), Leaf pt3 ->
     Node (x, Part.map part2 (apply2 vars (fun pt2 -> f pt1 pt2) (Leaf pt3)))
  | _ , Node (x, part1), Leaf pt2, Leaf pt3 ->
     Node (x, Part.map part1 (apply2 vars (fun pt1 -> f pt1 pt2) (Leaf pt3)))
  | w :: vars, Leaf pt1, Node (y, part2), Node (z, part3) ->
     if Term.equal y w && Term.equal z w then
       Node (w, Part.merge2 (apply2 vars (f pt1)) part2 part3)
     else (if Term.equal y w then
             Node (y, Part.map part2 (fun expl2 -> apply2 vars (f pt1) expl2 (Node (z, part3))))
           else (if Term.equal z w then
                   Node (z, Part.map part3 (fun expl3 -> apply2 vars (f pt1) (Node (y, part2)) expl3))
                 else apply3 vars f (Leaf pt1) (Node (y, part2)) (Node(z, part3))))
  | w :: vars, Node (x, part1), Node (y, part2), Leaf pt3 ->
     if Term.equal x w && Term.equal y w then
       Node (w, Part.merge2 (apply2 vars (fun pt1 pt2 -> f pt1 pt2 pt3)) part1 part2)
     else (if Term.equal x w then
             Node (x, Part.map part1 (fun expl1 -> apply2 vars (fun pt1 pt2 -> f pt1 pt2 pt3) expl1 (Node (y, part2))))
           else (if Term.equal y w then
                   Node (y, Part.map part2 (fun expl2 -> apply2 vars (fun pt1 pt2 -> f pt1 pt2 pt3) (Node (x, part1)) expl2))
                 else apply3 vars f (Node (x, part1)) (Node (y, part2)) (Leaf pt3)))
  | w :: vars, Node (x, part1), Leaf pt2, Node (z, part3) ->
     if Term.equal x w && Term.equal z w then
       Node (w, Part.merge2 (apply2 vars (fun pt1 -> f pt1 pt2)) part1 part3)
     else (if Term.equal x w then
             Node (x, Part.map part1 (fun expl1 -> apply2 vars (fun pt1 -> f pt1 pt2) expl1 (Node (z, part3))))
           else (if Term.equal z w then
                   Node (z, Part.map part3 (fun expl3 -> apply2 vars (fun pt1 -> f pt1 pt2) (Node (x, part1)) expl3))
                 else apply3 vars f (Node (x, part1)) (Leaf pt2) (Node (z, part3))))
  | w :: vars, Node (x, part1), Node (y, part2), Node (z, part3) ->
     if Term.equal x w && Term.equal y w && Term.equal z w then
       Node (z, Part.merge3 (apply3 vars f) part1 part2 part3)
     else (if Term.equal x w && Term.equal y w then
             Node (w, Part.merge2 (apply3 vars (fun pt3 pt1 pt2 -> f pt1 pt2 pt3) (Node (z, part3))) part1 part2)
           else (if Term.equal x w && Term.equal z w then
                   Node (w, Part.merge2 (apply3 vars (fun pt2 pt1 pt3 -> f pt1 pt2 pt3) (Node (y, part2))) part1 part3)
                 else (if Term.equal y w && Term.equal z w then
                         Node (w, Part.merge2 (apply3 vars (fun pt1 -> f pt1) (Node (x, part1))) part2 part3)
                       else (if Term.equal x w then
                               Node (x, Part.map part1 (fun expl1 -> apply3 vars f expl1 (Node (y, part2)) (Node (z, part3))))
                             else (if Term.equal y w then
                                     Node (y, Part.map part2
                                                (fun expl2 -> apply3 vars f (Node (x, part1)) expl2 (Node (z, part3))))
                                   else (if Term.equal z w then
                                           Node (z, Part.map part3
                                                      (fun expl3 -> apply3 vars f (Node (x, part1)) (Node (y, part2)) expl3))
                                         else apply3 vars f (Node (x, part1)) (Node (y, part2)) (Node (z, part3))))))))
  | _ -> raise (Invalid_argument "variable list is empty")

let rec to_string indent = function
  | Leaf pt -> Printf.sprintf "%sLeaf (%s)\n%s" indent (Proof.to_string "" pt) indent
  | Node (x, part) -> Printf.sprintf "%sNode (%s,\n%s)\n" indent (Term.to_string x)
                        (Part.to_string "    " to_string part)
