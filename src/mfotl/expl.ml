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

type 'a part = Abs_part of ((Domain.t, Domain.comparator_witness) Coset.t * 'a) list

type sproof =
  | STT of int
  | SPred of int * string * Pred.Term.t list
  | SNeg of vproof
  | SOrL of sproof
  | SOrR of sproof
  | SAnd of sproof * sproof
  | SImpL of vproof
  | SImpR of sproof
  | SIffSS of sproof * sproof
  | SIffVV of vproof * vproof
  | SExists of string * Domain.t * sproof
  | SForall of string * (sproof part)
  | SPrev of sproof
  | SNext of sproof
  | SOnce of int * sproof
  | SEventually of int * sproof
  | SHistorically of int * int * sproof list
  | SHistoricallyOutL of int
  | SAlways of int * int * sproof list
  | SSince of sproof * sproof list
  | SUntil of sproof * sproof list
and vproof =
  | VFF of int
  | VPred of int * string * Pred.Term.t list
  | VNeg of sproof
  | VOr of vproof * vproof
  | VAndL of vproof
  | VAndR of vproof
  | VImp of sproof * vproof
  | VIffSV of sproof * vproof
  | VIffVS of vproof * sproof
  | VExists of string * (vproof part)
  | VForall of string * Domain.t * vproof
  | VPrev of vproof
  | VPrev0
  | VPrevOutL of int
  | VPrevOutR of int
  | VNext of vproof
  | VNextOutL of int
  | VNextOutR of int
  | VOnceOut of int
  | VOnce of int * int * vproof list
  | VEventually of int * int * vproof list
  | VHistorically of int * vproof
  | VAlways of int * vproof
  | VSinceOut of int
  | VSince of int * vproof * vproof list
  | VSinceInf of int * int * vproof list
  | VUntil of int * vproof * vproof list
  | VUntilInf of int * int * vproof list

type 'a pdt = Leaf of 'a | Node of string * ('a pdt) part

type proof = S of sproof | V of vproof

type expl = proof pdt

let the_part = function
  | Abs_part part -> part

let map_part part f = match part with
  | Abs_part part -> Abs_part (List.map part (fun (s, p) -> (s, f p)))

let rec merge_part2 f part1 part2 = match part1, part2 with
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
     Abs_part (part12 @ (the_part (merge_part2 f (Abs_part part1) (Abs_part part2not1))))

let rec apply_pdt1 vars f expl = match vars, expl with
  | vars, Leaf pt -> Leaf (f pt)
  | z :: vars, Node (x, part) ->
     if String.equal x z then
       Node (x, map_part part (apply_pdt1 vars f))
     else apply_pdt1 vars f (Node (x, part))
  | _ -> raise (Invalid_argument "variable list is empty")

let rec apply_pdt2 vars f expl1 expl2 = match vars, expl1, expl2 with
  | vars, Leaf pt1, Leaf pt2 -> Leaf (f pt1 pt2)
  | vars, Leaf pt1, Node (x, part2) ->
     Node (x, map_part part2 (apply_pdt1 vars (f pt1)))
  | vars, Node (x, part1), Leaf pt2 ->
     Node (x, map_part part1 (apply_pdt1 vars (fun pt1 -> f pt1 pt2)))
  | z :: vars, Node (x, part1), Node (y, part2) ->
     if String.equal x z && String.equal y z then
       Node (z, merge_part2 (apply_pdt2 vars f) part1 part2)
     else (if String.equal x z then
             Node (x, map_part part1 (fun e1 -> apply_pdt2 vars f e1 (Node (y, part2))))
           else (if String.equal y z then
                   Node (y, map_part part2 (apply_pdt2 vars f (Node (x, part1))))
                 else apply_pdt2 vars f (Node (x, part1)) (Node (y, part2))))
  | _ -> raise (Invalid_argument "variable list is empty")
