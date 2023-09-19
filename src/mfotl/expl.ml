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

module Fdeque = Core_kernel.Fdeque

module Part = struct

  (* TODO: Remove concrete type from signature file                *)
  (*       In order to do this, I must rewrite do_exists/do_forall *)
  type 'a t = ((Domain.t, Domain.comparator_witness) Setc.t * 'a) list

  let random_empty_set = Set.empty (module String)

  let trivial p = [(Setc.univ (module Domain), p)]

  let hd part = snd (List.hd_exn part)

  let map part f = List.map part ~f:(fun (s, p) -> (s, f p))

  let fold_left part init f = List.fold_left part ~init:init ~f:(fun acc (_, p) -> f acc p)

  let filter part f = List.filter part ~f:(fun (_, p) -> f p)

  let exists part f = List.exists part ~f:(fun (_, p) -> f p)

  let for_all part f = List.for_all part ~f:(fun (_, p) -> f p)

  let values part = List.map part ~f:(fun (_, p) -> p)

  let rec tabulate ds f z =
    (Setc.Complement ds, z) ::
      (Set.fold ds ~init:[] ~f:(fun acc d -> (Setc.Finite (Set.of_list (module Domain) [d]), f d) :: acc))

  let rec merge2 f part1 part2 = match part1, part2 with
    | [], _ -> []
    | (sub1, v1) :: part1, part2 ->
       let part12 = List.filter_map part2
                      (fun (sub2, v2) ->
                        (if not (Setc.is_empty (Setc.inter sub1 sub2))
                         then Some (Setc.inter sub1 sub2, f v1 v2) else None)) in
       let part2not1 = List.filter_map part2
                         (fun (sub2, v2) ->
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
    | SExists of Term.t * Domain.t * sp
    | SForall of Term.t * (sp Part.t)
    | SPrev of sp
    | SNext of sp
    | SOnce of int * sp
    | SEventually of int * sp
    | SHistorically of int * int * sp Fdeque.t
    | SHistoricallyOut of int
    | SAlways of int * int * sp Fdeque.t
    | SSince of sp * sp Fdeque.t
    | SUntil of sp * sp Fdeque.t
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
    | VExists of Term.t * (vp Part.t)
    | VForall of Term.t * Domain.t * vp
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

  (* TODO: Rewrite this with Either *)
  type t = S of sp | V of vp

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
                              (Term.value_to_string x) (Domain.to_string d) (s_to_string indent' sp)
    | SForall (x, part) -> Printf.sprintf "%sSForall{%d}{%s}\n%s\n" indent (s_at (SForall (x, part)))
                             (Term.value_to_string x) (Part.to_string indent' x s_to_string part)
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
    | VPred (tp, r, trms) -> Printf.sprintf "%sVPred(%d, %s, %s)" indent tp r (Term.list_to_string trms)
    | VNeg sp -> Printf.sprintf "%sVNeg{%d}\n%s" indent (v_at p) (s_to_string indent' sp)
    | VOr (vp1, vp2) -> Printf.sprintf "%sVOr{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vp1) (v_to_string indent' vp2)
    | VAndL vp1 -> Printf.sprintf "%sVAndL{%d}\n%s" indent (v_at p) (v_to_string indent' vp1)
    | VAndR vp2 -> Printf.sprintf "%sVAndR{%d}\n%s" indent (v_at p) (v_to_string indent' vp2)
    | VImp (sp1, vp2) -> Printf.sprintf "%sVImp{%d}\n%s\n%s" indent (v_at p) (s_to_string indent' sp1) (v_to_string indent' vp2)
    | VIffSV (sp1, vp2) -> Printf.sprintf "%sVIffSV{%d}\n%s\n%s" indent (v_at p) (s_to_string indent' sp1) (v_to_string indent' vp2)
    | VIffVS (vp1, sp2) -> Printf.sprintf "%sVIffVS{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vp1) (s_to_string indent' sp2)
    | VExists (x, part) -> Printf.sprintf "%sVExists{%d}{%s}\n%s\n" indent (v_at (VExists (x, part)))
                             (Term.value_to_string x) (Part.to_string indent' x v_to_string part)
    | VForall (x, d, vp) -> Printf.sprintf "%sVForall{%d}{%s=%s}\n%s\n" indent (v_at p)
                              (Term.value_to_string x) (Domain.to_string d) (v_to_string indent' vp)
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

  let val_changes_to_latex v =
    if List.is_empty v then "v"
    else "v[" ^ Etc.string_list_to_string (List.map v ~f:(fun (x, d) -> Printf.sprintf "%s \\mapsto %s" x d)) ^ "]"

  let rec s_to_latex indent v idx p (h: Formula.t) =
    let indent' = "\t" ^ indent in
    match p, h with
    | STT tp, TT  ->
       Printf.sprintf "\\infer[\\top]{%s, %d \\pvd true}{}\n" (val_changes_to_latex v) tp
    | SPred (tp, r, trms), Predicate (_, _) ->
       Printf.sprintf "\\infer[\\Spred]{%s, %d \\pvd %s\\,(%s)}{(%s,[%s]) \\in\\Gamma_{%d}}\n"
         (val_changes_to_latex v) tp (Etc.escape_underscores r) (Term.list_to_string trms)
         (Etc.escape_underscores r) (Term.list_to_string trms) tp
    | SNeg vp, Neg f ->
       Printf.sprintf "\\infer[\\Sneg]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (v_to_latex indent' v idx vp f)
    | SOrL sp1, Or (f, g) ->
       Printf.sprintf "\\infer[\\Sdisjl]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (s_to_latex indent' v idx sp1 f)
    | SOrR sp2, Or (f, g) ->
       Printf.sprintf "\\infer[\\Sdisjr]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (s_to_latex indent' v idx sp2 g)
    | SAnd (sp1, sp2), And (f, g) ->
       Printf.sprintf "\\infer[\\Sconj]{%s, %d \\pvd %s}\n%s{%s & %s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h)
         indent (s_to_latex indent' v idx sp1 f) (s_to_latex indent' v idx sp2 g)
    | SImpL vp1, Imp (f, g) ->
       Printf.sprintf "\\infer[\\SimpL]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (v_to_latex indent' v idx vp1 f)
    | SImpR sp2, Imp (f, g) ->
       Printf.sprintf "\\infer[\\SimpR]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (s_to_latex indent' v idx sp2 g)
    | SIffSS (sp1, sp2), Iff (f, g) ->
       Printf.sprintf "\\infer[\\SiffSS]{%s, %d \\pvd %s}\n%s{%s & %s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h)
         indent (s_to_latex indent' v idx sp1 f) (s_to_latex indent' v idx sp2 g)
    | SIffVV (vp1, vp2), Iff (f, g) ->
       Printf.sprintf "\\infer[\\SiffVV]{%s, %d \\pvd %s}\n%s{%s & %s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h)
         indent (v_to_latex indent' v idx vp1 f) (v_to_latex indent' v idx vp2 g)
    | SExists (x, d, sp), Exists (Var y, f) ->
       let v' = v @ [(Term.value_to_string x, Domain.to_string d)] in
       Printf.sprintf "\\infer[\\Sexists]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (s_to_latex indent' v' idx sp f)
    | SForall (x, part), Forall (_, f) ->
       Printf.sprintf "\\infer[\\Sforall]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent
         (String.concat ~sep:"&" (List.map part ~f:(fun (sub, sp) ->
                                      let idx' = idx + 1 in
                                      let v' = v @ [(Term.value_to_string x, "d_" ^ (Int.to_string idx') ^ " \\in " ^ (Setc.to_latex sub))] in
                                      "{" ^ (s_to_latex indent' v' idx' sp f) ^ "}")))
    | SPrev sp, Prev (i, f) ->
       Printf.sprintf "\\infer[\\Sprev{}]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (s_to_latex indent' v idx sp f)
    | SNext sp, Next (i, f) ->
       Printf.sprintf "\\infer[\\Snext{}]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (s_to_latex indent' v idx sp f)
    | SOnce (tp, sp), Once (i, f) ->
       Printf.sprintf "\\infer[\\Sonce{}]{%s, %d \\pvd %s}\n%s{%d \\leq %d & \\tau_%d - \\tau_%d \\in %s & {%s}}\n"
         (val_changes_to_latex v) tp (Formula.to_latex h) indent
         (s_at sp) tp tp (s_at sp) (Interval.to_latex i) (s_to_latex indent' v idx sp f)
    | SEventually (tp, sp), Eventually (i, f) ->
       Printf.sprintf "\\infer[\\Seventually{}]{%s, %d \\pvd %s}\n%s{%d \\geq %d & \\tau_%d - \\tau_%d \\in %s & {%s}}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent
         (s_at sp) tp (s_at sp) tp (Interval.to_latex i) (s_to_latex indent' v idx sp f)
    | SHistorically (tp, _, sps), Historically (i, f) ->
       Printf.sprintf "\\infer[\\Shistorically{}]{%s, %d \\pvd %s}\n%s{\\tau_%d - \\tau_0 \\geq %d & {%s}}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent tp (Interval.left i)
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map sps ~f:(fun sp -> "{" ^ (s_to_latex indent' v idx sp f) ^ "}"))))
    | SHistoricallyOut _, Historically (i, f) ->
       Printf.sprintf "\\infer[\\ShistoricallyL{}]{%s, %d \\pvd %s}\n%s{\\tau_%d - \\tau_0 < %d}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent (s_at p) (Interval.left i)
    | SAlways (_, _, sps), Always (i, f) ->
       Printf.sprintf "\\infer[\\Salways{}]{%s, %d \\pvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map sps ~f:(fun sp -> "{" ^ (s_to_latex indent' v idx sp f) ^ "}"))))
    | SSince (sp2, sp1s), Since (i, f, g) ->
       Printf.sprintf "\\infer[\\Ssince{}]{%s, %d \\pvd %s}\n%s{%d \\leq %d & \\tau_%d - \\tau_%d \\in %s & {%s} & %s}\n"
         (val_changes_to_latex v) (s_at p) (Formula.to_latex h) indent
         (s_at sp2) (s_at p) (s_at p) (s_at sp2) (Interval.to_latex i) (s_to_latex indent' v idx sp2 g)
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map sp1s ~f:(fun sp -> "{" ^ (s_to_latex indent' v idx sp f) ^ "}"))))
    | SUntil (sp2, sp1s), Until (i, f, g) ->
       Printf.sprintf "\\infer[\\Suntil{}]{%s, %d \\pvd %s}\n%s{%d \\leq %d & \\tau_%d - \\tau_%d \\in %s & %s & {%s}}\n"
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
    | VPred (tp, r, trms), Predicate (_, _) ->
       Printf.sprintf "\\infer[\\Vpred]{%s, %d \\nvd %s\\,(%s)}{(%s,[%s]) \\notin\\Gamma_{%d}}\n"
         (val_changes_to_latex v) tp (Etc.escape_underscores r) (Term.list_to_string trms)
         (Etc.escape_underscores r) (Term.list_to_string trms) tp
    | VNeg sp, Neg f ->
       Printf.sprintf "\\infer[\\Vneg]{%s, %d \\nvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent (s_to_latex indent' v idx sp f)
    | VOr (vp1, vp2), Or (f, g) ->
       Printf.sprintf "\\infer[\\Vdisj]{%s, %d \\nvd %s}\n%s{%s & %s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h)
         indent (v_to_latex indent' v idx vp1 f) (v_to_latex indent' v idx vp2 g)
    | VAndL vp1, And (f, _) ->
       Printf.sprintf "\\infer[\\Vconjl]{%s, %d \\nvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent (v_to_latex indent' v idx vp1 f)
    | VAndR vp2, And (_, g) ->
       Printf.sprintf "\\infer[\\Vconjr]{%s, %d \\nvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent (v_to_latex indent' v idx vp2 g)
    | VImp (sp1, vp2), Imp (f, g) ->
       Printf.sprintf "\\infer[\\Vimp]{%s, %d \\nvd %s}\n%s{%s & %s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h)
         indent (s_to_latex indent' v idx sp1 f) (v_to_latex indent' v idx vp2 g)
    | VIffSV (sp1, vp2), Iff (f, g) ->
       Printf.sprintf "\\infer[\\ViffSV]{%s, %d \\nvd %s}\n%s{%s & %s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h)
         indent (s_to_latex indent' v idx sp1 f) (v_to_latex indent' v idx vp2 g)
    | VIffVS (vp1, sp2), Iff (f, g) ->
       Printf.sprintf "\\infer[\\ViffSV]{%s, %d \\nvd %s}\n%s{%s & %s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h)
         indent (v_to_latex indent' v idx vp1 f) (s_to_latex indent' v idx sp2 g)
    | VExists (x, part), Exists (_, f) ->
       Printf.sprintf "\\infer[\\Vexists]{%s, %d \\nvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent
         (String.concat ~sep:"&" (List.map part ~f:(fun (sub, vp) ->
                                      let idx' = idx + 1 in
                                      let v' = v @ [(Term.value_to_string x, "d_" ^ (Int.to_string idx') ^ " \\in " ^ (Setc.to_latex sub))] in
                                      "{" ^ (v_to_latex indent' v' idx' vp f) ^ "}")))
    | VForall (x, d, vp), Forall (_, f) ->
       let v' = v @ [(Term.value_to_string x, Domain.to_string d)] in
       Printf.sprintf "\\infer[\\Vforall]{%s, %d \\nvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent (v_to_latex indent' v' idx vp f)
    | VPrev vp, Prev (i, f) ->
       Printf.sprintf "\\infer[\\Vprev{}]{%s, %d \\nvd %s}\n%s{%d > 0 & %s}\n"
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
       Printf.sprintf "\\infer[\\Vonce{}]{%s, %d \\nvd %s}\n%s{\\tau_%d - \\tau_0 \\geq %d & {%s}}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent (v_at p) (Interval.left i)
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map vps ~f:(fun vp -> "{" ^ (v_to_latex indent' v idx vp f) ^ "}"))))
    | VEventually (_, _, vps), Eventually (i, f) ->
       Printf.sprintf "\\infer[\\Veventually{}]{%s, %d \\nvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map vps ~f:(fun vp -> "{" ^ (v_to_latex indent' v idx vp f) ^ "}"))))
    | VHistorically (tp, vp), Historically (i, f) ->
       Printf.sprintf "\\infer[\\Vhistorically{}]{%s, %d \\nvd %s}\n%s{%d \\leq %d & \\tau_%d - \\tau_%d \\in %s & %s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent
         (v_at vp) tp tp (v_at vp) (Interval.to_latex i) (v_to_latex indent' v idx vp f)
    | VAlways (tp, vp), Always (i, f) ->
       Printf.sprintf "\\infer[\\Valways{}]{%s, %d \\nvd %s}\n%s{%d \\geq %d & \\tau_%d - \\tau_%d \\in %s & %s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent
         (v_at vp) tp (v_at vp) tp (Interval.to_latex i) (v_to_latex indent' v idx vp f)
    | VSinceOut tp, Since (i, f, g) ->
       Printf.sprintf "\\infer[\\Vsincel{}]{%s, %d \\nvd %s}\n%s{\\tau_%d - \\tau_0 < %d}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent (v_at p) (Interval.left i)
    | VSince (tp, vp1, vp2s), Since (i, f, g) ->
       Printf.sprintf "\\infer[\\Vsince{}]{%s, %d \\nvd %s}\n%s{%d \\leq %d & \\tau_%d - \\tau_0 \\geq %d & {%s} & %s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent
         (v_at vp1) tp tp (Interval.left i) (v_to_latex indent' v idx vp1 f)
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map vp2s ~f:(fun vp -> "{" ^ (v_to_latex indent' v idx vp g) ^ "}"))))
    | VSinceInf (tp, _, vp2s), Since (i, f, g) ->
       Printf.sprintf "\\infer[\\Vsinceinf{}]{%s, %d \\nvd %s}\n%s{\\tau_%d - \\tau_0 \\geq %d & %s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent tp (Interval.left i)
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map vp2s ~f:(fun vp -> "{" ^ (v_to_latex indent' v idx vp g) ^ "}"))))
    | VUntil (tp, vp1, vp2s), Until (i, f, g) ->
       Printf.sprintf "\\infer[\\Vuntil{}]{%s, %d \\nvd %s}\n%s{%d \\leq %d & %s & {%s}}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent tp (v_at vp1)
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map vp2s ~f:(fun vp -> "{" ^ (v_to_latex indent' v idx vp g) ^ "}"))))
         (v_to_latex indent' v idx vp1 f)
    | VUntilInf (_, _, vp2s), Until (i, f, g) ->
       Printf.sprintf "\\infer[\\Vuntil{}]{%s, %d \\nvd %s}\n%s{%s}\n"
         (val_changes_to_latex v) (v_at p) (Formula.to_latex h) indent
         (String.concat ~sep:"&" (Fdeque.to_list (Fdeque.map vp2s ~f:(fun vp -> "{" ^ (v_to_latex indent' v idx vp g) ^ "}"))))
    | _ -> ""

  let to_latex indent fmla = function
    | S p -> s_to_latex indent [] 0 p fmla
    | V p -> v_to_latex indent [] 0 p fmla

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

    let minp_bool = cmp p

    let minp x y = if p x <= p y then x else y

    let minp_list = function
      | [] -> raise (Invalid_argument "function not defined for empty lists")
      | x :: xs -> List.fold_left xs ~init:x ~f:minp

  end

end

module Pdt = struct

  type 'a t = Leaf of 'a | Node of Term.t * ('a t) Part.t

  let rec apply1 vars f pdt = match vars, pdt with
    | _ , Leaf l -> Leaf (f l)
    | z :: vars, Node (x, part) ->
       if Term.equal x z then
         Node (x, Part.map part (apply1 vars f))
       else apply1 vars f (Node (x, part))
    | _ -> raise (Invalid_argument "variable list is empty")

  let rec apply2 vars f pdt1 pdt2 = match vars, pdt1, pdt2 with
    | _ , Leaf l1, Leaf l2 -> Leaf (f l1 l2)
    | _ , Leaf l1, Node (x, part2) -> Node (x, Part.map part2 (apply1 vars (f l1)))
    | _ , Node (x, part1), Leaf l2 -> Node (x, Part.map part1 (apply1 vars (fun l1 -> f l1 l2)))
    | z :: vars, Node (x, part1), Node (y, part2) ->
       if Term.equal x z && Term.equal y z then
         Node (z, Part.merge2 (apply2 vars f) part1 part2)
       else (if Term.equal x z then
               Node (x, Part.map part1 (fun pdt1 -> apply2 vars f pdt1 (Node (y, part2))))
             else (if Term.equal y z then
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
       if Term.equal y w && Term.equal z w then
         Node (w, Part.merge2 (apply2 vars (f l1)) part2 part3)
       else (if Term.equal y w then
               Node (y, Part.map part2 (fun pdt2 -> apply2 vars (f l1) pdt2 (Node (z, part3))))
             else (if Term.equal z w then
                     Node (z, Part.map part3 (fun pdt3 -> apply2 vars (f l1) (Node (y, part2)) pdt3))
                   else apply3 vars f (Leaf l1) (Node (y, part2)) (Node(z, part3))))
    | w :: vars, Node (x, part1), Node (y, part2), Leaf l3 ->
       if Term.equal x w && Term.equal y w then
         Node (w, Part.merge2 (apply2 vars (fun l1 l2 -> f l1 l2 l3)) part1 part2)
       else (if Term.equal x w then
               Node (x, Part.map part1 (fun pdt1 -> apply2 vars (fun pt1 pt2 -> f pt1 pt2 l3) pdt1 (Node (y, part2))))
             else (if Term.equal y w then
                     Node (y, Part.map part2 (fun pdt2 -> apply2 vars (fun l1 l2 -> f l1 l2 l3) (Node (x, part1)) pdt2))
                   else apply3 vars f (Node (x, part1)) (Node (y, part2)) (Leaf l3)))
    | w :: vars, Node (x, part1), Leaf l2, Node (z, part3) ->
       if Term.equal x w && Term.equal z w then
         Node (w, Part.merge2 (apply2 vars (fun l1 -> f l1 l2)) part1 part3)
       else (if Term.equal x w then
               Node (x, Part.map part1 (fun pdt1 -> apply2 vars (fun l1 -> f l1 l2) pdt1 (Node (z, part3))))
             else (if Term.equal z w then
                     Node (z, Part.map part3 (fun pdt3 -> apply2 vars (fun l1 -> f l1 l2) (Node (x, part1)) pdt3))
                   else apply3 vars f (Node (x, part1)) (Leaf l2) (Node (z, part3))))
    | w :: vars, Node (x, part1), Node (y, part2), Node (z, part3) ->
       if Term.equal x w && Term.equal y w && Term.equal z w then
         Node (z, Part.merge3 (apply3 vars f) part1 part2 part3)
       else (if Term.equal x w && Term.equal y w then
               Node (w, Part.merge2 (fun pdt1 pdt2 -> apply3 vars f pdt1 pdt2 (Node (z, part3))) part1 part2)
             else (if Term.equal x w && Term.equal z w then
                     Node (w, Part.merge2 (fun pdt1 pdt3 -> apply3 vars f pdt1 (Node (y, part2)) pdt3) part1 part3)
                   else (if Term.equal y w && Term.equal z w then
                           Node (w, Part.merge2 (apply3 vars (fun l1 -> f l1) (Node (x, part1))) part2 part3)
                         else (if Term.equal x w then
                                 Node (x, Part.map part1 (fun pdt1 -> apply3 vars f pdt1 (Node (y, part2)) (Node (z, part3))))
                               else (if Term.equal y w then
                                       Node (y, Part.map part2 (fun pdt2 -> apply3 vars f (Node (x, part1)) pdt2 (Node (z, part3))))
                                     else (if Term.equal z w then
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
    | Node (x, part) -> (Part.to_string indent x (to_string f) part)

  let rec to_latex f indent = function
    | Leaf pt -> Printf.sprintf "%s%s\n" indent (f pt)
    | Node (x, part) -> (Part.to_string indent x (to_latex f) part)

  let unleaf = function
    | Leaf l -> l
    | _ -> raise (Invalid_argument "function not defined for nodes")

  let rec hide vars f pdt =
    match vars, pdt with
    |  _ , Leaf l -> Leaf (f (Either.First l))
    | [x], Node (y, part) -> Leaf (f (Either.Second (Part.map part unleaf)))
    | x :: vars, Node (y, part) -> if Term.equal x y then
                                     Node (y, Part.map part (hide vars f))
                                   else hide vars f (Node (y, part))
    | _ -> raise (Invalid_argument "function not defined for other cases")

end

type t = Proof.t Pdt.t

let rec at = function
  | Pdt.Leaf pt -> Proof.p_at pt
  | Node (_, part) -> at (Part.hd part)

let to_string expl = Pdt.to_string (Proof.to_string "") "" expl

let to_latex fmla expl = Pdt.to_latex (Proof.to_latex "" fmla) "" expl
