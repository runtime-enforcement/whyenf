(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Etc
open Expl
open Formula
open Checker.Whymon

module Fdeque = Core_kernel.Fdeque

let int_of_nat n = Z.to_int (integer_of_nat n)
let nat_of_int i = nat_of_integer (Z.of_int i)
let enat_of_integer i = Enat (nat_of_integer i)

module Checker_interface = struct

  type proof = (event_data sproof, event_data vproof) sum
  type trace = (string set * nat) list
  type trace_lst = (timestamp * (Db.Event.t, Db.Event.comparator_witness) Set.t) list

  let to_event_data (d: Domain.t) = match d with
    | Int v -> EInt (Z.of_int v)
    | Str v -> EString v
    | _ -> raise (Invalid_argument "type not supported yet")

  let of_event_data (ed: event_data) = match ed with
    | EInt v -> Domain.Int (Z.to_int v)
    | EString v -> Str v
    | _ -> raise (Invalid_argument "type not supported yet")

  let convert_term (t: Pred.Term.t) = match t with
    | Const c -> Const (to_event_data c)
    | Var x -> Var x

  (* fset: formalized sets (from Isabelle) *)
  let to_fset = function
    | Setc.Finite s -> Set (List.rev (Set.fold s ~init:[] ~f:(fun acc d -> (to_event_data d) :: acc)))
    | Setc.Complement s -> Coset (List.rev (Set.fold s ~init:[] ~f:(fun acc d -> (to_event_data d) :: acc)))

  let of_fset = function
    | Set s -> Setc.Finite (Set.of_list (module Domain)
                              (List.rev (List.fold s ~init:[] ~f:(fun acc ed -> (of_event_data ed) :: acc))))
    | Coset cs -> Setc.Complement (Set.of_list (module Domain)
                                     (List.rev (List.fold cs ~init:[] ~f:(fun acc ed -> (of_event_data ed) :: acc))))

  let of_poly_set = function
    | Set s -> List.rev (List.fold s ~init:[] ~f:(fun acc l -> l :: acc))
    | Coset cs -> List.rev (List.fold cs ~init:[] ~f:(fun acc l -> l :: acc))

  let rec convert_sp_part part =
    let part_lst = List.map part ~f:(fun (coset, sp) ->
                       (to_fset coset, convert_sp sp)) in
    abs_part (part_lst)
  and convert_vp_part part =
    let part_lst = List.map part ~f:(fun (coset, vp) ->
                       (to_fset coset, convert_vp vp)) in
    abs_part (part_lst)
  and convert_sp (sp: Proof.sp) : (event_data sproof) = match sp with
    | STT tp -> STT (nat_of_int tp)
    | SPred (tp, s, trms) -> SPred (nat_of_int tp, s, List.map trms convert_term)
    | SNeg vp1 -> SNeg (convert_vp vp1)
    | SOrL sp1 -> SOrL (convert_sp sp1)
    | SOrR sp2 -> SOrR (convert_sp sp2)
    | SAnd (sp1, sp2) -> SAnd (convert_sp sp1, convert_sp sp2)
    | SImpL vp1 -> SImpL (convert_vp vp1)
    | SImpR sp2 -> SImpR (convert_sp sp2)
    | SIffSS (sp1, sp2) -> SIffSS (convert_sp sp1, convert_sp sp2)
    | SIffVV (vp1, vp2) -> SIffVV (convert_vp vp1, convert_vp vp2)
    | SExists (x, d, sp) -> SExists (Pred.Term.unvar x, to_event_data d, convert_sp sp)
    | SForall (x, part) -> SForall (Pred.Term.unvar x, convert_sp_part part)
    | SPrev sp1 -> SPrev (convert_sp sp1)
    | SNext sp1 -> SNext (convert_sp sp1)
    | SOnce (tp, sp1) -> SOnce (nat_of_int tp, convert_sp sp1)
    | SHistorically (tp, etp, sp2s) ->
       let sp2s' = List.rev(Fdeque.fold sp2s ~init:[] ~f:(fun acc sp2 -> (convert_sp sp2)::acc)) in
       SHistorically (nat_of_int tp, nat_of_int etp, sp2s')
    | SHistoricallyOut tp -> SHistoricallyOut (nat_of_int tp)
    | SEventually (tp, sp1) -> SEventually (nat_of_int tp, convert_sp sp1)
    | SAlways (tp, ltp, sp2s) ->
       let sp2s' = List.rev(Fdeque.fold sp2s ~init:[] ~f:(fun acc sp2 -> (convert_sp sp2)::acc)) in
       SAlways (nat_of_int tp, nat_of_int ltp, sp2s')
    | SSince (sp2, sp1s) ->
       let sp1s' = List.rev(Fdeque.fold sp1s ~init:[] ~f:(fun acc sp1 -> (convert_sp sp1)::acc)) in
       SSince (convert_sp sp2, sp1s')
    | SUntil (sp2, sp1s) ->
       let sp1s' = List.rev(Fdeque.fold sp1s ~init:[] ~f:(fun acc sp1 -> (convert_sp sp1)::acc)) in
       SUntil (sp1s', convert_sp sp2)
  and convert_vp (vp: Proof.vp) : (event_data vproof) = match vp with
    | VFF tp -> VFF (nat_of_int tp)
    | VPred (tp, s, trms) -> VPred (nat_of_int tp, s, List.map trms convert_term)
    | VNeg sp1 -> VNeg (convert_sp sp1)
    | VOr (vp1, vp2) -> VOr (convert_vp vp1, convert_vp vp2)
    | VAndL vp1 -> VAndL (convert_vp vp1)
    | VAndR vp2 -> VAndR (convert_vp vp2)
    | VImp (sp1, vp2) -> VImp (convert_sp sp1, convert_vp vp2)
    | VIffSV (sp1, vp2) -> VIffSV (convert_sp sp1, convert_vp vp2)
    | VIffVS (vp1, sp2) -> VIffVS (convert_vp vp1, convert_sp sp2)
    | VExists (x, part) -> VExists (Pred.Term.unvar x, convert_vp_part part)
    | VForall (x, d, vp) -> VForall (Pred.Term.unvar x, to_event_data d, convert_vp vp)
    | VPrev vp1 -> VPrev (convert_vp vp1)
    | VPrev0 -> VPrevZ
    | VPrevOutL tp -> VPrevOutL (nat_of_int tp)
    | VPrevOutR tp -> VPrevOutR (nat_of_int tp)
    | VNext vp -> VNext (convert_vp vp)
    | VNextOutL tp -> VNextOutL (nat_of_int tp)
    | VNextOutR tp -> VNextOutR (nat_of_int tp)
    | VOnceOut tp -> VOnceOut (nat_of_int tp)
    | VOnce (tp, etp, vp1s) ->
       let vp1s' = List.rev(Fdeque.fold vp1s ~init:[] ~f:(fun acc vp1 -> (convert_vp vp1)::acc)) in
       VOnce (nat_of_int tp, nat_of_int etp, vp1s')
    | VHistorically (tp, vp1) -> VHistorically (nat_of_int tp, convert_vp vp1)
    | VEventually (tp, ltp, vp1s) ->
       let vp1s' = List.rev(Fdeque.fold vp1s ~init:[] ~f:(fun acc vp1 -> (convert_vp vp1)::acc)) in
       VEventually (nat_of_int tp, nat_of_int ltp, vp1s')
    | VAlways (tp, vp1) -> VAlways (nat_of_int tp, convert_vp vp1)
    | VSinceOut tp -> VSinceOut (nat_of_int tp)
    | VSince (tp, vp1, vp2s) ->
       let vp2s' = List.rev(Fdeque.fold vp2s ~init:[] ~f:(fun acc vp2 -> (convert_vp vp2)::acc)) in
       VSince (nat_of_int tp, convert_vp vp1, vp2s')
    | VSinceInf (tp, etp, vp2s) ->
       let vp2s' = List.rev(Fdeque.fold vp2s ~init:[] ~f:(fun acc vp2 -> (convert_vp vp2)::acc)) in
       VSinceInf (nat_of_int tp, nat_of_int etp, vp2s')
    | VUntil (tp, vp1, vp2s) ->
       let vp2s' = List.rev(Fdeque.fold vp2s ~init:[] ~f:(fun acc vp2 -> (convert_vp vp2)::acc)) in
       VUntil (nat_of_int tp, vp2s', convert_vp vp1)
    | VUntilInf (tp, ltp, vp2s) ->
       let vp2s' = List.rev(Fdeque.fold vp2s ~init:[] ~f:(fun acc vp2 -> (convert_vp vp2)::acc)) in
       VUntilInf (nat_of_int tp, nat_of_int ltp, vp2s')

  let rec convert_pdt_part part =
    let part_lst = List.map part ~f:(fun (coset, pdt) ->
                       (to_fset coset, convert_pdt pdt)) in
    abs_part (part_lst)
  and convert_pdt = function
    | Expl.Pdt.Leaf pt -> (match pt with
                       | Proof.S sp -> Leaf (Inl (convert_sp sp))
                       | V vp -> Leaf (Inr (convert_vp vp)))
    | Node (x, part) -> Node (Pred.Term.unvar x, convert_pdt_part part)

  let convert_p = function
    | Proof.S sp -> Inl (convert_sp sp)
    | V vp -> Inr (convert_vp vp)

  let rec convert_expl = function
    | Expl.Pdt.Leaf pt -> Leaf (convert_p pt)
    | Node (x, part) -> Node (Pred.Term.unvar x, convert_pdt_part part)

  let convert_interval = function
    | Interval.B bi -> (match bi with
                        | BI (l, r) -> interval (nat_of_int l) (Enat (nat_of_int r)))
    | U ui -> (match ui with
               | UI l -> interval (nat_of_int l) Infinity_enat)

  let rec convert_f = function
    | Formula.TT -> TT
    | FF -> FF
    | Predicate (x, trms) -> Pred (x, List.map trms ~f:convert_term)
    | Neg (f) -> Neg (convert_f f)
    | Or (f, g) -> Or (convert_f f, convert_f g)
    | And (f, g) -> And (convert_f f, convert_f g)
    | Imp (f, g) -> Imp (convert_f f, convert_f g)
    | Iff (f, g) -> Iff (convert_f f, convert_f g)
    | Exists (x, f) -> Exists (Pred.Term.unvar x, convert_f f)
    | Forall (x, f) -> Forall (Pred.Term.unvar x, convert_f f)
    | Prev (i, f) -> Prev (convert_interval i, convert_f f)
    | Next (i, f) -> Next (convert_interval i, convert_f f)
    | Once (i, f) -> Once (convert_interval i, convert_f f)
    | Eventually (i, f) -> Eventually (convert_interval i, convert_f f)
    | Historically (i, f) -> Historically (convert_interval i, convert_f f)
    | Always (i, f) -> Always (convert_interval i, convert_f f)
    | Since (i, f, g) -> Since (convert_f f, convert_interval i, convert_f g)
    | Until (i, f, g) -> Until (convert_f f, convert_interval i, convert_f g)

  let convert_db db =
    specialized_set (Set.fold db ~init:[] ~f:(fun acc (name, ds) ->
                         (name, List.map ds ~f:to_event_data)::acc))

  let convert_trace_aux trace_lst =
    List.rev(List.fold_left trace_lst ~init:[] ~f:(fun acc (ts, db) ->
                 (convert_db db, nat_of_int ts)::acc))

  let convert_trace trace_lst =
    trace_of_list_specialized (convert_trace_aux trace_lst)

end

module Checker_domain = struct

  let to_string = function
    | EString v -> v
    | EInt v -> Int.to_string (Z.to_int v)

  let list_to_string ds =
    String.drop_suffix (List.fold ds ~init:"" ~f:(fun acc d -> acc ^ (to_string d) ^ ", ")) 2

end

module Checker_term = struct

  let to_string = function
    | Var x -> Printf.sprintf "Var %s" x
    | Const d -> Printf.sprintf "Const %s" (Checker_domain.to_string d)

  let rec list_to_string trms =
    match trms with
    | [] -> ""
    | (Var x) :: trms -> if List.is_empty trms then x
                         else Printf.sprintf "%s, %s" x (list_to_string trms)
    | (Const d) :: trms -> if List.is_empty trms then (Checker_domain.to_string d)
                           else Printf.sprintf "%s, %s" (Checker_domain.to_string d) (list_to_string trms)

end

module Checker_set = struct

  let to_string cs =
    let rec format = function
      | [] -> ""
      | [x] -> Checker_domain.to_string x
      | x :: xs -> Printf.sprintf "%s, " (Checker_domain.to_string x) ^ (format xs) in
    match cs with
    | Set s -> Printf.sprintf "Set {%s}" (format s)
    | Coset s -> Printf.sprintf "Coset {%s}" (format s)

end

module Checker_part = struct

  let rec el_to_string indent f (sub, v) =
    Printf.sprintf "%sset = {%s}\n%s%s" indent (Checker_set.to_string sub) indent (f indent v)

  let to_string indent f = function
    | [] -> indent ^ "[]"
    | [x] -> indent ^ Etc.eat "[" ((el_to_string indent f x) ^ "]")
    | x :: xs ->
       List.fold_left ~f:(fun s el -> Etc.eat (s ^ "\n" ^ indent ^ "; ") (el_to_string indent f el))
         ~init:(indent ^ Etc.eat "[ " (el_to_string indent f x)) xs ^ " ]"

end

module Checker_proof = struct

  let rec sp_at = function
    | STT tp -> tp
    | SPred (tp, _, _) -> tp
    | SNeg vp -> vp_at vp
    | SOrL sp1 -> sp_at sp1
    | SOrR sp2 -> sp_at sp2
    | SAnd (sp1, _) -> sp_at sp1
    | SImpL vp1 -> vp_at vp1
    | SImpR sp2 -> sp_at sp2
    | SIffSS (sp1, _) -> sp_at sp1
    | SIffVV (vp1, _) -> vp_at vp1
    | SExists (_, _, sp) -> sp_at sp
    | SForall (_, part) -> sp_at (part_hd part)
    | SPrev sp -> sum_nat (sp_at sp) (nat_of_int 1)
    | SNext sp -> sub_nat (sp_at sp) (nat_of_int 1)
    | SOnce (tp, _) -> tp
    | SEventually (tp, _) -> tp
    | SHistorically (tp, _, _) -> tp
    | SHistoricallyOut tp -> tp
    | SAlways (tp, _, _) -> tp
    | SSince (sp2, sp1s) -> if List.is_empty sp1s then sp_at sp2
                            else sp_at (List.last_exn sp1s)
    | SUntil (sp1s, sp2) -> if List.is_empty sp1s then sp_at sp2
                            else sp_at (List.hd_exn sp1s)
  and vp_at = function
    | VFF tp -> tp
    | VPred (tp, _, _) -> tp
    | VNeg sp -> sp_at sp
    | VOr (vp1, _) -> vp_at vp1
    | VAndL vp1 -> vp_at vp1
    | VAndR vp2 -> vp_at vp2
    | VImp (sp1, _) -> sp_at sp1
    | VIffSV (sp1, _) -> sp_at sp1
    | VIffVS (vp1, _) -> vp_at vp1
    | VExists (_, part) -> vp_at (part_hd part)
    | VForall (_, _, vp) -> vp_at vp
    | VPrev vp -> sum_nat (vp_at vp) (nat_of_int 1)
    | VPrevZ -> (nat_of_int 0)
    | VPrevOutL tp -> tp
    | VPrevOutR tp -> tp
    | VNext vp -> sub_nat (vp_at vp) (nat_of_int 1)
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

  let rec sp_to_string indent p =
    let indent' = "\t" ^ indent in
    match p with
    | STT tp -> Printf.sprintf "%strue{%d}" indent (int_of_nat tp)
    | SPred (tp, r, trms) -> Printf.sprintf "%sSPred(%d, %s, %s)" indent (int_of_nat tp) r (Checker_term.list_to_string trms)
    | SNeg vp -> Printf.sprintf "%sSNeg{%d}\n%s" indent (int_of_nat (sp_at p)) (vp_to_string indent' vp)
    | SOrL sp1 -> Printf.sprintf "%sSOrL{%d}\n%s" indent (int_of_nat (sp_at p)) (sp_to_string indent' sp1)
    | SOrR sp2 -> Printf.sprintf "%sSOrR{%d}\n%s" indent (int_of_nat (sp_at p)) (sp_to_string indent' sp2)
    | SAnd (sp1, sp2) -> Printf.sprintf "%sSAnd{%d}\n%s\n%s" indent (int_of_nat (sp_at p))
                           (sp_to_string indent' sp1) (sp_to_string indent' sp2)
    | SImpL vp1 -> Printf.sprintf "%sSImpL{%d}\n%s" indent (int_of_nat (sp_at p)) (vp_to_string indent' vp1)
    | SImpR sp2 -> Printf.sprintf "%sSImpR{%d}\n%s" indent (int_of_nat (sp_at p)) (sp_to_string indent' sp2)
    | SIffSS (sp1, sp2) -> Printf.sprintf "%sSIffSS{%d}\n%s\n%s" indent (int_of_nat (sp_at p))
                             (sp_to_string indent' sp1) (sp_to_string indent' sp2)
    | SIffVV (vp1, vp2) -> Printf.sprintf "%sSIffVV{%d}\n%s\n%s" indent (int_of_nat (sp_at p))
                             (vp_to_string indent' vp1) (vp_to_string indent' vp2)
    | SExists (x, d, sp) -> Printf.sprintf "%sSExists{%d}{%s=%s}\n%s\n" indent (int_of_nat (sp_at p))
                              x (Checker_domain.to_string d) (sp_to_string indent' sp)
    | SForall (x, part) -> Printf.sprintf "%sSForall{%d}{%s}\n%s\n" indent (int_of_nat (sp_at (part_hd part)))
                             x (Checker_part.to_string indent' sp_to_string (subsvals part))
    | SPrev sp -> Printf.sprintf "%sSPrev{%d}\n%s" indent (int_of_nat (sp_at p)) (sp_to_string indent' sp)
    | SNext sp -> Printf.sprintf "%sSNext{%d}\n%s" indent (int_of_nat (sp_at p)) (sp_to_string indent' sp)
    | SOnce (_, sp) -> Printf.sprintf "%sSOnce{%d}\n%s" indent (int_of_nat (sp_at p)) (sp_to_string indent' sp)
    | SEventually (_, sp) -> Printf.sprintf "%sSEventually{%d}\n%s" indent (int_of_nat (sp_at p))
                               (sp_to_string indent' sp)
    | SHistorically (_, _, sps) -> Printf.sprintf "%sSHistorically{%d}\n%s" indent (int_of_nat (sp_at p))
                                     (Etc.list_to_string indent' sp_to_string sps)
    | SHistoricallyOut tp -> Printf.sprintf "%sSHistoricallyOut{%d}" indent' (int_of_nat tp)
    | SAlways (_, _, sps) -> Printf.sprintf "%sSAlways{%d}\n%s" indent (int_of_nat (sp_at p))
                               (Etc.list_to_string indent' sp_to_string sps)
    | SSince (sp2, sp1s) -> Printf.sprintf "%sSSince{%d}\n%s\n%s" indent (int_of_nat (sp_at p)) (sp_to_string indent' sp2)
                              (Etc.list_to_string indent' sp_to_string sp1s)
    | SUntil (sp1s, sp2) -> Printf.sprintf "%sSUntil{%d}\n%s\n%s" indent (int_of_nat (sp_at p))
                              (Etc.list_to_string indent' sp_to_string sp1s) (sp_to_string indent' sp2)
  and vp_to_string indent p =
    let indent' = "\t" ^ indent in
    match p with
    | VFF tp -> Printf.sprintf "%sfalse{%d}" indent (int_of_nat tp)
    | VPred (tp, r, trms) -> Printf.sprintf "%sVPred(%d, %s, %s)" indent (int_of_nat tp) r (Checker_term.list_to_string trms)
    | VNeg sp -> Printf.sprintf "%sVNeg{%d}\n%s" indent (int_of_nat (vp_at p)) (sp_to_string indent' sp)
    | VOr (vp1, vp2) -> Printf.sprintf "%sVOr{%d}\n%s\n%s" indent (int_of_nat (vp_at p)) (vp_to_string indent' vp1) (vp_to_string indent' vp2)
    | VAndL vp1 -> Printf.sprintf "%sVAndL{%d}\n%s" indent (int_of_nat (vp_at p)) (vp_to_string indent' vp1)
    | VAndR vp2 -> Printf.sprintf "%sVAndR{%d}\n%s" indent (int_of_nat (vp_at p)) (vp_to_string indent' vp2)
    | VImp (sp1, vp2) -> Printf.sprintf "%sVImp{%d}\n%s\n%s" indent (int_of_nat (vp_at p)) (sp_to_string indent' sp1) (vp_to_string indent' vp2)
    | VIffSV (sp1, vp2) -> Printf.sprintf "%sVIffSV{%d}\n%s\n%s" indent (int_of_nat (vp_at p)) (sp_to_string indent' sp1) (vp_to_string indent' vp2)
    | VIffVS (vp1, sp2) -> Printf.sprintf "%sVIffVS{%d}\n%s\n%s" indent (int_of_nat (vp_at p)) (vp_to_string indent' vp1) (sp_to_string indent' sp2)
    | VExists (x, part) -> Printf.sprintf "%sVExists{%d}{%s}\n%s\n" indent (int_of_nat (vp_at (part_hd part)))
                             x (Checker_part.to_string indent' vp_to_string (subsvals part))
    | VForall (x, d, vp) -> Printf.sprintf "%sSExists{%d}{%s=%s}\n%s\n" indent (int_of_nat (vp_at p))
                              x (Checker_domain.to_string d) (vp_to_string indent' vp)
    | VPrev vp -> Printf.sprintf "%sVPrev{%d}\n%s" indent (int_of_nat (vp_at p)) (vp_to_string indent' vp)
    | VPrevZ -> Printf.sprintf "%sVPrevZ{0}" indent'
    | VPrevOutL tp -> Printf.sprintf "%sVPrevOutL{%d}" indent' (int_of_nat tp)
    | VPrevOutR tp -> Printf.sprintf "%sVPrevOutR{%d}" indent' (int_of_nat tp)
    | VNext vp -> Printf.sprintf "%sVNext{%d}\n%s" indent (int_of_nat (vp_at p)) (vp_to_string indent' vp)
    | VNextOutL tp -> Printf.sprintf "%sVNextOutL{%d}" indent' (int_of_nat tp)
    | VNextOutR tp -> Printf.sprintf "%sVNextOutR{%d}" indent' (int_of_nat tp)
    | VOnceOut tp -> Printf.sprintf "%sVOnceOut{%d}" indent' (int_of_nat tp)
    | VOnce (_, _, vps) -> Printf.sprintf "%sVOnce{%d}\n%s" indent (int_of_nat (vp_at p))
                             (Etc.list_to_string indent' vp_to_string vps)
    | VEventually (_, _, vps) -> Printf.sprintf "%sVEventually{%d}\n%s" indent (int_of_nat (vp_at p))
                                   (Etc.list_to_string indent' vp_to_string vps)
    | VHistorically (_, vp) -> Printf.sprintf "%sVHistorically{%d}\n%s" indent (int_of_nat (vp_at p)) (vp_to_string indent' vp)
    | VAlways (_, vp) -> Printf.sprintf "%sVAlways{%d}\n%s" indent (int_of_nat (vp_at p)) (vp_to_string indent' vp)
    | VSinceOut tp -> Printf.sprintf "%sVSinceOut{%d}" indent' (int_of_nat tp)
    | VSince (_, vp1, vp2s) -> Printf.sprintf "%sVSince{%d}\n%s\n%s" indent (int_of_nat (vp_at p)) (vp_to_string indent' vp1)
                                 (Etc.list_to_string indent' vp_to_string vp2s)
    | VSinceInf (_, _, vp2s) -> Printf.sprintf "%sVSinceInf{%d}\n%s" indent (int_of_nat (vp_at p))
                                  (Etc.list_to_string indent' vp_to_string vp2s)
    | VUntil (_, vp2s, vp1) -> Printf.sprintf "%sVUntil{%d}\n%s\n%s" indent (int_of_nat (vp_at p))
                                 (Etc.list_to_string indent' vp_to_string vp2s) (vp_to_string indent' vp1)
    | VUntilInf (_, _, vp2s) -> Printf.sprintf "%sVUntilInf{%d}\n%s" indent (int_of_nat (vp_at p))
                                  (Etc.list_to_string indent' vp_to_string vp2s)

  let to_string indent = function
    | Inl p -> sp_to_string indent p
    | Inr p -> vp_to_string indent p

end

module Checker_trace = struct

  type t = ((string * event_data list) set * nat) list

  let evt_to_string (name, ds) =
    Printf.sprintf "[debug] %s(%s)" name (Checker_domain.list_to_string ds)

  let db_to_string db =
    List.fold db ~init:"" ~f:(fun acc evt -> acc ^ evt_to_string evt ^ "\n")

  let to_string trace_lst = List.fold_left trace_lst ~init:"" ~f:(fun acc (db, ts) ->
                                acc ^ Printf.sprintf "[debug] TS = %d:\n" (int_of_nat ts) ^
                                  (match db with
                                   | Set s -> db_to_string s
                                   | Coset _ -> raise (Failure "set of dbs should not be converted to coset")) ^ "\n")

end

module Checker_pdt = struct

  type t = (event_data, (event_data sproof, event_data vproof) sum) pdt

  let rec to_string indent = function
    | Leaf pt -> Printf.sprintf "%s Leaf (%s)\n%s" indent (Checker_proof.to_string "" pt) indent
    | Node (x, part) -> Printf.sprintf "%s Node (%s,\n%s)\n" indent x
                          (Checker_part.to_string "    " to_string (subsvals part))

end

let check trace_lst f expls =
  let f' = Checker_interface.convert_f f in
  let trace_lst' = Checker_interface.convert_trace_aux trace_lst in
  let trace' = Checker_interface.convert_trace trace_lst in
  List.fold_left expls ~init:[] ~f:(fun acc expl ->
      let expl' = Checker_interface.convert_expl expl in
      (check_all_specialized trace' f' expl', expl', trace_lst')::acc)

let false_paths trace_lst f expls =
  let f' = Checker_interface.convert_f f in
  let trace_lst' = Checker_interface.convert_trace_aux trace_lst in
  let trace' = Checker_interface.convert_trace trace_lst in
  List.fold_left expls ~init:[] ~f:(fun acc expl ->
      let expl' = Checker_interface.convert_expl expl in
      let paths = collect_paths_specialized trace' f' expl' in
      match paths with
      | None -> None::acc
      | Some ps -> Some(List.map (Checker_interface.of_poly_set ps) ~f:(fun l ->
                            List.map l (fun l' -> Checker_interface.of_fset l')))::acc)
