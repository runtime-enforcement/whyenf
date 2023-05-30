(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Etc
open Expl

type period = PAST | FUTURE
type idx = int

module Pred = struct

  type cell = timepoint * idx * Db.t

  type row = (cell * (cell list)) list

  let preds_row tp db f =
    List.rev (List.foldi (Set.to_list (Formula.pred_names f)) ~init:[] ~f:(fun idx acc r ->
                  (tp, idx, Set.filter db ~f:(fun (r', _) -> String.equal r r')) :: acc))

end

module Subf = struct

  type cell = timepoint * idx * (Interval.t * period) option * bool option

  type row = (cell * (cell list)) list

  let cell_col = function
    | (_, col, _, _) -> col

  let rec cell_idx idx = function
    | Formula.TT | FF | Predicate _ -> idx
    | Neg f' | Exists (_, f') | Forall (_, f')
      | Prev (_, f') | Next (_, f')
      | Once (_, f') | Eventually (_, f')
      | Historically (_, f') | Always (_, f') -> cell_idx (idx+1) f'
    | And (f1, f2) | Or (f1, f2)
      | Imp (f1, f2) | Iff (f1, f2)
      | Since (_, f1, f2) | Until (_, f1, f2) -> let idx' = cell_idx (idx+1) f1 in
                                                 cell_idx (idx'+1) f2

  let rec cell_row tbl idx (f: Formula.t) (p: Proof.t) =
    match f, p with
    | TT, S (STT _) ->
       let cell = (Proof.p_at p, idx, None, Some(true)) in
       ((cell, []) :: tbl, idx)
    | Predicate _, S (SPred _) ->
       let cell = (Proof.p_at p, idx, None, Some(true)) in
       ((cell, []) :: tbl, idx)
    | Neg f', S (SNeg vp) ->
       let vp_idx = idx+1 in
       let (tbl', idx') = cell_row tbl vp_idx f' (V vp) in
       let cell = (Proof.p_at p, idx, None, Some(true)) in
       let cells = [(Proof.v_at vp, vp_idx, None, Some(false))] in
       ((cell, cells) :: tbl', idx')
    | Or (f1, _), S (SOrL sp1) ->
       let sp1_idx = idx+1 in
       let (tbl', idx') = cell_row tbl sp1_idx f1 (S sp1) in
       let cell = (Proof.p_at p, idx, None, Some(true)) in
       let cells = [(Proof.s_at sp1, sp1_idx, None, Some(true))] in
       ((cell, cells) :: tbl', idx')
    | Or (f1, f2), S (SOrR sp2) ->
       let sp1_idx = idx+1 in
       let sp2_idx = (cell_idx sp1_idx f1)+1 in
       let (tbl', idx') = cell_row tbl sp2_idx f2 (S sp2) in
       let cell = (Proof.p_at p, idx, None, Some(true)) in
       let cells = [(Proof.s_at sp2, sp2_idx, None, Some(true))] in
       ((cell, cells) :: tbl', idx')
    | And (f1, f2), S (SAnd (sp1, sp2)) ->
       let sp1_idx = idx+1 in
       let (tbl', idx') = cell_row tbl sp1_idx f1 (S sp1) in
       let sp2_idx = idx'+1 in
       let (tbl'', idx'') = cell_row tbl' sp2_idx f2 (S sp2) in
       let cell = (Proof.p_at p, idx, None, Some(true)) in
       let cells = [(Proof.s_at sp1, sp1_idx, None, Some(true)); (Proof.s_at sp2, sp2_idx, None, Some(true))] in
       ((cell, cells) :: tbl'', idx'')
    | Imp (f1, f2), S (SImpL (vp1)) ->
       let vp1_idx = idx+1 in
       let (tbl', idx') = cell_row tbl vp1_idx f1 (V vp1) in
       let cell = (Proof.p_at p, idx, None, Some(true)) in
       let cells = [(Proof.v_at vp1, vp1_idx, None, Some(false))] in
       ((cell, cells) :: tbl', idx')
    | Imp (f1, f2), S (SImpR (sp2)) ->
       let sp1_idx = idx+1 in
       let sp2_idx = (cell_idx sp1_idx f1)+1 in
       let (tbl', idx') = cell_row tbl sp2_idx f2 (S sp2) in
       let cell = (Proof.p_at p, idx, None, Some(true)) in
       let cells = [(Proof.s_at sp2, sp2_idx, None, Some(true))] in
       ((cell, cells) :: tbl', idx')
    | Iff (f1, f2), S (SIffSS (sp1, sp2)) ->
       let sp1_idx = idx+1 in
       let (tbl', idx') = cell_row tbl sp1_idx f1 (S sp1) in
       let sp2_idx = idx'+1 in
       let (tbl'', idx'') = cell_row tbl' sp2_idx f2 (S sp2) in
       let cell = (Proof.p_at p, idx, None, Some(true)) in
       let cells = [(Proof.s_at sp1, sp1_idx, None, Some(true)); (Proof.s_at sp2, sp2_idx, None, Some(true))] in
       ((cell, cells) :: tbl'', idx'')
    | Iff (f1, f2), S (SIffVV (vp1, vp2)) ->
       let vp1_idx = idx+1 in
       let (tbl', idx') = cell_row tbl vp1_idx f1 (V vp1) in
       let vp2_idx = idx'+1 in
       let (tbl'', idx'') = cell_row tbl' vp2_idx f2 (V vp2) in
       let cell = (Proof.p_at p, idx, None, Some(true)) in
       let cells = [(Proof.v_at vp1, vp1_idx, None, Some(false)); (Proof.v_at vp2, vp2_idx, None, Some(false))] in
       ((cell, cells) :: tbl'', idx'')
    | Exists (_, f'), S (SExists (_, _, sp)) ->
       let sp_idx = idx+1 in
       let (tbl', idx') = cell_row tbl sp_idx f' (S sp) in
       let cell = (Proof.p_at p, idx, None, None) in
       let cells = [(Proof.s_at sp, sp_idx, None, Some(true))] in
       ((cell, cells) :: tbl', idx')
    | Forall (_, f'), S (SForall (_, part)) ->
       let sps_idx = idx+1 in
       let (tbl', idx') = Part.fold_left part (tbl, sps_idx)
                            (fun (t, _) sp -> cell_row t sps_idx f' (S sp)) in
       let cell = (Proof.p_at p, idx, None, None) in
       let cells = Part.values (Part.map part (fun sp -> (Proof.s_at sp, sps_idx, None, Some(true)))) in
       ((cell, cells) :: tbl', idx')
    | Prev (i, f'), S (SPrev sp)
      | Once (i, f'), S (SOnce (_, sp))
      | Next (i, f'), S (SNext sp)
      | Eventually (i, f'), S (SEventually (_, sp)) ->
       let sp_idx = idx+1 in
       let (tbl', idx') = cell_row tbl sp_idx f' (S sp) in
       let cell = match f with Prev _
                             | Once _ -> (Proof.p_at p, idx, Some(i, PAST), Some(true))
                             | Next _
                               | Eventually _ -> (Proof.p_at p, idx, Some(i, FUTURE), Some(true))
                             | _ -> raise (Invalid_argument "unexpected proof constructor") in
       let cells = [(Proof.s_at sp, sp_idx, None, Some(true))] in
       ((cell, cells) :: tbl', idx')
    | Historically (i, f'), S (SHistorically (_, _, sps))
      | Always (i, f'), S (SAlways (_, _, sps)) ->
       let sps_idx = idx+1 in
       let (tbl', idx') = Fdeque.fold sps ~init:(tbl, sps_idx)
                            ~f:(fun (t, _) sp -> cell_row t sps_idx f' (S sp)) in
       let cell = match f with Historically _ -> (Proof.p_at p, idx, Some(i, PAST), Some(true))
                             | Always _ -> (Proof.p_at p, idx, Some(i, FUTURE), Some(true))
                             | _ -> raise (Invalid_argument "unexpected proof constructor") in
       let cells = Fdeque.to_list (Fdeque.map sps ~f:(fun sp -> (Proof.s_at sp, sps_idx, None, Some(true)))) in
       ((cell, cells) :: tbl', idx')
    | Since (i, f1, f2), S (SSince (sp2, sp1s))
      | Until (i, f1, f2), S (SUntil (sp2, sp1s)) when Fdeque.is_empty sp1s ->
       let sp1_idx = idx+1 in
       (* Recursive calls *)
       let sp2_idx = (cell_idx sp1_idx f1)+1 in
       let (tbl', idx') = cell_row tbl sp2_idx f2 (S sp2) in
       (* State update *)
       let cell = match f with Since _ -> (Proof.p_at p, idx, Some(i, PAST), Some(true))
                             | Until _ -> (Proof.p_at p, idx, Some(i, FUTURE), Some(true))
                             | _ -> raise (Invalid_argument "unexpected proof constructor") in
       let cells = [(Proof.s_at sp2, sp2_idx, None, Some(true))] in
       ((cell, cells) :: tbl', idx')
    | Since (i, f1, f2), S (SSince (sp2, sp1s))
      | Until (i, f1, f2), S (SUntil (sp2, sp1s)) ->
       let sp1_idx = idx+1 in
       (* Recursive calls *)
       let (tbl', idx') = Fdeque.fold sp1s ~init:(tbl, sp1_idx)
                            ~f:(fun (t, _) sp1 -> cell_row t sp1_idx f1 (S sp1)) in
       let sp2_idx = idx'+1 in
       let (tbl'', idx'') = cell_row tbl' sp2_idx f2 (S sp2) in
       (* State update *)
       let cell = match f with Since _ -> (Proof.p_at p, idx, Some(i, PAST), Some(true))
                             | Until _ -> (Proof.p_at p, idx, Some(i, FUTURE), Some(true))
                             | _ -> raise (Invalid_argument "unexpected proof constructor") in
       let cells = (Proof.s_at sp2, sp2_idx, None, Some(true)) ::
                     (Fdeque.to_list (Fdeque.map sp1s ~f:(fun sp1 -> (Proof.s_at sp1, sp1_idx, None, Some(true))))) in
       ((cell, cells) :: tbl'', idx'')
    | FF, V (VFF _) ->
       let cell = (Proof.p_at p, idx, None, Some(false)) in
       ((cell, []) :: tbl, idx)
    | Predicate _, V (VPred _) ->
       let cell = (Proof.p_at p, idx, None, Some(false)) in
       ((cell, []) :: tbl, idx)
    | Neg f', V (VNeg sp) ->
       let sp_idx = idx+1 in
       let (tbl', idx') = cell_row tbl sp_idx f' (S sp) in
       let cell = (Proof.p_at p, idx, None, Some(false)) in
       let cells = [(Proof.s_at sp, sp_idx, None, Some(true))] in
       ((cell, cells) :: tbl', idx')
    | Or (f1, f2), V (VOr (vp1, vp2)) ->
       let vp1_idx = idx+1 in
       let (tbl', idx') = cell_row tbl vp1_idx f1 (V vp1) in
       let vp2_idx = idx'+1 in
       let (tbl'', idx'') = cell_row tbl' vp2_idx f2 (V vp2) in
       let cell = (Proof.p_at p, idx, None, Some(false)) in
       let cells = [(Proof.v_at vp1, vp1_idx, None, Some(false)); (Proof.v_at vp2, vp2_idx, None, Some(false))] in
       ((cell, cells) :: tbl'', idx'')
    | And (f1, _), V (VAndL vp1) ->
       let vp1_idx = idx+1 in
       let (tbl', idx') = cell_row tbl vp1_idx f1 (V vp1) in
       let cell = (Proof.p_at p, idx, None, Some(false)) in
       let cells = [(Proof.v_at vp1, vp1_idx, None, Some(false))] in
       ((cell, cells) :: tbl', idx')
    | And (f1, f2), V (VAndR vp2) ->
       let vp1_idx = idx+1 in
       let vp2_idx = (cell_idx vp1_idx f1)+1 in
       let (tbl', idx') = cell_row tbl vp2_idx f2 (V vp2) in
       let cell = (Proof.p_at p, idx, None, Some(false)) in
       let cells = [(Proof.v_at vp2, vp2_idx, None, Some(false))] in
       ((cell, cells) :: tbl', idx')
    | Imp (f1, f2), V (VImp (sp1, vp2))
      | Iff (f1, f2), V (VIffSV (sp1, vp2)) ->
       let sp1_idx = idx+1 in
       let (tbl', idx') = cell_row tbl sp1_idx f1 (S sp1) in
       let vp2_idx = idx'+1 in
       let (tbl'', idx'') = cell_row tbl' vp2_idx f2 (V vp2) in
       let cell = (Proof.p_at p, idx, None, Some(false)) in
       let cells = [(Proof.s_at sp1, sp1_idx, None, Some(true)); (Proof.v_at vp2, vp2_idx, None, Some(false))] in
       ((cell, cells) :: tbl'', idx'')
    | Iff (f1, f2), V (VIffVS (vp1, sp2)) ->
       let vp1_idx = idx+1 in
       let (tbl', idx') = cell_row tbl vp1_idx f1 (V vp1) in
       let sp2_idx = idx'+1 in
       let (tbl'', idx'') = cell_row tbl' sp2_idx f2 (S sp2) in
       let cell = (Proof.p_at p, idx, None, Some(false)) in
       let cells = [(Proof.v_at vp1, vp1_idx, None, Some(false)); (Proof.s_at sp2, sp2_idx, None, Some(true))] in
       ((cell, cells) :: tbl'', idx'')
    | Exists (_, f'), V (VExists (_, part)) ->
       let vps_idx = idx+1 in
       let (tbl', idx') = Part.fold_left part (tbl, vps_idx)
                            (fun (t, _) vp -> cell_row t vps_idx f' (V vp)) in
       let cell = (Proof.p_at p, idx, None, None) in
       let cells = Part.values (Part.map part (fun vp -> (Proof.v_at vp, vps_idx, None, Some(false)))) in
       ((cell, cells) :: tbl', idx')
    | Forall (_, f'), V (VForall (_, _, vp)) ->
       let vp_idx = idx+1 in
       let (tbl', idx') = cell_row tbl vp_idx f' (V vp) in
       let cell = (Proof.p_at p, idx, None, None) in
       let cells = [(Proof.v_at vp, vp_idx, None, Some(false))] in
       ((cell, cells) :: tbl', idx')
    | Prev (i, f'), V (VPrev vp)
      | Historically (i, f'), V (VHistorically (_, vp))
      | Next (i, f'), V (VNext vp)
      | Always (i, f'), V (VAlways (_, vp)) ->
       let vp_idx = idx+1 in
       let (tbl', idx') = cell_row tbl vp_idx f' (V vp) in
       let cell = match f with Prev _
                             | Historically _ -> (Proof.p_at p, idx, Some(i, PAST), Some(false))
                             | Always _
                               | Next _ -> (Proof.p_at p, idx, Some(i, FUTURE), Some(false))
                             | _ -> raise (Invalid_argument "unexpected proof constructor") in
       let cells = [(Proof.v_at vp, vp_idx, None, Some(false))] in
       ((cell, cells) :: tbl', idx')
    | Once (i, f'), V (VOnce (_, _, vps))
      | Eventually (i, f'), V (VEventually (_, _, vps)) ->
       let vps_idx = idx+1 in
       let (tbl', idx') = Fdeque.fold vps ~init:(tbl, vps_idx)
                            ~f:(fun (t, _) vp -> cell_row t vps_idx f' (V vp)) in
       let cell = match f with Once _ -> (Proof.p_at p, idx, Some(i, PAST), Some(false))
                             | Eventually _ -> (Proof.p_at p, idx, Some(i, FUTURE), Some(false))
                             | _ -> raise (Invalid_argument "unexpected proof constructor") in
       let cells = Fdeque.to_list (Fdeque.map vps ~f:(fun vp -> (Proof.v_at vp, vps_idx, None, Some(false)))) in
       ((cell, cells) :: tbl', idx')
    | Since (i, f1, _), V (VSince (_, vp1, vp2s))
      | Until (i, f1, _), V (VUntil (_, vp1, vp2s)) when Fdeque.is_empty vp2s ->
       let vp1_idx = idx+1 in
       let (tbl', idx') = cell_row tbl vp1_idx f1 (V vp1) in
       let cell = match f with Since _ -> (Proof.p_at p, idx, Some(i, PAST), Some(false))
                             | Until _ -> (Proof.p_at p, idx, Some(i, FUTURE), Some(false))
                             | _ -> raise (Invalid_argument "unexpected proof constructor") in
       let cells = [(Proof.v_at vp1, vp1_idx, None, Some(false))] in
       ((cell, cells) :: tbl', idx')
    | Since (i, f1, f2), V (VSince (_, vp1, vp2s))
      | Until (i, f1, f2), V (VUntil (_, vp1, vp2s)) ->
       let vp1_idx = idx+1 in
       let (tbl', idx') = cell_row tbl vp1_idx f1 (V vp1) in
       let vp2_idx = idx'+1 in
       let (tbl'', idx'') = Fdeque.fold vp2s ~init:(tbl', vp2_idx)
                              ~f:(fun (t, _) vp2 -> cell_row t vp2_idx f2 (V vp2)) in
       let cell = match f with Since _ -> (Proof.p_at p, idx, Some(i, PAST), Some(false))
                             | Until _ -> (Proof.p_at p, idx, Some(i, FUTURE), Some(false))
                             | _ -> raise (Invalid_argument "unexpected proof constructor") in
       let cells = (Proof.v_at vp1, vp1_idx, None, Some(false)) ::
                     (Fdeque.to_list (Fdeque.map vp2s ~f:(fun vp2 -> (Proof.v_at vp2, vp2_idx, None, Some(false))))) in
       ((cell, cells) :: tbl'', idx'')
    | Since (i, f1, f2), V (VSinceInf (_, _, vp2s))
      | Until (i, f1, f2), V (VUntilInf (_, _, vp2s)) ->
       let vp1_idx = idx+1 in
       let vp2_idx = (cell_idx vp1_idx f1)+1 in
       let (tbl', idx') = Fdeque.fold vp2s ~init:(tbl, vp2_idx)
                            ~f:(fun (t, _) vp2 -> cell_row t vp2_idx f2 (V vp2)) in
       let cell = match f with Since _ -> (Proof.p_at p, idx, Some(i, PAST), Some(false))
                             | Until _ -> (Proof.p_at p, idx, Some(i, FUTURE), Some(false))
                             | _ -> raise (Invalid_argument "unexpected proof constructor") in
       let cells = Fdeque.to_list (Fdeque.map vp2s ~f:(fun vp2 -> (Proof.v_at vp2, vp2_idx, None, Some(false)))) in
       ((cell, cells) :: tbl', idx')
    | Historically (_, _), S (SHistoricallyOut _)
      | Once (_, _), V (VOnceOut _)
      | Prev (_, _), V VPrev0
      | Prev (_, _), V (VPrevOutL _)
      | Prev (_, _), V (VPrevOutR _)
      | Next (_, _), V (VNextOutL _)
      | Next (_, _), V (VNextOutR _)
      | Since (_, _, _), V (VSinceOut _) ->
       let cell = (Proof.p_at p, idx, None, Some(false)) in
       ((cell, []) :: tbl, idx)
    | _ -> raise (Invalid_argument "invalid formula/proof pair")


end
