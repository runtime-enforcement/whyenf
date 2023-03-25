(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2022:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Formula
open Expl
open Util
open Interval

module List = Base.List

type idx = int
type period = PAST | FUTURE
type cell = timepoint * idx * (interval * period) option * bool
type table = (cell * (cell list)) list

exception UNEXPECTED_FORMULA of string
exception UNEXPECTED_PAIR of string

let cell_col cell = match cell with
  | (_, col, _, _) -> col

let rec f_idx idx f =
  match f with
  | TT | FF | P _ -> idx
  | Neg f' | Prev (_, f') | Next (_, f')
  | Once (_, f') | Historically (_, f')
  | Eventually (_, f') | Always (_, f') -> f_idx (idx+1) f'
  | Conj (f1, f2) | Disj (f1, f2)
  | Imp (f1, f2) | Iff (f1, f2)
  | Since (_, f1, f2) | Until (_, f1, f2) -> let idx' = f_idx (idx+1) f1 in
                                             f_idx (idx'+1) f2

let rec update_atoms_table tbl idx f sap tp atoms =
  match f with
  | TT | FF -> (tbl, idx, atoms)
  | P s -> let b = SS.mem s sap in
           let cell = (tp, idx, None, b) in
           if (List.exists atoms ~f:(fun s' -> s = s')) then (tbl, idx, atoms)
           else ((cell, []) :: tbl, idx+1, s :: atoms)
  | Neg f' | Prev (_, f') | Next (_, f')
  | Once (_, f') | Historically (_, f')
  | Eventually (_, f') | Always (_, f') -> update_atoms_table tbl idx f' sap tp atoms
  | Conj (f1, f2) | Disj (f1, f2)
  | Imp (f1, f2) | Iff (f1, f2)
  | Since (_, f1, f2)
  | Until (_, f1, f2) -> let (tbl', idx', atoms') = update_atoms_table tbl idx f1 sap tp atoms in
                         update_atoms_table tbl' idx' f2 sap tp atoms'

let rec update_expl_table tbl idx f p =
  match f, p with
  | TT, S (STT i) ->
     let cell = (p_at p, idx, None, true) in
     ((cell, []) :: tbl, idx)
  | P s1, S (SAtom (i, s2)) ->
     let cell = (p_at p, idx, None, true) in
     ((cell, []) :: tbl, idx)
  | Neg f', S (SNeg vp) ->
     let vp_idx = idx+1 in
     let (tbl', idx') = update_expl_table tbl vp_idx f' (V vp) in
     let cell = (p_at p, idx, None, true) in
     let cells = [(v_at vp, vp_idx, None, false)] in
     ((cell, cells) :: tbl', idx')
  | Disj (f1, _), S (SDisjL sp1) ->
     let sp1_idx = idx+1 in
     let (tbl', idx') = update_expl_table tbl sp1_idx f1 (S sp1) in
     let cell = (p_at p, idx, None, true) in
     let cells = [(s_at sp1, sp1_idx, None, true)] in
     ((cell, cells) :: tbl', idx')
  | Disj (f1, f2), S (SDisjR sp2) ->
     let sp1_idx = idx+1 in
     let sp2_idx = (f_idx sp1_idx f1)+1 in
     let (tbl', idx') = update_expl_table tbl sp2_idx f2 (S sp2) in
     let cell = (p_at p, idx, None, true) in
     let cells = [(s_at sp2, sp2_idx, None, true)] in
     ((cell, cells) :: tbl', idx')
  | Conj (f1, f2), S (SConj (sp1, sp2)) ->
     let sp1_idx = idx+1 in
     let (tbl', idx') = update_expl_table tbl sp1_idx f1 (S sp1) in
     let sp2_idx = idx'+1 in
     let (tbl'', idx'') = update_expl_table tbl' sp2_idx f2 (S sp2) in
     let cell = (p_at p, idx, None, true) in
     let cells = [(s_at sp1, sp1_idx, None, true); (s_at sp2, sp2_idx, None, true)] in
     ((cell, cells) :: tbl'', idx'')
  | Imp (f1, f2), S (SImplL (vp1)) ->
     let vp1_idx = idx+1 in
     let (tbl', idx') = update_expl_table tbl vp1_idx f1 (V vp1) in
     let cell = (p_at p, idx, None, true) in
     let cells = [(v_at vp1, vp1_idx, None, false)] in
     ((cell, cells) :: tbl', idx')
  | Imp (f1, f2), S (SImplR (sp2)) ->
     let sp1_idx = idx+1 in
     let sp2_idx = (f_idx sp1_idx f1)+1 in
     let (tbl', idx') = update_expl_table tbl sp2_idx f2 (S sp2) in
     let cell = (p_at p, idx, None, true) in
     let cells = [(s_at sp2, sp2_idx, None, true)] in
     ((cell, cells) :: tbl', idx')
  | Iff (f1, f2), S (SIffSS (sp1, sp2)) ->
     let sp1_idx = idx+1 in
     let (tbl', idx') = update_expl_table tbl sp1_idx f1 (S sp1) in
     let sp2_idx = idx'+1 in
     let (tbl'', idx'') = update_expl_table tbl' sp2_idx f2 (S sp2) in
     let cell = (p_at p, idx, None, true) in
     let cells = [(s_at sp1, sp1_idx, None, true); (s_at sp2, sp2_idx, None, true)] in
     ((cell, cells) :: tbl'', idx'')
  | Iff (f1, f2), S (SIffVV (vp1, vp2)) ->
     let vp1_idx = idx+1 in
     let (tbl', idx') = update_expl_table tbl vp1_idx f1 (V vp1) in
     let vp2_idx = idx'+1 in
     let (tbl'', idx'') = update_expl_table tbl' vp2_idx f2 (V vp2) in
     let cell = (p_at p, idx, None, true) in
     let cells = [(v_at vp1, vp1_idx, None, false); (v_at vp2, vp2_idx, None, false)] in
     ((cell, cells) :: tbl'', idx'')
  | Prev (i, f'), S (SPrev sp)
  | Once (i, f'), S (SOnce (_, sp))
  | Next (i, f'), S (SNext sp)
  | Eventually (i, f'), S (SEventually (_, sp)) ->
     let sp_idx = idx+1 in
     let (tbl', idx') = update_expl_table tbl sp_idx f' (S sp) in
     let cell = match f with Prev _
                           | Once _ -> (p_at p, idx, Some(i, PAST), true)
                           | Next _
                           | Eventually _ -> (p_at p, idx, Some(i, FUTURE), true)
                           | _ -> raise (UNEXPECTED_FORMULA "Formula must be either Next or Prev") in
     let cells = [(s_at sp, sp_idx, None, true)] in
     ((cell, cells) :: tbl', idx')
  | Historically (i, f'), S (SHistorically (_, _, sps))
  | Always (i, f'), S (SAlways (_, _, sps)) ->
     let sps_idx = idx+1 in
     let (tbl', idx') = List.fold sps ~init:(tbl, sps_idx)
                          ~f:(fun (t, _) sp -> update_expl_table t sps_idx f' (S sp)) in
     let cell = match f with Historically _ -> (p_at p, idx, Some(i, PAST), true)
                           | Always _ -> (p_at p, idx, Some(i, FUTURE), true)
                           | _ -> raise (UNEXPECTED_FORMULA "Formula must be either Historically or Always") in
     let cells = List.map sps ~f:(fun sp -> (s_at sp, sps_idx, None, true)) in
     ((cell, cells) :: tbl', idx')
  | Since (i, f1, f2), S (SSince (sp2, []))
  | Until (i, f1, f2), S (SUntil (sp2, [])) ->
     let sp1_idx = idx+1 in
     (* Recursive calls *)
     let sp2_idx = (f_idx sp1_idx f1)+1 in
     let (tbl', idx') = update_expl_table tbl sp2_idx f2 (S sp2) in
     (* State update *)
     let cell = match f with Since _ -> (p_at p, idx, Some(i, PAST), true)
                           | Until _ -> (p_at p, idx, Some(i, FUTURE), true)
                           | _ -> raise (UNEXPECTED_FORMULA "Formula must be either Since or Until") in
     let cells = [(s_at sp2, sp2_idx, None, true)] in
     ((cell, cells) :: tbl', idx')
  | Since (i, f1, f2), S (SSince (sp2, sp1s))
  | Until (i, f1, f2), S (SUntil (sp2, sp1s)) ->
     let sp1_idx = idx+1 in
     (* Recursive calls *)
     let (tbl', idx') = List.fold sp1s ~init:(tbl, sp1_idx)
                          ~f:(fun (t, _) sp1 -> update_expl_table t sp1_idx f1 (S sp1)) in
     let sp2_idx = idx'+1 in
     let (tbl'', idx'') = update_expl_table tbl' sp2_idx f2 (S sp2) in
     (* State update *)
     let cell = match f with Since _ -> (p_at p, idx, Some(i, PAST), true)
                           | Until _ -> (p_at p, idx, Some(i, FUTURE), true)
                           | _ -> raise (UNEXPECTED_FORMULA "Formula must be either Since or Until") in
     let cells = (s_at sp2, sp2_idx, None, true) ::
                   (List.map sp1s ~f:(fun sp1 -> (s_at sp1, sp1_idx, None, true))) in
     ((cell, cells) :: tbl'', idx'')
  | FF, V (VFF i) ->
     let cell = (p_at p, idx, None, false) in
     ((cell, []) :: tbl, idx)
  | P s1, V (VAtom (i, s2)) ->
     let cell = (p_at p, idx, None, false) in
     ((cell, []) :: tbl, idx)
  | Neg f', V (VNeg sp) ->
     let sp_idx = idx+1 in
     let (tbl', idx') = update_expl_table tbl sp_idx f' (S sp) in
     let cell = (p_at p, idx, None, false) in
     let cells = [(s_at sp, sp_idx, None, true)] in
     ((cell, cells) :: tbl', idx')
  | Disj (f1, f2), V (VDisj (vp1, vp2)) ->
     let vp1_idx = idx+1 in
     let (tbl', idx') = update_expl_table tbl vp1_idx f1 (V vp1) in
     let vp2_idx = idx'+1 in
     let (tbl'', idx'') = update_expl_table tbl' vp2_idx f2 (V vp2) in
     let cell = (p_at p, idx, None, false) in
     let cells = [(v_at vp1, vp1_idx, None, false); (v_at vp2, vp2_idx, None, false)] in
     ((cell, cells) :: tbl'', idx'')
  | Conj (f1, _), V (VConjL vp1) ->
     let vp1_idx = idx+1 in
     let (tbl', idx') = update_expl_table tbl vp1_idx f1 (V vp1) in
     let cell = (p_at p, idx, None, false) in
     let cells = [(v_at vp1, vp1_idx, None, false)] in
     ((cell, cells) :: tbl', idx')
  | Conj (f1, f2), V (VConjR vp2) ->
     let vp1_idx = idx+1 in
     let vp2_idx = (f_idx vp1_idx f1)+1 in
     let (tbl', idx') = update_expl_table tbl vp2_idx f2 (V vp2) in
     let cell = (p_at p, idx, None, false) in
     let cells = [(v_at vp2, vp2_idx, None, false)] in
     ((cell, cells) :: tbl', idx')
  | Imp (f1, f2), V (VImpl (sp1, vp2))
  | Iff (f1, f2), V (VIffSV (sp1, vp2)) ->
     let sp1_idx = idx+1 in
     let (tbl', idx') = update_expl_table tbl sp1_idx f1 (S sp1) in
     let vp2_idx = idx'+1 in
     let (tbl'', idx'') = update_expl_table tbl' vp2_idx f2 (V vp2) in
     let cell = (p_at p, idx, None, false) in
     let cells = [(s_at sp1, sp1_idx, None, true); (v_at vp2, vp2_idx, None, false)] in
     ((cell, cells) :: tbl'', idx'')
  | Iff (f1, f2), V (VIffVS (vp1, sp2)) ->
     let vp1_idx = idx+1 in
     let (tbl', idx') = update_expl_table tbl vp1_idx f1 (V vp1) in
     let sp2_idx = idx'+1 in
     let (tbl'', idx'') = update_expl_table tbl' sp2_idx f2 (S sp2) in
     let cell = (p_at p, idx, None, false) in
     let cells = [(v_at vp1, vp1_idx, None, false); (s_at sp2, sp2_idx, None, true)] in
     ((cell, cells) :: tbl'', idx'')
  | Prev (i, f'), V (VPrev vp)
  | Historically (i, f'), V (VHistorically (_, vp))
  | Next (i, f'), V (VNext vp)
  | Always (i, f'), V (VAlways (_, vp)) ->
     let vp_idx = idx+1 in
     let (tbl', idx') = update_expl_table tbl vp_idx f' (V vp) in
     let cell = match f with Prev _
                           | Historically _ -> (p_at p, idx, Some(i, PAST), false)
                           | Always _
                           | Next _ -> (p_at p, idx, Some(i, FUTURE), false)
                           | _ -> raise (UNEXPECTED_FORMULA "Formula must be either Next or Prev") in
     let cells = [(v_at vp, vp_idx, None, false)] in
     ((cell, cells) :: tbl', idx')
  | Once (i, f'), V (VOnce (_, _, vps))
  | Eventually (i, f'), V (VEventually (_, _, vps)) ->
     let vps_idx = idx+1 in
     let (tbl', idx') = List.fold vps ~init:(tbl, vps_idx)
                          ~f:(fun (t, _) vp -> update_expl_table t vps_idx f' (V vp)) in
     let cell = match f with Once _ -> (p_at p, idx, Some(i, PAST), false)
                           | Eventually _ -> (p_at p, idx, Some(i, FUTURE), false)
                           | _ -> raise (UNEXPECTED_FORMULA "Formula must be either Historically or Always") in
     let cells = List.map vps ~f:(fun vp -> (v_at vp, vps_idx, None, false)) in
     ((cell, cells) :: tbl', idx')
  | Since (i, f1, _), V (VSince (_, vp1, []))
  | Until (i, f1, _), V (VUntil (_, vp1, [])) ->
     let vp1_idx = idx+1 in
     let (tbl', idx') = update_expl_table tbl vp1_idx f1 (V vp1) in
     let cell = match f with Since _ -> (p_at p, idx, Some(i, PAST), false)
                           | Until _ -> (p_at p, idx, Some(i, FUTURE), false)
                           | _ -> raise (UNEXPECTED_FORMULA "Formula must be either Since or Until") in
     let cells = [(v_at vp1, vp1_idx, None, false)] in
     ((cell, cells) :: tbl', idx')
  | Since (i, f1, f2), V (VSince (_, vp1, vp2s))
  | Until (i, f1, f2), V (VUntil (_, vp1, vp2s)) ->
     let vp1_idx = idx+1 in
     let (tbl', idx') = update_expl_table tbl vp1_idx f1 (V vp1) in
     let vp2_idx = idx'+1 in
     let (tbl'', idx'') = List.fold vp2s ~init:(tbl', vp2_idx)
                            ~f:(fun (t, _) vp2 -> update_expl_table t vp2_idx f2 (V vp2)) in
     let cell = match f with Since _ -> (p_at p, idx, Some(i, PAST), false)
                           | Until _ -> (p_at p, idx, Some(i, FUTURE), false)
                           | _ -> raise (UNEXPECTED_FORMULA "Formula must be either Since or Until") in
     let cells = (v_at vp1, vp1_idx, None, false) ::
                   (List.map vp2s ~f:(fun vp2 -> (v_at vp2, vp2_idx, None, false))) in
     ((cell, cells) :: tbl'', idx'')
  | Since (i, f1, f2), V (VSinceInf (_, _, vp2s))
  | Until (i, f1, f2), V (VUntilInf (_, _, vp2s)) ->
     let vp1_idx = idx+1 in
     let vp2_idx = (f_idx vp1_idx f1)+1 in
     let (tbl', idx') = List.fold vp2s ~init:(tbl, vp2_idx)
                          ~f:(fun (t, _) vp2 -> update_expl_table t vp2_idx f2 (V vp2)) in
     let cell = match f with Since _ -> (p_at p, idx, Some(i, PAST), false)
                           | Until _ -> (p_at p, idx, Some(i, FUTURE), false)
                           | _ -> raise (UNEXPECTED_FORMULA "Formula must be either Since or Until") in
     let cells = List.map vp2s ~f:(fun vp2 -> (v_at vp2, vp2_idx, None, false)) in
     ((cell, cells) :: tbl', idx')
  | Historically (_, _), S (SHistoricallyOutL _)
  | Once (_, _), V (VOnceOutL _)
  | Prev (_, _), V VPrev0
  | Prev (_, _), V (VPrevOutL _)
  | Prev (_, _), V (VPrevOutR _)
  | Next (_, _), V (VNextOutL _)
  | Next (_, _), V (VNextOutR _)
  | Since (_, _, _), V (VSinceOutL _) ->
     let cell = (p_at p, idx, None, false) in
     ((cell, []) :: tbl, idx)
  | _ -> raise (UNEXPECTED_PAIR "Explanator2 can't handle this pair of formula/proof.")

let cell_to_json (tp, col, i_opt, b) cells =
  let ident = "    " in
  let ident2 = "    " ^ ident in
  let ident3 = "    " ^ ident2 in
  let ident4 = "    " ^ ident3 in
  (Printf.sprintf "%s{\n" ident2) ^
  (Printf.sprintf "%s\"tp\": %d,\n" ident3 tp) ^
  (Printf.sprintf "%s\"col\": %d,\n" ident3 col) ^
  (if Option.is_none i_opt then ""
   else (let (i, p) = Option.get i_opt in
         Printf.sprintf "%s\"interval\": \"%s\",\n" ident3 (interval_to_string i) ^
         (match p with
          | PAST -> Printf.sprintf "%s\"period\": \"past\",\n" ident3
          | FUTURE -> Printf.sprintf "%s\"period\": \"future\",\n" ident3))) ^
  (Printf.sprintf "%s\"bool\": %B,\n" ident3 b) ^
  (Printf.sprintf "%s\"cells\":" ident3) ^
    (if List.is_empty cells then " []"
     else ((Printf.sprintf " [\n") ^
           (String.concat ",\n" (List.map cells ~f:(fun (tp', col', _, b') ->
                                     (Printf.sprintf "%s{\n" ident3) ^
                                     (Printf.sprintf "%s\"tp\": %d,\n" ident4 tp') ^
                                     (Printf.sprintf "%s\"col\": %d,\n" ident4 col') ^
                                     (Printf.sprintf "%s\"bool\": %B\n" ident4 b') ^
                                     (Printf.sprintf "%s}" ident3))))) ^
           (Printf.sprintf "]\n")) ^
   (Printf.sprintf "\n%s}" ident2)

let atoms_to_json f sap tp =
  let (tbl, _, _) = update_atoms_table [] 0 f sap tp [] in
  let ident = "    " in
  let ident2 = "    " ^ ident in
  (Printf.sprintf "%s\"aps\": [\n" ident2) ^
  (String.concat ",\n" (List.map tbl ~f:(fun (cell, cells) -> cell_to_json cell cells))) ^
  (Printf.sprintf "]")

let expl_to_json f p =
  (* (Printf.printf "f = %s\n" (formula_to_string f));
   * (Printf.printf "p = %s\n" (expl_to_string p)); *)
  let atoms = Formula.atoms f in
  let start_idx = List.length atoms in
  let (tbl, _) = update_expl_table [] start_idx f p in
  (* let tbl' = List.filter tbl ~f:(fun (cell, cells) -> (not (List.is_empty cells)) || (cell_col cell) = 0) in *)
  let ident = "    " in
  let ident2 = "    " ^ ident in
  (Printf.sprintf "%s\"table\": [\n" ident2) ^
  (String.concat ",\n" (List.map tbl ~f:(fun (cell, cells) -> cell_to_json cell cells))) ^
  (Printf.sprintf "]")
