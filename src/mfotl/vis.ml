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

type idx = int
type period = PAST | FUTURE
type cell = timepoint * idx * (Interval.t * period) option * bool
type table = (cell * (cell list)) list

let cell_col cell = match cell with
  | (_, col, _, _) -> col

let rec f_idx idx = function
  | Formula.TT | FF | Predicate _ -> idx
  | Neg f' | Exists (_, f') | Forall (_, f')
    | Prev (_, f') | Next (_, f')
    | Once (_, f') | Eventually (_, f')
    | Historically (_, f') | Always (_, f') -> f_idx (idx+1) f'
  | And (f1, f2) | Or (f1, f2)
    | Imp (f1, f2) | Iff (f1, f2)
    | Since (_, f1, f2) | Until (_, f1, f2) -> let idx' = f_idx (idx+1) f1 in
                                               f_idx (idx'+1) f2

(* let rec update_preds_table tbl idx sap tp atoms = function *)
(*   | Formula.TT | FF -> (tbl, idx, atoms) *)
(*   | P s -> let b = SS.mem s sap in *)
(*            let cell = (tp, idx, None, b) in *)
(*            if (List.exists atoms ~f:(fun s' -> s = s')) then (tbl, idx, atoms) *)
(*            else ((cell, []) :: tbl, idx+1, s :: atoms) *)
(*   | Neg f' | Prev (_, f') | Next (_, f') *)
(*   | Once (_, f') | Historically (_, f') *)
(*   | Eventually (_, f') | Always (_, f') -> update_atoms_table tbl idx f' sap tp atoms *)
(*   | Conj (f1, f2) | Disj (f1, f2) *)
(*   | Imp (f1, f2) | Iff (f1, f2) *)
(*   | Since (_, f1, f2) *)
(*   | Until (_, f1, f2) -> let (tbl', idx', atoms') = update_atoms_table tbl idx f1 sap tp atoms in *)
(*                          update_atoms_table tbl' idx' f2 sap tp atoms' *)
