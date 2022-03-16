(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2022:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Mtl
open Expl
open Util

module List = Base.List

type idx = int
type cell = timepoint * idx * bool
type table = (cell * (cell list)) list
type state = table * int

let st_tbl st = match st with
  | (tbl, _) -> tbl

let st_idx st = match st with
  | (_, idx) -> idx

let next_idx l = (max_list l) + 1

let rec update_state st f p =
  match f, p with
  | P s1, S (SAtom (i, s2)) ->
     let cur_idx = st_idx st in
     let cell = (p_at p, cur_idx, true) in
     let tbl = (cell, []) :: (st_tbl st) in
     (tbl, cur_idx)
  | Since (i, f1, f2), S (SSince (sp2, sp1s)) ->
     let cur_idx = st_idx st in
     (* Recursive calls *)
     let st_0 = List.fold sp1s ~init:(st_tbl st, cur_idx+1) ~f:(fun st' sp1 -> update_state st' f1 (S sp1)) in
     let st_1 = update_state (st_tbl st_0, cur_idx+2) f2 (S sp2) in
     (* State update *)
     let cell = (p_at p, cur_idx, true) in
     let cells = (s_at sp2, cur_idx+2, true) ::
                   (List.map sp1s ~f:(fun sp1 -> (s_at sp1, cur_idx+1, true))) in
     let tbl = (cell, cells) :: (st_tbl st_1) in
     (tbl, cur_idx)
  | _ -> failwith ""

(* let json_cells cells =
 *   `Assoc
 *     (List.map cells ~f:(fun (tp', col', b') ->
 *          [
 *            ("tp", `Int tp');
 *            ("col", `Int col');
 *            ("verdict", `Bool b');
 *          ]
 *        )
 *     )
 *
 * let json_pair (tp, col, b) cells =
 *   `Assoc
 *     [
 *       ("tp", `Int tp);
 *       ("col", `Int col);
 *       ("verdict", `Bool b);
 *       (\* ("cells", (json_cells cells)); *\)
 *     ]
 *
 * let json_output tbl =
 *   List.map tbl ~f:(fun (cell, cells) -> json_pair cell cells)
 *
 * let json f p =
 *   let st = update_state ([], [], 0) f p in
 *   let oc = stdout in
 *   List.iter (json_output (st_tbl st)) ~f:(fun json -> Yojson.Basic.pretty_to_channel oc json);
 *   output_string oc "\n" *)
