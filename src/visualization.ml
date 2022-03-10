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

type cell = timepoint * int * bool
type table = (cell * (cell list)) list
type assoc_list = (int * formula) list
type state = table * assoc_list * int

let st_tbl st = match st with
  | (tbl, _, _) -> tbl

let st_alist st = match st with
  | (_, alist, _) -> alist

let st_idx st = match st with
  | (_, _, idx) -> idx

let rec update_state st f p =
  match f.node, p with
  | Since (i, f1, f2), S (SSince (sp2, sp1s)) ->
     let st_1 = update_state (st_tbl st, st_alist st, (st_idx st)+1) f2 (S sp2) in
     let st_2 = List.fold sp1s ~init:st_1 ~f:(fun st' sp1 ->
                    update_state st' f1 (S sp1)) in
     let idxs = List.fold sp1s ~init:[] ~f:(fun acc idx -> acc @ [idx])
                    (acc @ [st_idx st_1], update_state st_1 f1 (S sp1))) in
     let cell = (p_at p, st_idx st, true) in
     let cells = (s_at sp2, (st_idx st) + 1, true) ::
                   (List.map2_exn idxs sp1s ~f:(fun idx sp1 -> (s_at sp1, idx, true))) in
     ((cell, cells) :: (st_tbl st_2), ((st_idx st), p) :: (st_alist st_2), st_idx st_2)
  | _ -> failwith ""
