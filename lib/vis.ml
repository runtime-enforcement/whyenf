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
  | TT, S (STT i) ->
     let cur_idx = st_idx st in
     let cell = (p_at p, cur_idx, true) in
     let tbl = (cell, []) :: (st_tbl st) in
     (tbl, cur_idx)
  | P s1, S (SAtom (i, s2)) ->
     let cur_idx = st_idx st in
     let cell = (p_at p, cur_idx, true) in
     let tbl = (cell, []) :: (st_tbl st) in
     (tbl, cur_idx)
  | Neg f, S (SNeg vp) ->
     let cur_idx = st_idx st in
     let st_0 = update_state (st_tbl st, cur_idx+1) f (V vp) in
     let cell = (p_at p, cur_idx, true) in
     let cells = [(v_at vp, cur_idx+1, false)] in
     let tbl = (cell, cells) :: (st_tbl st) in
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

let cell_to_json (tp, col, b) cells =
  let ident = "    " in
  let ident2 = "    " ^ ident in
  let ident3 = "    " ^ ident2 in
  (Printf.sprintf "%s{\n" ident) ^
  (Printf.sprintf "%s\"tp\": %d,\n" ident2 tp) ^
  (Printf.sprintf "%s\"col\": %d,\n" ident2 col) ^
  (Printf.sprintf "%s\"bool\": %B,\n" ident2 b) ^
  (Printf.sprintf "%s\"cells\":" ident2) ^
  (if List.is_empty cells then " []"
   else ((Printf.sprintf " [\n") ^
         (String.concat ",\n" (List.map cells ~f:(fun (tp', col', b') ->
                                   (Printf.sprintf "%s{\n" ident2) ^
                                   (Printf.sprintf "%s\"tp\": %d,\n" ident3 tp') ^
                                   (Printf.sprintf "%s\"col\": %d,\n" ident3 col') ^
                                   (Printf.sprintf "%s\"bool\": %B\n" ident3 b') ^
                                   (Printf.sprintf "%s}" ident2)))) ^
         (Printf.sprintf "]\n"))) ^
  (Printf.sprintf "\n%s}" ident)

let expl_to_json f p =
  (* (Printf.printf "f = %s\n" (formula_to_string f));
   * (Printf.printf "p = %s\n" (expl_to_string p)); *)
  let st = update_state ([], 0) f p in
  let ident = "    " in
  (Printf.sprintf "%s\"table\": [\n" ident) ^
  (String.concat ",\n" (List.map (st_tbl st) ~f:(fun (cell, cells) -> cell_to_json cell cells))) ^
  (Printf.sprintf "]")
