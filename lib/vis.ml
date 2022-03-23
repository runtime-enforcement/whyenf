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

let rec update_state tbl idx f p =
  match f, p with
  | TT, S (STT i) ->
     let cell = (p_at p, idx, true) in
     (cell, []) :: tbl
  | P s1, S (SAtom (i, s2)) ->
     let cell = (p_at p, idx, true) in
     (cell, []) :: tbl
  | Neg f, S (SNeg vp) ->
     let vp_idx = idx+1 in
     let tbl' = update_state tbl vp_idx f (V vp) in
     let cell = (p_at p, idx, true) in
     let cells = [(v_at vp, vp_idx, false)] in
     (cell, cells) :: tbl'
  | Disj (f1, _), S (SDisjL sp) ->
     let sp_idx = idx+1 in
     let tbl' = update_state tbl sp_idx f1 (S sp) in
     let cell = (p_at p, idx, true) in
     let cells = [(s_at sp, sp_idx, true)] in
     (cell, cells) :: tbl'
  | Disj (_, f2), S (SDisjR sp) ->
     let sp_idx = idx+2 in
     let tbl' = update_state tbl sp_idx f2 (S sp) in
     let cell = (p_at p, idx, true) in
     let cells = [(s_at sp, sp_idx, true)] in
     (cell, cells) :: tbl'
  | Conj (f1, f2), S (SConj (sp1, sp2)) ->
     let sp1_idx = idx+1 in
     let sp2_idx = idx+2 in
     let tbl' = update_state tbl sp1_idx f1 (S sp1) in
     let tbl'' = update_state tbl' sp2_idx f2 (S sp2) in
     let cell = (p_at p, idx, true) in
     let cells = [(s_at sp1, sp1_idx, true); (s_at sp2, sp2_idx, true)] in
     (cell, cells) :: tbl''
  | Prev (_, f), S (SPrev sp) ->
     let sp_idx = idx+1 in
     let tbl' = update_state tbl sp_idx f (S sp) in
     let cell = (p_at p, idx, true) in
     let cells = [(s_at sp, sp_idx, true)] in
     (cell, cells) :: tbl'
  | Since (_, f1, f2), S (SSince (sp2, sp1s)) ->
     let sp1_idx = idx+1 in
     let sp2_idx = idx+2 in
     (* Recursive calls *)
     let tbl' = List.fold sp1s ~init:tbl ~f:(fun t sp1 -> update_state t sp1_idx f1 (S sp1)) in
     let tbl'' = update_state tbl' sp2_idx f2 (S sp2) in
     (* State update *)
     let cell = (p_at p, idx, true) in
     let cells = (s_at sp2, sp2_idx, true) ::
                   (List.map sp1s ~f:(fun sp1 -> (s_at sp1, sp1_idx, true))) in
     (cell, cells) :: tbl''

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
  let tbl = update_state [] 0 f p in
  let ident = "    " in
  (Printf.sprintf "%s\"table\": [\n" ident) ^
  (String.concat ",\n" (List.map tbl ~f:(fun (cell, cells) -> cell_to_json cell cells))) ^
  (Printf.sprintf "]")
