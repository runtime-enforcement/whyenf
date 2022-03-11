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
open Yojson

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

let next_idx l = (max_list l) + 1

let new_mem_alist l =
  List.fold l ~init:[]
    ~f:(fun acc (new', idx', f') -> if new' then (idx', f') :: acc else acc)

let rec update_state st f p =
  match (value f), p with
  | P s1, S (SAtom (i, s2)) ->
     let (new0, idx0) = match List.find (st_alist st) ~f:(fun (_, f') -> (hash f) = (hash f')) with
       | None -> (true, st_idx st)
       | Some (idx, _) -> (false, idx) in
     let idx3 = next_idx [(st_idx st); idx0] in
     let alist = (st_alist st) @ (new_mem_alist [(new0, idx0, f)]) in
     let cell = (p_at p, idx0, true) in
     let tbl = (cell, []) :: (st_tbl st) in
     (tbl, alist, idx3)
  | Since (i, f1, f2), S (SSince (sp2, sp1s)) ->
     (* Check if idxs already have an entry in the association list *)
     let (new0, idx0) = match List.find (st_alist st) ~f:(fun (_, f') -> (hash f) = (hash f')) with
       | None -> (true, st_idx st)
       | Some (idx, _) -> (false, idx) in
     let (new1, idx1) = match List.find (st_alist st) ~f:(fun (_, f') -> (hash f1) = (hash f')) with
       | None -> (true, next_idx [(st_idx st); idx0])
       | Some (idx, _) -> (false, idx) in
     let (new2, idx2) = match List.find (st_alist st) ~f:(fun (_, f') -> (hash f2) = (hash f')) with
       | None -> (true, next_idx [(st_idx st); idx0; idx1])
       | Some (idx, _) -> (false, idx) in
     let idx3 = next_idx [(st_idx st); idx0; idx1; idx2] in
     (* Update association lists with new indices *)
     let alist = (st_alist st) @ (new_mem_alist [(new0, idx0, f); (new1, idx1, f1); (new2, idx2, f2)]) in
     let st_0 = (st_tbl st, alist, idx3) in
     (* Recursive calls *)
     let st_1 = update_state st_0 f2 (S sp2) in
     let st_2 = List.fold sp1s ~init:st_1 ~f:(fun st' sp1 -> update_state st' f1 (S sp1)) in
     (* State update *)
     let cell = (p_at p, idx0, true) in
     let cells = (s_at sp2, idx2, true) ::
                   (List.map sp1s ~f:(fun sp1 -> (s_at sp1, idx1, true))) in
     let tbl = (cell, cells) :: (st_tbl st_2) in
     (tbl, st_alist st_2, st_idx st_2)
  | _ -> failwith ""

let json_output tbl =
  `Assoc
    (List.map tbl ~f:(fun ((tp, col, b), cells) ->
         [
           ("tp", `Int tp);
           ("col", `Int col);
           ("verdict", `Bool b);
           ("cells",
            `Assoc
              (List.map cells ~f:(fun (tp', col', b') ->
                   [
                     ("tp", `Int tp');
                     ("col", `Int col');
                     ("verdict", `Bool b');
                   ]
                 )
              )
           );
         ]
       )
    )

let json f p =
  let st = update_state ([], [], 0) f p in
  let oc = stdout in
  Yojson.Basic.pretty_to_channel oc (json_output (st_tbl st));
  output_string oc "\n"
