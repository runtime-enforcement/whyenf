(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Stdio
open Etc
open Checker_interface

module Plain = struct

  type mode = UNVERIFIED | VERIFIED | DEBUG | DEBUGVIS

  type t =
    | Explanation of (timestamp * timepoint) * Expl.t
    | ExplanationCheck of (timestamp * timepoint) * Expl.t * bool
    | ExplanationCheckDebug of (timestamp * timepoint) * Expl.t * bool * Checker_pdt.t * Checker_trace.t
                               * (Domain.t, Domain.comparator_witness) Setc.t list list option
    | Info of string

  let expl = function
    | Explanation ((ts, tp), e) ->
       Stdio.printf "%d:%d\nExplanation: \n%s\n\n" ts tp (Expl.to_string e)
    | ExplanationCheck ((ts, tp), e, b) ->
       Stdio.printf "%d:%d\nExplanation: \n%s\n" ts tp (Expl.to_string e);
       Stdio.printf "\nChecker output: %B\n\n" b;
    | ExplanationCheckDebug ((ts, tp), e, b, c_e, c_t, path_opt) ->
       Stdio.printf "%d:%d\nExplanation: \n%s\n" ts tp (Expl.to_string e);
       Stdio.printf "\nChecker output: %B\n\n" b;
       Stdio.printf "\n[debug] Checker explanation:\n%s\n\n" (Checker_interface.Checker_pdt.to_string "" c_e);
       Stdio.printf "\n[debug] Checker trace:\n%s" (Checker_interface.Checker_trace.to_string c_t);
       (match path_opt with
        | None -> ()
        | Some(l1) ->
           Stdio.printf "|l1| = %d\n" (List.length l1);
           Stdio.printf "\n[debug] Checker false path: %s\n"
             (Etc.list_to_string "" (fun _ l2 -> Etc.list_to_string ""
                                                   (fun _ s -> Setc.to_string s) l2) l1)
        );
    | Info s -> Stdio.printf "\nInfo: %s\n\n" s

  let expls ts tstp_expls checker_es_opt paths_opt = function
    | UNVERIFIED -> List.iter tstp_expls (fun ((_, tp), e) -> expl (Explanation ((ts, tp), e)))
    | VERIFIED -> List.iter2_exn tstp_expls (Option.value_exn checker_es_opt)
                    (fun ((_, tp), e) (b, _, _) -> expl (ExplanationCheck ((ts, tp), e, b)))
    | DEBUG -> List.iter2_exn (List.zip_exn tstp_expls (Option.value_exn checker_es_opt))
                 (Option.value_exn paths_opt)
                 ~f:(fun (((_, tp), e), (b, checker_e, trace)) path_opt ->
                   expl (ExplanationCheckDebug ((ts, tp), e, b, checker_e, trace, path_opt)))
    | DEBUGVIS -> raise (Failure "this function is undefined for the mode debugvis")

end

module Json = struct

  let error err =
    Printf.sprintf "ERROR: %s" (Error.to_string_hum err)

  let table_columns f =
    let sig_preds_columns = List.rev (Set.fold (Formula.pred_names f) ~init:[] ~f:(fun acc r ->
                                          let r_props = Hashtbl.find_exn Pred.Sig.table r in
                                          let var_names = fst (List.unzip r_props.ntconsts) in
                                          (Printf.sprintf "%s(%s)" r (Etc.string_list_to_string var_names)) :: acc)) in
    let subfs_columns = List.map (Formula.subfs_dfs f) Formula.op_to_string in
    let subfs = List.map (Formula.subfs_dfs f) Formula.to_string in
    Printf.sprintf "{\n  \"predsColumns\": %s,\n  \"subfsColumns\": %s,\n  \"subformulas\": %s}\n"
      (Etc.list_to_json sig_preds_columns) (Etc.list_to_json subfs_columns) (Etc.list_to_json subfs)

  let db ts tp db f =
    Printf.sprintf "%s{\n" (String.make 4 ' ') ^
      Printf.sprintf "%s\"ts\": %d,\n" (String.make 8 ' ') ts ^
        Printf.sprintf "%s\"tp\": %d,\n" (String.make 8 ' ') tp ^
          Printf.sprintf "%s\n" (Vis.Dbs.to_json tp db f) ^
            Printf.sprintf "%s}" (String.make 4 ' ')

  let expls tpts f es =
    List.map es ~f:(fun e ->
        let tp = (Expl.at e) in
        let ts = Hashtbl.find_exn tpts tp in
        Printf.sprintf "%s{\n" (String.make 4 ' ') ^
          Printf.sprintf "%s\"ts\": %d,\n" (String.make 8 ' ') ts ^
            Printf.sprintf "%s\"tp\": %d,\n" (String.make 8 ' ') tp ^
              Printf.sprintf "%s\"expl\": {\n" (String.make 8 ' ') ^
                Printf.sprintf "%s\n" (Vis.Expl.to_json f e) ^
                  Printf.sprintf "}%s}" (String.make 4 ' '))

  let aggregate dbs es =
    Printf.sprintf "{\n" ^
      Printf.sprintf "%s\"dbs_objs\": [\n" (String.make 4 ' ') ^
        String.concat ~sep:",\n" dbs ^
          Printf.sprintf "],\n" ^
            Printf.sprintf "%s\"expls_objs\": [\n" (String.make 4 ' ') ^
              String.concat ~sep:",\n" es ^
                Printf.sprintf "]}"

end
