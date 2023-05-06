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
open Import


module Stdin = struct

  (* TODO: Improve error handling here *)
  let parse_event inc =
    Db_parser.db Db_lexer.token (Lexing.from_channel inc)

  let parse_events inc =
    parse_event inc

end


module Stdout = struct

  type mode = UNVERIFIED | VERIFIED | DEBUG

  type t =
    | Explanation of (timestamp * timepoint) * Expl.t
    | ExplanationCheck of (timestamp * timepoint) * Expl.t * bool
    | ExplanationCheckDebug of (timestamp * timepoint) * Expl.t * bool * unit * unit
    | Info of string

  let expl = function
  | Explanation ((ts, tp), e) -> printf "%d:%d\nExplanation: \n%s\n" ts tp (Expl.to_string e)
  | ExplanationCheck ((ts, tp), e, b) ->
     printf "%d:%d\nExplanation: \n%s\n" ts tp (Expl.to_string e);
     printf "\nChecker output: %B\n" b;
  | ExplanationCheckDebug ((ts, tp), e, b, _, _) ->
     printf "%d:%d\nExplanation: \n%s\n" ts tp (Expl.to_string e);
     printf "\nChecker output: %B\n" b;
  | Info s -> printf "\nInfo: %s\n" s

  let expls ts es checker_es_opt = function
    | UNVERIFIED -> List.iter es (fun e -> expl (Explanation ((ts, (Expl.at e)), e)))
    | VERIFIED -> List.iter2_exn es (Option.value_exn checker_es_opt)
                    (fun e (b, _, _) -> expl (ExplanationCheck ((ts, (Expl.at e)), e, b)))
    | DEBUG -> List.iter2_exn es (Option.value_exn checker_es_opt)
                 (fun e (b, checker_e, trace) -> expl (ExplanationCheckDebug ((ts, (Expl.at e)), e, b, (), ())))

end

(* module Json = struct *)

(*   let trace_error = "Events are specified in the format: @1 a b" *)

(*   let parse_lines_from_string s = *)
(*     let events = String.split_lines s in *)
(*     List.fold_until events ~init:[] ~finish:(fun acc -> Ok (List.rev acc)) *)
(*       ~f:(fun acc e -> match parse_trace_line e with *)
(*                        | None -> Stop (Or_error.error_string trace_error) *)
(*                        | Some s -> Continue (s::acc)) *)

(*   let table_columns f = *)
(*     let aps_columns = Formula.atoms f in *)
(*     let subfs_columns = List.map (subfs_dfs f) op_to_string in *)
(*     let subfs = List.map (subfs_dfs f) formula_to_string in *)
(*     Printf.sprintf "{\n  \"apsColumns\": %s,\n  \"subfsColumns\": %s,\n  \"subformulas\": %s}\n" *)
(*       (list_to_json aps_columns) (list_to_json subfs_columns) (list_to_json subfs) *)

(*   let expls tp_ts f ps cbs_opt = *)
(*     let ident = "    " in *)
(*     let ident2 = "    " ^ ident in *)
(*     match cbs_opt with *)
(*     | None -> String.concat ~sep:",\n" (List.map ps ~f:(fun p -> *)
(*                                             let tp = (p_at p) in *)
(*                                             let ts = Hashtbl.find tp_ts tp in *)
(*                                             Printf.sprintf "%s{\n" ident ^ *)
(*                                               Printf.sprintf "%s\"ts\": %d,\n" ident2 ts ^ *)
(*                                                 Printf.sprintf "%s\"tp\": %d,\n" ident2 tp ^ *)
(*                                                   Printf.sprintf "%s\n" (expl_to_json f p) ^ *)
(*                                                     Printf.sprintf "%s}" ident)) *)
(*     | Some cbs -> String.concat ~sep:",\n" (List.map2_exn ps cbs ~f:(fun p cb -> *)
(*                                                 let tp = (p_at p) in *)
(*                                                 let ts = Hashtbl.find tp_ts tp in *)
(*                                                 Printf.sprintf "%s{\n" ident ^ *)
(*                                                   Printf.sprintf "%s\"ts\": %d,\n" ident2 ts ^ *)
(*                                                     Printf.sprintf "%s\"tp\": %d,\n" ident2 tp ^ *)
(*                                                       Printf.sprintf "%s\"checker\": \"%B\",\n" ident2 cb ^ *)
(*                                                         Printf.sprintf "%s\n" (expl_to_json f p) ^ *)
(*                                                           Printf.sprintf "%s}" ident)) *)

(*   let error err = *)
(*     Printf.sprintf "ERROR: %s" (Error.to_string_hum err) *)

(*   let atoms f sap tp ts = *)
(*     let ident = "    " in *)
(*     let ident2 = "    " ^ ident in *)
(*     Printf.sprintf "%s{\n" ident ^ *)
(*       Printf.sprintf "%s\"ts\": %d,\n" ident2 ts ^ *)
(*         Printf.sprintf "%s\"tp\": %d,\n" ident2 tp ^ *)
(*           Printf.sprintf "%s\n" (atoms_to_json f sap tp) ^ *)
(*             Printf.sprintf "%s}" ident *)

(* end *)
