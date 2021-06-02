(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Util
open Expl
open Interval

type input_type =
  | Event of event
  | Noise of string

type input_channel =
  | Input of in_channel
  | InputMock of input_type list

type output_type =
  | Explanation of (timestamp * timepoint) * expl
  | Info of string

type output_channel =
  | Output of out_channel
  | OutputDebug of timepoint * out_channel
  | OutputMock of output_type list

type channel =
  | IC of input_channel
  | OC of output_channel

exception End_of_mock of output_channel

let parse_line s =
  let s = String.trim s in 
  if String.length s > 1 && (String.get s 0) = '@' then
    match String.split_on_char ' ' (String.sub s 1 (String.length s - 1)) with
    | [] -> None
    | raw_t :: preds ->
       try Some (SS.of_list (List.map
                               (fun p ->
                                 String.trim (String.map (fun c ->
                                                  if c = '(' || c = ')' then ' '
                                                  else c) p))
                               (List.filter (fun x -> x <> "()") preds)),
                 int_of_string raw_t)
       with Failure _ -> None
  else None

let rec parse_lines line ch out =
  match ch with
  | Input x -> (match parse_line line with
                | Some s -> (s, ch)
                | None -> parse_lines (input_line x) ch out)
  | InputMock x -> (match parse_line line with
                    | Some x -> (x, ch)
                    | None -> match x with
                              | [] -> raise (End_of_mock out)
                              | a::ax -> match a with
                                         | Event ev -> (ev, InputMock ax)
                                         | Noise str -> parse_lines str (InputMock ax) out)

let input_event log out =
  match log with
  | Input x ->  parse_lines (input_line x) log out
  | InputMock x -> match x with
                   | [] -> raise (End_of_mock out)
                   | a::ax -> match a with
                              | Event ev -> (ev, InputMock ax)
                              | Noise s -> parse_lines s (InputMock ax) out

let output_event log event =
  match log with
  | Output x -> Printf.fprintf x "%s" event; log
  | OutputDebug (_, x) -> Printf.fprintf x "%s%!" event; log
  | OutputMock x -> OutputMock(x @ [Info event])

let insert_debug k s =
  let ls = String.split_on_char '\n' s in
  let rls = List.rev ls in
  let last = List.hd rls in
  let init = List.rev (List.tl rls) in
  if last = "" then
    String.concat (Printf.sprintf "\n[DEBUG %2d]: " k) init ^ "\n"
  else
    String.concat (Printf.sprintf "\n[DEBUG %2d]: " k) ls

let output_debug k log event =
  match log with
  | OutputDebug (l, x) when k <= l ->
     Printf.fprintf x "[DEBUG %2d]: %s%!" k (insert_debug k (event ())); log
  | _ -> log

let channel_to_string log = match log with
  | OC c ->
     (match c with
      | Output _ | OutputDebug _ -> ""
      | OutputMock ls ->
         List.fold_left (fun a x -> a ^ (match x with
                                         | Explanation ((t, i), p) ->
                                            Printf.sprintf "%d:%d\nProof: \n%s\n" t i (expl_to_string p)
                                         | Info s -> s)
                           ) "" ls)
  | IC c -> (match c with
             | Input _ -> ""
             | InputMock ls ->
                List.fold_left (fun a x ->
                    a ^ "\n" ^ (match x with
                                | Event (atoms, ts) ->
                                   let atoms_str = Util.SS.fold (fun a x ->
                                                       a ^ " " ^ x
                                                     ) atoms "" in
                                   Printf.sprintf "@%d %s" ts atoms_str
                                | Noise s -> s)
                  ) "" ls)

let sort ch = match ch with
  | OutputMock c -> OutputMock (List.sort (fun a b -> if a < b then -1 else 1) c)
  | _ -> ch

let output_explanation ch ((t, i), p) =
  match ch with
  | Output x -> Printf.fprintf x "%d:%d\nProof: \n%s\n" t i (Expl.expl_to_string p); ch
  | OutputDebug (_, x) -> Printf.fprintf x "%d:%d\nProof: \n%s\n" t i (Expl.expl_to_string p); ch
  | OutputMock x -> OutputMock(x @ [Explanation ((t, i), p)])

let output_interval out i = output_event out (interval_to_string i)
