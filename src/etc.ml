(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

module Fdeque = Core.Fdeque

type timepoint = int
type timestamp = int

let debug = ref false
let inc_ref = ref Stdio.In_channel.stdin
let outc_ref = ref Stdio.Out_channel.stdout

let eat s t = s ^ (String.strip t)
let paren h k x = if h>k then "("^^x^^")" else x
let is_digit = function
  | '0' .. '9' -> true
  | _ -> false

exception Parsing_error of Lexing.position*Lexing.position*string
let parsing_error i j fmt = Caml.Format.kasprintf (fun s -> raise (Parsing_error(i,j,s))) fmt
let lexing_error lexbuf fmt = parsing_error (Lexing.lexeme_start_p lexbuf) (Lexing.lexeme_end_p lexbuf) fmt
let lexbuf_error_msg (lexbuf: Lexing.lexbuf) =
  Printf.sprintf "a problem was found at line %d character %d"
    (lexbuf.lex_curr_p.pos_lnum) (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol) 

exception Empty_deque of string
let deque_to_string indent f d =
  if Fdeque.is_empty d then indent ^ "[]"
  else
    (if Int.equal (Fdeque.length d) 1 then
       indent ^ eat "[" (f indent (Fdeque.peek_front_exn d) ^ "]")
     else
       Fdeque.fold ~f:(fun s el -> eat (s ^ "\n" ^ indent ^ "; ") (f indent el))
         ~init:(indent ^ eat "[ " (f indent (Fdeque.peek_front_exn d))) (Fdeque.drop_front_exn d) ^ " ]")

let rec queue_drop q n =
  if Int.equal n 0 then q
  else (let _ = Queue.dequeue_exn q in queue_drop q (n-1))

let list_to_string indent f = function
  | [] -> indent ^ "[]"
  | [x] -> indent ^ eat "[" (f indent x ^ "]")
  | x :: xs ->
     List.fold_left xs ~init:(indent ^ eat "[ " (f indent x))
       ~f:(fun s el -> eat (s ^ "\n" ^ indent ^ "; ") (f indent el)) ^ " ]"

let rec string_list_to_string = function
  | [] -> ""
  | x :: xs -> if List.is_empty xs then x
               else Printf.sprintf "%s, %s" x (string_list_to_string xs)

type valuation = (string, Dom.t, String.comparator_witness) Map.t

let compare_valuation = Map.compare_direct Dom.compare
let equal_valuation = Map.equal Dom.equal
let empty_valuation: valuation = Map.empty (module String)
let sexp_of_valuation v =
  let f (k, d) = Sexp.List [Atom k; Atom (Dom.to_string d)] in
  Sexp.List (List.map (Map.to_alist v) ~f)
let extend_valuation v v' = Map.merge v v' ~f:(fun ~key d -> match d with `Left d -> Some d | `Right d -> Some d | `Both (d, _) -> Some d)
let hash_valuation (v: valuation) =
  List.fold_left ~init:0 ~f:(fun acc (x, d) -> String.hash x lxor Dom.hash d lxor acc) (Map.to_alist v)

let dom_map_to_string m =
  string_list_to_string
    (List.map (Map.to_alist m) ~f:(fun (x, d) -> Printf.sprintf "%s -> %s" x (Dom.to_string d)))

let valuation_to_string = dom_map_to_string

let some_string () = (String.of_char (Char.of_int_exn (Random.int_incl 97 122))) ^
                       (String.of_char (Char.of_int_exn (Random.int_incl 97 122))) ^
                         (String.of_char (Char.of_int_exn (Random.int_incl 97 122))) ^
                           (String.of_char (Char.of_int_exn (Random.int_incl 97 122)))

let string_list_to_json l =
  match l with
  | [] -> "[]"
  | _ -> let els_str = String.concat ~sep:"" (List.map l ~f:(fun el -> "\"" ^ el ^ "\",")) in
         "[" ^ (String.sub els_str ~pos:0 ~len:((String.length els_str)-1)) ^ "]"

let int_list_to_json l =
  match l with
  | [] -> "[]"
  | _ -> let els_str = String.concat ~sep:"" (List.map l ~f:(fun el -> (Int.to_string el) ^ ",")) in
         "[" ^ (String.sub els_str ~pos:0 ~len:((String.length els_str)-1)) ^ "]"

let unquote s =
    let len = String.length s in
    if Char.equal s.[0] '\"' && Char.equal s.[len-1] '\"' then
      String.sub s ~pos:1 ~len:(len-2)
    else s

let escape_underscores s =
  String.fold s ~init:"" ~f:(fun acc c -> if Char.equal c '_' then acc ^ "\\_" else acc ^ (Char.to_string c))

let rec fdeque_for_all2_exn d1 d2 ~f:((f : _ -> _ -> _)) =
  match Fdeque.dequeue_front d1, Fdeque.dequeue_front d2 with
  | None, None -> true
  | Some(a1, d1), Some(a2, d2) -> f a1 a2 && fdeque_for_all2_exn d1 d2 ~f
  | _, _ -> raise (Invalid_argument (Printf.sprintf "length mismatch in fdeque_for_all2_exn: %d <> %d" (Fdeque.length d1) (Fdeque.length d2)))

let rec spaces n = if n < 0 then "" else " " ^ spaces (n-1)

let rec lexicographics compare l l' =
  match l, l' with
  | [], [] -> 0
  | h::t, [] -> 1
  | [], h'::t' -> -1
  | h::t, h'::t' when compare h h' == 0 -> lexicographics compare t t'
  | h::t, h'::t' -> compare h h'

let lexicographic2 compare1 compare2 =
  fun (a, b) (a', b') ->
  if compare1 a a' < 0 then -1
  else if compare1 a a' > 0 then 1
  else compare2 b b'

let lexicographic3 compare1 compare2 compare3 =
  fun (a, b, c) (a', b', c') ->
  if compare1 a a' < 0 then -1
  else if compare1 a a' > 0 then 1
  else if compare2 b b' < 0 then -1
  else if compare2 b b' > 0 then 1
  else compare3 c c'

let lexicographic4 compare1 compare2 compare3 compare4 =
  fun (a, b, c, d) (a', b', c', d') ->
  if compare1 a a' < 0 then -1
  else if compare1 a a' > 0 then 1
  else if compare2 b b' < 0 then -1
  else if compare2 b b' > 0 then 1
  else if compare3 c c' < 0 then -1
  else if compare3 c c' > 0 then 1
  else compare4 d d'

let lexicographic5 compare1 compare2 compare3 compare4 compare5 =
  fun (a, b, c, d, e) (a', b', c', d', e') ->
  if compare1 a a' < 0 then -1
  else if compare1 a a' > 0 then 1
  else if compare2 b b' < 0 then -1
  else if compare2 b b' > 0 then 1
  else if compare3 c c' < 0 then -1
  else if compare3 c c' > 0 then 1
  else if compare4 d d' < 0 then -1
  else if compare4 d d' > 0 then 1
  else compare5 e e'


(* For debugging only *)
let _print s f x =
  Stdio.printf "%s:\n%s\n" s (f x);
  Stdlib.flush_all ();
  x

let rec reorder ~equal l = function
  | [] -> []
  | h::t when not (List.mem l h ~equal) -> reorder equal l t
  | h::t -> h :: (reorder equal (List.filter l (fun x -> not (equal x h))) t)

let rec dedup ~equal l = 
  let rec aux seen = function
    | [] -> List.rev seen
    | h::t when List.mem seen h ~equal -> aux seen t
    | h::t -> aux (h::seen) t in
  aux [] l 
  
let rec cartesian = function
  | [] -> [[]]
  | l :: t -> let rest = cartesian t in
              List.concat (List.map l (fun x -> List.map rest ~f:(fun l -> x::l)))


let gen_fresh s =
  let last_chr = List.last_exn (String.to_list s) in
  if not (String.is_empty s) &&
       Char.to_int last_chr >= 97 &&
         Char.to_int last_chr < 122 then
    (String.chop_suffix_exn s ~suffix:(Char.to_string last_chr)) ^
      (Char.to_string (Char.of_int_exn (Char.to_int last_chr + 1)))
  else s ^ "a"

