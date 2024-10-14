(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

type ('a, 'b) t = Finite of ('a, 'b) Set.t | Complement of ('a, 'b) Set.t

let phys_equal = Stdlib.( == )

(*let min_elt_exn = Set.min_elt_exn*)

let length = function
  | Finite s -> Set.length s
  | Complement s -> Set.length s

let empty m = Finite (Set.empty m)
let univ m = Complement (Set.empty m)

let equal cs1 cs2 = match cs1, cs2 with
  | Finite s1, Finite s2 -> Set.equal s1 s2
  | Complement s1, Complement s2 -> Set.equal s1 s2
  | _, _ -> false

let add cs el = match cs with
  | Finite s -> Finite (Set.add s el)
  | Complement s -> Complement (Set.remove s el)

let singleton m c = Finite (Set.singleton m c)

let is_empty = function
  | Finite s -> Set.is_empty s
  | Complement s -> false

let is_univ = function
  | Finite s -> false
  | Complement s -> Set.is_empty s

let mem cs el = match cs with
  | Finite s -> Set.mem s el
  | Complement s -> not (Set.mem s el)

let comp = function
  | Finite s -> Complement s
  | Complement s -> Finite s

let inter cs1 cs2 =
  if phys_equal cs1 cs2 then cs1
  else (match cs1, cs2 with
        | Finite s1, Finite s2 -> Finite (Set.inter s1 s2)
        | Finite s1, Complement s2 -> Finite (Set.diff s1 s2)
        | Complement s1, Finite s2 -> Finite (Set.diff s2 s1)
        | Complement s1, Complement s2 -> Complement (Set.union s1 s2))

let union cs1 cs2 =
  if phys_equal cs1 cs2 then cs1
  else (match cs1, cs2 with
        | Finite s1, Finite s2 -> Finite (Set.union s1 s2)
        | Finite s1, Complement s2 -> Complement (Set.diff s2 s1)
        | Complement s1, Finite s2 -> Complement (Set.diff s1 s2)
        | Complement s1, Complement s2 -> Complement (Set.inter s1 s2))

let inter_list m css =
  List.fold css ~init:(univ m) ~f:inter
  
let union_list m css =
  List.fold css ~init:(empty m) ~f:union

let diff cs1 cs2 = match cs1, cs2 with
  | Finite s1, Finite s2 -> Finite (Set.diff s1 s2)
  | Finite s1, Complement s2 -> Finite (Set.inter s1 s2)
  | Complement s1, Finite s2 -> Complement (Set.union s1 s2)
  | Complement s1, Complement s2 -> inter (Complement s1) (Finite s2)

(* TODO: This should be rewritten more carefully *)
let some_elt tt = function
  | Finite s -> Set.min_elt_exn s
  | Complement s -> (match tt with
                     | Dom.TInt -> let elt = ref (Dom.Int (Random.int Int.max_value)) in
                                      (while Set.mem s !elt do
                                         elt := Int (Random.int Int.max_value)
                                       done); !elt
                     | TStr -> let elt = ref (Dom.Str (Etc.some_string ())) in
                               (while Set.mem s !elt do
                                  elt := Str (Etc.some_string ())
                                done); !elt
                     | TFloat -> let elt = ref (Dom.Float (Random.float Float.max_value)) in
                                 (while Set.mem s !elt do
                                    elt := Float (Random.float Float.max_value)
                                  done); !elt)

let is_finite = function
  | Finite _ -> true
  | Complement _ -> false

let to_list = function
  | Finite s -> Set.to_list s
  | Complement _ -> raise (Invalid_argument "to_list is not defined for complement sets")

let to_json = function
  | Finite s -> (Printf.sprintf "\"subset_type\": \"finite\", \"subset_values\": %s,"
                   (Etc.string_list_to_json (List.map (Set.to_list s) ~f:Dom.to_string)))
  | Complement s -> (Printf.sprintf "\"subset_type\": \"complement\", \"subset_values\": %s,"
                       (Etc.string_list_to_json (List.map (Set.to_list s) ~f:Dom.to_string)))

let rec format s =
  if Int.equal (Set.length s) 0 then ""
  else (if Int.equal (Set.length s) 1 then Dom.to_string (Set.choose_exn s)
        else (let min = Set.min_elt_exn s in
              Printf.sprintf "%s, " (Dom.to_string min) ^ (format (Set.remove s min))))

let to_string = function
  | Finite s -> Printf.sprintf "{%s}" (format s)
  | Complement s -> Printf.sprintf "Complement of {%s}" (format s)

let to_latex = function
  | Finite s -> Printf.sprintf "\\{%s\\}" (format s)
  | Complement s -> Printf.sprintf "\\{%s\\}^\\cp" (format s)

type valuation = (string, (Dom.t, Dom.comparator_witness) t, String.comparator_witness) Map.t
let empty_valuation = Map.empty (module String)
