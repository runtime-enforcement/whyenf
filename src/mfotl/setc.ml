(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
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

let univ m = Complement (Set.empty m)

let equal cs1 cs2 = match cs1, cs2 with
  | Finite s1, Finite s2 -> Set.equal s1 s2
  | Complement s1, Complement s2 -> Set.equal s1 s2
  | _, _ -> false

let add cs el = match cs with
  | Finite s -> Finite (Set.add s el)
  | Complement s -> Complement (Set.remove s el)

let is_empty = function
  | Finite s -> Set.is_empty s
  | Complement s -> false

let inter cs1 cs2 =
  if phys_equal cs1 cs2 then cs1
  else (match cs1, cs2 with
        | Finite s1, Finite s2 -> Finite (Set.inter s1 s2)
        | Finite s1, Complement s2 -> Finite (Set.diff s1 s2)
        | Complement s1, Finite s2 -> Finite (Set.diff s2 s1)
        | Complement s1, Complement s2 -> Complement (Set.union s1 s2))

let diff cs1 cs2 = match cs1, cs2 with
  | Finite s1, Finite s2 -> Finite (Set.diff s1 s2)
  | Finite s1, Complement s2 -> Finite (Set.inter s1 s2)
  | Complement s1, Finite s2 -> Complement (Set.union s1 s2)
  | Complement s1, Complement s2 -> inter (Complement s1) (Finite s2)

(* TODO: This should be rewritten more carefully *)
let some_elt tt = function
  | Finite s -> Set.min_elt_exn s
  | Complement s -> (match tt with
                     | Domain.TInt -> let elt = ref (Domain.Int (Random.int 100000)) in
                                      (while Set.mem s !elt do
                                         elt := Int (Random.int 100000)
                                       done); !elt
                     | TStr -> let elt = ref (Domain.Str (Etc.some_string ())) in
                               (while Set.mem s !elt do
                                  elt := Str (Etc.some_string ())
                                done); !elt
                     | TFloat -> let elt = ref (Domain.Float (Random.float 100000.0)) in
                                 (while Set.mem s !elt do
                                    elt := Float (Random.float 100000.0)
                                  done); !elt)

let is_finite = function
  | Finite _ -> true
  | Complement _ -> false

let to_list = function
  | Finite s -> Set.to_list s
  | Complement _ -> raise (Invalid_argument "to_list is not defined for complement sets")

let to_string cs =
  let rec format s =
    if Int.equal (Set.length s) 0 then ""
    else (if Int.equal (Set.length s) 1 then Domain.to_string (Set.choose_exn s)
          else (let min = Set.min_elt_exn s in
                Printf.sprintf "%s, " (Domain.to_string min) ^ (format (Set.remove s min)))) in
  match cs with
  | Finite s -> Printf.sprintf "Finite {%s}" (format s)
  | Complement s -> Printf.sprintf "Complement {%s}" (format s)
