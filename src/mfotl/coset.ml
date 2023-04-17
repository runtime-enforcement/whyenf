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

let to_string cs =
  let rec format s =
    if Int.equal (Set.length s) 0 then ""
    else (if Int.equal (Set.length s) 1 then Domain.to_string (Set.choose_exn s)
          else (let min = Set.min_elt_exn s in
                Printf.sprintf "%s, " (Domain.to_string min) ^ (format (Set.remove s min)))) in
  match cs with
  | Finite s -> Printf.sprintf "Finite {%s}" (format s)
  | Complement s -> Printf.sprintf "Complement {%s}" (format s)
