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
open Pred

module Event = struct
  module T = struct
    type t = string * const list [@@deriving compare, sexp_of]
  end
  include T
  include Comparable.Make(T)
end

type t = int * (Event.t, Event.comparator_witness) Set.t

let sig_table : (string, Pred.Sig.t) Hashtbl.t = Hashtbl.create (module String)

(* TODO: Process signature file and populate this hashtable *)

let db ts events = (int_of_string ts, Set.of_list (module Event) events)

let event name consts =
  let pred_sig = Hashtbl.find_exn sig_table name in
  if pred_sig.arity = List.length consts then
    (name, List.map2_exn pred_sig.tconsts consts
             (fun tc c -> match tc with
                          | TInt -> Int (int_of_string c)
                          | TStr -> Str c
                          | TFloat -> Float (float_of_string c)))
  else raise (Invalid_argument (Printf.sprintf "predicate %s has arity %d" name pred_sig.arity))
