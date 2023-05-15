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
open Etc

module Event = struct

  module T = struct

    type t = string * Domain.t list [@@deriving compare, sexp_of]

    let to_string (name, ds) = Printf.sprintf "%s(%s)" name (Domain.list_to_string ds)

  end

  include T
  include Comparable.Make(T)

end

type t = timestamp * timepoint * (Event.t, Event.comparator_witness) Set.t

let db ts tp evts = (ts, tp, Set.of_list (module Event) evts)

let event name consts =
  let pred_sig = Hashtbl.find_exn Pred.Sig.table name in
  if pred_sig.arity = List.length consts then
    (name, List.map2_exn pred_sig.ntconsts consts
             (fun tc c -> match snd tc with
                          | TInt -> Domain.Int (Int.of_string c)
                          | TStr -> Str c
                          | TFloat -> Float (Float.of_string c)))
  else raise (Invalid_argument (Printf.sprintf "predicate %s has arity %d" name pred_sig.arity))

let add_event (ts, tp, evts) evt = (ts, tp, Set.add evts evt)

let to_string (ts, tp, evts) =
  Printf.sprintf "TS: %d | TP: %d\n" ts tp ^
    (Set.fold evts ~init:"" ~f:(fun acc evt -> acc ^ Event.to_string evt ^ "\n"))
