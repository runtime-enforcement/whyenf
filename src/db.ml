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
open Etc

module Event = struct

  module T = struct

    type t = string * Dom.t list [@@deriving compare, sexp_of]

    let equal (name1, ds1) (name2, ds2) =
      String.equal name1 name2 &&
        (match (List.for_all2 ds1 ds2 ~f:(fun d1 d2 -> Dom.equal d1 d2)) with
         | Ok b -> b
         | Unequal_lengths -> false)

    let to_string (name, ds) = Printf.sprintf "%s(%s)" name (Dom.list_to_string ds)

    let to_json (name, ds) =
      String.concat ~sep:", "
        (List.map2_exn (Pred.Sig.vars name) ds  ~f:(fun x d ->
             Printf.sprintf "{ " ^
               Printf.sprintf "\"var\": \"%s\", " x ^
                 Printf.sprintf "\"value\": \"%s\" " (Dom.to_string d) ^
                   Printf.sprintf "}"))

  end

  include T
  include Comparable.Make(T)

  let _tp = (Pred.tp_event_name, [])

end

type t = (Event.t, Event.comparator_witness) Set.t

let create evtl = Set.of_list (module Event) evtl

let mem = Set.mem
let is_empty = Set.is_empty

let event name consts =
  let pred_sig = Hashtbl.find_exn Pred.Sig.table name in
  if pred_sig.arity = List.length consts then
    (name, List.map2_exn pred_sig.ntconsts consts
             ~f:(fun tc c -> match snd tc with
                             | TInt -> Dom.Int (Int.of_string c)
                             | TStr -> Str c
                             | TFloat -> Float (Float.of_string c)))
  else raise (Invalid_argument (Printf.sprintf "predicate %s has arity %d" name pred_sig.arity))

let add_event db evt = Set.add db evt

let to_string db =
  Etc.string_list_to_string (List.map ~f:Event.to_string (Set.elements db))

let to_json db =
  "[ " ^ (String.concat ~sep:", "
            (List.rev(Set.fold db ~init:[] ~f:(fun acc evt ->
                          Event.to_json evt :: acc)))) ^ "] "
