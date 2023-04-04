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
    type t = string * const list  [@@deriving compare, sexp_of]
  end
  include T
  include Comparable.Make(T)
end

type t = int * (Event.t, Event.comparator_witness) Set.t

let db ts events = (int_of_string ts, Set.of_list (module Event) events)

let sig_table : (Pred.Sig.t, string) Hashtbl.t = Hashtbl.create (module Pred.Sig)

let event ts consts = (ts, consts)
