(*******************************************************************)
(*    This is part of Explanator2, it is distributed under the     *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Mtl
open Expl

val monitor: (expl -> expl -> bool) -> formula -> unit
