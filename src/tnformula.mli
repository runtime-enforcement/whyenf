open Base
open MFOTL_lib
open Tyformula
open Nformula

type let_def = {
  name               : string;
  enftype_opt        : Enftype.t option;
  args               : (Tterm.TypedVar.t * Dom.tt option) list;
  body_pos           : typed_t;
  body_neg_opt       : typed_t option;
  switch_pos_opt     : Switch.t option;
  switch_neg_opt     : Switch.t option;
  clauses            : Clause.t list;
  filter_trigger_opt : Trigger.t option;
}

type let_map = (string, let_def, String.comparator_witness) Map.t

(** Everything the Enfflash compiler needs. *)
type t = {
  let_names : string list;
  let_map   : let_map;
  clauses   : Clause.t list;
  formula   : typed_t;
}

val clean_unused_lets : t -> t
