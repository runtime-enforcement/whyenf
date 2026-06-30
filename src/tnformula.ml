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
  (* Set by [Extraction.downgrade_filter_lets] when this let is only ever used
     in filter (membership-test) positions: the compiler then emits it as a
     `filter let` (its whole body becomes a boolean test) instead of a
     materialised, enumerable let, keeping the tables it would otherwise
     enumerate out of the per-time-point complexity. *)
  force_filter       : bool;
}

type let_map = (string, let_def, String.comparator_witness) Map.t

(** Everything the Enfflash compiler needs. *)
type t = {
  let_names : string list;
  let_map   : let_map;
  clauses   : Clause.t list;
  formula   : typed_t;
}

let clean_unused_lets (tnf : t) =
  let used_names = List.fold_right tnf.let_names
      ~init:(Set.union_list (module String) (List.map ~f:Clause.predicates tnf.clauses))
      ~f:(fun (name: string) (n: (string, String.comparator_witness) Set.t) ->
          let le = Map.find_exn tnf.let_map name in
          let n =
            if Set.mem n le.name || Set.mem n (le.name ^ "_pos")
            then Set.union n (Tyformula.predicates le.body_pos)
            else n in
          if Set.mem n (le.name ^ "_neg")
          then Set.union n (Tyformula.predicates (Option.value_exn le.body_neg_opt))
          else n) in
  { tnf with let_names = List.filter tnf.let_names ~f:(Set.mem used_names);
             let_map   = Map.filteri tnf.let_map ~f:(fun ~key ~data:_ ->
                 Set.mem used_names key
                 || Set.mem used_names (key ^ "_pos")
                 || Set.mem used_names (key ^ "_neg")) }
          
  
