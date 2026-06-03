open Base
open MFOTL_lib

open Tyformula

module Var = Tterm.TypedVar
module Term = Tterm

(* ------------------------------------------------------------------ *)
(* Trigger, Clause, Switch, GuardInfo                                   *)
(* (shared IR between enforceability, extraction, and compilation)     *)
(* ------------------------------------------------------------------ *)

module Trigger = struct
  type t = {
    guards : Tyformula.t list list; (* DNF *)
    filter : Tyformula.t;
  } [@@deriving equal]

  let make (filter : Tyformula.t) : t = { guards = []; filter }

  let to_string (trig : t) : string =
    Printf.sprintf "{ guards = [%s];\n  filter = %s }"
      (Etc.string_list_to_string (List.map trig.guards ~f:(
           fun fs -> "[" ^ Etc.string_list_to_string (List.map ~f:Tyformula.to_string fs))))
      (Tyformula.to_string trig.filter)

  let to_formula (pos : bool) (trig : t) : Tyformula.t =
    let filter = trig.filter |> Tyformula.push_negs |> Tyformula.ac_simplify in
    match trig.guards with
    | [] -> filter
    | guards ->
      let guard_f = Tyformula.make_dummy (Or (N, List.map ~f:(
          fun fs -> Tyformula.make_dummy (And (N, fs))) guards)) in
      if pos then
        Tyformula.make_dummy (And (N, [guard_f; filter]))
      else
        Tyformula.make_dummy (Imp (N, guard_f, filter))
end

module Effect = struct
  type t =
    | Cau of string * Tterm.t list
    | Sup of string * Tterm.t list
    | EventuallyCau of Interval.t * string * Tterm.t list
    | EventuallySup of Interval.t * string * Tterm.t list
    | NextCau of Interval.t list * string * Tterm.t list
    | NextTT  of Interval.t list
    | NextSup of Interval.t list * string * Tterm.t list

  let eventualize itv = function
    | Cau (r, trms) -> EventuallyCau (itv, r, trms)
    | Sup (r, trms) -> EventuallySup (itv, r, trms)

  let nextize itvs = function
    | Cau (r, trms) -> NextCau (itvs, r, trms)
    | Sup (r, trms) -> NextSup (itvs, r, trms)

  let to_string = function
    | Cau (r, trms) -> Printf.sprintf "%s(%s)" r (Tterm.list_to_string trms)
    | Sup (r, trms) -> Printf.sprintf "¬%s(%s)" r (Tterm.list_to_string trms)
    | EventuallyCau (itv, r, trms) -> Printf.sprintf "◊%s %s(%s)" (Interval.to_string itv) r (Tterm.list_to_string trms)
    | NextTT itvs -> Printf.sprintf "○%s ⊤" (Etc.string_list_to_string (List.map ~f:Interval.to_string itvs))
    | NextCau (itvs, r, trms) -> Printf.sprintf "○%s %s(%s)"
                                   (Etc.string_list_to_string (List.map ~f:Interval.to_string itvs))
                                   r (Tterm.list_to_string trms)
    | NextSup (itvs, r, trms) -> Printf.sprintf "○%s ¬%s(%s)"
                                   (Etc.string_list_to_string (List.map ~f:Interval.to_string itvs))
                                   r (Tterm.list_to_string trms)

  let rec to_typed =
    let info enftype = { Tyformula.TypedInfo.dummy with enftype = Enftype.cau } in
    let rec add_next f = function
      | [] -> f
      | itv::itvs -> { form = Next (itv, add_next f itvs); info = info Enftype.cau } in
    function
    | Cau (r, trms) -> { form = Predicate (r, trms)
                       ; info = info Enftype.cau }
    | Sup (r, trms) -> { form = Neg ({ form = Predicate (r, trms); info = info Enftype.sup })
                       ; info = info Enftype.cau }
    | EventuallyCau (itv, r, trms) -> { form = Eventually (itv, { form = Predicate (r, trms); info = info Enftype.cau })
                                      ; info = info Enftype.cau }
    | NextTT itvs -> add_next { form = TT; info = info Enftype.cau } itvs
    | NextCau (itvs, r, trms) -> add_next (to_typed (Cau (r, trms))) itvs
    | NextSup (itvs, r, trms) -> add_next (to_typed (Sup (r, trms))) itvs

  let map_predicate ~f = function
    | Cau (r, trms) -> Cau (f true r, trms)
    | Sup (r, trms) -> Sup (f false r, trms)
    | EventuallyCau (itv, r, trms) -> EventuallyCau (itv, f true r, trms)
    | EventuallySup (itv, r, trms) -> EventuallySup (itv, f false r, trms)
    | NextTT n -> NextTT n
    | NextCau (n, r, trms) -> NextCau (n, f true r, trms)
    | NextSup (n, r, trms) -> NextSup (n, f false r, trms)

  let fvs es = fvs (List.map ~f:to_typed es)
    
end

module Clause = struct
  type t = {
    trigger : Trigger.t;
    effects : Effect.t list;
  }

  let to_string (c : t) : string =
    Printf.sprintf "{ trigger = %s;\n  effects = [%s] }"
      (Trigger.to_string c.trigger)
      (Etc.string_list_to_string (List.map ~f:Effect.to_string c.effects))
end

module Switch = struct
  type t =
    | Once  of Trigger.t
    | Prev  of Trigger.t
    | Since of Trigger.t * Trigger.t
    | Now   of Trigger.t

  let to_string : t -> string = function
    | Once  trigger -> "⧫(" ^ Trigger.to_string trigger ^ ")"
    | Prev  trigger -> "●(" ^ Trigger.to_string trigger ^ ")"
    | Since (ltrigger, rtrigger) ->
      "(" ^ Trigger.to_string ltrigger ^ ") S (" ^ Trigger.to_string rtrigger ^ ")"
    | Now   trigger -> Trigger.to_string trigger

  let to_formula (pos : bool) : t -> Tyformula.t = function
    | Once  trigger -> Tyformula.make_dummy (Once  (Interval.full, Trigger.to_formula pos trigger))
    | Prev  trigger -> Tyformula.make_dummy (Prev  (Interval.full, Trigger.to_formula pos trigger))
    | Since (ltrigger, rtrigger) ->
      Tyformula.make_dummy (Since (
          N, Interval.full,
          Trigger.to_formula (not pos) ltrigger,
          Trigger.to_formula pos rtrigger))
    | Now   trigger -> Trigger.to_formula pos trigger
end

module GuardInfo = struct
  type t = {
    switch_pos_opt : Switch.t option;
    body_str       : string;
  }
  type map = (string, t, String.comparator_witness) Map.t
end

(* ------------------------------------------------------------------ *)
(* Constraints                                                          *)
(* ------------------------------------------------------------------ *)

module Constraints = struct

  open Enftype.Constraint

  type constr =
    | CTT
    | CFF
    | CGeq of string * Enftype.t
    | CLeq of string * Enftype.t
    | CConj of constr list
    | CDisj of constr list [@@deriving equal, compare, sexp_of]

  let geq s t = CGeq (s, t)
  let leq s t = CLeq (s, t)

  let rec ac_flatten = function
    | CConj cs ->
      let cs = List.map ~f:ac_flatten cs in
      let cs = List.concat_map cs ~f:(function CConj xs -> xs | CTT -> [] | c -> [c]) in
      (match cs with [] -> CTT | [c] -> c | _ -> CConj cs)
    | CDisj cs ->
      let cs = List.map ~f:ac_flatten cs in
      let cs = List.concat_map cs ~f:(function CDisj xs -> xs | CFF -> [] | c -> [c]) in
      (match cs with [] -> CFF | [c] -> c | _ -> CDisj cs)
    | c -> c

  let rec ac_simplify = function
    | CConj cs ->
      let cs = List.map ~f:ac_simplify cs in
      let f_has_ff = function CFF -> true | _ -> false in
      (if List.exists cs ~f:f_has_ff then
         CFF
       else
         match ac_flatten (CConj cs) with
         | CConj cs' ->
           let cs', _ =
             let is_weaker_clause c ds =
               let isin d = List.for_all ~f:(List.mem d ~equal:equal_constr) in
               let d = match c with CDisj d -> d | _ -> [c] in
               d, List.exists ds ~f:(isin d) in
             let f c (cs, ds) =
               let d, b = is_weaker_clause c ds in
               if b then (cs, ds) else (c::cs, d::ds) in
             List.fold_right cs' ~init:([], []) ~f
           in
           CConj cs'
         | c -> c)
    | CDisj cs ->
      let cs = List.map ~f:ac_simplify cs in
      let f_has_tt = function CTT -> true | _ -> false in
      (if List.exists cs ~f:f_has_tt then
         CTT
       else
         match ac_flatten (CDisj cs) with
         | CDisj cs' ->
           let cs', _ =
             let is_weaker_clause c ds =
               let isin d = List.for_all ~f:(List.mem d ~equal:equal_constr) in
               let d = match c with CConj d -> d | _ -> [c] in
               d, List.exists ds ~f:(isin d) in
             let f c (cs, ds) =
               let d, b = is_weaker_clause c ds in
               if b then (cs, ds) else (c::cs, d::ds) in
             List.fold_right cs' ~init:([], []) ~f
           in
           CDisj cs'
         | c -> c)
    | c -> c

  let rec cartesian a = function
      [] -> []
    | h::t -> (List.map a ~f:(fun x -> (x, h))) @ cartesian a t

  let try_merge (a, b) =
    try Some (Map.merge a b ~f:merge)
    with CannotMerge _k -> None

  let rec to_string_rec l = function
    | CTT -> Printf.sprintf "⊤"
    | CFF -> Printf.sprintf "⊥"
    | CGeq (s, t) -> Printf.sprintf "t(%s) ≽ %s" s (Enftype.to_string t)
    | CLeq (s, t) -> Printf.sprintf "%s ≽ t(%s)" (Enftype.to_string t) s
    | CConj cs -> Printf.sprintf (Etc.paren l 4 "%s")
                    (String.concat ~sep:" ∧ " (List.map ~f:(to_string_rec 4) cs))
    | CDisj cs -> Printf.sprintf (Etc.paren l 3 "%s")
                    (String.concat ~sep:" ∨ " (List.map ~f:(to_string_rec 3) cs))

  let to_string = to_string_rec 0

  let rec solve c : (string, Enftype.Constraint.t, Base.String.comparator_witness) Base.Map.t list =
    let r = match c with
      | CTT -> [Map.empty (module String)]
      | CFF -> []
      | CGeq (s, t) -> [Map.singleton (module String) s (lower t)]
      | CLeq (s, t) -> [Map.singleton (module String) s (upper t)]
      | CConj [] -> [Map.empty (module String)]
      | CConj (c::cs) ->
        let f sol d = List.filter_map (cartesian sol (solve d)) ~f:try_merge in
        List.fold_left cs ~init:(solve c) ~f
      | CDisj cs -> List.concat_map cs ~f:solve
    in
    r

end

module Verdict = Verdict.Make(Tyformula)

type enf_sols = (Clause.t list * Constraints.constr) Verdict.v

type let_def = {
  name               : string;
  enftype_opt        : Enftype.t option;
  args               : (Var.t * Dom.tt option) list;
  body               : t;
  origin             : t;     (* original formula fragment before transformation *)
  cau_sols           : enf_sols;
  sup_sols           : enf_sols;
  switch_pos_opt     : Switch.t option;
  switch_neg_opt     : Switch.t option;
  filter_trigger_opt : Trigger.t option;
}

type let_map = (string, let_def, String.comparator_witness) Map.t

type t = {
  let_names : string list;
  let_map   : let_map;
  sols      : enf_sols;
}

