open Base

open Nformula
open Tnformula

(* ------------------------------------------------------------------ *)
(* Let-context maps                                                     *)
(* ------------------------------------------------------------------ *)

(* [Map.fold] visits the lets in name order, not in definition order, so one
   pass can read a let whose entry is not computed yet (e.g. [Agg1] reading
   [Once0]): it would then stand for an "event" named after that let.  Repeat
   the pass until nothing changes; lets are not recursive, so this ends after
   at most as many passes as lets are nested. *)
let rec fixpoint ~equal f x =
  let y = f x in
  if equal x y then x else fixpoint ~equal f y

let maps_of_lets (m : let_map) =
  let equal_map = Map.equal Set.equal in
  let pred_map =
    fixpoint ~equal:equal_map (fun init ->
    Map.fold m
      ~init
      ~f:(fun ~key:_ ~data:le lets ->
          let preds = Tyformula.predicates ~lets le.body_pos in
          let lets = Map.update lets le.name (fun _ -> preds) in
          let lets = Map.update lets (le.name ^ "_pos") (fun _ -> preds) in
          match le.body_neg_opt with
          | Some body_neg ->
            Map.update lets (le.name ^ "_neg") (fun _ -> Tyformula.predicates ~lets body_neg)
          | None -> lets)) (Map.empty (module String)) in
  let mon_map, anti_mon_map =
    fixpoint ~equal:(fun (a, b) (c, d) -> equal_map a c && equal_map b d) (fun init ->
    Map.fold m
      ~init
      ~f:(fun ~key:_ ~data:le (let_ctxt_mon, let_ctxt_anti_mon) ->
          let mon, anti_mon =
            Tyformula.non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon le.body_pos in
          let let_ctxt_mon, let_ctxt_anti_mon =
            Map.update let_ctxt_mon le.name (fun _ -> mon),
            Map.update let_ctxt_anti_mon le.name (fun _ -> anti_mon) in
          let let_ctxt_mon, let_ctxt_anti_mon =
            Map.update let_ctxt_mon (le.name ^ "_pos") (fun _ -> mon),
            Map.update let_ctxt_anti_mon (le.name ^ "_pos") (fun _ -> anti_mon) in
          match le.body_neg_opt with
          | Some body_neg ->
            let mon, anti_mon =
              Tyformula.non_monotone_predicates ~let_ctxt_mon ~let_ctxt_anti_mon body_neg in
            Map.update let_ctxt_mon (le.name ^ "_neg") (fun _ -> mon),
            Map.update let_ctxt_anti_mon (le.name ^ "_neg") (fun _ -> anti_mon)
          | None -> let_ctxt_mon, let_ctxt_anti_mon))
      (Map.empty (module String), Map.empty (module String)) in
  pred_map, mon_map, anti_mon_map

(* ================================================================== *)
(* Event splitting                                                     *)
(*                                                                     *)
(* Partition the *clauses* of a policy into groups that can be run by  *)
(* independent sub-enforcers (Clause Dependency Graph + heuristics).   *)
(* ================================================================== *)

module EventSplit = struct

  (* ------------------------------------------------------------------ *)
  (* Action type and effect extraction                                    *)
  (* ------------------------------------------------------------------ *)

  type action = Cau | Sup

  let equal_action a b = match a, b with
    | Cau, Cau | Sup, Sup -> true
    | _ -> false

  (* Extract the (predicate, action) label from an Effect.t, if any. *)
  let effect_action : Effect.t -> (string * action) option = function
    | Cau (r, _) | EventuallyCau (_, r, _) | NextCau (_, r, _) -> Some (r, Cau)
    | Sup (r, _) | EventuallySup (_, r, _) | NextSup (_, r, _) -> Some (r, Sup)
    | NextTT _ -> None

  (* ------------------------------------------------------------------ *)
  (* Graph + Tarjan SCC + condensation are provided generically by        *)
  (* [Graph_util]; here we only fix the concrete edge-label type carried  *)
  (* by the Clause Dependency Graph (which predicate^action created the   *)
  (* dependency).                                                         *)
  (* ------------------------------------------------------------------ *)

  type edge_label = {
    pred   : string;
    action : action;
  }

  module Graph       = Graph_util.Graph
  let tarjan         = Graph_util.tarjan
  let condensation   = Graph_util.condensation

  (* ------------------------------------------------------------------ *)
  (* Build CDG (possibly filtered by monotonicity)                        *)
  (*                                                                      *)
  (* Emits one labeled edge per (clause i, pred^action, clause j) triple *)
  (* that satisfies e ∈ Triggers(c_j) ∧ e^action ∈ Effects(c_i).       *)
  (* With ~filtered:true, edges where the effect is monotone-harmless are *)
  (* dropped (CDG* from the paper).                                       *)
  (* ------------------------------------------------------------------ *)

  let build_cdg ~filtered ~lets ~let_ctxt_mon ~let_ctxt_anti_mon
      (clauses : Clause.t array) : edge_label Graph.t =
    let n = Array.length clauses in
    let trig_preds =
      Array.init n ~f:(fun j ->
          Clause.trigger_predicates ~lets clauses.(j)) in
    let trig_mon, trig_anti_mon =
      if filtered then
        let pairs =
          Array.init n ~f:(fun j ->
              Clause.trigger_non_monotone_predicates
                ~let_ctxt_mon ~let_ctxt_anti_mon clauses.(j)) in
        Array.map pairs ~f:fst, Array.map pairs ~f:snd
      else
        Array.init n ~f:(fun _ -> Set.empty (module String)),
        Array.init n ~f:(fun _ -> Set.empty (module String))
    in
    let eff_events =
      Array.init n ~f:(fun i ->
          List.filter_map clauses.(i).effects ~f:effect_action) in
    let g = ref (Graph.empty n) in
    for i = 0 to n - 1 do
      for j = 0 to n - 1 do
        List.iter eff_events.(i) ~f:(fun (pred, action) ->
            if Set.mem trig_preds.(j) pred
            && (if filtered then
                  (* Synthetic internal events (Cau_/Sup_ helpers) always keep
                     their edges — their cross-clause deps are real and must
                     not be eliminated by the monotonicity filter. *)
                  let is_synthetic p =
                    String.is_prefix p ~prefix:"Cau_"
                    || String.is_prefix p ~prefix:"Sup_" in
                  is_synthetic pred ||
                  (match action with
                   | Cau -> not (Set.mem trig_mon.(j) pred)
                   | Sup -> not (Set.mem trig_anti_mon.(j) pred))
                else true)
            then
              g := Graph.add_edge !g ~src:i
                  ~lbl:{ pred; action } ~dst:j)
      done
    done;
    !g

end  (* module EventSplit *)
