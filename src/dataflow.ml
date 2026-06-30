open Base
open MFOTL_lib

(* ------------------------------------------------------------------ *)
(* Data-flow cycle check (replaces the strict/non-strict termination    *)
(* gate).                                                               *)
(*                                                                      *)
(* Build a graph over *argument positions* E.i.  For a clause whose      *)
(* trigger mentions E(.. x@i ..) and whose effect is F(.. t@j ..) with x  *)
(* occurring in t, add an edge  E.i --> F.j, labelled "stable" iff t is   *)
(* a variable, a constant, or an application of stable functions only.   *)
(*                                                                      *)
(* Enforcement terminates iff no data-flow cycle passes through a        *)
(* non-stable edge (e.g. A(x) ⇒ A(x+1) — a self-loop through "+1" — is    *)
(* rejected, while A(x) ⇒ A(x) and A(x) ⇒ B(x+1) are fine).             *)
(* We detect this by computing the flow graph's SCCs and flagging any     *)
(* non-stable edge whose endpoints share an SCC.                         *)
(* ------------------------------------------------------------------ *)

module TF     = Tyformula
module Clause = Nformula.Clause
module Effect = Nformula.Effect

type violation = {
  from_event : string;
  from_pos   : int;
  to_event   : string;
  to_pos     : int;
}

(* A function symbol is "stable" iff the signature marks it strict.
   Unknown symbols are treated as non-stable (conservative). *)
let stable_func (f : string) : bool =
  try Sig.strict_of_func f with _ -> false

let rec term_stable (t : Tterm.t) : bool =
  match t.trm with
  | Var _ | Const _ -> true
  | App (f, args)   -> stable_func f && List.for_all args ~f:term_stable
  | _               -> false

(* Collect predicate atoms (name, arg-terms) occurring in a trigger formula. *)
let rec collect_atoms (f : TF.t) (acc : (string * Tterm.t list) list)
  : (string * Tterm.t list) list =
  match f.form with
  | Predicate (name, args) | Predicate' (name, args, _) -> (name, args) :: acc
  | Neg g | Exists (_, g) | Forall (_, g)
  | Prev (_, g) | Next (_, g) | Once (_, g) | Eventually (_, g)
  | Historically (_, g) | Always (_, g) | Type (g, _) | Label (_, g)
  | Agg (_, _, _, _, g) -> collect_atoms g acc
  | And (_, gs) | Or (_, gs) -> List.fold gs ~init:acc ~f:(fun acc g -> collect_atoms g acc)
  | Imp (_, g, h) | Since (_, _, g, h) | Until (_, _, g, h)
  | Let (_, _, _, g, h) | Let' (_, _, _, g, h) ->
    collect_atoms h (collect_atoms g acc)
  | TT | FF | EqConst _ -> acc

(* (event, arg-terms) for every effect of a clause. *)
let effect_targets (c : Clause.t) : (string * Tterm.t list) list =
  List.filter_map c.Clause.effects ~f:(function
      | Effect.Cau (r, a) | Effect.Sup (r, a)
      | Effect.EventuallyCau (_, r, a) | Effect.EventuallySup (_, r, a)
      | Effect.NextCau (_, r, a) | Effect.NextSup (_, r, a) -> Some (r, a)
      | Effect.NextTT _ -> None)

let run (clauses : Clause.t array) : violation list =
  (* node universe: (event, position) keyed as "ev@pos" *)
  let node_of = Hashtbl.create (module String) in
  let names   = ref [] in
  let key e i = Printf.sprintf "%s@%d" e i in
  let node e i =
    let k = key e i in
    match Hashtbl.find node_of k with
    | Some id -> id
    | None ->
      let id = Hashtbl.length node_of in
      Hashtbl.set node_of ~key:k ~data:id;
      names := (e, i) :: !names; id in
  (* collect edges first (so we know the node count), then build the graph *)
  let edges = ref [] in   (* (src_id, dst_id, stable) *)
  Array.iter clauses ~f:(fun c ->
      let atoms = collect_atoms (Nformula.Trigger.to_formula true c.Clause.trigger) [] in
      (* var name -> positions (event, i) where it occurs as a bare variable *)
      let var_pos = Hashtbl.create (module String) in
      List.iter atoms ~f:(fun (e, args) ->
          List.iteri args ~f:(fun i a ->
              match a.Tterm.trm with
              | Var (v, _) -> Hashtbl.add_multi var_pos ~key:v ~data:(e, i)
              | _ -> ()));
      List.iter (effect_targets c) ~f:(fun (fe, targs) ->
          List.iteri targs ~f:(fun j t ->
              let st = term_stable t in
              List.iter (Tterm.fv_list [t]) ~f:(fun (v, _) ->
                  match Hashtbl.find var_pos v with
                  | None -> ()
                  | Some occs ->
                    List.iter occs ~f:(fun (e, i) ->
                        edges := (node e i, node fe j, st) :: !edges)))));
  let n = Hashtbl.length node_of in
  let name_arr = Array.create ~len:n ("", 0) in
  List.iter !names ~f:(fun (e, i) ->
      name_arr.(Hashtbl.find_exn node_of (key e i)) <- (e, i));
  (* build graph (labels = stable flag) and find its SCCs *)
  let g = List.fold !edges ~init:(Graph_util.Graph.empty n)
      ~f:(fun acc (u, v, st) -> Graph_util.Graph.add_edge acc ~src:u ~lbl:st ~dst:v) in
  let _scc_count, scc_of = Graph_util.tarjan g in
  (* a non-stable edge inside an SCC closes a non-terminating cycle *)
  List.filter_map !edges ~f:(fun (u, v, st) ->
      if (not st) && scc_of.(u) = scc_of.(v) then
        let (fe, fp) = name_arr.(u) and (te, tp) = name_arr.(v) in
        Some { from_event = fe; from_pos = fp; to_event = te; to_pos = tp }
      else None)
  |> List.dedup_and_sort ~compare:(fun a b ->
      [%compare: string * int * string * int]
        (a.from_event, a.from_pos, a.to_event, a.to_pos)
        (b.from_event, b.from_pos, b.to_event, b.to_pos))

let violations_to_string (vs : violation list) : string =
  String.concat ~sep:"\n"
    (List.map vs ~f:(fun v ->
         Printf.sprintf
           "  non-stable data flow %s.%d → %s.%d lies on a dependency cycle \
            (enforcement may not terminate)"
           v.from_event v.from_pos v.to_event v.to_pos))
