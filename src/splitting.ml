open Base

open Nformula
open Tnformula

(* ------------------------------------------------------------------ *)
(* Let-context maps                                                     *)
(* ------------------------------------------------------------------ *)

let maps_of_lets (m : let_map) =
  let pred_map =
    Map.fold m
      ~init:(Map.empty (module String))
      ~f:(fun ~key:_ ~data:le lets ->
          let preds = Tyformula.predicates ~lets le.body_pos in
          let lets = Map.update lets le.name (fun _ -> preds) in
          let lets = Map.update lets (le.name ^ "_pos") (fun _ -> preds) in
          match le.body_neg_opt with
          | Some body_neg ->
            Map.update lets (le.name ^ "_neg") (fun _ -> Tyformula.predicates ~lets body_neg)
          | None -> lets) in
  let mon_map, anti_mon_map =
    Map.fold m
      ~init:(Map.empty (module String), Map.empty (module String))
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
          | None -> let_ctxt_mon, let_ctxt_anti_mon) in
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
(* Graph submodule                                                      *)
(*                                                                      *)
(* Vertices are non-negative integers 0..n-1.                          *)
(* Each directed edge carries an [edge_label] that records which        *)
(* predicate and enforcement action (Cau/Sup) created the dependency.  *)
(* ------------------------------------------------------------------ *)

module Graph = struct

  type edge_label = {
    pred   : string;
    action : action;
  }

  (* adj maps each source vertex to the list of (label, destination) pairs.
     Invariant: no two entries in adj[v] share the same (pred, action, dst). *)
  type t = {
    n   : int;
    adj : (int, (edge_label * int) list, Int.comparator_witness) Map.t;
  }

  let empty n = { n; adj = Map.empty (module Int) }

  let labeled_successors g v =
    Option.value (Map.find g.adj v) ~default:[]

  (* Successor vertices, deduplicated (labels dropped). *)
  let successors g v =
    List.dedup_and_sort ~compare:Int.compare
      (List.map (labeled_successors g v) ~f:snd)

  (* Add the edge (src --lbl--> dst), silently ignoring exact duplicates. *)
  let add_edge g ~src ~(lbl : edge_label) ~dst =
    { g with adj =
        Map.update g.adj src ~f:(fun prev ->
          let prev = Option.value prev ~default:[] in
          if List.exists prev ~f:(fun (l, d) ->
              d = dst
              && String.equal l.pred lbl.pred
              && equal_action l.action lbl.action)
          then prev
          else (lbl, dst) :: prev) }

  (* Reverse all edges, preserving labels. *)
  let transpose g =
    { n = g.n;
      adj =
        Map.fold g.adj ~init:(Map.empty (module Int))
          ~f:(fun ~key:src ~data:succs acc ->
            List.fold succs ~init:acc ~f:(fun acc (lbl, dst) ->
              Map.update acc dst ~f:(fun prev ->
                let prev = Option.value prev ~default:[] in
                (lbl, src) :: prev))) }

  (* Vertices with no outgoing edges. *)
  let sinks g =
    List.filter (List.init g.n ~f:Fn.id)
      ~f:(fun v -> List.is_empty (successors g v))

  (* All vertices reachable from [start] (including [start] itself). *)
  let reachable g start =
    let rec dfs visited = function
      | [] -> visited
      | v :: rest ->
        if Set.mem visited v then dfs visited rest
        else dfs (Set.add visited v) (successors g v @ rest)
    in
    dfs (Set.empty (module Int)) [start]

  (* Flat list of all (src, label, dst) triples. *)
  let edges g =
    Map.fold g.adj ~init:[]
      ~f:(fun ~key:src ~data:succs acc ->
        List.map succs ~f:(fun (lbl, dst) -> (src, lbl, dst)) @ acc)

  let to_string g =
    let action_str = function Cau -> "C" | Sup -> "S" in
    let edge_strs =
      List.map (edges g) ~f:(fun (i, lbl, j) ->
        Printf.sprintf "%d -[%s^%s]-> %d" i lbl.pred (action_str lbl.action) j)
    in
    Printf.sprintf "Graph(%d vertices, [%s])" g.n
      (String.concat ~sep:"; " edge_strs)

end

(* ------------------------------------------------------------------ *)
(* Tarjan's SCC (uses Graph.successors for unlabeled traversal)        *)
(* Returns (scc_count, scc_of) where scc_of.(v) = SCC id of v.        *)
(* Tarjan outputs SCCs in reverse topological order of the condensation*)
(* so the first SCC finished is a sink of the condensation.            *)
(* ------------------------------------------------------------------ *)

let tarjan (g : Graph.t) : int * int array =
  let n       = g.n in
  let index   = Array.create ~len:n (-1) in
  let lowlink = Array.create ~len:n 0 in
  let on_stk  = Array.create ~len:n false in
  let scc_of  = Array.create ~len:n (-1) in
  let stk     = ref [] in
  let cnt     = ref 0 in
  let n_sccs  = ref 0 in
  let rec sc v =
    index.(v)   <- !cnt;
    lowlink.(v) <- !cnt;
    cnt         := !cnt + 1;
    stk         := v :: !stk;
    on_stk.(v)  <- true;
    List.iter (Graph.successors g v) ~f:(fun w ->
      if index.(w) = -1 then begin
        sc w;
        lowlink.(v) <- Int.min lowlink.(v) lowlink.(w)
      end else if on_stk.(w) then
        lowlink.(v) <- Int.min lowlink.(v) index.(w));
    if lowlink.(v) = index.(v) then begin
      let id = !n_sccs in
      n_sccs := !n_sccs + 1;
      let rec pop () =
        match !stk with
        | [] -> assert false
        | w :: rest ->
          stk := rest; on_stk.(w) <- false; scc_of.(w) <- id;
          if w <> v then pop ()
      in
      pop ()
    end
  in
  for v = 0 to n - 1 do
    if index.(v) = -1 then sc v
  done;
  !n_sccs, scc_of

(* Build the condensation DAG; edges carry the label from the original edge. *)
let condensation ~scc_count ~(scc_of : int array) (g : Graph.t) : Graph.t =
  List.fold (Graph.edges g) ~init:(Graph.empty scc_count)
    ~f:(fun acc (u, lbl, v) ->
      let su = scc_of.(u) and sv = scc_of.(v) in
      if su = sv then acc
      else Graph.add_edge acc ~src:su ~lbl ~dst:sv)

(* ------------------------------------------------------------------ *)
(* Build CDG (possibly filtered by monotonicity)                        *)
(*                                                                      *)
(* Emits one labeled edge per (clause i, pred^action, clause j) triple *)
(* that satisfies e ∈ Triggers(c_j) ∧ e^action ∈ Effects(c_i).       *)
(* With ~filtered:true, edges where the effect is monotone-harmless are *)
(* dropped (CDG* from the paper).                                       *)
(* ------------------------------------------------------------------ *)

let build_cdg ~filtered ~lets ~let_ctxt_mon ~let_ctxt_anti_mon
    (clauses : Clause.t array) : Graph.t =
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
                 ~lbl:{ Graph.pred; action } ~dst:j)
    done
  done;
  !g

(* ------------------------------------------------------------------ *)
(* Algorithm 1: Largest covering                                        *)
(* ------------------------------------------------------------------ *)

(* Returns (scc_count, scc_of, components) where each component is
   (generating_sink_scc_id, set_of_original_clause_indices). *)
let largest_covering (g : Graph.t)
  : int * int array * (int * (int, Int.comparator_witness) Set.t) list =
  let scc_count, scc_of = tarjan g in
  let cond   = condensation ~scc_count ~scc_of g in
  let cond_T = Graph.transpose cond in
  let sink_sccs = Graph.sinks cond in
  let components =
    List.map sink_sccs ~f:(fun s ->
      let ancestor_sccs = Graph.reachable cond_T s in
      let verts =
        Array.foldi scc_of ~init:(Set.empty (module Int))
          ~f:(fun v acc sv ->
            if Set.mem ancestor_sccs sv then Set.add acc v else acc) in
      (s, verts))
  in
  scc_count, scc_of, components

(* ------------------------------------------------------------------ *)
(* Merge heuristic                                                      *)
(* ------------------------------------------------------------------ *)

let rec batches_of n = function
  | [] -> []
  | xs ->
    let batch, rest = List.split_n xs n in
    batch :: batches_of n rest

(* aggressivity = 0 : return the largest covering unchanged.
   aggressivity = k : merge batches of k components into one group.
     Components are first ordered so that those sharing the same backbone
     (same ancestor-SCC set, differing only in their generating sink SCC)
     are adjacent — those merge first and most cheaply, since they duplicate
     no extra backbone clauses. Once a backbone-group is exhausted, batching
     continues across backbones, so the group count decreases monotonically
     from |components| (k <= 1) down to 1 (k >= |components|). *)

let apply_heuristic ~aggressivity ~(scc_of : int array)
    (components : (int * (int, Int.comparator_witness) Set.t) list)
  : (int, Int.comparator_witness) Set.t list =
  if aggressivity <= 0 then
    List.map components ~f:snd
  else begin
    let backbone (s, comp) =
      Set.filter comp ~f:(fun v -> not (Int.equal scc_of.(v) s)) in
    let add_to_groups groups entry =
      let bb = backbone entry in
      let rec go = function
        | [] -> [(bb, [entry])]
        | (bb', grp) :: rest ->
          if Set.equal bb bb' then (bb', grp @ [entry]) :: rest
          else (bb', grp) :: go rest
      in
      go groups
    in
    let groups = List.fold components ~init:[] ~f:add_to_groups in
    (* Flatten, keeping same-backbone components adjacent, then batch globally
       so that high aggressivity can also merge across distinct backbones. *)
    let ordered = List.concat_map groups ~f:(fun (_, grp) -> grp) in
    List.map (batches_of aggressivity ordered) ~f:(fun batch ->
      Set.union_list (module Int) (List.map batch ~f:snd))
  end

(* ------------------------------------------------------------------ *)
(* Balanced partition heuristic                                         *)
(*                                                                      *)
(* Instead of fixing a merge batch size, fix the *number* of groups [k] *)
(* and distribute the components over [k] bins so that the per-group    *)
(* clause count (the cardinality of the union of the bin's components)  *)
(* is as homogeneous as possible.                                       *)
(*                                                                      *)
(* Each component is closed under the dependency relation (sink + all   *)
(* its ancestors), so the union of any set of components is still a     *)
(* valid, self-contained enforcement group. We can therefore assign     *)
(* whole components to bins freely.                                     *)
(*                                                                      *)
(* Greedy LPT (longest-processing-time-first): process components from  *)
(* largest to smallest and drop each into the bin that would end up     *)
(* with the fewest clauses (smallest resulting union). Shared backbone  *)
(* clauses overlap, so the resulting union is often smaller than the    *)
(* naive sum, and the max-loaded bin is kept small.                     *)
(* ------------------------------------------------------------------ *)

let balanced_partition ~num_groups
    (components : (int * (int, Int.comparator_witness) Set.t) list)
  : (int, Int.comparator_witness) Set.t list =
  let k = max 1 num_groups in
  let comps =
    List.map components ~f:snd
    |> List.sort ~compare:(fun a b -> Int.compare (Set.length b) (Set.length a)) in
  let bins = Array.create ~len:k (Set.empty (module Int)) in
  List.iter comps ~f:(fun comp ->
    (* pick the bin minimising the resulting union size; tie-break on the
       bin that is currently smallest so load stays even. *)
    let best = ref 0 and best_union = ref Int.max_value and best_cur = ref Int.max_value in
    for i = 0 to k - 1 do
      let resulting = Set.length (Set.union bins.(i) comp) in
      let current   = Set.length bins.(i) in
      if resulting < !best_union
      || (resulting = !best_union && current < !best_cur)
      then begin best := i; best_union := resulting; best_cur := current end
    done;
    bins.(!best) <- Set.union bins.(!best) comp);
  Array.to_list bins |> List.filter ~f:(fun s -> not (Set.is_empty s))

(* ------------------------------------------------------------------ *)
(* Public API                                                           *)
(* ------------------------------------------------------------------ *)

(** Build the (possibly filtered) Clause Dependency Graph for [tnf].
    Vertices are clause indices into [tnf.clauses]; each edge carries
    the predicate and action (Cau/Sup) that creates the dependency. *)
let clause_dep_graph ?(filtered = false) (tnf : Tnformula.t) : Graph.t =
  let lets, let_ctxt_mon, let_ctxt_anti_mon = maps_of_lets tnf.let_map in
  let clauses = Array.of_list tnf.clauses in
  build_cdg ~filtered ~lets ~let_ctxt_mon ~let_ctxt_anti_mon clauses

(** [split tnf] returns a list of groups of clause indices (into
    [tnf.clauses]) to be enforced by independent parallel enforcers.

    ~filtered:true  uses CDG* (monotonicity-aware edge filtering).
    ~num_groups:k (k > 0) ignores [aggressivity] and instead balances the
      components into exactly (at most) [k] groups with homogeneous clause
      counts (see [balanced_partition]).
    ~aggressivity:0 returns the largest covering (most parallelism).
    ~aggressivity:k merges batches of k same-backbone components. *)
let split ?(filtered = false) ?(aggressivity = 0) ?(num_groups = 0) (tnf : Tnformula.t)
  : int list list =
  let g = clause_dep_graph ~filtered tnf in
  if g.Graph.n = 0 then []
  else begin
    let _scc_count, scc_of, components = largest_covering g in
    let groups =
      if num_groups > 0 then balanced_partition ~num_groups components
      else apply_heuristic ~aggressivity ~scc_of components in
    List.map groups ~f:Set.to_list
  end

end  (* module EventSplit *)

(* ================================================================== *)
(* Data splitting                                                      *)
(*                                                                     *)
(* A complementary axis: keep the whole policy, but partition the      *)
(* *event stream* by hashing field values so independent shards        *)
(* process disjoint data in parallel.  Soundness holds only along      *)
(* axes where events never interact — the connected components of a    *)
(* graph whose nodes are base-event fields and whose edges link fields *)
(* bound by a common variable.                                         *)
(*                                                                     *)
(* This module currently provides the *analysis* (build the graph and  *)
(* return its components); CLI selection, manifest routing rules and    *)
(* the Rust hash-router are a planned follow-up.                        *)
(* ================================================================== *)

module DataSplit = struct

  open Tyformula

  module Var  = Tterm.TypedVar
  module Term = Tterm

  (* A graph node is a *field* of a base event: (event_name, position).
     Encoded as "ev#i".  Variable idents (used only as connectors in the
     union-find) are encoded as "$ident" to keep the namespaces disjoint. *)
  let field_key ev i = Printf.sprintf "%s#%d" ev i
  let ident_key id   = "$" ^ id

  let decode_field key =
    match String.lsplit2 key ~on:'#' with
    | Some (ev, i) -> ev, Int.of_string i
    | None         -> key, 0

  (* "Event.field" using the signature's argument names where available. *)
  let field_name key =
    let ev, i = decode_field key in
    match (try Some (Sig.vars_of_pred ev) with _ -> None) with
    | Some names when i >= 0 && i < List.length names ->
      Printf.sprintf "%s.%s" ev (List.nth_exn names i)
    | _ -> Printf.sprintf "%s.%d" ev i

  (* ---- Pass 1: collect the formal-parameter idents of every let-def. ---- *)
  let collect_let_params (f : t) : (string, string array, String.comparator_witness) Map.t =
    let rec go acc (f : t) =
      match f.form with
      | Let (name, _, params, body, cont) | Let' (name, _, params, body, cont) ->
        let acc = Map.set acc ~key:name
            ~data:(Array.of_list (List.map params ~f:(fun (v, _) -> Var.ident v))) in
        go (go acc body) cont
      | Predicate' (_, _, g)
      | Neg g | Prev (_, g) | Next (_, g) | Once (_, g) | Eventually (_, g)
      | Historically (_, g) | Always (_, g) | Type (g, _) | Label (_, g)
      | Exists (_, g) | Forall (_, g)
      | Agg (_, _, _, _, g) | Top (_, _, _, _, g) -> go acc g
      | And (_, gs) | Or (_, gs) -> List.fold gs ~init:acc ~f:go
      | Imp (_, g, h) | Since (_, _, g, h) | Until (_, _, g, h) -> go (go acc g) h
      | Predicate _ | TT | FF | EqConst _ -> acc
    in
    go (Map.empty (module String)) f

  type raw = {
    mutable var_occ      : (string * string) list;  (* (field_key, ident_key) for base var fields *)
    mutable base_taint   : (string, String.comparator_witness) Set.t;     (* directly tainted fields *)
    mutable call_edges   : (string * string) list;  (* (actual ident_key, param ident_key) *)
    mutable app_params   : (string, String.comparator_witness) Set.t;     (* param idents fed a computed term *)
  }

  (* A field/parameter occurrence is one of:
       - a variable    → a graph node / connector edge,
       - a constant     → ignored: a constant in a field position is just a
         per-event filter, not a binding, and does not tie the field to any
         partitioning axis (each shard runs the whole policy, so the filter
         still applies wherever the event lands),
       - any other term (function application, operator, projection, …) → tainted:
         the value is *derived* from other variables, so the field cannot be
         assigned to a single hash axis and must be broadcast. *)
  let is_computed t = (not (Term.is_var t)) && (not (Term.is_const t))

  (* ---- Pass 2: walk the formula collecting occurrences and call edges. ---- *)
  let collect (letparams : (string, string array, String.comparator_witness) Map.t) (f : t) : raw =
    let r = { var_occ = []; base_taint = Set.empty (module String);
              call_edges = []; app_params = Set.empty (module String) } in
    let record_base name terms =
      List.iteri terms ~f:(fun i t ->
        let fk = field_key name i in
        match Term.unvar_opt t with
        | Some v -> r.var_occ <- (fk, ident_key (Var.ident v)) :: r.var_occ
        | None   -> if is_computed t then r.base_taint <- Set.add r.base_taint fk) in
    let record_call params terms =
      List.iteri terms ~f:(fun i t ->
        if i < Array.length params then
          let pk = ident_key params.(i) in
          match Term.unvar_opt t with
          | Some v -> r.call_edges <- (ident_key (Var.ident v), pk) :: r.call_edges
          | None   -> if is_computed t then r.app_params <- Set.add r.app_params pk) in
    let handle_pred name terms =
      match Map.find letparams name with
      | Some params -> record_call params terms   (* call to a let-def *)
      | None        -> record_base name terms      (* base (log) event *) in
    let rec go (f : t) =
      match f.form with
      | Predicate (name, terms) -> handle_pred name terms
      | Predicate' (name, terms, g) -> handle_pred name terms; go g
      | Let (_, _, _, body, cont) | Let' (_, _, _, body, cont) -> go body; go cont
      | Neg g | Prev (_, g) | Next (_, g) | Once (_, g) | Eventually (_, g)
      | Historically (_, g) | Always (_, g) | Type (g, _) | Label (_, g)
      | Exists (_, g) | Forall (_, g)
      | Agg (_, _, _, _, g) | Top (_, _, _, _, g) -> go g
      | And (_, gs) | Or (_, gs) -> List.iter gs ~f:go
      | Imp (_, g, h) | Since (_, _, g, h) | Until (_, _, g, h) -> go g; go h
      | TT | FF | EqConst _ -> ()
    in
    go f; r

  (* ---- Union-find over field/ident keys, then extract components. ---- *)
  let components (f : t) : string list list * string list =
    let letparams = collect_let_params f in
    let r = collect letparams f in
    (* A field is tainted iff it ever holds a computed (function/operator) term
       directly, or such a term flowed into the let-parameter it is bound to.
       Constants are not tainting — they are ignored entirely (see [is_computed]). *)
    let tainted =
      List.fold r.var_occ ~init:r.base_taint ~f:(fun acc (fk, idk) ->
          if Set.mem r.app_params idk then Set.add acc fk else acc) in
    let parent : (string, string) Hashtbl.t = Hashtbl.create (module String) in
    let rec find x =
      match Hashtbl.find parent x with
      | None -> x
      | Some p -> let root = find p in Hashtbl.set parent ~key:x ~data:root; root in
    let union a b =
      let ra = find a and rb = find b in
      if not (String.equal ra rb) then Hashtbl.set parent ~key:ra ~data:rb in
    (* Edges: a non-tainted base field with the variable it holds; call edges
       identify an actual with the matching formal parameter. Tainted fields
       are excluded so they never bridge other fields. *)
    let live_fields = Hash_set.create (module String) in
    List.iter r.var_occ ~f:(fun (fk, idk) ->
        if not (Set.mem tainted fk) then begin
          Hash_set.add live_fields fk; union fk idk
        end);
    List.iter r.call_edges ~f:(fun (a, p) -> union a p);
    (* Group the live field nodes by representative. *)
    let groups : (string, string list) Hashtbl.t = Hashtbl.create (module String) in
    Hash_set.iter live_fields ~f:(fun fk ->
        Hashtbl.update groups (find fk)
          ~f:(function None -> [fk] | Some l -> fk :: l));
    let comps =
      Hashtbl.data groups
      |> List.map ~f:(List.sort ~compare:String.compare)
      |> List.sort ~compare:(fun a b ->
          match Int.compare (List.length b) (List.length a) with
          | 0 -> List.compare String.compare a b
          | c -> c) in
    let tainted_l = List.sort ~compare:String.compare (Set.to_list tainted) in
    comps, tainted_l

  (* Analysis entry point: connected components and tainted fields, rendered
     with signature field names. *)
  let analyze (f : t) : string list list * string list =
    let comps, tainted = components f in
    List.map comps ~f:(List.map ~f:field_name),
    List.map tainted ~f:field_name

  (* ---- Selection resolution (for the runtime data-router). ---- *)

  (* One hashing axis: route an event of name [ev] by [args.(idx)] modulo
     [da_modulo], where [da_fields] maps each participating event to the arg
     index it exposes on this axis. *)
  type data_axis = { da_modulo : int; da_fields : (string * int) list }

  (* Map a user-facing field name ("Event.field", or "Event.<int>") to its
     internal field key. *)
  let key_of_field_name (name : string) : string =
    match String.rsplit2 name ~on:'.' with
    | None -> failwith (Printf.sprintf "malformed field '%s' (expected Event.field)" name)
    | Some (ev, fld) ->
      match Option.try_with (fun () -> Int.of_string fld) with
      | Some i -> field_key ev i
      | None ->
        match (try Some (Sig.vars_of_pred ev) with _ -> None) with
        | None -> failwith (Printf.sprintf "unknown event '%s' in field '%s'" ev name)
        | Some names ->
          match List.findi names ~f:(fun _ n -> String.equal n fld) with
          | Some (i, _) -> field_key ev i
          | None -> failwith (Printf.sprintf "unknown field '%s' of event '%s'" fld ev)

  (* Resolve user selections [(field_name, num_buckets)] into hashing axes and
     the set of events that must broadcast (those carrying a tainted field).
     Selections naming the same component are merged (first bucket count wins,
     with a warning). *)
  let resolve_selection (f : t) (sels : (string * int) list) : data_axis list * string list =
    let comps, tainted = components f in
    let used = Hash_set.create (module String) in   (* component signatures already taken *)
    let axes =
      List.filter_map sels ~f:(fun (fname, n) ->
          let key = key_of_field_name fname in
          match List.find comps ~f:(fun c -> List.mem c key ~equal:String.equal) with
          | None ->
            failwith (Printf.sprintf
                        "field '%s' is not on any data axis (tainted or unconstrained)" fname)
          | Some comp ->
            let sig_ = String.concat ~sep:"," comp in
            if Hash_set.mem used sig_ then begin
              Stdio.eprintf "WARNING: '%s' selects an already-chosen data component; ignoring\n" fname;
              None
            end else begin
              Hash_set.add used sig_;
              (* event -> the arg index it is routed by on this axis (its
                 lowest-indexed field in the component).  When an event exposes
                 several fields of the same component, they are assumed to carry
                 the same value within a matching rule instance (as in C(y,y)),
                 so hashing any one of them routes consistently. *)
              let tbl = Hashtbl.create (module String) in
              List.iter comp ~f:(fun k ->
                  let ev, i = decode_field k in
                  Hashtbl.update tbl ev ~f:(function None -> i | Some j -> Int.min i j));
              let da_fields =
                Hashtbl.to_alist tbl
                |> List.sort ~compare:(fun (a,_) (b,_) -> String.compare a b) in
              Some { da_modulo = Int.max 1 n; da_fields }
            end) in
    let broadcast =
      List.map tainted ~f:(fun k -> fst (decode_field k))
      |> List.dedup_and_sort ~compare:String.compare in
    axes, broadcast

end  (* module DataSplit *)
