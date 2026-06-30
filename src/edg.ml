open Base
open MFOTL_lib

(* ------------------------------------------------------------------ *)
(* Event Dependency Graph (EDG)                                         *)
(*                                                                      *)
(* Nodes are *events* (base predicate names, after let-explosion).      *)
(* There is an edge  E --[clause k ^ action]--> F  whenever event E      *)
(* appears in the trigger of a clause k whose effect causes/suppresses  *)
(* event F.  Thus an edge points from an influencing event to an event  *)
(* it influences.                                                       *)
(*                                                                      *)
(* SCCs of this graph are sets of mutually-influencing events; the      *)
(* per-SCC SMT and data-flow checks (Smt_check, Dataflow) run on them.  *)
(* SCC ids from [Graph_util.tarjan] are in reverse-topological order of  *)
(* the condensation (sinks first), so an SCC's *influencers* are the    *)
(* SCCs that can reach it in the condensation DAG.                      *)
(* ------------------------------------------------------------------ *)

module ES    = Splitting.EventSplit
module Clause = Nformula.Clause

type label = { clause : int; action : ES.action }

type t = {
  nodes     : string array;                                   (* event id -> name *)
  node_of   : (string, int, String.comparator_witness) Map.t; (* name -> id *)
  graph     : label Graph_util.Graph.t;
  clauses   : Clause.t array;
  scc_count : int;
  scc_of    : int array;                                      (* event id -> SCC id *)
}

let action_to_string = function ES.Cau -> "C" | ES.Sup -> "S"

(* Build the EDG from a list of enforcement clauses.  [lets] is the
   let-context predicate map (from [Splitting.maps_of_lets]) used to explode
   let predicates into the base events they stand for. *)
let build ?(lets = Map.empty (module String)) (clause_list : Clause.t list) : t =
  let clauses = Array.of_list clause_list in
  let n = Array.length clauses in
  (* trigger events (let-exploded) and effect (event, action) per clause *)
  let trig = Array.map clauses ~f:(fun c -> Clause.trigger_predicates ~lets c) in
  let effs =
    Array.map clauses ~f:(fun c ->
        List.filter_map c.Clause.effects ~f:ES.effect_action) in
  (* node universe = every event mentioned as a trigger predicate or an effect *)
  let names =
    let s = ref (Set.empty (module String)) in
    Array.iter trig ~f:(fun preds -> s := Set.union !s preds);
    Array.iter effs ~f:(fun es -> List.iter es ~f:(fun (e, _) -> s := Set.add !s e));
    Set.to_list !s in
  let nodes = Array.of_list names in
  let node_of =
    Array.foldi nodes ~init:(Map.empty (module String))
      ~f:(fun i acc name -> Map.set acc ~key:name ~data:i) in
  let id name = Map.find_exn node_of name in
  let g = ref (Graph_util.Graph.empty (Array.length nodes)) in
  for k = 0 to n - 1 do
    List.iter effs.(k) ~f:(fun (f, action) ->
        Set.iter trig.(k) ~f:(fun e ->
            g := Graph_util.Graph.add_edge !g
                   ~src:(id e) ~lbl:{ clause = k; action } ~dst:(id f)))
  done;
  let graph = !g in
  let scc_count, scc_of = Graph_util.tarjan graph in
  { nodes; node_of; graph; clauses; scc_count; scc_of }

(* Event ids belonging to SCC [s]. *)
let scc_members (t : t) (s : int) : int list =
  Array.foldi t.scc_of ~init:[] ~f:(fun v acc sv -> if sv = s then v :: acc else acc)

(* For each SCC, the set of event *names* lying in strictly-upstream SCCs
   (the influencers: SCCs that can reach this one in the condensation).
   These are the only events the SMT incompatibility check may rely on. *)
let upstream_events_by_scc (t : t) : (int, (string, String.comparator_witness) Set.t) Hashtbl.t =
  let cond = Graph_util.condensation ~scc_count:t.scc_count ~scc_of:t.scc_of t.graph in
  let cond_t = Graph_util.Graph.transpose cond in
  let tbl = Hashtbl.create (module Int) in
  for s = 0 to t.scc_count - 1 do
    (* ancestors of s = SCCs reachable from s in the transposed condensation *)
    let ancestors = Set.remove (Graph_util.Graph.reachable cond_t s) s in
    let names =
      Array.foldi t.scc_of ~init:(Set.empty (module String))
        ~f:(fun v acc sv -> if Set.mem ancestors sv then Set.add acc t.nodes.(v) else acc) in
    Hashtbl.set tbl ~key:s ~data:names
  done;
  tbl

(* Graphviz DOT, with one cluster per SCC. *)
let to_dot (t : t) : string =
  Graph_util.Graph.to_dot ~name:"EDG" ~scc_of:t.scc_of
    ~node_label:(fun v -> t.nodes.(v))
    ~label_to_string:(fun lbl ->
        Printf.sprintf "c%d^%s" lbl.clause (action_to_string lbl.action))
    t.graph

(* ─── Filtered / per-SCC views ─────────────────────────────────────────────── *)

(* Bare quantifier/table helper predicates (OnceN, ExistsN, …, TP) — internal
   plumbing, dropped from the focused view. *)
let is_bare_helper name =
  String.equal name "TP"
  || List.exists ["Once"; "Exists"; "Since"; "Prev"; "Scope"; "Label"]
       ~f:(fun pre -> String.is_prefix name ~prefix:pre)

let is_synth name =
  String.is_prefix name ~prefix:"Sup_" || String.is_prefix name ~prefix:"Cau_"

let esc s = String.substr_replace_all s ~pattern:"\"" ~with_:"'"

let sizes_of (t : t) =
  let sizes = Array.create ~len:t.scc_count 0 in
  Array.iter t.scc_of ~f:(fun s -> sizes.(s) <- sizes.(s) + 1);
  sizes

(* The cyclic (recursive) SCCs — those with more than one event. *)
let cyclic_sccs (t : t) : int list =
  let sizes = sizes_of t in
  List.filter (List.init t.scc_count ~f:Fn.id) ~f:(fun s -> sizes.(s) > 1)

(* Focused condensation: collapse each SCC to one node, keep the cyclic cores
   and the real / Sup_ / Cau_ events, drop bare helper singletons and isolated
   nodes.  Mirrors the hand-built "focus" view. *)
let focused_dot (t : t) : string =
  let sizes = sizes_of t in
  let members = Array.create ~len:t.scc_count [] in
  Array.iteri t.scc_of ~f:(fun v s -> members.(s) <- t.nodes.(v) :: members.(s));
  let keep_scc s =
    sizes.(s) > 1
    || (match members.(s) with [n] -> not (is_bare_helper n) | _ -> true) in
  let rep s =
    let ms = members.(s) in
    let real = List.filter ms ~f:(fun n -> not (is_synth n) && not (is_bare_helper n)) in
    let pick = if List.is_empty real then ms else real in
    Option.value (List.min_elt pick
                    ~compare:(fun a b -> Int.compare (String.length a) (String.length b)))
      ~default:"?" in
  let cond =
    List.filter_map (Graph_util.Graph.edges t.graph) ~f:(fun (u, _, v) ->
        let a = t.scc_of.(u) and b = t.scc_of.(v) in
        if a <> b && keep_scc a && keep_scc b then Some (a, b) else None)
    |> List.dedup_and_sort ~compare:[%compare: int * int] in
  let touched =
    List.fold cond ~init:(Set.empty (module Int))
      ~f:(fun acc (a, b) -> Set.add (Set.add acc a) b) in
  let touched =
    List.fold (List.init t.scc_count ~f:Fn.id) ~init:touched
      ~f:(fun acc s -> if sizes.(s) > 1 then Set.add acc s else acc) in
  let kept s = keep_scc s && Set.mem touched s in
  let buf = Buffer.create 2048 in
  Buffer.add_string buf
    "digraph EDG_focus {\n  rankdir=LR;\n  node [shape=box, style=filled, fontsize=10];\n\
    \  edge [color=\"#999999\", arrowsize=0.5];\n";
  for s = 0 to t.scc_count - 1 do
    if kept s then begin
      let nm = List.hd_exn members.(s) in
      let color =
        if sizes.(s) > 1 then "#ff9999"
        else if String.is_prefix nm ~prefix:"Sup_" then "#ffe0b3"
        else if String.is_prefix nm ~prefix:"Cau_" then "#d9f2d9"
        else "#cfe8ff" in
      let lbl =
        if sizes.(s) > 1 then Printf.sprintf "%s\\nSCC%d (%d)" (esc (rep s)) s sizes.(s)
        else esc nm in
      Buffer.add_string buf
        (Printf.sprintf "  s%d [label=\"%s\", fillcolor=\"%s\"];\n" s lbl color)
    end
  done;
  List.iter cond ~f:(fun (a, b) ->
      if kept a && kept b then
        Buffer.add_string buf (Printf.sprintf "  s%d -> s%d;\n" a b));
  Buffer.add_string buf "}\n";
  Buffer.contents buf

(* Expanded graph of one SCC: its member events and the edges among them. *)
let scc_subgraph_dot (t : t) (s : int) : string =
  let buf = Buffer.create 512 in
  Buffer.add_string buf
    (Printf.sprintf "digraph SCC%d {\n  rankdir=LR;\n  node [shape=box, fontsize=8];\n" s);
  Array.iteri t.scc_of ~f:(fun v sv ->
      if sv = s then
        Buffer.add_string buf
          (Printf.sprintf "  n%d [label=\"%s\"];\n" v (esc t.nodes.(v))));
  List.iter (Graph_util.Graph.edges t.graph) ~f:(fun (u, lbl, v) ->
      if t.scc_of.(u) = s && t.scc_of.(v) = s then
        Buffer.add_string buf
          (Printf.sprintf "  n%d -> n%d [label=\"%s\"];\n" u v
             (Printf.sprintf "c%d^%s" lbl.clause (action_to_string lbl.action))));
  Buffer.add_string buf "}\n";
  Buffer.contents buf

let summary_to_string (t : t) : string =
  let buf = Buffer.create 256 in
  Buffer.add_string buf
    (Printf.sprintf "EDG: %d event(s), %d SCC(s)\n"
       (Array.length t.nodes) t.scc_count);
  for s = 0 to t.scc_count - 1 do
    let members = List.map (scc_members t s) ~f:(fun v -> t.nodes.(v)) in
    if List.length members > 1 then
      Buffer.add_string buf
        (Printf.sprintf "  SCC %d (cyclic): %s\n" s (String.concat ~sep:", " members))
  done;
  Buffer.contents buf
