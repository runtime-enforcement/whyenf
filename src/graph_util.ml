open Base

(* ------------------------------------------------------------------ *)
(* Generic directed multigraph over integer vertices 0..n-1 with        *)
(* polymorphic edge labels, plus Tarjan SCC + condensation.             *)
(*                                                                      *)
(* Factored out of [Splitting.EventSplit] so the Clause Dependency      *)
(* Graph, the Event Dependency Graph (Edg), and the data-flow graph     *)
(* (Dataflow) can all share the same SCC machinery while carrying        *)
(* different label types.                                                *)
(* ------------------------------------------------------------------ *)

module Graph = struct

  (* adj maps each source vertex to the list of (label, destination) pairs.
     Invariant: no two entries in adj[v] share the same (label, dst). *)
  type 'lbl t = {
    n   : int;
    adj : (int, ('lbl * int) list, Int.comparator_witness) Map.t;
  }

  let empty n = { n; adj = Map.empty (module Int) }

  let labeled_successors g v =
    Option.value (Map.find g.adj v) ~default:[]

  (* Successor vertices, deduplicated (labels dropped). *)
  let successors g v =
    List.dedup_and_sort ~compare:Int.compare
      (List.map (labeled_successors g v) ~f:snd)

  (* Add the edge (src --lbl--> dst), silently ignoring exact duplicates.
     Label equality uses structural (polymorphic) comparison. *)
  let add_edge g ~src ~lbl ~dst =
    { g with adj =
        Map.update g.adj src ~f:(fun prev ->
          let prev = Option.value prev ~default:[] in
          if List.exists prev ~f:(fun (l, d) -> d = dst && Poly.equal l lbl)
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

  let to_string ?(label_to_string = fun _ -> "") g =
    let edge_strs =
      List.map (edges g) ~f:(fun (i, lbl, j) ->
        Printf.sprintf "%d -[%s]-> %d" i (label_to_string lbl) j)
    in
    Printf.sprintf "Graph(%d vertices, [%s])" g.n
      (String.concat ~sep:"; " edge_strs)

  (* Emit Graphviz DOT.  When [scc_of] is given, nodes are grouped into one
     [subgraph cluster_k] per SCC id so the SCCs are visually distinct. *)
  let to_dot ?(name = "G") ?scc_of
      ?(node_label = Int.to_string) ?(label_to_string = fun _ -> "") g =
    let buf = Buffer.create 256 in
    Buffer.add_string buf (Printf.sprintf "digraph %s {\n" name);
    Buffer.add_string buf "  rankdir=LR;\n  node [shape=box];\n";
    let emit_node v =
      Buffer.add_string buf
        (Printf.sprintf "  n%d [label=\"%s\"];\n" v (node_label v)) in
    (match scc_of with
     | None -> for v = 0 to g.n - 1 do emit_node v done
     | Some scc_of ->
       let by_scc = Hashtbl.create (module Int) in
       for v = 0 to g.n - 1 do
         Hashtbl.add_multi by_scc ~key:scc_of.(v) ~data:v
       done;
       Hashtbl.iteri by_scc ~f:(fun ~key:sid ~data:verts ->
         Buffer.add_string buf
           (Printf.sprintf "  subgraph cluster_%d {\n    label=\"SCC %d\";\n" sid sid);
         List.iter (List.rev verts) ~f:(fun v ->
           Buffer.add_string buf
             (Printf.sprintf "    n%d [label=\"%s\"];\n" v (node_label v)));
         Buffer.add_string buf "  }\n"));
    List.iter (edges g) ~f:(fun (i, lbl, j) ->
      let l = label_to_string lbl in
      if String.is_empty l
      then Buffer.add_string buf (Printf.sprintf "  n%d -> n%d;\n" i j)
      else Buffer.add_string buf
          (Printf.sprintf "  n%d -> n%d [label=\"%s\"];\n" i j l));
    Buffer.add_string buf "}\n";
    Buffer.contents buf

end

(* ------------------------------------------------------------------ *)
(* Tarjan's SCC (uses Graph.successors for unlabeled traversal).        *)
(* Returns (scc_count, scc_of) where scc_of.(v) = SCC id of v.         *)
(* SCC ids are assigned in reverse topological order of the            *)
(* condensation, so the first SCC finished is a sink of the DAG.       *)
(* ------------------------------------------------------------------ *)

let tarjan (g : _ Graph.t) : int * int array =
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
let condensation ~scc_count ~(scc_of : int array) (g : 'lbl Graph.t) : 'lbl Graph.t =
  List.fold (Graph.edges g) ~init:(Graph.empty scc_count)
    ~f:(fun acc (u, lbl, v) ->
      let su = scc_of.(u) and sv = scc_of.(v) in
      if su = sv then acc
      else Graph.add_edge acc ~src:su ~lbl ~dst:sv)

(* ------------------------------------------------------------------ *)
(* SCC wave decomposition and topological ordering                      *)
(*                                                                      *)
(* sccs_in_waves groups SCCs into parallel waves: all SCCs in a wave    *)
(* are mutually independent (no condensation edge between any two in   *)
(* the same wave), so they can be evaluated concurrently.  Each wave   *)
(* is a list of (recursive, members) pairs in arbitrary order.  Waves  *)
(* are returned in dependency order (sources first).                    *)
(*                                                                      *)
(* sccs_in_topo_order is a linear topological order (any linearisation  *)
(* of the wave list is valid); implemented as a flatten of the waves.   *)
(*                                                                      *)
(* An SCC is "recursive" when it has more than one node, or when any   *)
(* of its nodes has a self-loop in [g].  (Tarjan alone does not        *)
(* distinguish singleton SCCs from those with self-loops because a     *)
(* self-loop does not raise lowlink above index.)                       *)
(* ------------------------------------------------------------------ *)

let sccs_in_waves (g : 'lbl Graph.t) : (bool * int list) list list =
  let n = g.Graph.n in
  if n = 0 then []
  else begin
    let self_loop = Array.create ~len:n false in
    List.iter (Graph.edges g) ~f:(fun (i, _, j) -> if i = j then self_loop.(i) <- true);
    let scc_count, scc_of = tarjan g in
    let scc_members = Array.create ~len:scc_count [] in
    for i = n - 1 downto 0 do
      scc_members.(scc_of.(i)) <- i :: scc_members.(scc_of.(i))
    done;
    let scc_recursive = Array.create ~len:scc_count false in
    Array.iteri scc_of ~f:(fun i s -> if self_loop.(i) then scc_recursive.(s) <- true);
    for s = 0 to scc_count - 1 do
      if List.length scc_members.(s) > 1 then scc_recursive.(s) <- true
    done;
    (* Build condensation adjacency and compute BFS levels:
       level(s) = 1 + max(level(predecessor) for each predecessor of s).
       Sources (no predecessors) are at level 0.  Computed via Kahn's
       pass, updating the successor's level when its last predecessor is
       processed so that each successor gets the maximum predecessor level. *)
    let cond      = Array.create ~len:scc_count (Set.empty (module Int)) in
    let rem_indeg = Array.create ~len:scc_count 0 in
    List.iter (Graph.edges g) ~f:(fun (u, _, v) ->
        let a = scc_of.(u) and b = scc_of.(v) in
        if a <> b && not (Set.mem cond.(a) b) then begin
          cond.(a) <- Set.add cond.(a) b;
          rem_indeg.(b) <- rem_indeg.(b) + 1
        end);
    let level = Array.create ~len:scc_count 0 in
    let ready = Queue.create () in
    for s = 0 to scc_count - 1 do
      if rem_indeg.(s) = 0 then Queue.enqueue ready s
    done;
    while not (Queue.is_empty ready) do
      let s = Queue.dequeue_exn ready in
      Set.iter cond.(s) ~f:(fun t ->
          level.(t) <- Int.max level.(t) (level.(s) + 1);
          rem_indeg.(t) <- rem_indeg.(t) - 1;
          if rem_indeg.(t) = 0 then Queue.enqueue ready t)
    done;
    (* Defensive: any SCC not placed by BFS (cycle in condensation, impossible
       for a DAG but guard against it) gets assigned to the last level. *)
    let num_waves = Array.fold level ~init:0 ~f:Int.max + 1 in
    let wave_sccs = Array.create ~len:num_waves [] in
    for s = 0 to scc_count - 1 do
      wave_sccs.(level.(s)) <- s :: wave_sccs.(level.(s))
    done;
    Array.to_list wave_sccs
    |> List.filter_map ~f:(fun sccs ->
        let entries =
          List.filter_map sccs ~f:(fun s ->
              if List.is_empty scc_members.(s) then None
              else Some (scc_recursive.(s), scc_members.(s))) in
        if List.is_empty entries then None else Some entries)
  end

(* Flatten waves into a single topological order. *)
let sccs_in_topo_order (g : 'lbl Graph.t) : (bool * int list) list =
  List.concat (sccs_in_waves g)
