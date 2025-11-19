open Base

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm
module Valuation = ITerm.Valuation

module Fdeque = Core.Fdeque
module Part = Pdt.Part

module Pdt = struct

  module I = struct
    include Int
    let minimum = List.fold_left ~f:min ~init:max_int
  end

  include Pdt.Make(I)

  let rec specialize_partial (lbls: Lbl.t list) (v: Valuation.t) = function
    | Leaf l -> Leaf l
    | Node (i, part) ->
      match List.nth_exn lbls i with
      | LEx x
      | LAll x -> Node (i, Part.map part (specialize_partial lbls (Map.remove v i)))
      | lbl ->
        match (Sig.eval_lbl lbls v lbl).trm with
        | Const d -> specialize_partial lbls v (Part.find part d)
        | _ -> Node (i, Part.map part (specialize_partial lbls v))
                 
  let distribute x callback v (s', p) =
    let update v x' d = Map.update v x' ~f:(fun _ -> d) in
    match s' with
    | Setc.Finite s' ->
       List.map (Set.elements s') ~f:(fun d -> callback (update v x d) p)
    | Complement _ -> [callback v p]

  let rec specialize (lbls: Lbl.t list) (f_ex: 'a list -> 'a) (f_all : 'a list -> 'a) (v: Valuation.t) : 'a t -> 'a =
    function
    | Leaf l -> l
    | Node (i, part) ->
      match List.nth_exn lbls i with
      | LVar x when Map.mem v i ->
        specialize lbls f_ex f_all v (Part.find part (Map.find_exn v i))
      | LEx x ->
        let all_p = List.concat (Part.map2 part (fun (s, p) ->
            distribute i (specialize lbls f_ex f_all) v (s, p))) in
        f_ex all_p
      | LAll x -> 
        let all_p = List.concat (Part.map2 part (fun (s, p) ->
            distribute i (specialize lbls f_ex f_all) v (s, p))) in
        f_all all_p
      | lbl -> match Part.get_trivial part with
        | Some pdt -> specialize lbls f_ex f_all v pdt
        | None     -> specialize lbls f_ex f_all v (Part.find part (Term.unconst (Sig.eval_lbl lbls v lbl)))

  let collect (lbls: Lbl.t list) f_leaf f_ex f_all (v: Valuation.t) (j: int) p =
    let rec aux (v: Valuation.t) (s: (Dom.t, Dom.comparator_witness) Setc.t) =
      function
      | Leaf l when f_leaf l -> s
      | Leaf _ -> Setc.empty (module Dom)
      | Node (i, part) ->
        match List.nth_exn lbls i with
        | _ when Int.equal j i ->
          let s = Setc.union_list (module Dom)
              (Part.map2 part (fun (s', p) -> aux v (Setc.inter s s') p)) in
          s
        | LVar x' -> 
          let d = Map.find_exn v i in
          aux v s (Part.find part d)
        | LEx x' -> 
          let all_s = List.concat (Part.map2 part (distribute i (fun v p -> aux v s p) v)) in
          f_ex all_s
        | LAll x' -> 
          let all_s = List.concat (Part.map2 part (distribute i (fun v p -> aux v s p) v)) in
          f_all all_s
        | LClos (_, terms) as term ->
          (match s, Part.get_trivial part with
           | _, Some p -> aux v s p
           | Finite s, _ when
               Set.is_subset
                 (Set.of_list (module String) (Term.fv_list terms))
                 ~of_:((Set.of_list (module String) (ITerm.to_vars lbls (j :: Map.keys v)))) ->
             let f d =
               let v = Map.update v j ~f:(fun _ -> d) in
               let d' = Term.unconst (Sig.eval_lbl lbls v term) in
               aux v (Setc.singleton (module Dom) d)
                 (snd (Part.find2 part (fun s -> Setc.mem s d'))) in
             let s = Setc.union_list (module Dom) (List.map (Set.elements s) ~f) in
             s
           | _ -> s) in
    let r = aux v (Setc.univ (module Dom)) p in
    r
           
  
  let rec from_valuation ?(i=0) (lbls: Lbl.t list) (v: Valuation.t) p p' =
    match lbls with
    | [] -> Leaf p
    | (LVar x)::lbls ->
       let d = Map.find_exn v i in
       let rest = from_valuation ~i:(i+1) lbls v p p' in
       let part = Part.tabulate (Set.singleton (module Dom) d) (fun _ -> rest) (Leaf p') in
       Node (i, part)
    | _::lbls -> from_valuation ~i:(i+1) lbls v p p'

end

type t = bool Pdt.t

let rec is_violated = function
  | Pdt.Leaf l -> not l
  | Node (_, part) -> Part.exists part is_violated

let rec is_satisfied = function
  | Pdt.Leaf l -> l
  | Node (_, part) -> Part.exists part is_satisfied

let to_string expl = Pdt.to_string Bool.to_string "" expl

let to_light_string expl = Pdt.to_light_string Bool.to_string "" expl

let rec pdt_of ?(i=0) tp r lbls maps : t =
  if i >= List.length lbls then
    Leaf true
  else
    let ds = List.filter_map maps ~f:(fun map -> Map.find map i) in
    let find_maps d =
      List.filter_map maps ~f:(fun map -> match Map.find map i with
          | Some d' when Dom.equal d d' -> Some map
          | _ -> None)  in
    if List.is_empty ds then
      pdt_of ~i:(i+1) tp r lbls maps
    else
      let part = Part.tabulate_dedup (Pdt.eq Bool.equal) (Set.of_list (module Dom) ds)
          (fun d -> pdt_of ~i:(i+1) tp r lbls (find_maps d))
          (Leaf false) in
      Node (i, part)

(* [s_1, ..., s_k] <- OP (y; f) where p is a Pdt for f *)
let table_operator
    (op: Dom.t list list -> Dom.t list list)
    (s: int list)
    (f: int -> int)
    (tp: int)
    (x: Term.t list) (y: string list)
    (lbls: Lbl.t list) (lbls': Lbl.t list)
    (p: t) =
  let merge_pdts merge = function
    | [] -> raise (Errors.EnforcementError "cannot merge 0 PDTs")
    | [pdt] -> pdt
    | pdts -> Pdt.applyN_reduce (List.equal Valuation.equal) merge (List.map ~f:(fun pdt -> (Etc.id, pdt)) pdts) in
  let tabulate sv =
    let aux vs = function
      | (Term.Var x, Setc.Finite s) ->
         List.concat_map (Set.elements s) ~f:(fun d ->
             List.map vs ~f:(fun v -> Map.update v (ITerm.of_var lbls' x) ~f:(fun _ -> d)))
      | (Term.Const d, s) when Setc.mem s d -> vs
      | (Term.Const _, _) -> []
      | (trm, s) -> List.filter vs ~f:(fun v -> Setc.mem s (Term.unconst (Sig.teval lbls' v (Term.make_dummy trm)))) in
    List.fold_left sv ~init:([Valuation.empty]) ~f:aux in 
  let rec gather sv gs lbls (w: Valuation.t) p =
    match p, gs with
    | Pdt.Leaf true, _ -> 
       Pdt.Leaf (tabulate (List.rev sv))
    | Leaf _, _ -> Leaf []
    | Node (i, part), g :: gs when Lbl.equal (List.nth_exn lbls i) (LVar g) ->
       let part = Part.map2 part (fun (s, p) -> (s, gather ((Var g, s)::sv) gs lbls w p)) in
       Node (i, part)
    | Node (i, part), _ ->
      match List.nth_exn lbls i with
      | LEx x' ->
        let pdts = List.concat (Part.map2 part (Pdt.distribute i (gather sv gs lbls) w)) in
        merge_pdts List.concat pdts
      | LAll x' ->
        let pdts = List.concat (Part.map2 part (Pdt.distribute i (gather sv gs lbls) w)) in
        merge_pdts (Etc.list_intersection Valuation.equal) pdts
      | _ -> 
        let pdts = Part.map2 part (fun (s, p) -> gather (((Lbl.term (List.nth_exn lbls i)).trm, s)::sv) gs lbls w p) in
        merge_pdts List.concat pdts in
  let rec collect_leaf_values i = function
    | Pdt.Leaf None  -> Set.empty (module Dom)
    | Leaf (Some vs) -> Set.of_list (module Dom) (List.map ~f:(fun v -> Map.find_exn v i) vs)
    | Node (_, part) -> Set.union_list (module Dom)
                          (List.map part ~f:(fun (_, pdt) -> collect_leaf_values i pdt)) in
  let rec insert ?(i=0) (lbls: Lbl.t list) (v: Valuation.t) (pdt: Valuation.t list option Pdt.t) =
    match pdt with
    | _ when List.mem s i ~equal:Int.equal ->
      let ds = collect_leaf_values i pdt in
      (if Set.is_empty ds then
         Pdt.Leaf false
       else
         let v d = Map.update v i ~f:(fun _ -> d) in
         let parts = Part.tabulate_dedup (Pdt.eq Bool.equal) ds
             (fun d -> insert ~i:(i+1) lbls (v d) pdt)
             (Leaf false) in
         Pdt.Node (i, parts))
    | Node (lbl', part) ->
      Pdt.Node (lbl', Part.map part (insert ~i:(i+1) lbls v))
    | Leaf (Some vs) ->
       if List.exists vs ~f:(fun v' ->
              Map.for_alli v ~f:(fun ~key ~data -> Dom.equal (Map.find_exn v' key) data))
       then Pdt.Leaf true
       else Pdt.Leaf false
    | Leaf None ->
       Pdt.Leaf false
  in
  let apply_op (vs: Valuation.t list) : Valuation.t list option =
    if List.is_empty vs && List.length y > 0
    then None
    else (
      let dss = List.map ~f:(fun v -> List.map ~f:(fun x -> Term.unconst (Sig.teval lbls' v x)) x) vs in
      let vs = List.map ~f:(fun v -> Valuation.of_alist_exn s v) (op dss) in
      Some vs) in
  let r = insert lbls Valuation.empty
      (Pdt.apply1_reduce (Option.equal (List.equal (Valuation.equal))) apply_op f (gather [] y lbls' Valuation.empty p)) in
  if !Global.debug then
      Stdio.printf "[debug:Expl] table_operator (s=[%s], x=%s, y=[%s], lbls=%s, lbls'=%s, p=%s) = %s"
      (String.concat ~sep:", " (List.map ~f:string_of_int s))
      (Term.list_to_string x)
      (Etc.string_list_to_string y)
      (Lbl.to_string_list lbls)
      (Lbl.to_string_list lbls')
      (to_string p)
      (to_string r);
  r

let aggregate
    (agg: (Dom.t, Dom.comparator_witness) Multiset.t -> Dom.t)
    (s: int)
    (f: int -> int)
    (tp: int)
    (x: Term.t)
    (y: string list)
    (lbls: Lbl.t list) (lbls': Lbl.t list)
    (p: t)  =
  let multiset dss = Multiset.of_list (module Dom) (List.map ~f:List.hd_exn dss) in
  table_operator (fun dss -> [[agg (multiset dss)]]) [s] f tp [x] y lbls lbls' p
