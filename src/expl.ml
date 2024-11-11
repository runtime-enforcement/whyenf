(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

module Fdeque = Core.Fdeque

module Part = struct

  type sub = (Dom.t, Dom.comparator_witness) Setc.t

  type 'a t = (sub * 'a) list

  let random_empty_set = Set.empty (module String)

  let trivial p = [(Setc.univ (module Dom), p)]

  let get_trivial = function
    | [(s, p)] when Setc.is_univ s -> Some p
    | _ -> None

  let hd part = snd (List.hd_exn part)

  let length part = List.length part

  let map part f = List.map part ~f:(fun (s, p) -> (s, f p))

  let map2 part f = List.map part ~f:(fun (s, p) -> f (s, p))

  let fold_left part init f = List.fold_left part ~init:init ~f:(fun acc (_, p) -> f acc p)

  let fold_left2 part init f = List.fold_left part ~init:init ~f:(fun acc (d, p) -> f acc d p)

  let filter part f = List.filter part ~f:(fun (_, p) -> f p)

  let exists part f = List.exists part ~f:(fun (_, p) -> f p)

  let for_all part f = List.for_all part ~f:(fun (_, p) -> f p)

  let values part = List.map part ~f:(fun (_, p) -> p)

  let find part x = snd (List.find_exn part ~f:(fun (s, p) -> Setc.mem s x))

  let find2 part f = List.find_exn part ~f:(fun (s, p) -> f p)

  let find3 part f = List.find_exn part ~f:(fun (s, p) -> f s)

  let rec tabulate ds f z =
    (Setc.Complement ds, z) ::
      (Set.fold ds ~init:[] ~f:(fun acc d -> (Setc.Finite (Set.of_list (module Dom) [d]), f d) :: acc))

  let rec merge2 f part1 part2 = match part1, part2 with
    | [], _ -> []
    | (sub1, v1) :: part1, part2 ->
       let part12 = List.filter_map part2
                      ~f:(fun (sub2, v2) ->
                        (if not (Setc.is_empty (Setc.inter sub1 sub2))
                         then Some (Setc.inter sub1 sub2, f v1 v2) else None)) in
       let part2not1 = List.filter_map part2
                         ~f:(fun (sub2, v2) ->
                           (if not (Setc.is_empty (Setc.diff sub2 sub1))
                            then Some (Setc.diff sub2 sub1, v2) else None)) in
       part12 @ (merge2 f part1 part2not1)

  let merge3 f part1 part2 part3 = match part1, part2, part3 with
    | [], _ , _
      | _ , [], _
      | _ , _ , [] -> raise (Invalid_argument "one of the partitions is empty")
    | part1, part2, part3 ->
       merge2 (fun pt3 f' -> f' pt3) part3 (merge2 f part1 part2)

  let split_prod part = (map part fst, map part snd)

  let split_list part =
    let subs = List.map part ~f:fst in
    let vs = List.map part ~f:snd in
    List.map (Option.value_exn (List.transpose vs)) ~f:(List.zip_exn subs)

  let el_to_string indent s f (sub, v) =
    Printf.sprintf "%s%s ∈ %s\n\n%s"
      indent s (Setc.to_string sub) (f (indent ^ (String.make 4 ' ')) v)

  let to_string indent s f = function
    | [] -> indent ^ "❮ · ❯"
    | [x] -> indent ^ "❮\n\n" ^ (el_to_string indent s f x) ^ "\n" ^ indent ^ "❯\n"
    | xs -> indent ^ "❮\n\n"
            ^ String.concat ~sep:"\n" (List.map xs (el_to_string indent s f)) ^ "\n"
            ^ indent ^ "❯\n"


  (* dedup related *)
  let dedup p_eq part =
    let rec aux acc (s,v) =
      match acc with
      | [] -> [(s,v)]
      | (t,u) :: acc -> if p_eq u v then (Setc.union s t, u) :: acc
                        else (t,u) :: aux acc (s,v) in
    let rec dedup_rec part acc =
      match part with
      | [] -> acc
      | (s,v) :: part -> let acc' = aux acc (s,v) in
                         dedup_rec part acc' in
    dedup_rec part []

  let map_dedup p_eq part f = dedup p_eq (map part f)

  let map2_dedup p_eq part f = dedup p_eq (map2 part f)

  let tabulate_dedup p_eq ds f z = dedup p_eq (tabulate ds f z)

  let merge2_dedup p_eq f part1 part2 = dedup p_eq (merge2 f part1 part2)

  let merge3_dedup p_eq f part1 part2 part3 = dedup p_eq (merge3 f part1 part2 part3)

  let split_prod_dedup p_eq part =
    let part1, part2 = split_prod part in
    (dedup p_eq part1, dedup p_eq part2)

  let split_list_dedup p_eq part = List.map (split_list part) ~f:(dedup p_eq)

end



module Pdt = struct

  type 'a t = Leaf of 'a | Node of Lbl.t * ('a t) Part.t

  let rec apply1 lbls f pdt = match lbls, pdt with
    | _ , Leaf l -> Leaf (f l)
    | z :: lbls, Node (x, part) ->
       if Lbl.equal z x then
         Node (x, Part.map part (apply1 lbls f))
       else apply1 lbls f (Node (x, part))
    | _ -> raise (Invalid_argument "variable list is empty")

  let rec apply2 lbls f pdt1 pdt2 = match lbls, pdt1, pdt2 with
    | _ , Leaf l1, Leaf l2 -> Leaf (f l1 l2)
    | _ , Leaf l1, Node (x, part2) -> Node (x, Part.map part2 (apply1 lbls (f l1)))
    | _ , Node (x, part1), Leaf l2 -> Node (x, Part.map part1 (apply1 lbls (fun l1 -> f l1 l2)))
    | z :: lbls, Node (x, part1), Node (y, part2) ->
       if Lbl.equal z x && Lbl.equal z y then
         Node (x, Part.merge2 (apply2 lbls f) part1 part2)
       else (if Lbl.equal z x then
               Node (x, Part.map part1 (fun pdt1 -> apply2 lbls f pdt1 (Node (y, part2))))
             else (if Lbl.equal z y then
                     Node (y, Part.map part2 (apply2 lbls f (Node (x, part1))))
                   else apply2 lbls f (Node (x, part1)) (Node (y, part2))))
    | _ -> raise (Invalid_argument "variable list is empty")

  let rec apply3 lbls f pdt1 pdt2 pdt3 = match lbls, pdt1, pdt2, pdt3 with
    | _ , Leaf l1, Leaf l2, Leaf l3 -> Leaf (f l1 l2 l3)
    | _ , Leaf l1, Leaf l2, Node (x, part3) ->
       Node (x, Part.map part3 (apply1 lbls (fun l3 -> f l1 l2 l3)))
    | _ , Leaf l1, Node (x, part2), Leaf l3 ->
       Node (x, Part.map part2 (apply1 lbls (fun l2 -> f l1 l2 l3)))
    | _ , Node (x, part1), Leaf l2, Leaf l3 ->
       Node (x, Part.map part1 (apply1 lbls (fun l1 -> f l1 l2 l3)))
    | w :: lbls, Leaf l1, Node (y, part2), Node (z, part3) ->
       if Lbl.equal w y && Lbl.equal w z then
         Node (y, Part.merge2 (apply2 lbls (f l1)) part2 part3)
       else (if Lbl.equal w y then
               Node (y, Part.map part2 (fun pdt2 -> apply2 lbls (f l1) pdt2 (Node (z, part3))))
             else (if Lbl.equal w z then
                     Node (z, Part.map part3 (fun pdt3 -> apply2 lbls (f l1) (Node (y, part2)) pdt3))
                   else apply3 lbls f (Leaf l1) (Node (y, part2)) (Node(z, part3))))
    | w :: lbls, Node (x, part1), Node (y, part2), Leaf l3 ->
       if Lbl.equal w x && Lbl.equal w y then
         Node (x, Part.merge2 (apply2 lbls (fun l1 l2 -> f l1 l2 l3)) part1 part2)
       else (if Lbl.equal w x then
               Node (x, Part.map part1 (fun pdt1 -> apply2 lbls (fun pt1 pt2 -> f pt1 pt2 l3) pdt1 (Node (y, part2))))
             else (if Lbl.equal w y then
                     Node (y, Part.map part2 (fun pdt2 -> apply2 lbls (fun l1 l2 -> f l1 l2 l3) (Node (x, part1)) pdt2))
                   else apply3 lbls f (Node (x, part1)) (Node (y, part2)) (Leaf l3)))
    | w :: lbls, Node (x, part1), Leaf l2, Node (z, part3) ->
       if Lbl.equal w x && Lbl.equal w z then
         Node (x, Part.merge2 (apply2 lbls (fun l1 -> f l1 l2)) part1 part3)
       else (if Lbl.equal w x then
               Node (x, Part.map part1 (fun pdt1 -> apply2 lbls (fun l1 -> f l1 l2) pdt1 (Node (z, part3))))
             else (if Lbl.equal w z then
                     Node (z, Part.map part3 (fun pdt3 -> apply2 lbls (fun l1 -> f l1 l2) (Node (x, part1)) pdt3))
                   else apply3 lbls f (Node (x, part1)) (Leaf l2) (Node (z, part3))))
    | w :: lbls, Node (x, part1), Node (y, part2), Node (z, part3) ->
       if Lbl.equal w x && Lbl.equal w y && Lbl.equal w z then
         Node (z, Part.merge3 (apply3 lbls f) part1 part2 part3)
       else (if Lbl.equal w x && Lbl.equal w y then
               Node (x, Part.merge2 (fun pdt1 pdt2 -> apply3 lbls f pdt1 pdt2 (Node (z, part3))) part1 part2)
             else (if Lbl.equal w x && Lbl.equal w z then
                     Node (x, Part.merge2 (fun pdt1 pdt3 -> apply3 lbls f pdt1 (Node (y, part2)) pdt3) part1 part3)
                   else (if Lbl.equal w y && Lbl.equal w z then
                           Node (y, Part.merge2 (apply3 lbls (fun l1 -> f l1) (Node (x, part1))) part2 part3)
                         else (if Lbl.equal w x then
                                 Node (x, Part.map part1 (fun pdt1 -> apply3 lbls f pdt1 (Node (y, part2)) (Node (z, part3))))
                               else (if Lbl.equal w y then
                                       Node (y, Part.map part2 (fun pdt2 -> apply3 lbls f (Node (x, part1)) pdt2 (Node (z, part3))))
                                     else (if Lbl.equal w z then
                                             Node (z, Part.map part3 (fun pdt3 -> apply3 lbls f (Node (x, part1)) (Node (y, part2)) pdt3))
                                           else apply3 lbls f (Node (x, part1)) (Node (y, part2)) (Node (z, part3))))))))
    | _ -> raise (Invalid_argument "variable list is empty")

  let rec split_prod = function
    | Leaf (l1, l2) -> (Leaf l1, Leaf l2)
    | Node (x, part) -> let (part1, part2) = Part.split_prod (Part.map part split_prod) in
                           (Node (x, part1), Node (x, part2))

  let rec split_list = function
    | Leaf l -> List.map l ~f:(fun el -> Leaf el)
    | Node (x, part) -> List.map (Part.split_list (Part.map part split_list)) ~f:(fun el -> Node (x, el))

  let rec to_string f indent = function
    | Leaf pt -> Printf.sprintf "%s%s\n" indent (f pt)
    | Node (x, part) -> (Part.to_string indent (Lbl.to_string x) (to_string f) part)

  let rec to_light_string f indent = function
    | Leaf pt -> Printf.sprintf "%s%s\n" indent (f pt)
    | Node (x, part) -> (Part.to_string indent (Lbl.to_string x) (to_light_string f) part)

  let unleaf = function
    | Leaf l -> l
    | _ -> raise (Invalid_argument "function not defined for nodes")

  let rec hide vars f_leaf f_node pdt = match vars, pdt with
    |  _ , Leaf l -> Leaf (f_leaf l)
    | [x], Node (y, part) -> Leaf (f_node (Part.map part unleaf))
    | x :: vars, Node (y, part) -> if Lbl.equal x y then
                                        Node (y, Part.map part (hide vars f_leaf f_node))
                                      else
                                        hide vars f_leaf f_node (Node (y, part))
    | _ -> raise (Invalid_argument "function not defined for other cases")

  (* reduce related *)
  let rec eq p_eq pdt1 pdt2 =
    match pdt1, pdt2 with
    | Leaf l1, Leaf l2 -> p_eq l1 l2
    | Node (x, part), Node (x', part') ->
       Lbl.equal x x'  && Int.equal (Part.length part) (Part.length part') &&
         List.for_all2_exn part part' ~f:(fun (s, v) (s', v') ->
             Setc.equal s s' && eq p_eq v v')
    | _ -> false

  let rec reduce p_eq = function
    | Leaf l -> Leaf l
    | Node (x, part) -> Node (x, Part.dedup (eq p_eq) (Part.map part (reduce p_eq)))

  let rec apply1_reduce p_eq vars f pdt = match vars, pdt with
    | _ , Leaf l -> Leaf (f l)
    | z :: vars, Node (x, part) ->
       if Lbl.equal z x then
         Node (x, Part.map_dedup (eq p_eq) part (apply1_reduce p_eq vars f))
       else
         apply1_reduce p_eq vars f (Node (x, part))
    | _ -> raise (Invalid_argument "variable list is empty")

  let rec apply2_reduce p_eq vars f pdt1 pdt2 = match vars, pdt1, pdt2 with
    | _ , Leaf l1, Leaf l2 -> Leaf (f l1 l2)
    | _ , Leaf l1, Node (x, part2) -> Node (x, Part.map_dedup (eq p_eq) part2 (apply1_reduce p_eq vars (f l1)))
    | _ , Node (x, part1), Leaf l2 -> Node (x, Part.map_dedup (eq p_eq) part1 (apply1_reduce p_eq vars (fun l1 -> f l1 l2)))
    | z :: vars, Node (x, part1), Node (y, part2) ->
       if Lbl.equal z x && Lbl.equal z y then
         Node (x, Part.merge2_dedup (eq p_eq) (apply2_reduce p_eq vars f) part1 part2)
       else (if Lbl.equal z x then
               Node (x, Part.map_dedup (eq p_eq) part1 (fun pdt1 -> apply2_reduce p_eq vars f pdt1 (Node (y, part2))))
             else (if Lbl.equal z y then
                     Node (y, Part.map_dedup (eq p_eq) part2 (apply2_reduce p_eq vars f (Node (x, part1))))
                   else apply2_reduce p_eq vars f (Node (x, part1)) (Node (y, part2))))
    | _ -> raise (Invalid_argument "variable list is empty")

  let apply3_reduce p_eq vars f pdt1 pdt2 pdt3 =
    let p_eq2 (a, b) (a', b') = a == a' && b == b' in
    let pdt12 = apply2_reduce p_eq2 vars (fun a b -> (a, b)) pdt1 pdt2 in
    apply2_reduce p_eq vars (fun (a, b) c -> f a b c) pdt12 pdt3

  let rec split_prod_reduce p_eq = function
    | Leaf (l1, l2) -> (Leaf l1, Leaf l2)
    | Node (x, part) -> let (part1, part2) = Part.split_prod_dedup (eq p_eq) (Part.map part (split_prod_reduce p_eq)) in
                        (Node (x, part1), Node (x, part2))

  let rec split_list_reduce p_eq = function
    | Leaf l -> List.map l ~f:(fun el -> Leaf el)
    | Node (x, part) -> List.map (Part.split_list_dedup (eq p_eq) (Part.map part (split_list_reduce p_eq))) ~f:(fun el -> Node (x, el))

  let rec specialize_partial (v: Etc.valuation) = function
    | Leaf l -> Leaf l
    | Node (LEx x as lbl, part)
      | Node (LAll x as lbl, part) -> Node (lbl, Part.map part (specialize_partial (Map.remove v x)))
    | Node (x, part) ->
       match Lbl.eval v x with
       | Const d -> specialize_partial v (Part.find part d)
       | _ -> Node ((match x with
                     | LVar s               -> LVar s
                     | LClos (f, terms, v') -> LClos (f, List.map terms ~f:(Sig.eval v), v')),
                    Part.map part (specialize_partial v))

  let rec quantify ~forall x' = function
    | Leaf l -> Leaf l
    | Node (LVar x, part) when String.equal x x'  ->
       Node ((if forall then LAll x else LEx x), Part.map part (quantify ~forall x))
    | Node (LClos (f, trms, vars), part) ->
       let vars = if List.mem ~equal:String.equal (Term.fv_list trms) x' then
                    Set.add vars x'
                  else
                    vars in
       Node (LClos (f, trms, vars), Part.map part (quantify ~forall x'))
    | Node (lbl, part) -> Node (lbl, Part.map part (quantify ~forall x'))

  let distribute x callback v (s', p) =
    let update v x' d = Map.update v x' (fun _ -> d) in
    match s' with
    | Setc.Finite s' ->
       List.map (Set.elements s') ~f:(fun d -> callback (update v x d) p)
    | Complement s' -> [callback v p]

  let rec specialize f_ex f_all (v: Etc.valuation) =
    function
    | Leaf l -> l
    | Node (LVar x, part) when Map.mem v x ->
       specialize f_ex f_all v (Part.find part (Map.find_exn v x))
    | Node (LEx x, part) ->
       let all_p = List.concat (Part.map2 part (fun (s, p) ->
                                    distribute x (specialize f_ex f_all) v (s, p))) in
       f_ex all_p
    | Node (LAll x, part) ->
       let all_p = List.concat (Part.map2 part (fun (s, p) ->
                                    distribute x (specialize f_ex f_all) v (s, p))) in
       f_all all_p
    | Node (x, part) ->
       match Part.get_trivial part with
       | Some pdt -> specialize f_ex f_all v pdt
       | None     -> specialize f_ex f_all v (Part.find part (Term.unconst (Lbl.eval v x)))

  let rec collect f_leaf f_ex f_all (v: Etc.valuation) (x: string) p =
    let rec aux (v: Etc.valuation) (x: string) (s: (Dom.t, Dom.comparator_witness) Setc.t) =
      function
      | Leaf l when f_leaf l -> s
      | Leaf l -> Setc.empty (module Dom)
      | Node (LVar x', part) when String.equal x x' ->
         let s = Setc.union_list (module Dom)
                   (Part.map2 part (fun (s', p) -> aux v x (Setc.inter s s') p)) in
         s
      | Node (LVar x', part) ->
         let d = Map.find_exn v x' in
         aux v x s (Part.find part d)
      | Node (LEx x', part) ->
         let all_s = List.concat (Part.map2 part (distribute x' (fun v p -> aux v x s p) v)) in
         f_ex all_s
      | Node (LAll x', part) ->
         let all_s = List.concat (Part.map2 part (distribute x' (fun v p -> aux v x s p) v)) in
         f_all all_s
      | Node (LClos (f, terms, vars) as term, part) ->
         (match s, Part.get_trivial part with
          | _, Some p -> aux v x s p
          | Finite s, _ when
                 Set.is_subset
                   (Set.of_list (module String) (Term.fv_list terms))
                   ~of_:((Set.of_list (module String) (x :: (Map.keys v)))) ->
                let f d =
                  let v = Map.update v x (fun _ -> d) in
                  let d' = Term.unconst (Lbl.eval v term) in
                  aux v x (Setc.singleton (module Dom) d)
                    (snd (Part.find3 part (fun s -> Setc.mem s d'))) in
                let s = Setc.union_list (module Dom) (List.map (Set.elements s) ~f) in
                s
          | _ -> s)
    in aux v x (Setc.univ (module Dom)) p
    
  let rec from_valuation (lbls: Lbl.t list) (v: Etc.valuation) p p' =
    match lbls with
    | [] -> Leaf p
    | (LVar x)::lbls ->
       let d = Map.find_exn v x in
       let rest = from_valuation lbls v p p' in
       let part = Part.tabulate (Set.singleton (module Dom) d) (fun _ -> rest) (Leaf p') in
       Node (LVar x, part)
    | _::lbls -> from_valuation lbls v p p'

  let rec exquant = function
    | Leaf l              -> Leaf l
    | Node (LEx x,  part) -> Node (LAll x, Part.map part exquant)
    | Node (LAll x, part) -> Node (LEx x,  Part.map part exquant)
    | Node (lbl,    part) -> Node (lbl,    Part.map part exquant)

end

module type ProofT = sig

  type sp
  type vp

  type t = S of sp | V of vp

  val s_equal: sp -> sp -> bool
  val v_equal: vp -> vp -> bool
  val equal: t -> t -> bool

  val unS: t -> sp
  val unV: t -> vp
  val isS: t -> bool
  val isV: t -> bool

  val s_append: sp -> sp -> sp
  val v_append: vp -> vp -> vp
  val s_drop: sp -> sp option
  val v_drop: vp -> vp option

  val s_at: sp -> int
  val v_at: vp -> int
  val p_at: t -> int

  val s_ltp: sp -> int
  val v_etp: vp -> int

  val s_to_string: string -> sp -> string
  val v_to_string: string -> vp -> string
  val to_string: string -> t -> string
  val to_bool: t -> string

  val make_stt: int -> sp
  val make_seqconst: int -> Term.t -> Dom.t -> sp
  val make_spred: int -> string -> Term.t list -> sp
  val make_sneg: vp -> sp
  val make_sorl: sp -> sp
  val make_sorr: sp -> sp
  val make_sand: sp -> sp -> sp
  val make_simpl: vp -> sp
  val make_simpr: sp -> sp
  val make_siffss: sp -> sp -> sp
  val make_siffvv: vp -> vp -> sp
  val make_sexists: string -> Dom.t -> sp -> sp
  val make_sforall: string -> sp Part.t -> sp
  val make_sprev: sp -> sp
  val make_snext: sp -> sp
  val make_snextassm: int -> sp
  val make_sonce: int -> sp -> sp
  val make_seventually: int -> sp -> sp
  val make_seventuallyassm: int -> Interval.t -> sp
  val make_seventuallynow: sp -> Interval.t -> sp
  val make_shistorically: int -> int -> sp Fdeque.t -> sp
  val make_shistoricallyout: int -> sp
  val make_salways: int -> int -> sp Fdeque.t -> sp
  val make_salwaysassm: int -> sp option -> Interval.t -> sp
  val make_ssince: sp -> sp Fdeque.t -> sp
  val make_suntil: sp -> sp Fdeque.t -> sp
  val make_suntilassm: int -> sp -> Interval.t -> sp
  val make_suntilnow: sp -> Interval.t -> sp

  val make_vff: int -> vp
  val make_veqconst: int -> Term.t -> Dom.t -> vp
  val make_vpred: int -> string -> Term.t list -> vp
  val make_vneg: sp -> vp
  val make_vor: vp -> vp -> vp
  val make_vandl: vp -> vp
  val make_vandr: vp -> vp
  val make_vimp: sp -> vp -> vp
  val make_viffsv: sp -> vp -> vp
  val make_viffvs: vp -> sp -> vp
  val make_vexists: string -> vp Part.t -> vp
  val make_vforall: string -> Dom.t -> vp -> vp
  val make_vprev: vp -> vp
  val make_vprev0: vp
  val make_vprevoutl: int -> vp
  val make_vprevoutr: int -> vp
  val make_vnext: vp -> vp
  val make_vnextoutl: int -> vp
  val make_vnextoutr: int -> vp
  val make_vnextassm: int -> Interval.t -> vp
  val make_vonceout: int -> vp
  val make_vonce: int -> int -> vp Fdeque.t -> vp
  val make_veventually: int -> int -> vp Fdeque.t -> vp
  val make_veventuallyassm: int -> vp option -> Interval.t -> vp
  val make_vhistorically: int -> vp -> vp
  val make_valways: int -> vp -> vp
  val make_valwaysassm: int -> Interval.t -> vp
  val make_valwaysnow: vp -> Interval.t -> vp
  val make_vsinceout: int -> vp
  val make_vsince: int -> vp -> vp Fdeque.t -> vp
  val make_vsinceinf: int -> int -> vp Fdeque.t -> vp
  val make_vuntil: int -> vp -> vp Fdeque.t -> vp
  val make_vuntilinf: int -> int -> vp Fdeque.t -> vp
  val make_vuntilassm: int -> vp -> Interval.t -> vp
  val make_vuntilnow: vp -> Interval.t -> vp

  val decompose_vsince: vp -> (vp * vp Fdeque.t) option
  val decompose_vuntil: vp -> (vp * vp Fdeque.t) option
  
  module Size : sig

    val minp_bool: t -> t -> bool
    val minp: t -> t -> t
    val minp_list: t list -> t

  end

end

module type ExplT = sig

  module Proof: ProofT
  type t = Proof.t Pdt.t

  val is_violated: t -> bool
  val is_satisfied: t -> bool
  val at: t -> int

  val to_string: t -> string
  val to_light_string: t -> string
  
  val pdt_of: int -> string -> Term.t list -> Lbl.t list -> (Lbl.t, Dom.t, 'a) Map.t list -> Proof.t Pdt.t

  val table_operator: (Dom.t list list -> Dom.t list list) -> string list -> int -> Term.t list -> string list -> Lbl.t list -> Lbl.t list -> t -> t
  val aggregate: ((Dom.t, Dom.comparator_witness) Multiset.t -> Dom.t) -> string -> int -> Term.t -> string list -> Lbl.t list -> Lbl.t list -> t -> t
  
end

type t_sp =
  | STT of int
  | SEqConst of int * Term.t * Dom.t
  | SPred of int * string * Term.t list
  | SNeg of t_vp
  | SOrL of t_sp
  | SOrR of t_sp
  | SAnd of t_sp * t_sp
  | SImpL of t_vp
  | SImpR of t_sp
  | SIffSS of t_sp * t_sp
  | SIffVV of t_vp * t_vp
  | SExists of string * Dom.t * t_sp
  | SForall of string * (t_sp Part.t)
  | SPrev of t_sp
  | SNext of t_sp
  | SNextAssm of int
  | SOnce of int * t_sp
  | SEventually of int * t_sp
  | SEventuallyAssm of int * Interval.t
  | SEventuallyNow of t_sp * Interval.t
  | SHistorically of int * int * t_sp Fdeque.t
  | SHistoricallyOut of int
  | SAlways of int * int * t_sp Fdeque.t
  | SAlwaysAssm of int * t_sp option * Interval.t
  | SSince of t_sp * t_sp Fdeque.t
  | SUntil of t_sp * t_sp Fdeque.t
  | SUntilAssm of int * t_sp * Interval.t
  | SUntilNow of t_sp * Interval.t
and t_vp =
  | VFF of int
  | VEqConst of int * Term.t * Dom.t
  | VPred of int * string * Term.t list
  | VNeg of t_sp
  | VOr of t_vp * t_vp
  | VAndL of t_vp
  | VAndR of t_vp
  | VImp of t_sp * t_vp
  | VIffSV of t_sp * t_vp
  | VIffVS of t_vp * t_sp
  | VExists of string * (t_vp Part.t)
  | VForall of string * Dom.t * t_vp
  | VPrev of t_vp
  | VPrev0
  | VPrevOutL of int
  | VPrevOutR of int
  | VNext of t_vp
  | VNextOutL of int
  | VNextOutR of int
  | VNextAssm of int * Interval.t
  | VOnceOut of int
  | VOnce of int * int * t_vp Fdeque.t
  | VEventually of int * int * t_vp Fdeque.t
  | VEventuallyAssm of int * t_vp option * Interval.t
  | VHistorically of int * t_vp
  | VAlways of int * t_vp
  | VAlwaysAssm of int * Interval.t
  | VAlwaysNow of t_vp * Interval.t
  | VSinceOut of int
  | VSince of int * t_vp * t_vp Fdeque.t
  | VSinceInf of int * int * t_vp Fdeque.t
  | VUntil of int * t_vp * t_vp Fdeque.t
  | VUntilInf of int * int * t_vp Fdeque.t
  | VUntilAssm of int * t_vp * Interval.t
  | VUntilNow of t_vp * Interval.t


module LightProof : ProofT with type sp = int and type vp = int = struct

  type sp = int
  type vp = int
  
  type t = S of sp | V of vp

  let rec s_equal x y = true
  let rec v_equal x y = true
 
  let equal x y = match x, y with
    | S sp1, S sp2 -> true
    | V vp1, V vp2 -> true
    | _ -> false

  let unS = function
    | S tp -> tp
    | _ -> raise (Invalid_argument "unS is not defined for V proofs")

  let unV = function
    | V tp -> tp
    | _ -> raise (Invalid_argument "unV is not defined for S proofs")

  let isS = function
    | S _ -> true
    | V _ -> false

  let isV = function
    | S _ -> false
    | V _ -> true

  let s_append sp sp1 = sp

  let v_append vp vp2 = vp

  let s_drop _ = None

  let v_drop _ = None

  let s_at sp = sp
  let v_at vp = vp

  let p_at = function
    | S sp -> s_at sp
    | V vp -> v_at vp

  let s_ltp _ = 0

  let v_etp _ = 0

  let cmp f p1 p2 = f p1 <= f p2

  let s_to_string indent sp =
    Printf.sprintf "%strue{%d}" indent sp

  let v_to_string indent vp =
    Printf.sprintf "%sfalse{%d}" indent vp

  let to_string indent = function
    | S sp -> s_to_string indent sp
    | V vp -> v_to_string indent vp

  let to_bool = function 
    | S _ -> "true\n"
    | V _ -> "false\n"

  let make_stt tp = tp
  let make_seqconst tp x c = tp
  let make_spred tp r terms = tp
  let make_sneg vp = vp
  let make_sorl sp = sp
  let make_sorr sp = sp
  let make_sand sp1 sp2 = sp1
  let make_simpl vp = vp
  let make_simpr sp = sp
  let make_siffss sp1 sp2 = sp1
  let make_siffvv vp1 vp2 = vp1
  let make_sexists x d sp = sp
  let make_sforall x sps = Part.hd sps
  let make_sprev sp = sp + 1
  let make_snext sp = sp - 1
  let make_snextassm tp = tp 
  let make_sonce tp sp = tp
  let make_seventually tp sp = tp
  let make_seventuallyassm tp i = tp
  let make_seventuallynow sp i = sp
  let make_shistorically tp ltp sps = tp
  let make_shistoricallyout tp = tp
  let make_salways tp ltp sps = tp
  let make_salwaysassm tp sp_opt i = tp
  let make_ssince sp sps = sp
  let make_suntil sp sps = sp
  let make_suntilassm tp sp i = tp
  let make_suntilnow sp i = sp

  let make_vff tp = tp
  let make_veqconst tp x c = tp
  let make_vpred tp r terms = tp
  let make_vneg sp = sp
  let make_vor vp1 vp2 = vp1
  let make_vandl vp = vp
  let make_vandr vp = vp
  let make_vimp sp vp = sp
  let make_viffsv sp vp = sp
  let make_viffvs vp sp = vp
  let make_vexists x vps = Part.hd vps
  let make_vforall x d vp = vp
  let make_vprev vp = vp + 1
  let make_vprev0 = 0
  let make_vprevoutl tp = tp
  let make_vprevoutr tp = tp
  let make_vnext vp = vp - 1
  let make_vnextoutl tp = tp
  let make_vnextoutr tp = tp
  let make_vnextassm tp i = tp
  let make_vonceout tp = tp
  let make_vonce tp ltp vps = tp
  let make_veventually tp ltp vps = tp
  let make_veventuallyassm tp vp_opt i = tp
  let make_vhistorically tp vp = tp
  let make_valways tp vp = tp
  let make_valwaysassm tp i = tp
  let make_valwaysnow vp i = vp
  let make_vsinceout tp = tp
  let make_vsince tp vp vps = tp
  let make_vsinceinf tp ltp vps = tp
  let make_vuntil tp vp vps = tp
  let make_vuntilinf tp ltp vps = tp
  let make_vuntilassm tp vp i = tp
  let make_vuntilnow vp i = vp

  let decompose_vsince vp = Some (vp, Fdeque.of_list [])

  let decompose_vuntil vp = Some (vp, Fdeque.of_list [])

  module Size = struct

    let minp_bool _ _ = true
    let minp x y = x
    let minp_list = function
      | [] -> raise (Invalid_argument "function not defined for empty lists")
      | x :: xs -> x

  end

end

module Make (P: ProofT) = struct

  module Proof = P
  type t = Proof.t Pdt.t

  let rec is_violated = function
    | Pdt.Leaf l -> (match l with
                     | Proof.S _ -> false
                     | V _ -> true)
    | Node (x, part) -> Part.exists part is_violated

  let rec is_satisfied = function
    | Pdt.Leaf l -> (match l with
                     | Proof.S _ -> true
                     | V _ -> false)
    | Node (x, part) -> Part.exists part is_satisfied

  let rec at = function
    | Pdt.Leaf pt -> Proof.p_at pt
    | Node (_, part) -> at (Part.hd part)

  let to_string expl = Pdt.to_string (Proof.to_string "") "" expl

  let to_light_string expl = Pdt.to_light_string Proof.to_bool "" expl

  let rec pdt_of tp r trms (lbls: Lbl.t list) maps : t = match lbls with
    | [] -> Leaf (S (Proof.make_spred tp r trms))
    | lbl :: lbls ->
       let ds = List.filter_map maps ~f:(fun map -> Map.find map lbl) in
       let find_maps d =
         List.filter_map maps ~f:(fun map -> match Map.find map lbl with
                                             | Some d' when Dom.equal d d' -> Some map
                                             | _ -> None)  in
       if List.is_empty ds then
         pdt_of tp r trms lbls maps
       else
         let part = Part.tabulate_dedup (Pdt.eq Proof.equal) (Set.of_list (module Dom) ds)
                      (fun d -> pdt_of tp r trms lbls (find_maps d))
                      (Leaf (V (Proof.make_vpred tp r trms))) in
         Node (lbl, part)

  (* [s_1, ..., s_k] <- OP (y; f) where p is a Pdt for f *)
  let table_operator (op: Dom.t list list -> Dom.t list list) (s: string list) tp x y lbls lbls' p =
    let merge_pdts merge = function
         | [pdt] -> pdt
         | pdt::pdts -> List.fold pdts ~init:pdt
                          ~f:(Pdt.apply2_reduce (List.equal Etc.equal_valuation) lbls' merge) in
    let tabulate sv =
      let aux vs = function
        | (Term.Var x, Setc.Finite s) ->
           List.concat_map (Set.elements s) ~f:(fun d -> List.map vs (fun v -> Map.update v x ~f:(fun _ -> d)))
        | (Term.Const d, s) when Setc.mem s d -> vs
        | (Term.Const _, _) -> []
        | (trm, s) -> List.filter vs ~f:(fun v -> Setc.mem s (Term.unconst (Sig.eval v trm))) in
      List.fold_left sv ~init:([Map.empty (module String)]) ~f:aux in 
    let rec gather sv gs trms w p  =
      (*print_endline "--gather"; 
      print_endline (String.concat ~sep:", " (List.map ~f:Lbl.to_string trms));
      print_endline (String.concat ~sep:", " gs);*)
      match p, gs, trms with
      | Pdt.Leaf l, _, _ when Proof.isS l ->
         Pdt.Leaf (tabulate (List.rev sv))
      | Leaf l, _, _ -> Leaf []
      | Node (lbl, _), g :: gs, trm :: trms
           when not (Lbl.equal trm lbl) && Lbl.equal trm (LVar g) ->
         gather sv gs trms w p
      | Node (lbl, _), _, trm :: trms when not (Lbl.equal trm lbl) ->
         gather sv gs trms w p
      | Node (lbl, part), g :: gs, _ :: trms when Lbl.equal (LVar g) lbl ->
         let part = Part.map2 part (fun (s, p) -> (s, gather ((Var g, s)::sv) gs trms w p)) in
         Node (lbl, part)
      | Node (LEx x', part), _, _ :: trms ->
         let pdts = List.concat (Part.map2 part (Pdt.distribute x' (gather sv gs trms) w)) in
         merge_pdts (@) pdts 
      | Node (LAll x', part), _, _ :: trms ->
         let pdts = List.concat (Part.map2 part (Pdt.distribute x' (gather sv gs trms) w)) in
         merge_pdts (fun l l' -> List.filter l (List.mem l' ~equal:Etc.equal_valuation)) pdts 
      | Node (lbl, part), _, _ :: trms ->
         let pdts = Part.map2 part (fun (s, p) -> gather ((Lbl.term lbl, s)::sv) gs trms w p) in
         merge_pdts (@) pdts in
    let rec collect_leaf_values x = function
      | Pdt.Leaf None  -> Set.empty (module Dom)
      | Leaf (Some vs) -> Set.of_list (module Dom) (List.map ~f:(fun v -> Map.find_exn v x) vs)
      | Node (_, part) -> Set.union_list (module Dom)
                            (List.map part ~f:(fun (_, pdt) -> collect_leaf_values x pdt)) in
    let rec insert lbls (v: Etc.valuation) (pdt: Etc.valuation list option Pdt.t) =
      (*print_endline ("--insert_aggregations");
      print_endline ("insert_aggregations.lbls=" ^ String.concat ~sep:", " (List.map ~f:Lbl.to_strigbng lbls));*)
      (*let print_pdt pdt =
        Pdt.to_string (fun vs_opt ->
            match vs_opt with
            | None -> ""
            | Some vs -> Etc.list_to_string "" (fun _ -> Etc.valuation_to_string) vs) "" pdt in
      print_endline ("insert_aggregations.pdt =" ^ print_pdt pdt);*)
(*      print_endline ("insert_aggregations.s   =" ^ Etc.list_to_string "" (fun _ x -> x) s);*)
      let r = "~aggregate" and trms = List.map ~f:Term.var s in
      match pdt, lbls with
      | _, (Lbl.LVar x') :: lbls when List.mem s x' ~equal:String.equal ->
         (*print_endline "case 1";*)
         let ds = collect_leaf_values x' pdt in
         (if Set.is_empty ds then
            Pdt.Leaf (P.V (Proof.make_vpred tp r trms))
          else
            let v d = Map.update v x' (fun _ -> d) in
            let parts = Part.tabulate_dedup (Pdt.eq Proof.equal) ds
                          (fun d -> insert lbls (v d) pdt)
                          (Leaf (V (Proof.make_vpred tp r trms))) in
            Pdt.Node (Lbl.LVar x', parts)
            (*print_endline ("p=" ^ Pdt.to_string (P.to_string "") "" p);         
            p*))
      | Node (lbl', part), lbl :: lbls when Lbl.equal lbl lbl' ->
         (*print_endline "case 2";*)
         (*let p = *)Pdt.Node (lbl', Part.map part (insert lbls v))(* in*)
         (*print_endline ("p=" ^ Pdt.to_string (P.to_string "") "" p);
         p*)
      | Node _, _ :: lbls ->
         (*print_endline "case 3";*)
         insert lbls v pdt
      | Leaf (Some vs), _ ->
         if List.exists vs ~f:(fun v' ->
                Map.for_alli v ~f:(fun ~key ~data -> Dom.equal (Map.find_exn v' key) data))
         then Pdt.Leaf (S (Proof.make_spred tp r trms))
         else Pdt.Leaf (V (Proof.make_vpred tp r trms))
      | Leaf None, _ ->
         Pdt.Leaf (V (Proof.make_vpred tp r trms))
    in
    let apply_op (vs: Etc.valuation list) : Etc.valuation list option =
      if List.is_empty vs && List.length y > 0
      then None
      else (
        let dss = List.map ~f:(fun v -> List.map ~f:(fun x -> Term.unconst (Sig.eval v x)) x) vs in
        
        let vs = List.map ~f:(fun v -> Map.of_alist_exn (module String) (List.zip_exn s v)) (op dss) in
        Some vs) in
    insert lbls Etc.empty_valuation
      (Pdt.apply1 lbls' apply_op (gather [] y lbls' Etc.empty_valuation p))

  let aggregate (agg: (Dom.t, Dom.comparator_witness) Multiset.t -> Dom.t) s tp x_trm y lbls lbls' p =
    let multiset dss = Multiset.of_list (module Dom) (List.map ~f:List.hd_exn dss) in
    table_operator (fun dss -> [[agg (multiset dss)]]) [s] tp [x_trm] y lbls lbls' p


end
