open Base

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm

module type L = sig

  type t [@@deriving equal, compare]

  val minimum : t list -> t

  val to_string : t -> string

end

module Part = struct

  type sub = (Dom.t, Dom.comparator_witness) Setc.t

  type 'a t = (sub * 'a) list

  (*let random_empty_set = Set.empty (module String)*)

  let trivial p = [(Setc.univ (module Dom), p)]

  let get_trivial = function
    | [(s, p)] when Setc.is_univ s -> Some p
    | _ -> None

  let hd part = snd (List.hd_exn part)

  let length part = List.length part

  let map part f = List.map part ~f:(fun (s, p) -> (s, f p))

  let map2 part f = List.map part ~f:(fun (s, p) -> f (s, p))

  let fold_left part init f = List.fold_left part ~init:init ~f:(fun acc (_, p) -> f acc p)

  (*let fold_left2 part init f = List.fold_left part ~init:init ~f:(fun acc (d, p) -> f acc d p)*)

  let filter part f = List.filter part ~f:(fun (_, p) -> f p)

  let exists part f = List.exists part ~f:(fun (_, p) -> f p)

  let for_all part f = List.for_all part ~f:(fun (_, p) -> f p)

  let values part = List.map part ~f:(fun (_, p) -> p)

  let find part x = snd (List.find_exn part ~f:(fun (s, _) -> Setc.mem s x))

  let find2 part f = List.find_exn part ~f:(fun (s, _) -> f s)

  let tabulate ds f z =
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
      | _ , _ , [] -> raise (Errors.MonitoringError "one of the partitions is empty")
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
            ^ String.concat ~sep:"\n" (List.map xs ~f:(el_to_string indent s f)) ^ "\n"
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

  let map_dedup p_eq f part = dedup p_eq (map part f)

  let map2_dedup p_eq f part = dedup p_eq (map2 part f)

  let tabulate_dedup p_eq ds f z = dedup p_eq (tabulate ds f z)

  let merge2_dedup p_eq f part1 part2 = dedup p_eq (merge2 f part1 part2)

  let split_prod_dedup p_eq part =
    let part1, part2 = split_prod part in
    (dedup p_eq part1, dedup p_eq part2)

  let split_list_dedup p_eq part = List.map (split_list part) ~f:(dedup p_eq)

  let rec join_parts ps = match ps with 
    | [] -> trivial []
    | [p] -> List.map ~f:(fun (sub, x) -> (sub, [x])) p
    | p :: ps -> merge2 (fun x y -> x :: y) p (join_parts ps)


end

module Make (Lbl : L) = struct

  type 'a t = Leaf of 'a | Node of Lbl.t * ('a t) Part.t

  let is_leaf = function
    | Leaf _ -> true
    | Node _ -> false

  let unleaf = function
    | Leaf l -> Some l
    | _ -> None
  
  let unleaf_exn = function
    | Leaf l -> l
    | _ -> raise (Errors.EnforcementError "function not defined for nodes")
  
  let rec papply_list f xs ys = match xs, ys with 
    | [], _ -> f ys
    | None :: xs, y :: ys -> papply_list (fun zs -> f (y :: zs)) xs ys 
    | Some x :: xs, ys -> papply_list (fun zs -> f (x :: zs)) xs ys 
    | _, _ -> raise (Errors.EnforcementError "cannot use papply_list if the ys list is empty")
  
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

  (* reduce related *)
  let rec eq p_eq pdt1 pdt2 =
    match pdt1, pdt2 with
    | Leaf l1, Leaf l2 -> p_eq l1 l2
    | Node (x, part), Node (x', part') ->
       Lbl.equal x x' && Int.equal (Part.length part) (Part.length part') &&
         List.for_all2_exn part part' ~f:(fun (s, v) (s', v') ->
             Setc.equal s s' && eq p_eq v v')
    | _ -> false

  let simplify = function
    | Leaf l -> Leaf l
    | Node (x, part) ->
      match Part.get_trivial part with
      | Some pdt -> pdt
      | None -> Node (x, part)
        
  let rec reduce p_eq = function
    | Leaf l -> Leaf l
    | Node (x, part) -> simplify (Node (x, Part.dedup (eq p_eq) (Part.map part (reduce p_eq))))

  let rec apply1_reduce p_eq f proj pdt = match pdt with
    | Leaf l -> Leaf (f l)
    | Node (x, part) ->
      simplify (Node (proj x, Part.map_dedup (eq p_eq) (apply1_reduce p_eq f proj) part))
    | _ -> raise (Errors.EnforcementError "variable list is empty")

  let rec apply2_reduce p_eq f proj1 proj2 pdt1 pdt2 = match pdt1, pdt2 with
    | Leaf l1, Leaf l2 -> Leaf (f l1 l2)
    | Leaf l1, Node (x, part2) ->
       simplify (Node (x, Part.map_dedup (eq p_eq) (apply1_reduce p_eq (f l1) proj2) part2))
    | Node (x, part1), Leaf l2 ->
       simplify (Node (x, Part.map_dedup (eq p_eq) (apply1_reduce p_eq (fun l1 -> f l1 l2) proj1) part1))
    | Node (x, part1), Node (y, part2) ->
       if Lbl.equal (proj1 x) (proj2 y) then
         simplify (Node (proj1 x, Part.merge2_dedup (eq p_eq) (apply2_reduce p_eq f proj1 proj2) part1 part2))
       else (if Lbl.compare (proj1 x) (proj2 y) < 0 then
               simplify (Node (proj1 x, Part.map_dedup (eq p_eq) (fun pdt1 -> apply2_reduce p_eq f proj1 proj2 pdt1 (Node (y, part2))) part1))
             else simplify (Node (proj2 y, Part.map_dedup (eq p_eq) (apply2_reduce p_eq f proj1 proj2 (Node (x, part1))) part2)))
    | _ -> raise (Errors.EnforcementError "variable list is empty")

  let apply3_reduce p_eq f proj1 proj2 proj3 pdt1 pdt2 pdt3 =
    let p_eq2 (a, b) (a', b') = phys_equal a a' && phys_equal b b' in
    let pdt12 = apply2_reduce p_eq2 (fun a b -> (a, b)) proj1 proj2 pdt1 pdt2 in
    apply2_reduce p_eq (fun (a, b) c -> f a b c) proj2 proj3 pdt12 pdt3

  let rec applyN_reduce p_eq f projs_pdts : 'a t = 
    let f' = papply_list f (List.map ~f:(fun (_, pdt) -> unleaf pdt) projs_pdts) in
    let projs_nodes = List.filter ~f:(fun (_, pdt) -> not (is_leaf pdt)) projs_pdts in
    if not (List.is_empty projs_nodes) then begin
      let ws = List.filter_map
          ~f:(function (proj, Node (x, _)) -> Some (proj x) | _ -> None)
          projs_nodes in
      let w = Lbl.minimum ws in
      let f_other_nodes (proj, pdt) = match pdt with
        | Node (x, _) when Lbl.equal (proj x) w -> None
        | pdt -> Some (proj, pdt) in
      let other_projs_nodes = List.map ~f:f_other_nodes projs_nodes in
      let f_w_parts (proj, pdt) = match pdt with
        | Node (x, part) when Lbl.equal (proj x) w -> Some (Part.map part (fun s -> (proj, s)))
        | _ -> None in
      let w_parts = List.filter_map ~f:f_w_parts projs_nodes in
      if List.is_empty w_parts then
        applyN_reduce p_eq f' projs_nodes
      else
        simplify
          ((Node (w, Part.map_dedup (eq p_eq)
                    (fun pdts -> papply_list (applyN_reduce p_eq f') other_projs_nodes pdts)
                    (Part.join_parts w_parts))))
    end
    else
      Leaf (f (List.map projs_pdts ~f:(fun (_, pdt) -> unleaf_exn pdt)))

  let rec split_prod_reduce p_eq = function
    | Leaf (l1, l2) -> (Leaf l1, Leaf l2)
    | Node (x, part) -> let (part1, part2) = Part.split_prod_dedup (eq p_eq) (Part.map part (split_prod_reduce p_eq)) in
                        (Node (x, part1), Node (x, part2))

  let rec split_list_reduce p_eq = function
    | Leaf l -> List.map l ~f:(fun el -> Leaf el)
    | Node (x, part) -> List.map (Part.split_list_dedup (eq p_eq) (Part.map part (split_list_reduce p_eq))) ~f:(fun el -> Node (x, el))


end

