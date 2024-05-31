open Base

type op = ASum | AAvg | AMed | ACnt | AMin | AMax [@@deriving compare, sexp_of, hash, equal]

type op_fun = (Dom.t, int, Dom.comparator_witness) Map.t -> Dom.t

let op_to_string = function
  | ASum -> "SUM"
  | AAvg -> "AVG"
  | AMed -> "MED"
  | ACnt -> "CNT"
  | AMin -> "MIN"
  | AMax -> "MAX"

(* Order terms in trms' to fulfill the following invariants:
    * all variables in y, ordered as in trms, come first
    * then comes x
    * then come all other variables not in x or y
    * any term using a variable z comes after z
 *)
let order_trms trms trms' x y =
  let vars  = Pred.Term.filter_vars trms in
  let trms1 = List.map (Etc.reorder String.equal y vars) ~f:Pred.Term.var @ [x] in
  let trms2 = List.filter trms' ~f:(fun trm -> not (List.mem trms1 trm ~equal:Pred.Term.equal)) in
  trms1 @ trms2


let median compare xs =
  let xs = List.sort xs ~compare:(fun (k, _) (k', _) -> compare k k') in
  let total = List.fold_left xs ~init:0 ~f:(fun sum (_, v) -> sum + v) in
  let sums_xs = snd (List.fold_left xs ~init:(0, [])
                       ~f:(fun (sum, sums) (k, i) -> (sum + i, (k, sum + i)::sums))) in
  fst (List.find_exn sums_xs ~f:(fun (_, sum) -> sum >= total / 2))

let ret_tt op tt =
  match op, tt with
  | ASum, Dom.TInt   -> Some Dom.TInt
  | ASum, Dom.TFloat -> Some Dom.TFloat
  | AAvg, Dom.TInt   -> Some Dom.TInt
  | AAvg, Dom.TFloat -> Some Dom.TFloat
  | AMed, Dom.TInt   -> Some Dom.TInt
  | AMed, Dom.TFloat -> Some Dom.TFloat
  | ACnt, _          -> Some Dom.TInt
  | AMin, Dom.TInt   -> Some Dom.TInt
  | AMin, Dom.TFloat -> Some Dom.TFloat
  | AMax, Dom.TInt   -> Some Dom.TInt
  | AMax, Dom.TFloat -> Some Dom.TFloat
  | _                -> None

let ret_tt_exn op tt =
  Option.value_exn (ret_tt op tt)

let eval op tt m =
  match op, tt with
  | ASum, Dom.TInt ->
     let f ~key ~data acc = acc + (Dom.to_int_exn key) * data in
     Dom.Int (Map.fold m ~init:0 ~f)
  | ASum, Dom.TFloat ->
     let f ~key ~data acc = acc +. (Dom.to_float_exn key) *. (float_of_int data) in
     Dom.Float (Map.fold m ~init:0. ~f)
  | AAvg, Dom.TInt ->
     let f ~key ~data acc = acc + (Dom.to_int_exn key) * data in
     let g ~key ~data acc = acc + data in
     if Map.is_empty m then
       Dom.Int 0
     else
       Dom.Int (Map.fold m ~init:0 ~f / Map.fold m ~init:0 ~f:g)
  | AAvg, Dom.TFloat ->
     let f ~key ~data acc = acc +. (Dom.to_float_exn key) *. (float_of_int data) in
     let g ~key ~data acc = acc + data in
     if Map.is_empty m then
       Dom.Float 0.
     else
       Dom.Float (Map.fold m ~init:0. ~f /. (float_of_int (Map.fold m ~init:0 ~f:g)))
  | AMed, Dom.TInt ->
     if Map.is_empty m then
       Dom.Int 0
     else
       median Dom.compare (Map.to_alist m)
  | AMed, Dom.TFloat ->
     if Map.is_empty m then
       Dom.Int 0
     else
       median Dom.compare (Map.to_alist m)
  | ACnt, _ ->
     let f ~key ~data acc = acc + data in
     if Map.is_empty m then
       Dom.Int 0
     else
       Dom.Int (Map.fold m ~init:0 ~f)
  | AMin, Dom.TInt ->
     if Map.is_empty m then
       Dom.Int Int.max_value
     else
       fst (Map.min_elt_exn m)
  | AMin, Dom.TFloat ->
     if Map.is_empty m then
       Dom.Float Float.max_value
     else
       fst (Map.min_elt_exn m)
  | AMax, Dom.TInt ->
     if Map.is_empty m then
       Dom.Int Int.min_value
     else
       fst (Map.max_elt_exn m)
  | AMin, Dom.TFloat ->
     if Map.is_empty m then
       Dom.Float Float.min_value
     else
       fst (Map.max_elt_exn m)
  | _, _ -> assert false
