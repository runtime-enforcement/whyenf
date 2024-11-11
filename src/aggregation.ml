open Base

type op = ASum | AAvg | AMed | ACnt | AMin | AMax | AStd | AAssign
  [@@deriving compare, sexp_of, hash, equal]

type op_fun = (Dom.t, Dom.comparator_witness) Multiset.t -> Dom.t
type op_tfun = Dom.t list list -> Dom.t list list

let op_to_string = function
  | ASum -> "SUM"
  | AAvg -> "AVG"
  | AMed -> "MED"
  | ACnt -> "CNT"
  | AMin -> "MIN"
  | AMax -> "MAX"
  | AStd -> "STD"
  | AAssign -> "ASSIGN"

let init = function
  | Sformula.Aop.ASum -> ASum
  | AAvg -> AAvg
  | AMed -> AMed
  | ACnt -> ACnt
  | AMin -> AMin
  | AMax -> AMax
  | AStd -> AStd

(* Order terms in lbls' to fulfill the following invariants:
    * all variables in y, ordered as in lbls, come first
    * then comes x
    * then come all other variables not in x or y
    * any term using a variable z comes after z
 *)
let order_lbls lbls lbls' x y =
  let vars  = List.filter lbls ~f:Lbl.is_var in
  let lbls1 = (Etc.reorder Lbl.equal (List.map y ~f:Lbl.var) vars) @ [x] in
  let lbls2 = List.filter lbls' ~f:(fun lbl -> not (List.mem lbls1 lbl ~equal:Lbl.equal)) in
  lbls1 @ lbls2

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
  | AStd, Dom.TFloat -> Some Dom.TFloat
  | AAssign, x       -> Some x
  | _                -> None

let ret_tt_exn op tt =
  Option.value_exn (ret_tt op tt)

let eval op tt m =
  match op, tt with
  | ASum, Dom.TInt ->
     let f ~value ~card acc = acc + (Dom.to_int_exn value) * card in
     Dom.Int (Multiset.fold m ~init:0 ~f)
  | ASum, Dom.TFloat ->
     let f ~value ~card acc = acc +. (Dom.to_float_exn value) *. (float_of_int card) in
     Dom.Float (Multiset.fold m ~init:0. ~f)
  | AAvg, Dom.TInt ->
     let f ~value ~card acc = acc + (Dom.to_int_exn value) * card in
     if Multiset.is_empty m then
       Dom.Int 0
     else
       Dom.Int (Multiset.fold m ~init:0 ~f / Multiset.card m)
  | AAvg, Dom.TFloat ->
     let f ~value ~card acc = acc +. (Dom.to_float_exn value) *. (float_of_int card) in
     if Multiset.is_empty m then
       Dom.Float 0.
     else
       Dom.Float (Multiset.fold m ~init:0. ~f /. float_of_int (Multiset.card m))
  | AMed, Dom.TInt ->
     if Multiset.is_empty m then
       Dom.Int 0
     else
       Multiset.median ~compare:Dom.compare m
  | AMed, Dom.TFloat ->
     if Multiset.is_empty m then
       Dom.Int 0
     else
       Multiset.median ~compare:Dom.compare m
  | ACnt, _ ->
     Dom.Int (Multiset.card m)
  | AMin, Dom.TInt ->
     if Multiset.is_empty m then
       Dom.Int Int.max_value
     else
       Multiset.min m
  | AMin, Dom.TFloat ->
     if Multiset.is_empty m then
       Dom.Float Float.max_value
     else
       Multiset.max m
  | AMax, Dom.TInt ->
     if Multiset.is_empty m then
       Dom.Int Int.min_value
     else
       Multiset.max m
  | AMin, Dom.TFloat ->
     if Multiset.is_empty m then
       Dom.Float Float.min_value
     else
       Multiset.min m
  | AStd, Dom.TFloat ->
     if Multiset.is_empty m then
       Dom.Float 0.
     else
       let f ~value ~card acc = acc +. (Dom.to_float_exn value) *. (float_of_int card) in
       let a = Multiset.fold m ~init:0. ~f /. float_of_int (Multiset.card m) in
       let center_and_square = function Dom.Float x -> Dom.Float ((x -. a) **. 2.) in
       let m_sq = Multiset.map (module Dom) ~f:center_and_square m in
       Dom.Float (Float.sqrt (Multiset.fold m_sq ~init:0. ~f /. float_of_int (Multiset.card m_sq)))
  | AAssign, ty ->
     Multiset.min m
  | _, _ -> assert false
