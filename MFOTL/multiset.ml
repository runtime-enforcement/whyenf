open Base

type ('a, 'b) t = ('a, int, 'b) Map.t

let is_empty (m: ('a, 'b) t) = Map.is_empty m

let empty mo = Map.empty mo

let equal m m' = Map.equal Int.equal m m'

let fold (m: ('a, 'b) t) ~init ~f =
  let f ~key ~data acc = f ~value:key ~card:data acc in
  Map.fold m ~init ~f

let card (m: ('a, 'b) t) =
  Map.fold m ~init:0 ~f:(fun ~key:_ ~data acc -> data + acc)

let median ~compare (m: ('a, 'b) t) =
  let xs = Map.to_alist m in
  let xs = List.sort xs ~compare:(fun (k, _) (k', _) -> compare k k') in
  let total = List.fold_left xs ~init:0 ~f:(fun sum (_, v) -> sum + v) in
  let sums_xs = snd (List.fold_left xs ~init:(0, [])
                       ~f:(fun (sum, sums) (k, i) -> (sum + i, (k, sum + i)::sums))) in
  fst (List.find_exn sums_xs ~f:(fun (_, sum) -> sum >= total / 2))

let min (m: ('a, 'b) t) = fst (Map.min_elt_exn m)
let max (m: ('a, 'b) t) = fst (Map.max_elt_exn m)

let map mo ~f (m: ('a, 'b) t) =
  let xs = Map.to_alist m in
  let xs = List.map ~f:(fun (k, v) -> (f k, v)) xs in
  Map.of_alist_fold mo xs ~init:0 ~f:(+)

let fold_merge mo fun_both fun_one m m' =
  Map.fold2 m m' ~init:(Map.empty mo) ~f:(fun ~key ~data m ->
      match data with
      | `Both (data, data')      -> Map.add_exn m ~key ~data:(fun_both data data')
      | `Left data | `Right data -> Map.add_exn m ~key ~data:(fun_one data))

let append m k = Map.update m k ~f:(function None -> 1 | Some v -> v)

let add   mo (m: ('a, 'b) t) (m': ('a, 'b) t) = fold_merge mo (+)     (fun x -> x) m m'
let union mo (m: ('a, 'b) t) (m': ('a, 'b) t) = fold_merge mo Int.max (fun x -> x) m m'
let inter mo (m: ('a, 'b) t) (m': ('a, 'b) t) = fold_merge mo Int.min (fun _ -> 0) m m'

let of_list mo l = List.fold_left l ~init:(empty mo) ~f:append
