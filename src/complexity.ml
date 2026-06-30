(* Symbolic (big-O) cost expressions for the compiled enfflash program.

   A [t] denotes an asymptotic bound on the per-time-point work of the engine
   in [enfflash/src/engine.rs], symbolic in the cardinalities of the relations
   it joins.  [Card s] is "the number of tuples currently held by relation [s]"
   (a table or let); [One] is O(1).  The analysis (see
   [Enfflash.clause_complexity]) assumes O(1) trace events per time-stamp, so
   event relations and bounded-window (metric) tables are O(1) and only
   unbounded relations carry a [Card]. *)

open Base

type t =
  | One                 (* O(1) *)
  | Card of string      (* |s| — size of relation s *)
  | Power of t * int    (* c^k *)
  | Prod of t list      (* c1 · c2 · … (a join / cross product) *)
  | Sum of t list       (* c1 + c2 + … (alternatives / independent work) *)
[@@deriving compare, equal, sexp_of]

let rec to_string ?(prio = 0) =
  let par prio_inner s = if prio_inner < prio then Printf.sprintf "(%s)" s else s in
  function
  | One -> "1"
  | Card s -> Printf.sprintf "|%s|" s
  | Power (c, k) -> par 3 (Printf.sprintf "%s^%d" (to_string ~prio:3 c) k)
  | Prod cs -> par 2 (String.concat ~sep:" · " (List.map ~f:(to_string ~prio:2) cs))
  | Sum cs -> par 1 (String.concat ~sep:" + " (List.map ~f:(to_string ~prio:1) cs))

(* ─── Simplification (asymptotic) ────────────────────────────────────────── *)

(* Multiset of irreducible factors of an expression (Power and Prod expanded),
   used to decide asymptotic dominance between summands. *)
let rec atoms = function
  | One -> []
  | Prod cs -> List.concat_map cs ~f:atoms
  | Power (c, k) -> List.concat (List.init k ~f:(fun _ -> atoms c))
  | x -> [ x ]

let remove_one y xs =
  let rec go acc = function
    | [] -> None
    | z :: zs -> if equal y z then Some (List.rev_append acc zs) else go (z :: acc) zs
  in
  go [] xs

(* Is [a] a sub-multiset of [b]?  (Then a's product divides b's.) *)
let rec submultiset a b =
  match a with
  | [] -> true
  | x :: xs -> (match remove_one x b with Some b' -> submultiset xs b' | None -> false)

(* Group runs of equal factors of a product into powers:
   |a| · |a| · |b|  ↦  |a|^2 · |b|. *)
let group_powers (factors : t list) : t list =
  let sorted = List.sort factors ~compare in
  List.group sorted ~break:(fun a b -> not (equal a b))
  |> List.map ~f:(fun grp ->
      match grp with
      | [] -> One
      | [ x ] -> x
      | x :: _ -> Power (x, List.length grp))

(* Normalises a cost expression under big-O equivalences:
     - c^0 = 1, c^1 = c, 1^k = 1, (c^j)^k = c^(j·k), (∏cᵢ)^k = ∏cᵢ^k
     - products: flatten, drop the O(1) factors, fold equal factors into powers
     - sums: flatten, drop O(1) terms when a larger term is present, and collapse
       duplicates (X + X = O(X)); an empty product/sum is O(1). *)
let rec simplify (c : t) : t =
  match c with
  | One -> One
  | Card s -> Card s
  | Power (c, k) -> simplify_power (simplify c) k
  | Prod cs -> simplify_prod (List.map cs ~f:simplify)
  | Sum cs -> simplify_sum (List.map cs ~f:simplify)

and simplify_power (c : t) (k : int) : t =
  if k = 0 then One
  else if k = 1 then c
  else
    match c with
    | One -> One
    | Power (c', j) -> simplify_power c' (j * k)
    | Prod cs -> simplify_prod (List.map cs ~f:(fun c -> simplify_power c k))
    | _ -> Power (c, k)

and simplify_prod (cs : t list) : t =
  (* flatten nested products and drop O(1) factors *)
  let factors =
    List.concat_map cs ~f:(function Prod xs -> xs | One -> [] | x -> [ x ])
  in
  match group_powers factors with
  | [] -> One
  | [ x ] -> x
  | fs -> Prod fs

and simplify_sum (cs : t list) : t =
  let terms =
    List.concat_map cs ~f:(function Sum xs -> xs | x -> [ x ])
    |> List.dedup_and_sort ~compare
  in
  (* O(1) terms are dominated as soon as any larger term is present. *)
  let non_one = List.filter terms ~f:(fun t -> not (equal t One)) in
  let terms = if List.is_empty non_one then terms else non_one in
  (* Drop a summand whose factors strictly divide another's: |a| + |a|·|b| = O(|a|·|b|). *)
  let terms =
    List.filter terms ~f:(fun t ->
        let at = atoms t in
        not (List.exists terms ~f:(fun u ->
            let au = atoms u in
            List.length at < List.length au && submultiset at au)))
  in
  match terms with
  | [] -> One
  | [ x ] -> x
  | ts -> Sum ts

(* ─── Convenience builders (already simplifying) ─────────────────────────── *)

let prod cs = simplify (Prod cs)
let sum cs = simplify (Sum cs)
let pow c k = simplify_power (simplify c) k

(* The relation names [|s|] occurring in a cost expression. *)
let rec cards = function
  | One -> []
  | Card s -> [ s ]
  | Power (c, _) -> cards c
  | Prod cs | Sum cs -> List.concat_map cs ~f:cards
