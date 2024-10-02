(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*           (see file LICENSE for more details)                   *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Pred

module Side = struct

  type t = N | L | R | LR [@@deriving compare, sexp_of, hash]

  let equal s s' = match s, s' with
    | N, N
      | L, L
      | R, R
      | LR, LR -> true
    | _ -> false

  let to_string = function
    | N  -> ""
    | L  -> ":L"
    | R  -> ":R"
    | LR -> ":LR"

  let to_string2 =
    let aux = function N  -> "N" | L  -> "L" | R  -> "R" | LR -> "LR"
    in function (N, N) -> "" | (a, b) -> ":" ^ aux a ^ "," ^ aux b

  let of_string = function
    | "L"  -> L
    | "R"  -> R
    | "LR" -> LR

end


type t =
  | TT
  | FF
  | EqConst of Term.t * Dom.t
  | Predicate of string * Term.t list
  | Let of string * string list * t * t
  | Agg of string * Aggregation.op * Term.t * string list * t
  | Neg of t
  | And of Side.t * t * t
  | Or of Side.t * t * t
  | Imp of Side.t * t * t
  | Iff of Side.t * Side.t * t * t
  | Exists of string * t
  | Forall of string * t
  | Prev of Interval.t * t
  | Next of Interval.t * t
  | Once of Interval.t * t
  | Eventually of Interval.t * t
  | Historically of Interval.t * t
  | Always of Interval.t * t
  | Since of Side.t * Interval.t * t * t
  | Until of Side.t * Interval.t * t * t [@@deriving compare, sexp_of, hash]


(* Free variables *)
let rec fv = function
  | TT | FF -> Set.empty (module String)
  | EqConst (Var x, _) -> Set.of_list (module String) [x]
  | EqConst _ -> Set.empty (module String)
  | Agg (s, _, _, y, _) -> Set.of_list (module String) (s::y)
  | Predicate (x, trms) -> Set.of_list (module String) (Pred.Term.fv_list trms)
  | Predicate _ -> Set.empty (module String)
  | Let (_, _, _, g) -> fv g
  | Exists (x, f)
    | Forall (x, f) -> Set.filter (fv f) ~f:(fun y -> not (String.equal x y))
  | Neg f
    | Prev (_, f)
    | Once (_, f)
    | Historically (_, f)
    | Eventually (_, f)
    | Always (_, f)
    | Next (_, f) -> fv f
  | And (_, f1, f2)
    | Or (_, f1, f2)
    | Imp (_, f1, f2)
    | Iff (_, _, f1, f2)
    | Since (_, _, f1, f2)
    | Until (_, _, f1, f2) -> Set.union (fv f1) (fv f2)

let list_fv e = Set.elements (fv e)

(* Bound variables *)
let rec bv = function
  | TT | FF -> Set.empty (module String)
  | EqConst _ -> Set.empty (module String)
  | Agg _ -> Set.empty (module String)
  | Predicate _ -> Set.empty (module String)
  | Let (_, _, _, g) -> bv g
  | Exists (x, f)
    | Forall (x, f) -> Set.add (bv f) x
  | Neg f
    | Prev (_, f)
    | Once (_, f)
    | Historically (_, f)
    | Eventually (_, f)
    | Always (_, f)
    | Next (_, f) -> bv f
  | And (_, f1, f2)
    | Or (_, f1, f2)
    | Imp (_, f1, f2)
    | Iff (_, _, f1, f2)
    | Since (_, _, f1, f2)
    | Until (_, _, f1, f2) -> Set.union (bv f1) (bv f2)

(* Replace y with z in list *)
let rec replace y z l = match l with
  | [] -> []
  | x::xs -> if String.equal x y then z::xs
             else x::(replace y z xs)

let rec replace_trms y z l = match l with
  | [] -> []
  | x::xs -> if Term.equal x y then z::xs
             else x::(replace_trms y z xs)

(* Replaces free variable y with z in f *)
let rec subst v f = match f with
  | TT | FF -> f
  | EqConst (trm, c) -> EqConst (Term.subst v trm, c)
  | Agg (s, op, w, xs, f) ->
     (match Map.find v s with
      | Some (Var z) -> Agg (z, op, w, xs, f)
      | Some trm     ->
         raise (Invalid_argument (
                Printf.sprintf "cannot substitute non-variable term %s for aggregation variable %s"
                  (Term.to_string trm)
                  s))
      | None         -> Agg (s, op, w, xs, f))
  | Predicate (r, trms) -> Predicate (r, Term.substs v trms)
  | Exists (x, f) -> Exists (x, subst (Map.remove v x) f)
  | Forall (x, f) -> Forall (x, subst (Map.remove v x) f)
  | Let (r, vars, f, g) -> let filter x = not (List.mem vars x ~equal:String.equal) in
                           Let (r, vars, f, subst (Map.filter_keys v filter) g)
  | Neg f -> Neg (subst v f)
  | Prev (i, f) -> Prev (i, subst v f)
  | Once (i, f) -> Once (i, subst v f)
  | Historically (i, f) -> Historically (i, subst v f)
  | Eventually (i, f) -> Eventually (i, subst v f)
  | Always (i, f) -> Always (i, subst v f)
  | Next (i, f) -> Next (i, subst v f)
  | And (s, f1, f2) -> And (s, subst v f1, subst v f2)
  | Or (s, f1, f2) -> Or (s, subst v f1, subst v f2)
  | Imp (s, f1, f2) -> Imp (s, subst v f1, subst v f2)
  | Iff (s1, s2, f1, f2) -> Iff (s1, s2, subst v f1, subst v f2)
  | Since (s, i, f1, f2) -> Since (s, i, subst v f1, subst v f2)
  | Until (s, i, f1, f2) -> Until (s, i, subst v f1, subst v f2)

(* Replaces bound variable y with z in f *)
let rec replace_bv y z f = match f with
  | TT | FF
    | EqConst _
    | Agg _
    | Predicate _ -> f
  | Exists (x, f) -> if String.equal x y then
                       Exists (z, f)
                     else Exists (x, replace_bv y z f)
  | Forall (x, f) -> if String.equal x y then
                       Forall (z, f)
                     else Forall (x, replace_bv y z f)
  | Let (name, vars, f, g) -> Let (name, vars, f, replace_bv y z g)
  | Neg f -> Neg (replace_bv y z f)
  | Prev (i, f) -> Prev (i, replace_bv y z f)
  | Once (i, f) -> Once (i, replace_bv y z f)
  | Historically (i, f) -> Historically (i, replace_bv y z f)
  | Eventually (i, f) -> Eventually (i, replace_bv y z f)
  | Always (i, f) -> Always (i, replace_bv y z f)
  | Next (i, f) -> Next (i, replace_bv y z f)
  | And (s, f1, f2) -> And (s, replace_bv y z f1, replace_bv y z f2)
  | Or (s, f1, f2) -> Or (s, replace_bv y z f1, replace_bv y z f2)
  | Imp (s, f1, f2) -> Imp (s, replace_bv y z f1, replace_bv y z f2)
  | Iff (s1, s2, f1, f2) -> Iff (s1, s2, replace_bv y z f1, replace_bv y z f2)
  | Since (s, i, f1, f2) -> Since (s, i, replace_bv y z f1, replace_bv y z f2)
  | Until (s, i, f1, f2) -> Until (s, i, replace_bv y z f1, replace_bv y z f2)

let tt = TT
let ff = FF
let eqconst x d = EqConst (x, d)
let agg s op x y f = Agg (s, op, x, y, f)
let predicate p_name trms = Predicate (p_name, trms)
let flet r vars f g = Let (r, vars, f, g)
let neg f = Neg f
let conj s f g = And (s, f, g)
let disj s f g = Or (s, f, g)
let imp s f g = Imp (s, f, g)
let iff s t f g = Iff (s, t, f, g)
let exists x f = Exists (x, f)
let forall x f = Forall (x, f)
(*  try Forall (x, List.hd_exn (var_tt x f), f)
  with e -> raise (Invalid_argument ("unused variable " ^ x))*)
let prev i f = Prev (i, f)
let next i f = Next (i, f)
let once i f = Once (i, f)
let eventually i f = Eventually (i, f)
let historically i f = Historically (i, f)
let always i f = Always (i, f)
let since s i f g = Since (s, i, f, g)
let until s i f g = Until (s, i, f, g)

(* Rewriting of non-native operators *)
let trigger s i f g = Neg (Since (s, i, Neg f, Neg g))
let release s i f g = Neg (Until (s, i, Neg f, Neg g))

(* TODO: I don't think phys_equal achieves the intended goal here (equal should be rec) *)
(* Disclaimer: this function doesn't seem to be used anywhere *)
let equal x y = match x, y with
  | TT, TT | FF, FF -> true
  | EqConst (x, c), EqConst (x', c') -> Term.equal x x'
  | Agg (s, op, x, y, f), Agg (s', op', x', y', f') ->
     String.equal s s' && Aggregation.equal_op op op' && Term.equal x x' && List.length y == List.length y'
     && List.for_all (List.zip_exn y y') (fun (y, y') -> String.equal y y') && phys_equal f f'
  | Predicate (r, trms), Predicate (r', trms') -> String.equal r r' && List.equal Term.equal trms trms'
  | Let (r, vars, f, g), Let (r', vars', f', g') -> String.equal r r' &&
                                                      List.equal String.equal vars vars' &&
                                                        phys_equal f f' && phys_equal g g'
  | Neg f, Neg f' -> phys_equal f f'
  | And (s, f, g), And (s', f', g')
    | Or (s, f, g), Or (s', f', g')
    | Imp (s, f, g), Imp (s', f', g') -> Side.equal s s' && phys_equal f f' && phys_equal g g'
  | Iff (s, t, f, g), Iff (s', t', f', g') -> Side.equal s s' && Side.equal t t' && phys_equal f f' && phys_equal g g'
  | Exists (x, f), Exists (x', f')
    | Forall (x, f), Forall (x', f') -> String.equal x x' && phys_equal f f'
  | Prev (i, f), Prev (i', f')
    | Next (i, f), Next (i', f')
    | Once (i, f), Once (i', f')
    | Eventually (i, f), Eventually (i', f')
    | Historically (i, f), Historically (i', f')
    | Always (i, f), Always (i', f') -> Interval.equal i i' && phys_equal f f'
  | Since (s, i, f, g), Since (s', i', f', g')
    | Until (s, i, f, g), Until (s', i', f', g') -> Side.equal s s' && Interval.equal i i' &&
                                                      phys_equal f f' && phys_equal g g'
  | _ -> false

let rec terms = function
  | TT | FF -> Set.empty (module Term)
  | EqConst (trm, c) -> Set.singleton (module Term) trm
  | Agg (s, _, _, y, f) -> Set.of_list (module Term) (List.map (s::y) ~f:(fun v -> Term.Var v))
  | Predicate (x, trms) -> Set.of_list (module Term) trms
  | Let (_, _, _, g) -> terms g
  | Exists (x, f) | Forall (x, f) ->
     let filter y = not (List.mem (Term.fv_list [y]) x ~equal:String.equal) in
     Set.filter (terms f) ~f:filter
  | Neg f
    | Prev (_, f)
    | Once (_, f)
    | Historically (_, f)
    | Eventually (_, f)
    | Always (_, f)
    | Next (_, f) -> terms f
  | And (_, f1, f2)
    | Or (_, f1, f2)
    | Imp (_, f1, f2)
    | Iff (_, _, f1, f2)
    | Since (_, _, f1, f2)
    | Until (_, _, f1, f2) -> Set.union (terms f1) (terms f2)

(*let lbls fvs f =
  let nodup l =
    List.remove_consecutive_duplicates
      (List.sort l ~compare:Lbl.compare) ~equal:Lbl.equal in
  let rec nonvars = function
  | TT | FF | EqConst (Const _, _) | EqConst (Var _, _) | Agg _ -> [] 
  | EqConst (t, _) -> [Lbl.of_term t]
  | Predicate (x, ts) ->
     nodup (List.filter_map ts (function | Const _ | Var _ -> None
                                         | t -> Some (Lbl.of_term t)))
  | Let (_, _, _, g) -> nonvars g
  | Exists (x, f) -> (LEx x) :: List.map (nonvars f) (Lbl.quantify ~forall:false x)
  | Forall (x, f) -> (LAll x) :: List.map (nonvars f) (Lbl.quantify ~forall:true x)
  | Neg f
    | Prev (_, f)
    | Once (_, f)
    | Historically (_, f)
    | Eventually (_, f)
    | Always (_, f)
    | Next (_, f) -> nonvars f
  | And (_, f1, f2)
    | Or (_, f1, f2)
    | Imp (_, f1, f2)
    | Iff (_, _, f1, f2)
    | Since (_, _, f1, f2)
    | Until (_, _, f1, f2) -> nodup (nonvars f1 @ nonvars f2)
  in (List.map fvs ~f:Lbl.var) @ (nonvars f)*)

let check_bindings f =
  let fv_f = fv f in
  let rec check_bindings_rec bound_vars = function
    | TT | FF -> (bound_vars, true)
    | EqConst (x, c) -> (bound_vars, true)
    | Agg (s, x, y, _, f) -> ((Set.add bound_vars s), (not (Set.mem fv_f s)) && (not (Set.mem bound_vars s)))
    | Predicate _ -> (bound_vars, true)
    | Let (_, _, _, g) -> check_bindings_rec bound_vars g
    | Exists (x, f)
      | Forall (x, f) -> ((Set.add bound_vars x), (not (Set.mem fv_f x)) && (not (Set.mem bound_vars x)))
    | Neg f
      | Prev (_, f)
      | Once (_, f)
      | Historically (_, f)
      | Eventually (_, f)
      | Always (_, f)
      | Next (_, f) -> check_bindings_rec bound_vars f
    | And (_, f1, f2)
      | Or (_, f1, f2)
      | Imp (_, f1, f2)
      | Iff (_, _, f1, f2)
      | Since (_, _, f1, f2)
      | Until (_, _, f1, f2) -> let (bound_vars1, b1) = check_bindings_rec bound_vars f1 in
                                let (bound_vars2, b2) = check_bindings_rec (Set.union bound_vars1 bound_vars) f2 in
                                (bound_vars2, b1 && b2) in
  snd (check_bindings_rec (Set.empty (module String)) f)

(* Past height *)
let rec hp = function
  | TT
    | FF
    | EqConst _
    | Predicate _ -> 0
  | Let (_, _, _, g) -> hp g
  | Neg f
    | Exists (_, f)
    | Forall (_, f) -> hp f
  | And (_, f1, f2)
    | Or (_, f1, f2)
    | Imp (_, f1, f2)
    | Iff (_, _, f1, f2) -> max (hp f1) (hp f2)
  | Prev (_, f)
    | Once (_, f)
    | Historically (_, f) -> hp f + 1
  | Eventually (_, f)
    | Always (_, f)
    | Next (_, f)
    | Agg (_, _, _, _, f) -> hp f
  | Since (_, _, f1, f2) -> max (hp f1) (hp f2) + 1
  | Until (_, _, f1, f2) -> max (hp f1) (hp f2)

(* Future height *)
let rec hf = function
  | TT
    | FF
    | EqConst _
    | Predicate _ -> 0
  | Let (_, _, _, g) -> hf g
  | Neg f
    | Exists (_, f)
    | Forall (_, f) -> hf f
  | And (_, f1, f2)
    | Or (_, f1, f2)
    | Imp (_, f1, f2)
    | Iff (_, _, f1, f2) -> max (hf f1) (hf f2)
  | Prev (_, f)
    | Once (_, f)
    | Historically (_, f)
    | Agg (_, _, _, _, f) -> hf f
  | Eventually (_, f)
    | Always (_, f)
    | Next (_, f) -> hf f + 1
  | Since (_, _, f1, f2) -> max (hf f1) (hf f2)
  | Until (_, _, f1, f2) -> max (hf f1) (hf f2) + 1

let height f = hp f + hf f

let immediate_subfs = function
  | TT
    | FF
    | EqConst _
    | Predicate _ -> []
  | Let (_, _, _, g) -> [g]
  | Neg f
    | Exists (_, f)
    | Forall (_, f)
    | Prev (_, f)
    | Next (_, f)
    | Once (_, f)
    | Eventually (_, f)
    | Historically (_, f)
    | Always (_, f)
    | Agg (_, _, _, _, f) -> [f]
  | And (_, f, g)
    | Or (_, f, g)
    | Imp (_, f, g)
    | Iff (_, _, f, g) -> [f; g]
  | Since (_, _, f, g)
    | Until (_, _, f, g) -> [f; g]

let rec subfs_bfs xs =
  xs @ (List.concat (List.map xs ~f:(fun x -> subfs_bfs (immediate_subfs x))))

let rec subfs_dfs h = match h with
  | TT | FF | EqConst _ | Predicate _ -> [h]
  | Let (_, _, _, g) -> [h] @ (subfs_dfs g)
  | Neg f -> [h] @ (subfs_dfs f)
  | And (_, f, g) -> [h] @ (subfs_dfs f) @ (subfs_dfs g)
  | Or (_, f, g) -> [h] @ (subfs_dfs f) @ (subfs_dfs g)
  | Imp (_, f, g) -> [h] @ (subfs_dfs f) @ (subfs_dfs g)
  | Iff (_, _, f, g) -> [h] @ (subfs_dfs f) @ (subfs_dfs g)
  | Exists (_, f) -> [h] @ (subfs_dfs f)
  | Forall (_, f) -> [h] @ (subfs_dfs f)
  | Prev (_, f) -> [h] @ (subfs_dfs f)
  | Next (_, f) -> [h] @ (subfs_dfs f)
  | Once (_, f) -> [h] @ (subfs_dfs f)
  | Eventually (_, f) -> [h] @ (subfs_dfs f)
  | Historically (_, f) -> [h] @ (subfs_dfs f)
  | Always (_, f) -> [h] @ (subfs_dfs f)
  | Agg (_, _, _, _, f) -> [h] @ (subfs_dfs f)
  | Since (_, _, f, g) -> [h] @ (subfs_dfs f) @ (subfs_dfs g)
  | Until (_, _, f, g) -> [h] @ (subfs_dfs f) @ (subfs_dfs g)

let subfs_scope h i =
  let rec subfs_scope_rec h i =
    match h with
    | TT | FF | EqConst _ | Predicate _ -> (i, [(i, ([], []))])
    | Let (_, _, _, f)
      | Neg f
      | Exists (_, f)
      | Forall (_, f)
      | Prev (_, f)
      | Next (_, f)
      | Once (_, f)
      | Eventually (_, f)
      | Historically (_, f)
      | Always (_, f)
      | Agg (_, _, _, _, f) -> let (i', subfs_f) = subfs_scope_rec f (i+1) in
                               (i', [(i, (List.map subfs_f ~f:fst, []))] @ subfs_f)
    | And (_, f, g)
      | Or (_, f, g)
      | Imp (_, f, g)
      | Iff (_, _, f, g)
      | Since (_, _, f, g)
      | Until (_, _, f, g) -> let (i', subfs_f) = subfs_scope_rec f (i+1) in
                              let (i'', subfs_g) = subfs_scope_rec g (i'+1) in
                              (i'', [(i, ((List.map subfs_f ~f:fst), (List.map subfs_g ~f:fst)))]
                                    @ subfs_f @ subfs_g) in
  snd (subfs_scope_rec h i)

let rec preds = function
  | TT | FF | EqConst _ -> []
  | Predicate (r, trms) -> [Predicate (r, trms)]
  | Let (_, _, _, g) -> preds g
  | Neg f | Exists (_, f) | Forall (_, f)
    | Next (_, f) | Prev (_, f)
    | Once (_, f) | Historically (_, f)
    | Eventually (_, f) | Always (_, f)
    | Agg (_, _, _, _, f) -> preds f
  | And (_, f1, f2) | Or (_, f1, f2)
    | Imp (_, f1, f2) | Iff (_, _, f1, f2)
    | Until (_, _, f1, f2) | Since (_, _, f1, f2) -> let a1s = List.fold_left (preds f1) ~init:[]
                                                           ~f:(fun acc a -> if List.mem acc a ~equal:equal then acc
                                                                            else acc @ [a])  in
                                               let a2s = List.fold_left (preds f2) ~init:[]
                                                           ~f:(fun acc a ->
                                                             if (List.mem acc a ~equal:equal) ||
                                                                  (List.mem a1s a ~equal:equal) then acc
                                                             else acc @ [a]) in
                                               List.append a1s a2s

let pred_names f =
  let rec pred_names_rec s = function
    | TT | FF | EqConst _ -> s
    | Predicate (r, trms) -> Set.add s r
    | Let (_, _, _, g) -> pred_names_rec s g
    | Neg f | Exists (_, f) | Forall (_, f)
      | Prev (_, f) | Next (_, f)
      | Once (_, f) | Eventually (_, f)
      | Historically (_, f) | Always (_, f)
      | Agg (_, _, _, _, f) -> pred_names_rec s f
    | And (_, f1, f2) | Or (_, f1, f2)
      | Imp (_, f1, f2) | Iff (_, _, f1, f2)
      | Until (_, _, f1, f2) | Since (_, _, f1, f2) -> Set.union (pred_names_rec s f1) (pred_names_rec s f2) in
  pred_names_rec (Set.empty (module String)) f

let op_to_string = function
  | TT -> Printf.sprintf "⊤"
  | FF -> Printf.sprintf "⊥"
  | EqConst (x, c) -> Printf.sprintf "="
  | Predicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | Let (r, _, _, _) -> Printf.sprintf "LET %s" r
  | Agg (_, op, x, y, _) -> Printf.sprintf "%s(%s; %s)" (Aggregation.op_to_string op) (Term.value_to_string x)
                              (String.concat ~sep:", " y)
  | Neg _ -> Printf.sprintf "¬"
  | And (_, _, _) -> Printf.sprintf "∧"
  | Or (_, _, _) -> Printf.sprintf "∨"
  | Imp (_, _, _) -> Printf.sprintf "→"
  | Iff (_, _, _, _) -> Printf.sprintf "↔"
  | Exists (x, _) -> Printf.sprintf "∃ %s." x
  | Forall (x, _) -> Printf.sprintf "∀ %s." x
  | Prev (i, _) -> Printf.sprintf "●%s" (Interval.to_string i)
  | Next (i, _) -> Printf.sprintf "○%s" (Interval.to_string i)
  | Once (i, f) -> Printf.sprintf "⧫%s" (Interval.to_string i)
  | Eventually (i, f) -> Printf.sprintf "◊%s" (Interval.to_string i)
  | Historically (i, f) -> Printf.sprintf "■%s" (Interval.to_string i)
  | Always (i, f) -> Printf.sprintf "□%s" (Interval.to_string i)
  | Since (_, i, _, _) -> Printf.sprintf "S%s" (Interval.to_string i)
  | Until (_, i, _, _) -> Printf.sprintf "U%s" (Interval.to_string i)

let rec to_string_rec l = function
  | TT -> Printf.sprintf "⊤"
  | FF -> Printf.sprintf "⊥"
  | EqConst (trm, c) -> Printf.sprintf "{%s} = %s" (Term.value_to_string trm) (Dom.to_string c)
  | Predicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | Let (r, vars, f, g) -> Printf.sprintf "LET %s(%s) = %a IN %a" r
                                  (Etc.string_list_to_string vars)
                                  (fun x -> to_string_rec 4) f (fun x -> to_string_rec 4) g
  | Agg (s, op, x, y, f) -> Printf.sprintf "%s <- %s(%s; %s; %s)" s (Aggregation.op_to_string op)
                              (Term.value_to_string x) (String.concat ~sep:", " y) (to_string_rec 5 f)
  | Neg f -> Printf.sprintf "¬%a" (fun x -> to_string_rec 5) f
  | And (s, f, g) -> Printf.sprintf (Etc.paren l 4 "%a ∧%a %a") (fun x -> to_string_rec 4) f
                       (fun x -> Side.to_string) s (fun x -> to_string_rec 4) g
  | Or (s, f, g) -> Printf.sprintf (Etc.paren l 3 "%a ∨%a %a") (fun x -> to_string_rec 3) f
                      (fun x -> Side.to_string) s (fun x -> to_string_rec 4) g
  | Imp (s, f, g) -> Printf.sprintf (Etc.paren l 5 "%a →%a %a") (fun x -> to_string_rec 5) f
                       (fun x -> Side.to_string) s (fun x -> to_string_rec 5) g
  | Iff (s, t, f, g) -> Printf.sprintf (Etc.paren l 5 "%a ↔%a %a") (fun x -> to_string_rec 5) f
                          (fun x -> Side.to_string2) (s, t) (fun x -> to_string_rec 5) g
  | Exists (x, f) -> Printf.sprintf (Etc.paren l 5 "∃%s. %a") x (fun x -> to_string_rec 5) f
  | Forall (x, f) -> Printf.sprintf (Etc.paren l 5 "∀%s. %a") x (fun x -> to_string_rec 5) f
  | Prev (i, f) -> Printf.sprintf (Etc.paren l 5 "●%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
  | Next (i, f) -> Printf.sprintf (Etc.paren l 5 "○%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
  | Once (i, f) -> Printf.sprintf (Etc.paren l 5 "⧫%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
  | Eventually (i, f) -> Printf.sprintf (Etc.paren l 5 "◊%a %a") (fun x -> Interval.to_string) i
                           (fun x -> to_string_rec 5) f
  | Historically (i, f) -> Printf.sprintf (Etc.paren l 5 "■%a %a") (fun x -> Interval.to_string) i
                             (fun x -> to_string_rec 5) f
  | Always (i, f) -> Printf.sprintf (Etc.paren l 5 "□%a %a") (fun x -> Interval.to_string) i
                       (fun x -> to_string_rec 5) f
  | Since (s, i, f, g) -> Printf.sprintf (Etc.paren l 0 "%a S%a%a %a") (fun x -> to_string_rec 5) f
                          (fun x -> Interval.to_string) i (fun x -> Side.to_string) s (fun x -> to_string_rec 5) g
  | Until (s, i, f, g) -> Printf.sprintf (Etc.paren l 0 "%a U%a%a %a") (fun x -> to_string_rec 5) f
                         (fun x -> Interval.to_string) i (fun x -> Side.to_string) s (fun x -> to_string_rec 5) g
let to_string = to_string_rec 0

let rec to_json_rec indent pos f =
  let indent' = "  " ^ indent in
  match f with
  | TT -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"TT\"\n%s}"
            indent pos indent' indent
  | FF -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"FF\"\n%s}"
            indent pos indent' indent
  | EqConst (trm, c) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"EqConst\",\n
                                        %s\"variable\": \"%s\",\n%s\"constant\": \"%s\"\n%s}"
                          indent pos indent' indent' (Term.to_string trm) indent' (Dom.to_string c) indent
  | Predicate (r, trms) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Predicate\",\n
                                           %s\"name\": \"%s\",\n%s\"terms\": \"%s\"\n%s}"
                             indent pos indent' indent' r indent' (Term.list_to_string trms) indent
  | Let _ -> ""
  | Agg (s, op, x, y, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Agg\",\n
                                            %s\"variable\": \"%s\",\n%s\"agg_variable\": \"%s\"\n
                                            %s\"groupby_variables\": \"%s,%s\n%s}"
                              indent pos indent' indent' s indent' (Term.to_string x) indent'
                              (String.concat ~sep:", " y) (to_json_rec indent' "f" f) indent
  | Neg f -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Neg\",\n%s\n%s}"
               indent pos indent' (to_json_rec indent' "" f) indent
  | And (_, f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"And\",\n%s,\n%s\n%s}"
                    indent pos indent' (to_json_rec indent' "l" f) (to_json_rec indent' "r" g) indent
  | Or (_, f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Or\",\n%s,\n%s\n%s}"
                   indent pos indent' (to_json_rec indent' "l" f) (to_json_rec indent' "r" g) indent
  | Imp (_, f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Imp\",\n%s,\n%s\n%s}"
                    indent pos indent' (to_json_rec indent' "l" f) (to_json_rec indent' "r" g) indent
  | Iff (_, _, f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Iff\",\n%s,\n%s\n%s}"
                    indent pos indent' (to_json_rec indent' "l" f) (to_json_rec indent' "r" g) indent
  | Exists (x, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Exists\",\n%s\"variable\": \"%s\",\n%s\n%s}"
                       indent pos indent' indent' x (to_json_rec indent' "" f) indent
  | Forall (x, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Forall\",\n%s\"variable\": \"%s\",\n%s\n%s}"
                       indent pos indent' indent' x (to_json_rec indent' "" f) indent
  | Prev (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Prev\",\n%s\"Interval.t\": \"%s\",\n%s\n%s}"
                     indent pos indent' indent' (Interval.to_string i) (to_json_rec indent' "" f) indent
  | Next (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Next\",\n%s\"Interval.t\": \"%s\",\n%s\n%s}"
                     indent pos indent' indent' (Interval.to_string i) (to_json_rec indent' "" f) indent
  | Once (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Once\",\n%s\"Interval.t\": \"%s\",\n%s\n%s}"
                     indent pos indent' indent' (Interval.to_string i) (to_json_rec indent' "" f) indent
  | Eventually (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Eventually\",\n%s\"Interval.t\": \"%s\",\n
                                         %s\n%s}"
                           indent pos indent' indent' (Interval.to_string i) (to_json_rec indent' "" f) indent
  | Historically (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Historically\",\n
                                           %s\"Interval.t\": \"%s\",\n%s\n%s}"
                             indent pos indent' indent' (Interval.to_string i) (to_json_rec indent' "" f) indent
  | Always (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Always\",\n%s\"Interval.t\": \"%s\",\n%s\n%s}"
                       indent pos indent' indent' (Interval.to_string i) (to_json_rec indent' "" f) indent
  | Since (_, i, f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Since\",\n%s\"Interval.t\": \"%s\",\n
                                          %s,\n%s\n%s}"
                            indent pos indent' indent' (Interval.to_string i) (to_json_rec indent' "l" f)
                            (to_json_rec indent' "r" g) indent
  | Until (_, i, f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Until\",\n%s\"Interval.t\": \"%s\",\n
                                          %s,\n%s\n%s}"
                            indent pos indent' indent' (Interval.to_string i) (to_json_rec indent' "l" f)
                            (to_json_rec indent' "r" g) indent
let to_json = to_json_rec "    " ""

let rec to_latex_rec l = function
  | TT -> Printf.sprintf "\\top"
  | FF -> Printf.sprintf "\\bot"
  | EqConst (trm, c) -> Printf.sprintf "{%s = %s}" (Etc.escape_underscores (Term.to_string trm)) (Dom.to_string c)
  | Predicate (r, trms) -> Printf.sprintf "%s\\,(%s)" (Etc.escape_underscores r) (Term.list_to_string trms)
  | Agg (s, op, x, y, f) -> Printf.sprintf "%s \\leftarrow %s %s;%s. %s" (Etc.escape_underscores s)
                              (Aggregation.op_to_string op) (Etc.escape_underscores (Term.to_string x))
                              (Etc.escape_underscores (String.concat ~sep:", " y)) (to_latex_rec 5 f)
  | Neg f -> Printf.sprintf "\\neg %a" (fun x -> to_latex_rec 5) f
  | And (_, f, g) -> Printf.sprintf (Etc.paren l 4 "%a \\land %a") (fun x -> to_latex_rec 4) f
                       (fun x -> to_latex_rec 4) g
  | Or (_, f, g) -> Printf.sprintf (Etc.paren l 3 "%a \\lor %a") (fun x -> to_latex_rec 3) f (fun x -> to_latex_rec 4) g
  | Imp (_, f, g) -> Printf.sprintf (Etc.paren l 5 "%a \\rightarrow %a") (fun x -> to_latex_rec 5) f
                       (fun x -> to_latex_rec 5) g
  | Iff (_, _, f, g) -> Printf.sprintf (Etc.paren l 5 "%a \\leftrightarrow %a") (fun x -> to_latex_rec 5) f
                          (fun x -> to_latex_rec 5) g
  | Exists (x, f) -> Printf.sprintf (Etc.paren l 5 "\\exists %s. %a") x (fun x -> to_latex_rec 5) f
  | Forall (x, f) -> Printf.sprintf (Etc.paren l 5 "\\forall %s. %a") x (fun x -> to_latex_rec 5) f
  | Prev (i, f) -> Printf.sprintf (Etc.paren l 5 "\\Prev{%a} %a") (fun x -> Interval.to_latex) i
                     (fun x -> to_latex_rec 5) f
  | Next (i, f) -> Printf.sprintf (Etc.paren l 5 "\\Next{%a} %a") (fun x -> Interval.to_latex) i
                     (fun x -> to_latex_rec 5) f
  | Once (i, f) -> Printf.sprintf (Etc.paren l 5 "\\Once{%a} %a") (fun x -> Interval.to_latex) i
                     (fun x -> to_latex_rec 5) f
  | Eventually (i, f) -> Printf.sprintf (Etc.paren l 5 "\\Eventually{%a} %a") (fun x -> Interval.to_latex) i
                           (fun x -> to_latex_rec 5) f
  | Historically (i, f) -> Printf.sprintf (Etc.paren l 5 "\\Historically{%a} %a") (fun x -> Interval.to_latex) i
                             (fun x -> to_latex_rec 5) f
  | Always (i, f) -> Printf.sprintf (Etc.paren l 5 "\\Always{%a} %a") (fun x -> Interval.to_latex) i
                       (fun x -> to_latex_rec 5) f
  | Since (_, i, f, g) -> Printf.sprintf (Etc.paren l 0 "%a \\Since{%a} %a") (fun x -> to_latex_rec 5) f
                         (fun x -> Interval.to_latex) i (fun x -> to_latex_rec 5) g
  | Until (_, i, f, g) -> Printf.sprintf (Etc.paren l 0 "%a \\Until{%a} %a") (fun x -> to_latex_rec 5) f
                         (fun x -> Interval.to_latex) i (fun x -> to_latex_rec 5) g
let to_latex = to_latex_rec 0


let rec solve_past_guarded x p f =
  let vars = fv f in
  let rec aux x p f =
    let s =
      match f, p with
      | TT, false -> Some (Set.empty (module String))
      | FF, true -> Some (Set.empty (module String))
      | EqConst (y, _), true when Term.equal (Term.Var x) y -> Some (Set.empty (module String))
      | Predicate (r, ts), true when List.exists ~f:(Term.equal (Term.Var x)) ts ->
         Some (Set.singleton (module String) r)
      | Agg (s, _, t, _, f), true when String.equal s x ->
         Option.map ~f:(Etc.inter_list (module String))
           (Option.all (List.map (Term.fv_list [t]) ~f:(fun z -> solve_past_guarded z p f)))
      | Agg (_, _, _, y, f), _ when List.mem y x ~equal:String.equal -> aux x p f
      | Neg f, _ -> aux x (not p) f
      | And (_, f', g'), true | Or (_, f', g'), false | Imp (_, f', g'), false ->
         let q = match f with Imp _ -> not p | _ -> p in
         Option.merge (aux x q f') (aux x p g') ~f:Set.union
      | And (_, f', g'), false | Or (_, f', g'), true | Imp (_, f', g'), true ->
         let q = match f with Imp _ -> not p | _ -> p in
         Option.map2 (aux x q f') (aux x p g') ~f:Set.inter
      | Iff (_, _, f, g), _ -> aux x p (And (N, Imp (N, f, g), Imp (N, g, f)))
      | Exists (y, f), _ | Forall (y, f), _ when x != y -> aux x p f
      | Prev (_, f), true -> aux x p f
      | Once (_, f), true | Eventually (_, f), true -> aux x p f
      | Once (i, f), false | Eventually (i, f), false when Interval.has_zero i -> aux x p f
      | Historically (_, f), false | Always (_, f), false -> aux x p f
      | Historically (i, f), true | Always (i, f), true when Interval.has_zero i -> aux x p f
      | Since (_, i, f, g), true when not (Interval.has_zero i) -> aux x p (And (N, f, g))
      | Since (_, i, f, g), true -> aux x p g
      | Since (_, i, f, g), false | Until (_, i, f, g), false when Interval.has_zero i -> aux x p g
      | Until (_, i, f, g), true when not (Interval.has_zero i) -> aux x p f
      | Until (_, i, f, g), true -> aux x p (Or (N, f, g))
      | _ -> None in
    (*print_endline (Printf.sprintf "solve_past_guarded(%s, %b, %s) = %b" x p (to_string f) s);*)
    s in
  aux x p f

and is_past_guarded x p f =
  Option.is_some (solve_past_guarded x p f)

(*
let rec is_past_guarded x p f =
  match f with
  | TT -> not p
  | FF -> p
  | EqConst (y, _) -> p && (Term.Var x == y)
  | Predicate (_, ts) when p -> List.exists ~f:(Term.equal (Term.Var x)) ts
  | Let (_, _, f, g) -> is_past_guarded x p f && is_past_guarded x p g
  | Agg (s, _, _, y, f) when List.mem y x ~equal:String.equal -> is_past_guarded x p f
  | Agg (s, _, _, _, _) -> String.equal s x
  | Neg f -> is_past_guarded x (not p) f
  | And (_, f, g) when p -> is_past_guarded x p f || is_past_guarded x p g
  | And (_, f, g) -> is_past_guarded x p f && is_past_guarded x p g
  | Or (_, f, g) when p -> is_past_guarded x p f && is_past_guarded x p g
  | Or (_, f, g) -> is_past_guarded x p f || is_past_guarded x p g
  | Imp (_, f, g) when p -> is_past_guarded x (not p) f && is_past_guarded x p g
  | Imp (_, f, g) -> is_past_guarded x (not p) f || is_past_guarded x p g
  | Iff (_, _, f, g) when p -> is_past_guarded x (not p) f && is_past_guarded x p g
                               || is_past_guarded x p f && is_past_guarded x (not p) g
  | Iff (_, _, f, g) -> (is_past_guarded x (not p) f || is_past_guarded x p g)
                        && (is_past_guarded x p f || is_past_guarded x (not p) g)
  | Exists (y, f) | Forall (y, f) -> x != y && is_past_guarded x p f
  | Prev (_, f) -> p && is_past_guarded x p f
  | Once (_, f) | Eventually (_, f) when p -> is_past_guarded x p f
  | Once (i, f) | Eventually (i, f) -> Interval.has_zero i && is_past_guarded x p f
  | Historically (_, f) | Always (_, f) when not p -> is_past_guarded x p f
  | Historically (i, f) | Eventually (i, f) -> Interval.has_zero i && is_past_guarded x p f
  | Since (_, i, f, g) when p -> not (Interval.has_zero i) && is_past_guarded x p f
                                      || is_past_guarded x p g
  | Until (_, i, f, g) when p -> not (Interval.has_zero i) && is_past_guarded x p f
                                      || is_past_guarded x p f && is_past_guarded x p g
  | Since (_, i, f, g) | Until (_, i, f, g) -> Interval.has_zero i && is_past_guarded x p g
  | _ -> false
 *)

let check_agg types s op x y f =
  let x_tt = Sig.tt_of_term_exn types x in
  match Aggregation.ret_tt op x_tt with
  | None -> raise (Invalid_argument (
                       Printf.sprintf "type clash for operator %s: invalid type %s"
                         (Aggregation.op_to_string op) (Dom.tt_to_string x_tt)))
  | Some s_tt when Map.mem types s && not (Dom.tt_equal s_tt (Map.find_exn types s)) ->
     raise (Invalid_argument (
                Printf.sprintf "type clash for return type of operator %s: found %s, expected %s"
                  (Aggregation.op_to_string op)
                  (Dom.tt_to_string s_tt)
                  (Dom.tt_to_string (Map.find_exn types s))))
  | Some s_tt ->
     let types = Map.update types s ~f:(fun _ -> s_tt) in
     let vars = (Term.fv_list [x]) @ y in
     let fv = fv f in
     List.iter vars ~f:(
         fun x ->
         if not (Set.mem fv x) then
           raise (Invalid_argument (
                      Printf.sprintf "variable %s is used in aggregation, but not free in %s"
                        x (to_string f)))
         else ());
     (*if Set.mem fv s then
       raise (Invalid_argument (
       Printf.sprintf "variable %s is both the target of an aggregation and free in %s"
       s (to_string f)));*)
     types

let unroll_let =
  let rec aux (v : (String.t, string list * t, String.comparator_witness) Map.t) = function
    | TT -> TT
    | FF -> FF
    | EqConst (x, c) -> EqConst (x, c)
    | Predicate (r, trms) ->
       (match Map.find v r with
        | None -> Predicate (r, trms)
        | Some (vars, e) -> subst (Map.of_alist_exn (module String) (List.zip_exn vars trms)) e)
    | Let (r, vars, f, g) ->
       aux (Map.update v r (fun _ -> (vars, aux v f))) g
    | Agg (s, op, x, y, f) -> Agg (s, op, x, y, aux v f)
    | Neg f -> Neg (aux v f)
    | And (s, f, g) -> And (s, aux v f, aux v g)
    | Or (s, f, g) -> Or (s, aux v f, aux v g)
    | Imp (s, f, g) -> Imp (s, aux v f, aux v g)
    | Iff (s, t, f, g) -> Iff (s, t, aux v f, aux v g)
    | Exists (x, f) -> Exists (x, aux (Map.remove v x) f)
    | Forall (x, f) -> Forall (x, aux (Map.remove v x) f)
    | Prev (i, f) -> Prev (i, aux v f)
    | Next (i, f) -> Next (i, aux v f)
    | Once (i, f) -> Once (i, aux v f)
    | Eventually (i, f) -> Eventually (i, aux v f)
    | Historically (i, f) -> Historically (i, aux v f)
    | Always (i, f) -> Always (i, aux v f)
    | Since (s, i, f, g) -> Since (s, i, aux v f, aux v g)
    | Until (s, i, f, g) -> Until (s, i, aux v f, aux v g)
  in aux (Map.empty (module String))

let formula_to_string = to_string

module Filter = struct

  type filter = An of string | AllOf of filter list | OneOf of filter list [@@deriving equal, compare, hash, sexp_of]

  let _true = AllOf []
  let _false = OneOf []

  let is_an = function An _ -> true | _ -> false
  let is_allof = function AllOf _ -> true | _ -> false
  let is_oneof = function OneOf _ -> true | _ -> false

  let rec eval (db : Db.t) = function
    | An e -> (*print_endline (Printf.sprintf "eval(%s, An %s)=%b" (Db.to_string db) e  (Db.mem_trace db e)); *)(Db.mem_trace db e)
    | AllOf fis -> List.for_all fis ~f:(eval db)
    | OneOf fis -> List.exists fis ~f:(eval db)
  
  let rec to_string_rec l = function
    | An e -> e
    | AllOf [] -> "⊤"
    | OneOf [] -> "⊥"
    | AllOf fis -> Printf.sprintf (Etc.paren l 4 "%s") (String.concat ~sep:"∧" (List.map fis ~f:(to_string_rec 4)))
    | OneOf fis -> Printf.sprintf (Etc.paren l 3 "%s") (String.concat ~sep:"∨" (List.map fis ~f:(to_string_rec 3)))
      
  let to_string = to_string_rec 0

  let rec simplify = function
    | An e -> An e
    | AllOf [] -> AllOf []
    | OneOf [] -> OneOf []
    | AllOf fis ->
       let fis        = List.map fis ~f:simplify in
       let all_of_fis = List.concat_map fis ~f:(function AllOf fis -> fis | _ -> []) in
       let one_ofs    = List.filter fis ~f:is_oneof in
       let ans        = List.filter fis ~f:is_an in
       let one_of_bad = List.exists one_ofs ~f:(equal_filter _false) in
       if one_of_bad then
         _false
       else
         AllOf (all_of_fis @ one_ofs @ ans)
    | OneOf fis ->
       let fis        = List.map fis ~f:simplify in
       let one_of_fis = List.concat_map fis ~f:(function OneOf fis -> fis | _ -> []) in
       let all_ofs    = List.filter fis ~f:is_allof in
       let ans        = List.filter fis ~f:is_an in
       let all_of_bad = List.exists all_ofs ~f:(equal_filter _true) in
       if all_of_bad then
         _true
       else
         OneOf (one_of_fis @ all_ofs @ ans)

  let rec present_filter_ ?(b=true) f =
    let filter = 
      match f with
      | TT -> if b then _true else _false
      | FF -> if b then _false else _true
      | Predicate (e, _) when b -> An e
      | Neg f -> present_filter_ ~b:(not b) f
      | And (_, f, g) when b -> AllOf [present_filter_ ~b f; present_filter_ ~b g]
      | And (_, f, g) -> OneOf [present_filter_ ~b f; present_filter_ ~b g]
      | Or (_, f, g) when b -> OneOf [present_filter_ ~b f; present_filter_ ~b g]
      | Or (_, f, g) -> AllOf [present_filter_ ~b f; present_filter_ ~b g]
      | Imp (_, f, g) when b -> OneOf [present_filter_ ~b:(not b) f; present_filter_ ~b g]
      | Imp (_, f, g) -> AllOf [present_filter_ ~b:(not b) f; present_filter_ ~b g]
      | Iff (_, _, f, g) -> present_filter_ ~b (And (N, Imp (N, f, g), Imp (N, g, f)))
      | Exists (_, f) | Forall (_, f) -> present_filter_ ~b f
      | _ -> _true
    in (*print_endline (Printf.sprintf "present_filter_ %s (%s) = %s" (Bool.to_string b) (formula_to_string f) (to_string filter));*)
       filter

  let present_filter ?(b=true) f =
    simplify (present_filter_ ~b f)

  let conj fi1 fi2 = simplify (AllOf [fi1; fi2])
  let disj fi1 fi2 = simplify (OneOf [fi1; fi2])

end


