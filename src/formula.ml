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
open Sformula

type t =
  | TT
  | FF
  | EqConst of Term.t * Dom.t
  | Predicate of string * Term.t list
  | Predicate' of string * Term.t list * t
  | Let of string * Enftype.t option * string list * t * t
  | Let' of string * string list * t * t
  | Agg of string * Aggregation.op * Term.t * string list * t
  | Top of string list * string * Term.t list * string list * t
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
  | Top (s, _, x, y, _) -> Set.of_list (module String) (s@y)
  | Predicate (x, trms) -> Set.of_list (module String) (Term.fv_list trms)
  | Predicate _ -> Set.empty (module String)
  | Predicate' (_, _, f) -> fv f
  | Let (_, _, _, _, g) -> fv g
  | Let' (_, _, _, g) -> fv g
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
let subst_var v s =
  match Map.find v s with
  | Some (Term.Var z) -> z
  | Some trm ->
     raise (Invalid_argument (
                Printf.sprintf "cannot substitute non-variable term %s for aggregation variable %s"
                  (Term.to_string trm) s))
  | None -> s
  
let rec subst v f = match f with
  | TT | FF -> f
  | EqConst (trm, c) -> EqConst (Term.subst v trm, c)
  | Agg (s, op, t, y, f) -> Agg (subst_var v s, op, t, y, f)
  | Top (s, op, x, y, f) -> Top (List.map ~f:(subst_var v) s, op, x, y, f)
  | Predicate (r, trms) -> Predicate (r, Term.substs v trms)
  | Predicate' (r, trms, f) -> Predicate' (r, Term.substs v trms, subst v f)
  | Exists (x, f) -> Exists (x, subst (Map.remove v x) f)
  | Forall (x, f) -> Forall (x, subst (Map.remove v x) f)
  | Let (r, enftype, vars, f, g) -> let filter x = not (List.mem vars x ~equal:String.equal) in
                                    Let (r, enftype, vars, f, subst (Map.filter_keys v filter) g)
  | Let' (r, vars, f, g) -> Let' (r, vars, f, subst v g)
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

let tt = TT
let ff = FF
let eqconst x d = EqConst (x, d)
let agg s op x y f = Agg (s, op, x, y, f)
let top s op x y f = Top (s, op, x, y, f)
let predicate p_name trms = Predicate (p_name, trms)
let flet r enftype vars f g = Let (r, enftype, vars, f, g)
let neg f = Neg f
let conj s f g = And (s, f, g)
let disj s f g = Or (s, f, g)
let imp s f g = Imp (s, f, g)
let iff s t f g = Iff (s, t, f, g)
let exists x f = Exists (x, f)
let forall x f = Forall (x, f)
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

let exists_of_agg y f =
  let z = List.filter (list_fv f) ~f:(fun x -> not (List.mem y x ~equal:String.equal)) in
  List.fold_right z ~f:(fun z f -> Exists (z, f)) ~init:f

(* TODO: I don't think phys_equal achieves the intended goal here (equal should be rec) *)
(* Disclaimer: this function doesn't seem to be used anywhere *)
let equal x y = match x, y with
  | TT, TT | FF, FF -> true
  | EqConst (x, c), EqConst (x', c') -> Term.equal x x'
  | Agg (s, op, x, y, f), Agg (s', op', x', y', f') ->
     String.equal s s' && Aggregation.equal_op op op' && Term.equal x x' && List.length y == List.length y'
     && List.for_all (List.zip_exn y y') (fun (y, y') -> String.equal y y') && phys_equal f f'
  | Top (s, op, x, y, f), Top (s', op', x', y', f') ->
     List.equal String.equal s s' && String.equal op op' && List.equal Term.equal x x'
     && List.equal String.equal y y' && phys_equal f f'
  | Predicate (r, trms), Predicate (r', trms') -> String.equal r r' && List.equal Term.equal trms trms'
  | Predicate' (r, trms, f), Predicate' (r', trms', f') ->
     String.equal r r' && List.equal Term.equal trms trms' && phys_equal f f'
  | Let (r, enftype, vars, f, g), Let (r', enftype', vars', f', g') ->
     String.equal r r' && (match enftype, enftype' with
                           | None, None -> true
                           | Some t, Some t' -> Enftype.equal t t')
     && List.equal String.equal vars vars' && phys_equal f f' && phys_equal g g'
  | Let' (r, vars, f, g), Let' (r', vars', f', g') ->
     String.equal r r' && List.equal String.equal vars vars' &&
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
  | Agg (s, _, _, y, _) -> Set.of_list (module Term) (List.map (s::y) ~f:(fun v -> Term.Var v))
  | Top (s, _, x, y, _) -> Set.of_list (module Term) (List.map (s@y) ~f:(fun v -> Term.Var v))
  | Predicate (x, trms) -> Set.of_list (module Term) trms
  | Predicate' (_, _, f) -> terms f
  | Let (_, _, _, _, g) -> terms g
  | Let' (_, _, _, g) -> terms g
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

let rec init =
  let side s_opt = Option.value s_opt ~default:Side.N in
  function
  | SConst (CBool true)               -> TT
  | SConst (CBool false)              -> FF
  | SBop (None, t, Bop.BEq, SConst c) -> EqConst (Term.init t, Const.to_dom c)
  | SBop (None, t, bop, u) as term
       when Bop.is_relational bop     -> EqConst (Term.init term, Dom.Int 1)
  | SAgg (s, aop, x, y, t)            -> Agg (s, Aggregation.init aop, Term.init x, y, init t)
  | STop (s, op, x, y, t)             -> Top (s, op, List.map ~f:Term.init x, y, init t)
  | SAssign (t, s, x)                 -> let f = init t in
                                         Agg (s, Aggregation.AAssign, Term.init x, list_fv f, f)
  | SApp (p, ts)                      -> Predicate (p, List.map ~f:Term.init ts)
  | SLet (x, enftype, y, t, u)        -> Let (x, enftype, y, init t, init u)
  | SExists (xs, t)                   -> List.fold_right xs ~init:(init t) ~f:exists
  | SForall (xs, t)                   -> List.fold_right xs ~init:(init t) ~f:forall
  | SUop (Uop.UNot, t)                -> Neg (init t)
  | SUtop (i, Utop.UPrev, t)          -> Prev (i, init t)
  | SUtop (i, Utop.UNext, t)          -> Next (i, init t)
  | SUtop (i, Utop.UHistorically, t)  -> Historically (i, init t)
  | SUtop (i, Utop.UAlways, t)        -> Always (i, init t)
  | SUtop (i, Utop.UOnce, t)          -> Once (i, init t)
  | SUtop (i, Utop.UEventually, t)    -> Eventually (i, init t)
  | SBop (s_opt, t, Bop.BAnd, u)      -> And (side s_opt, init t, init u)
  | SBop (s_opt, t, Bop.BOr, u)       -> Or (side s_opt, init t, init u)
  | SBop (s_opt, t, Bop.BImp, u)      -> Imp (side s_opt, init t, init u)
  | SBop2 (s_opt, t, Bop2.BIff, u)    -> let s1, s2 = Option.value s_opt ~default:(N, N) in Iff (s1, s2, init t, init u)
  | SBtop (s_opt, i, t, Btop.BSince, u) -> Since (side s_opt, i, init t, init u)
  | SBtop (s_opt, i, t, Btop.BUntil, u) -> Until (side s_opt, i, init t, init u)
  | SBtop (s_opt, i, t, Btop.BRelease, u) -> release (side s_opt) i (init t) (init u)
  | SBtop (s_opt, i, t, Btop.BTrigger, u) -> trigger (side s_opt) i (init t) (init u)

let op_to_string = function
  | TT -> Printf.sprintf "⊤"
  | FF -> Printf.sprintf "⊥"
  | EqConst (x, c) -> Printf.sprintf "="
  | Predicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | Predicate' (r, trms, _) -> Printf.sprintf "%s٭(%s)" r (Term.list_to_string trms)
  | Let (r, _, _, _, _) -> Printf.sprintf "LET %s" r
  | Let' (r, _, _, _) -> Printf.sprintf "LET٭ %s" r
  | Agg (_, op, x, y, _) -> Printf.sprintf "%s(%s; %s)" (Aggregation.op_to_string op) (Term.value_to_string x)
                              (String.concat ~sep:", " y)
  | Top (_, op, x, y, _) -> Printf.sprintf "%s(%s; %s)" op (Term.list_to_string x) (String.concat ~sep:", " y)
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
  | Predicate' (r, trms, _) -> Printf.sprintf "%s٭(%s)" r (Term.list_to_string trms)
  | Let (r, enftype, vars, f, g) -> Printf.sprintf (Etc.paren l (-1) "LET %s(%s)%s = %a IN %a") r
                                      (Etc.string_list_to_string vars)
                                      (Option.fold enftype ~init:""
                                         ~f:(fun _ enftype -> " : " ^ Enftype.to_string enftype))
                                      (fun x -> to_string_rec (-1)) f
                                      (fun x -> to_string_rec (-1)) g
  | Let' (r, vars, f, g) -> Printf.sprintf (Etc.paren l (-1) "LET %s٭(%s) = %a IN %a")
                              r (Etc.string_list_to_string vars)
                              (fun x -> to_string_rec (-1)) f
                              (fun x -> to_string_rec (-1)) g
  | Agg (s, op, x, y, f) -> Printf.sprintf (Etc.paren l (-1) "%s <- %s(%s; %s; %s)")
                              s (Aggregation.op_to_string op)
                              (Term.value_to_string x) (String.concat ~sep:", " y)
                              (to_string_rec (-1) f)
  | Top (s, op, x, y, f) -> Printf.sprintf (Etc.paren l (-1) "[%s] <- %s([%s]; %s; %s)")
                              (String.concat ~sep:", " s) op
                              (Term.list_to_string x) (String.concat ~sep:", " y)
                              (to_string_rec (-1) f)
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
  | Since (s, i, f, g) -> Printf.sprintf (Etc.paren l 0 "%a S%a%a %a") (fun x -> to_string_rec 0) f
                          (fun x -> Interval.to_string) i (fun x -> Side.to_string) s (fun x -> to_string_rec 0) g
  | Until (s, i, f, g) -> Printf.sprintf (Etc.paren l 0 "%a U%a%a %a") (fun x -> to_string_rec 0) f
                         (fun x -> Interval.to_string) i (fun x -> Side.to_string) s (fun x -> to_string_rec 0) g
let to_string = to_string_rec 0

let solve_past_guarded x p f =
  let vars = fv f in
  let eib = Printf.sprintf "%s.%d.%b" in
  let matches ts x r i t = Term.equal (Term.Var x) t && Map.mem ts (eib r i true) in
  let rec aux ts x p f =
    let s =
      match f, p with
      | TT, false -> [Set.empty (module String)]
      | FF, true -> [Set.empty (module String)]
      | EqConst (y, _), true when Term.equal (Term.Var x) y -> [Set.empty (module String)]
      | Predicate (r, trms), _ when List.existsi ~f:(matches ts x r) trms ->
         let f i t = if matches ts x r i t then Some (Map.find_exn ts (eib r i p)) else None in
         List.concat (List.filter_mapi trms ~f)
      | Predicate (r, trms), true when List.exists ~f:(Term.equal (Term.Var x)) trms ->
         [Set.singleton (module String) r]
      | Let (e, _, vars, f, g), _ ->
         let f i ts z =
           let ts = Map.update ts (eib e i true) ~f:(fun _ -> aux ts z true f) in
           Map.update ts (eib e i false) ~f:(fun _ -> aux ts z false f) in
         let ts = List.foldi vars ~init:ts ~f in
         aux ts x p g
      | Agg (s, _, t, _, f), true when String.equal s x ->
         let sols_list = List.map (Term.fv_list [t]) ~f:(fun z -> aux ts z p f) in
         List.map ~f:(Etc.inter_list (module String)) (Etc.cartesian sols_list)
      | Agg (_, _, _, y, f), _ when List.mem y x ~equal:String.equal -> aux ts x p f
      | Top (_, _, _, y, f), _ when List.mem y x ~equal:String.equal -> aux ts x p f
      | Top (s, _, x', _, f), true when List.mem s x ~equal:String.equal ->
         let sols_list = List.map (Term.fv_list x') ~f:(fun z -> aux ts z p f) in
         List.map ~f:(Etc.inter_list (module String)) (Etc.cartesian sols_list)
      | Neg f, _ -> aux ts x (not p) f
      | And (_, f', g'), true | Or (_, f', g'), false | Imp (_, f', g'), false ->
         let q = match f with Imp _ -> not p | _ -> p in
         Etc.dedup ~equal:Set.equal (aux ts x q f' @ aux ts x p g')
      | And (_, f', g'), false | Or (_, f', g'), true | Imp (_, f', g'), true ->
         let q = match f with Imp _ -> not p | _ -> p in
         List.map ~f:(Etc.inter_list (module String)) (Etc.cartesian [aux ts x q f'; aux ts x p g'])
      | Iff (_, _, f, g), _ -> aux ts x p (And (N, Imp (N, f, g), Imp (N, g, f)))
      | Exists (y, f), _ | Forall (y, f), _ when x != y -> aux ts x p f
      | Prev (_, f), true | Once (_, f), true -> aux ts x p f
      | Once (i, f), false | Eventually (i, f), false when Interval.has_zero i -> aux ts x p f
      | Historically (_, f), false | Always (_, f), false -> aux ts x p f
      | Historically (i, f), true | Always (i, f), true when Interval.has_zero i -> aux ts x p f
      | Since (_, i, f, g), true when not (Interval.has_zero i) -> aux ts x p (And (N, f, g))
      | Since (_, i, f, g), true -> aux ts x p g
      | Since (_, i, f, g), false | Until (_, i, f, g), false when Interval.has_zero i -> aux ts x p g
      | Until (_, i, f, g), true when not (Interval.has_zero i) -> aux ts x p f
      | Until (_, i, f, g), true -> aux ts x p (Or (N, f, g))
      | _ -> [] in
    (*print_endline (Printf.sprintf "solve_past_guarded(%s, %b, %s) = [%s]" x p (to_string f)
                     (String.concat ~sep:"; " (List.map ~f:(fun es -> "{" ^ (String.concat ~sep:", " (Set.elements es)) ^ "}") s)) );*)
    s in
  aux (Map.empty (module String)) x p f

let is_past_guarded x p f =
  not (List.is_empty (solve_past_guarded x p f))

let check_agg types s op x y f =
  let x_tt = Sig.tt_of_term_exn types x in
  match Aggregation.ret_tt op x_tt with
  | None -> raise (Invalid_argument (
                       Printf.sprintf "type clash for aggregation operator %s: invalid type %s"
                         (Aggregation.op_to_string op) (Dom.tt_to_string x_tt)))
  | Some s_tt ->
     let types, _ = Sig.check_var types s (Ctxt.TConst s_tt) in
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
     types, s_tt

let check_top types s op x y f =
  let x_tts = List.map ~f:(Sig.tt_of_term_exn types) x in
  let arg_ttts = Sig.arg_ttts_of_func op in
  let ret_ttts = Sig.ret_ttts_of_func op in
  let types = List.fold2_exn ~init:types
                ~f:(fun types trm ttt -> fst (Sig.check_term types trm ttt)) arg_ttts x in
  let types = List.fold2_exn ~init:types
                ~f:(fun types ttt x -> fst (Sig.check_var types x ttt)) ret_ttts s in
  let vars = (Term.fv_list x) @ y in
  let fv = fv f in
  List.iter vars ~f:(
      fun x ->
      if not (Set.mem fv x) then
        raise (Invalid_argument (
                   Printf.sprintf "variable %s is used in aggregation, but not free in %s"
                     x (to_string f)))
      else ());
  types, List.map ~f:Ctxt.unconst ret_ttts

let unroll_let =
  let rec aux (v : (String.t, string list * t, String.comparator_witness) Map.t) = function
    | TT -> TT
    | FF -> FF
    | EqConst (x, c) -> EqConst (x, c)
    | Predicate (r, trms) ->
       (match Map.find v r with
        | None -> Predicate (r, trms)
        | Some (vars, e) -> Predicate' (r, trms, subst (Map.of_alist_exn (module String) (List.zip_exn vars trms)) e))
    | Let (r, _, vars, f, g) ->
       Let' (r, vars, aux v f, aux (Map.update v r (fun _ -> (vars, aux v f))) g)
    | Agg (s, op, x, y, f) -> Agg (s, op, x, y, aux v f)
    | Top (s, op, x, y, f) -> Top (s, op, x, y, aux v f)
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

let convert_vars f =
  let return f i = f, i in
  let (>>|) func fi i = let f, i = fi i in func f, i in
  let (>>=) func fi i = let f, i = fi i in let g, i = func f i in g, i in
  let name x k = Printf.sprintf "%s.%d" x k in
  let fresh (i, v) x =
    let xk, k = match Map.find i x with Some k -> name x (k+1), k+1 | None -> x, 0 in
    (Map.update i x ~f:(fun _ -> k), (Map.update v x ~f:(fun _ -> Term.Var xk))), xk  in
  let rec aux v = function
    | TT -> return TT 
    | FF -> return FF
    | EqConst (x, c) -> return (EqConst (Term.subst v x, c))
    | Predicate (r, trms) -> return (Predicate (r, Term.substs v trms))
    | Predicate' (r, trms, f) -> (fun f -> Predicate' (r, Term.substs v trms, f)) >>| (aux v f)
    | Let (r, enftype, vars, f, g) ->
       (fun i -> let (i, v), vars = List.fold_map vars ~init:(i, v) ~f:fresh in
                 ((fun f -> (fun g -> return (Let (r, enftype, vars, f, g))) >>= (aux v g)) >>= (aux v f)) i)
    | Let' (r, vars, f, g) ->
       (fun i -> let (i, v), vars = List.fold_map vars ~init:(i, v) ~f:fresh in
                 ((fun f -> (fun g -> return (Let' (r, vars, f, g))) >>= (aux v g)) >>= (aux v f)) i)
    | Agg (s, op, x, y, f) ->
       (fun i -> let fvs = Set.elements (Set.diff (fv f) (Set.of_list (module String) ((Term.fv_list [x])@y))) in
                 let (i, v), vars = List.fold_map fvs ~init:(i, v) ~f:fresh in
                 ((fun f -> return (Agg (s, op, Term.subst v x, y, f))) >>= (aux v f)) i)
    | Top (s, op, x, y, f) ->
       (fun i -> let fvs = Set.elements (Set.diff (fv f) (Set.of_list (module String) y)) in
                 let (i, v), vars = List.fold_map fvs ~init:(i, v) ~f:fresh in
                 ((fun f -> return (Top (s, op, Term.substs v x, y, f))) >>= (aux v f)) i)
    | Neg f -> (fun f -> return (Neg f)) >>= (aux v f)
    | And (s, f, g) -> (fun f -> (fun g -> return (And (s, f, g))) >>= (aux v g)) >>= (aux v f)
    | Or (s, f, g) -> (fun f -> (fun g -> return (Or (s, f, g))) >>= (aux v g)) >>= (aux v f)
    | Imp (s, f, g) -> (fun f -> (fun g -> return (Imp (s, f, g))) >>= (aux v g)) >>= (aux v f)
    | Iff (s, t, f, g) -> (fun f -> (fun g -> return (Iff (s, t, f, g))) >>= (aux v g)) >>= (aux v f)
    | Exists (x, f) -> (fun i -> let (i, v), xk = fresh (i, v) x in
                                 ((fun f -> return (Exists (xk, f))) >>= (aux v f)) i)
    | Forall (x, f) -> (fun i -> let (i, v), xk = fresh (i, v) x in
                                 ((fun f -> return (Forall (xk, f))) >>= (aux v f)) i)
    | Prev (i, f) -> (fun f -> Prev (i, f)) >>| (aux v f)
    | Next (i, f) -> (fun f -> Next (i, f)) >>| (aux v f)
    | Once (i, f) -> (fun f -> Once (i, f)) >>| (aux v f)
    | Eventually (i, f) -> (fun f -> Eventually (i, f)) >>| (aux v f)
    | Historically (i, f) -> (fun f -> Historically (i, f)) >>| (aux v f)
    | Always (i, f) -> (fun f -> Always (i, f)) >>| (aux v f)
    | Since (s, i, f, g) -> (fun f -> (fun g -> return (Since (s, i, f, g))) >>= (aux v g)) >>= (aux v f)
    | Until (s, i, f, g) -> (fun f -> (fun g -> return (Until (s, i, f, g))) >>= (aux v g)) >>= (aux v f)
  in fst (aux (Map.empty (module String)) f (Map.empty (module String)))

let convert_lets f =
  let return f i = f, i in
  let (>>|) func fi i = let f, i = fi i in func f, i in
  let (>>=) func fi i = let f, i = fi i in let g, i = func f i in g, i in
  let name x k = Printf.sprintf "%s.%d" x k in
  let fresh i r v =
    let rk, k = match Map.find i r with Some k -> name r (k+1), k+1 | None -> r, 0 in
    (Map.update i r ~f:(fun _ -> k)), (rk, (Map.update v r ~f:(fun _ -> rk))) in
  let rec aux v = function
    | TT -> return TT
    | FF -> return FF
    | EqConst (x, c) -> return (EqConst (x, c))
    | Predicate (r, trms) ->
       return (Predicate (Option.value (Map.find v r) ~default:r, trms))
    | Predicate' (r, trms, f) ->
       (fun f -> return (Predicate' (Option.value (Map.find v r) ~default:r, trms, f))) >>= (aux v f)
    | Let (r, enftype, vars, f, g) ->
       (fun i -> let i, (rk, v) = fresh i r v in
                 ((fun f -> (fun g -> return (Let (rk, enftype, vars, f, g))) >>= (aux v g))>>= (aux v f)) i)
    | Let' (r, vars, f, g) ->
       (fun i -> let i, (rk, v) = fresh i r v in
                 ((fun f -> (fun g -> return (Let' (rk, vars, f, g))) >>= (aux v g)) >>= (aux v f)) i)
    | Agg (s, op, x, y, f) -> (fun f -> return (Agg (s, op, x, y, f))) >>= (aux v f)
    | Top (s, op, x, y, f) -> (fun f -> return (Top (s, op, x, y, f))) >>= (aux v f)
    | Neg f -> (fun f -> return (Neg f)) >>= (aux v f)
    | And (s, f, g) -> (fun f -> (fun g -> return (And (s, f, g))) >>= (aux v g)) >>= (aux v f)
    | Or (s, f, g) -> (fun f -> (fun g -> return (Or (s, f, g))) >>= (aux v g)) >>= (aux v f)
    | Imp (s, f, g) -> (fun f -> (fun g -> return (Imp (s, f, g))) >>= (aux v g)) >>= (aux v f)
    | Iff (s, t, f, g) -> (fun f -> (fun g -> return (Iff (s, t, f, g))) >>= (aux v g)) >>= (aux v f)
    | Exists (x, f) -> (fun f -> Exists (x, f)) >>| (aux v f)
    | Forall (x, f) -> (fun f -> Forall (x, f)) >>| (aux v f)
    | Prev (i, f) -> (fun f -> Prev (i, f)) >>| (aux v f)
    | Next (i, f) -> (fun f -> Next (i, f)) >>| (aux v f)
    | Once (i, f) -> (fun f -> Once (i, f)) >>| (aux v f)
    | Eventually (i, f) -> (fun f -> Eventually (i, f)) >>| (aux v f)
    | Historically (i, f) -> (fun f -> Historically (i, f)) >>| (aux v f)
    | Always (i, f) -> (fun f -> Always (i, f)) >>| (aux v f)
    | Since (s, i, f, g) -> (fun f -> (fun g -> return (Since (s, i, f, g))) >>= (aux v g)) >>= (aux v f)
    | Until (s, i, f, g) -> (fun f -> (fun g -> return (Until (s, i, f, g))) >>= (aux v g)) >>= (aux v f)
  in fst (aux (Map.empty (module String)) f (Map.empty (module String)))

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
      | Predicate (e, _) when b -> (match Sig.kind_of_pred e with Trace -> An e | _ -> _true)
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


