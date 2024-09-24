(*******************************************************************)
(*     This is part of WhyEnf, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  François Hublet (ETH Zurich)                                   *)
(*******************************************************************)

open Base
open Pred
open Formula


type core_t =
  | TTT
  | TFF
  | TEqConst of Term.t * Dom.t
  | TPredicate of string * Term.t list
  | TLet of string * string list * t * t
  | TAgg of string * Dom.tt * Aggregation.op * Term.t * string list * t
  | TNeg of t
  | TAnd of Side.t * t list
  | TOr of Side.t * t list
  | TImp of Side.t * t * t
  | TIff of Side.t * Side.t * t * t
  | TExists of string * Dom.tt * bool * t
  | TForall of string * Dom.tt * bool * t
  | TPrev of Interval.t * t
  | TNext of Interval.t * t
  | TOnce of Interval.t * t
  | TEventually of Interval.t * bool * t
  | THistorically of Interval.t * t
  | TAlways of Interval.t * bool * t
  | TSince of Side.t * Interval.t * t * t
  | TUntil of Side.t * Interval.t * bool * t * t

and t = {
    f:       core_t;
    enftype: EnfType.t;
    filter:  Filter.filter;
  } [@@deriving compare, hash, sexp_of]

let rec core_of_formula f (types: Dom.ctxt) =
  let f_q ?(true_ok=true) f x =
    if Formula.is_past_guarded x true f then
      true
    else if Formula.is_past_guarded x false f && true_ok then
      false
    else
      raise (Invalid_argument
               (Printf.sprintf "variable %s is not monitorable in %s" x (Formula.to_string f)))
  in
  match f with
  | TT -> types, TTT
  | FF -> types, TFF
  | EqConst (trm, c) ->
     let types, trm = Pred.check_term types (Dom.tt_of_domain c) trm in
     types, TEqConst (trm, c)
  | Predicate (e, trms) when not (Sig.equal_pred_kind (Sig.kind_of_pred e) Sig.Predicate) ->
     let types, trms = Pred.check_terms types e trms in
     types, TPredicate (e, trms)
  | Predicate (e, trms) ->
     let types, trms = Pred.check_terms types e trms in
     types, TEqConst (Term.App (e, trms), Dom.Int 1)
  | Let (e, xs, f, g) ->
     let types, trms = Pred.check_terms types e (List.map xs ~f:(fun x -> Pred.Term.Var x)) in
     let types, mf = of_formula f types in
     let types, mg = of_formula g types in
     types, TLet (e, List.map trms ~f:(fun trm -> Pred.Term.unvar trm), mf, mg)
  | Agg (s, op, x, y, f) ->
     let types, mf = of_formula f types in
     let types = Formula.check_agg types s op x y f in
     let vars_to_monitor =
       Term.fv_list [x]
       @ (List.filter (Set.elements (Formula.fv f))
            ~f:(fun x -> List.mem y x ~equal:String.equal)) in
     ignore (List.map vars_to_monitor ~f:(f_q ~true_ok:false f));
     types, TAgg (s, Sig.tt_of_term_exn types x, op, x, y, mf)
  | Neg f ->
     let types, mf = of_formula f types in
     types, TNeg mf
  | And (s, f, g) ->
     let types, mf = of_formula f types in
     let types, mg = of_formula g types in
     types, TAnd (s, [mf; mg])
  | Or (s, f, g) ->
     let types, mf = of_formula f types in
     let types, mg = of_formula g types in
     types, TOr (s, [mf; mg])
  | Imp (s, f, g) ->
     let types, mf = of_formula f types in
     let types, mg = of_formula g types in
     types, TImp (s, mf, mg)
  | Iff (s, t, f, g) ->
     let types, mf = of_formula f types in
     let types, mg = of_formula g types in
     types, TIff (s, t, mf, mg)
  | Exists (x, f) ->
     let types, mf = of_formula f types in
     types, TExists (x, Map.find_exn types x, f_q f x, mf)
  | Forall (x, f) ->
     let types, mf = of_formula f types in
     types, TForall (x, Map.find_exn types x, f_q f x, mf)
  | Prev (i, f) ->
     let types, mf = of_formula f types in
     types, TPrev (i, mf)
  | Next (i, f) ->
     let types, mf = of_formula f types in
     types, TNext (i, mf)
  | Once (i, f) ->
     let types, mf = of_formula f types in
     types, TOnce (i, mf)
  | Eventually (i, f) ->
     let types, mf = of_formula f types in
     types, TEventually (i, true, mf)
  | Historically (i, f) ->
     let types, mf = of_formula f types in
     types, THistorically (i, mf)
  | Always (i, f) ->
     let types, mf = of_formula f types in
     types, TAlways (i, true, mf)
  | Since (s, i, f, g) ->
     let types, mf = of_formula f types in
     let types, mg = of_formula g types in
     types, TSince (s, i, mf, mg)
  | Until (s, i, f, g) ->
     let types, mf = of_formula f types in
     let types, mg = of_formula g types in
     types, TUntil (s, i, true, mf, mg)

and of_formula f (types: Dom.ctxt) =
  let types, f = core_of_formula f types in
  types, { f; enftype = EnfType.Obs; filter = Filter._true }

let of_formula' f =
  snd (of_formula f (Map.empty (module String)))

let rec rank = function
  | TTT | TFF -> 0
  | TEqConst _ -> 0
  | TPredicate (r, _) -> Pred.Sig.rank_of_pred r
  | TNeg f
    | TExists (_, _, _, f)
    | TForall (_, _, _, f)
    | TPrev (_, f)
    | TNext (_, f)
    | TOnce (_, f)
    | TEventually (_, _, f)
    | THistorically (_, f)
    | TAlways (_, _, f)
    | TAgg (_, _, _, _, _, f) -> rank f.f
  | TImp (_, f, g)
    | TIff (_, _, f, g)
    | TSince (_, _, f, g)
    | TUntil (_, _, _, f, g) -> rank f.f + rank g.f
  | TAnd (_, fs)
    | TOr (_, fs) -> let f f = rank f.f in
                     List.fold ~f:(+) ~init:0 (List.map fs ~f)


let fix_side s f g =
  match s with
  | Side.LR -> if rank f < rank g then Side.L
               else Side.R
  | _ -> s

let rec ac_simplify_core = function
  | TTT -> TTT
  | TFF -> TFF
  | TEqConst (x, v) -> TEqConst (x, v)
  | TPredicate (e, t) -> TPredicate (e, t)
  | TAgg (s, tt, op, x, y, f) -> TAgg (s, tt, op, x, y, ac_simplify f)
  | TNeg f -> TNeg f
  | TAnd (s, fs) ->
     let fs = List.map fs ~f:ac_simplify in
     let f fs f' = match f'.f with
       | TAnd (s', fs') when Side.equal s s' -> fs @ fs'
       | _ -> fs @ [f'] in
     let fs = List.fold_left fs ~init:[] ~f in
     TAnd (s, fs)
  | TOr (s, fs) ->
     let fs = List.map fs ~f:ac_simplify in
     let f fs f' = match f'.f with
       | TAnd (s', fs') when Side.equal s s' -> fs @ fs'
       | _ -> fs @ [f'] in
     let fs = List.fold_left fs ~init:[] ~f in
     TOr (s, fs)
  | TImp (s, f, g) -> TImp (s, ac_simplify f, ac_simplify g)
  | TIff (s, t, f, g) -> TIff (s, t, ac_simplify f, ac_simplify g)
  | TExists (x, tt, b, f) -> TExists (x, tt, b, ac_simplify f)
  | TForall (x, tt, b, f) -> TForall (x, tt, b, ac_simplify f)
  | TPrev (i, f) -> TPrev (i, ac_simplify f)
  | TNext (i, f) -> TNext (i, ac_simplify f)
  | TOnce (i, f) -> TOnce (i, ac_simplify f)
  | TEventually (i, b, f) -> TEventually (i, b, ac_simplify f)
  | THistorically (i, f) -> THistorically (i, ac_simplify f)
  | TAlways (i, b, f) -> TAlways (i, b, ac_simplify f)
  | TSince (s, i, f, g) -> TSince (s, i, ac_simplify f, ac_simplify g)
  | TUntil (s, i, b, f, g) -> TUntil (s, i, b, ac_simplify f, ac_simplify g)

and ac_simplify f =
  { f with f = ac_simplify_core f.f }

let rec to_formula f = match f.f with
  | TTT -> TT
  | TFF -> FF
  | TEqConst (x, v) -> EqConst (x, v)
  | TPredicate (e, t) -> Predicate (e, t)
  | TLet (e, xs, f, g) -> Let (e, xs, to_formula f, to_formula g)
  | TAgg (s, _, op, x, y, f) -> Agg (s, op, x, y, to_formula f)
  | TNeg f -> Neg (to_formula f)
  | TAnd (s, [f; g]) -> And (fix_side s f.f g.f, to_formula f, to_formula g)
  | TAnd (s, f :: fs) -> List.fold ~init:(to_formula f) ~f:(fun f g -> And (s, f, to_formula g)) fs
  | TOr (s, [f; g]) -> Or (fix_side s f.f g.f, to_formula f, to_formula g)
  | TOr (s, f :: fs) -> List.fold ~init:(to_formula f) ~f:(fun f g -> Or (s, f, to_formula g)) fs
  | TImp (s, f, g) -> Imp (fix_side s f.f g.f, to_formula f, to_formula g)
  | TIff (s, t, f, g) -> Iff (fix_side s f.f g.f, fix_side t f.f g.f, to_formula f, to_formula g)
  | TExists (x, _, _, f) -> Exists (x, to_formula f)
  | TForall (x, _, _, f) -> Forall (x, to_formula f)
  | TPrev (i, f) -> Prev (i, to_formula f)
  | TNext (i, f) -> Next (i, to_formula f)
  | TOnce (i, f) -> Once (i, to_formula f)
  | TEventually (i, _, f) -> Eventually (i, to_formula f)
  | THistorically (i, f) -> Historically (i, to_formula f)
  | TAlways (i, _, f) -> Always (i, to_formula f)
  | TSince (s, i, f, g) -> Since (fix_side s f.f g.f, i, to_formula f, to_formula g)
  | TUntil (s, i, _, f, g) -> Until (s, i, to_formula f, to_formula g)

let ttrue  = { f = TTT; enftype = Cau; filter = Filter._true }
let tfalse = { f = TFF; enftype = Sup; filter = Filter._true }

let neg f enftype = { f = TNeg f; enftype; filter = Filter._true }
let conj side f g enftype = { f = TAnd (side, [f; g]); enftype; filter = Filter._true }

let rec op_to_string_core = function
  | TTT -> Printf.sprintf "⊤"
  | TFF -> Printf.sprintf "⊥"
  | TEqConst (x, c) -> Printf.sprintf "="
  | TPredicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | TLet _ -> Printf.sprintf "let"
  | TAgg (_, _, op, x, y, _) -> Printf.sprintf "%s(%s; %s)" (Aggregation.op_to_string op) (Term.value_to_string x) (String.concat ~sep:", " y)
  | TNeg _ -> Printf.sprintf "¬"
  | TAnd (_, _) -> Printf.sprintf "∧"
  | TOr (_, _) -> Printf.sprintf "∨"
  | TImp (_, _, _) -> Printf.sprintf "→"
  | TIff (_, _, _, _) -> Printf.sprintf "↔"
  | TExists (x, _, _, _) -> Printf.sprintf "∃ %s." x
  | TForall (x, _, _, _) -> Printf.sprintf "∀ %s." x
  | TPrev (i, _) -> Printf.sprintf "●%s" (Interval.to_string i)
  | TNext (i, _) -> Printf.sprintf "○%s" (Interval.to_string i)
  | TOnce (i, f) -> Printf.sprintf "⧫%s" (Interval.to_string i)
  | TEventually (i, _, f) -> Printf.sprintf "◊%s" (Interval.to_string i)
  | THistorically (i, f) -> Printf.sprintf "■%s" (Interval.to_string i)
  | TAlways (i, _, f) -> Printf.sprintf "□%s" (Interval.to_string i)
  | TSince (_, i, _, _) -> Printf.sprintf "S%s" (Interval.to_string i)
  | TUntil (_, i, _,  _, _) -> Printf.sprintf "U%s" (Interval.to_string i)
and op_to_string f = op_to_string_core f.f


let rec to_string_core_rec l = function
  | TTT -> Printf.sprintf "⊤"
  | TFF -> Printf.sprintf "⊥"
  | TEqConst (trm, c) -> Printf.sprintf "{%s = %s}" (Term.value_to_string trm) (Dom.to_string c)
  | TPredicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | TLet (e, xs, f, g) -> Printf.sprintf "let %s(%s) = %s in\n%s" e (Term.list_to_string (List.map xs ~f:(fun x -> Pred.Term.Var x)))
                            (to_string_rec l f) (to_string_rec l g)
  | TAgg (s, _, op, x, y, f) -> Printf.sprintf "%s = %s(%s; %s; %s)" s (Aggregation.op_to_string op) (Term.value_to_string x) (String.concat ~sep:", " y) (to_string_rec 4 f)
  | TNeg f -> Printf.sprintf "¬%a" (fun x -> to_string_rec 5) f
  | TAnd (s, fs) -> Printf.sprintf (Etc.paren l 4 "%s") (String.concat ~sep:("∧" ^ Side.to_string s) (List.map fs ~f:(to_string_rec 4)))
  | TOr (s, fs) -> Printf.sprintf (Etc.paren l 3 "%s") (String.concat ~sep:("∨" ^ Side.to_string s) (List.map fs ~f:(to_string_rec 4)))
  | TImp (s, f, g) -> Printf.sprintf (Etc.paren l 5 "%a →%a %a") (fun x -> to_string_rec 5) f (fun x -> Side.to_string) s (fun x -> to_string_rec 5) g
  | TIff (s, t, f, g) -> Printf.sprintf (Etc.paren l 5 "%a ↔%a %a") (fun x -> to_string_rec 5) f (fun x -> Side.to_string2) (s, t) (fun x -> to_string_rec 5) g
  | TExists (x, _, _, f) -> Printf.sprintf (Etc.paren l 5 "∃%s. %a") x (fun x -> to_string_rec 5) f
  | TForall (x, _, _, f) -> Printf.sprintf (Etc.paren l 5 "∀%s. %a") x (fun x -> to_string_rec 5) f
  | TPrev (i, f) -> Printf.sprintf (Etc.paren l 5 "●%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
  | TNext (i, f) -> Printf.sprintf (Etc.paren l 5 "○%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
  | TOnce (i, f) -> Printf.sprintf (Etc.paren l 5 "⧫%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
  | TEventually (i, _, f) -> Printf.sprintf (Etc.paren l 5 "◊%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
  | THistorically (i, f) -> Printf.sprintf (Etc.paren l 5 "■%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
  | TAlways (i, _, f) -> Printf.sprintf (Etc.paren l 5 "□%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
  | TSince (s, i, f, g) -> Printf.sprintf (Etc.paren l 0 "%a S%a%a %a") (fun x -> to_string_rec 5) f
                         (fun x -> Interval.to_string) i (fun x -> Side.to_string) s (fun x -> to_string_rec 5) g
  | TUntil (s, i, _, f, g) -> Printf.sprintf (Etc.paren l 0 "%a U%a%a %a") (fun x -> to_string_rec 5) f
                             (fun x -> Interval.to_string) i (fun x -> Side.to_string) s (fun x -> to_string_rec 5) g
and to_string_rec l form =
  if form.enftype == EnfType.Obs then
    Printf.sprintf "%a" (fun x -> to_string_core_rec 5) form.f
  else
    Printf.sprintf (Etc.paren l 0 "%a : %s") (fun x -> to_string_core_rec 5) form.f (EnfType.to_string form.enftype)

let to_string = to_string_rec 0
