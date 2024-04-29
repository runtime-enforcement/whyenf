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
  | TEqConst of string * Dom.t
  | TPredicate of string * Term.t list
  | TNeg of t
  | TAnd of Side.t * t * t
  | TOr of Side.t * t * t
  | TImp of Side.t * t * t
  | TIff of Side.t * Side.t * t * t
  | TExists of string * Dom.tt * t
  | TForall of string * Dom.tt * t
  | TPrev of Interval.t * t
  | TNext of Interval.t * t
  | TOnce of Interval.t * t
  | TEventually of Interval.t * bool * t
  | THistorically of Interval.t * t
  | TAlways of Interval.t * bool * t
  | TSince of Side.t * Interval.t * t * t
  | TUntil of Side.t * Interval.t * bool * t * t

and t = { f: core_t; enftype: EnfType.t }

let rec core_of_formula = function
  | TT -> TTT
  | FF -> TFF
  | EqConst (x, v) -> TEqConst (x, v)
  | Predicate (e, t) -> TPredicate (e, t)
  | Neg f -> TNeg (of_formula f)
  | And (s, f, g) -> TAnd (s, of_formula f, of_formula g)
  | Or (s, f, g) -> TOr (s, of_formula f, of_formula g)
  | Imp (s, f, g) -> TImp (s, of_formula f, of_formula g)
  | Iff (s, t, f, g) -> TIff (s, t, of_formula f, of_formula g)
  | Exists (x, tt, f) -> TExists (x, tt, of_formula f)
  | Forall (x, tt, f) -> TForall (x, tt, of_formula f)
  | Prev (i, f) -> TPrev (i, of_formula f)
  | Next (i, f) -> TNext (i, of_formula f)
  | Once (i, f) -> TOnce (i, of_formula f)
  | Eventually (i, f) -> TEventually (i, true, of_formula f)
  | Historically (i, f) -> THistorically (i, of_formula f)
  | Always (i, f) -> TAlways (i, true, of_formula f)
  | Since (s, i, f, g) -> TSince (s, i, of_formula f, of_formula g)
  | Until (s, i, f, g) -> TUntil (s, i, true, of_formula f, of_formula g)

and of_formula f = { f = core_of_formula f; enftype = EnfType.Obs }

let rec rank = function
  | TTT | TFF -> 0
  | TEqConst _ -> 0
  | TPredicate (r, _) -> Pred.Sig.rank_of_pred r
  | TNeg f
    | TExists (_, _, f)
    | TForall (_, _, f)
    | TPrev (_, f)
    | TNext (_, f)
    | TOnce (_, f)
    | TEventually (_, _, f)
    | THistorically (_, f)
    | TAlways (_, _, f) -> rank f.f
  | TAnd (_, f, g)
    | TOr (_, f, g)
    | TImp (_, f, g)
    | TIff (_, _, f, g)
    | TSince (_, _, f, g)
    | TUntil (_, _, _, f, g) -> rank f.f + rank g.f

let fix_side s f g =
  match s with
  | Side.LR -> if rank f < rank g then Side.L
               else Side.R
  | _ -> s

let rec to_formula f = match f.f with
  | TTT -> TT
  | TFF -> FF
  | TEqConst (x, v) -> EqConst (x, v)
  | TPredicate (e, t) -> Predicate (e, t)
  | TNeg f -> Neg (to_formula f)
  | TAnd (s, f, g) -> And (fix_side s f.f g.f, to_formula f, to_formula g)
  | TOr (s, f, g) -> Or (fix_side s f.f g.f, to_formula f, to_formula g)
  | TImp (s, f, g) -> Imp (fix_side s f.f g.f, to_formula f, to_formula g)
  | TIff (s, t, f, g) -> Iff (fix_side s f.f g.f, fix_side t f.f g.f, to_formula f, to_formula g)
  | TExists (x, tt, f) -> Exists (x, tt, to_formula f)
  | TForall (x, tt, f) -> Forall (x, tt, to_formula f)
  | TPrev (i, f) -> Prev (i, to_formula f)
  | TNext (i, f) -> Next (i, to_formula f)
  | TOnce (i, f) -> Once (i, to_formula f)
  | TEventually (i, _, f) -> Eventually (i, to_formula f)
  | THistorically (i, f) -> Historically (i, to_formula f)
  | TAlways (i, _, f) -> Always (i, to_formula f)
  | TSince (s, i, f, g) -> Since (fix_side s f.f g.f, i, to_formula f, to_formula g)
  | TUntil (s, i, _, f, g) -> Until (s, i, to_formula f, to_formula g)

let ttrue  = { f = TTT; enftype = Cau }
let tfalse = { f = TFF; enftype = Sup }

let neg f enftype = { f = TNeg f; enftype }
let conj side f g enftype = { f = TAnd (side, f, g); enftype }

let rec op_to_string_core = function
  | TTT -> Printf.sprintf "⊤"
  | TFF -> Printf.sprintf "⊥"
  | TEqConst (x, c) -> Printf.sprintf "="
  | TPredicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | TNeg _ -> Printf.sprintf "¬"
  | TAnd (_, _, _) -> Printf.sprintf "∧"
  | TOr (_, _, _) -> Printf.sprintf "∨"
  | TImp (_, _, _) -> Printf.sprintf "→"
  | TIff (_, _, _, _) -> Printf.sprintf "↔"
  | TExists (x, _, _) -> Printf.sprintf "∃ %s." x
  | TForall (x, _, _) -> Printf.sprintf "∀ %s." x
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
  | TEqConst (x, c) -> Printf.sprintf "%s = %s" x (Dom.to_string c)
  | TPredicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | TNeg f -> Printf.sprintf "¬%a" (fun x -> to_string_rec 5) f
  | TAnd (s, f, g) -> Printf.sprintf (Etc.paren l 4 "%a ∧%a %a") (fun x -> to_string_rec 4) f (fun x -> Side.to_string) s (fun x -> to_string_rec 4) g
  | TOr (s, f, g) -> Printf.sprintf (Etc.paren l 3 "%a ∨%a %a") (fun x -> to_string_rec 3) f (fun x -> Side.to_string) s (fun x -> to_string_rec 4) g
  | TImp (s, f, g) -> Printf.sprintf (Etc.paren l 5 "%a →%a %a") (fun x -> to_string_rec 5) f (fun x -> Side.to_string) s (fun x -> to_string_rec 5) g
  | TIff (s, t, f, g) -> Printf.sprintf (Etc.paren l 5 "%a ↔%a %a") (fun x -> to_string_rec 5) f (fun x -> Side.to_string2) (s, t) (fun x -> to_string_rec 5) g
  | TExists (x, _, f) -> Printf.sprintf (Etc.paren l 5 "∃%s. %a") x (fun x -> to_string_rec 5) f
  | TForall (x, _, f) -> Printf.sprintf (Etc.paren l 5 "∀%s. %a") x (fun x -> to_string_rec 5) f
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
