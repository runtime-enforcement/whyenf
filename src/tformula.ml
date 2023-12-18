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
  | TExists of string * t
  | TForall of string * t
  | TPrev of Interval.t * t
  | TNext of Interval.t * t
  | TOnce of Interval.t * t
  | TEventually of Interval.t * t
  | THistorically of Interval.t * t
  | TAlways of Interval.t * t
  | TSince of Side.t * Interval.t * t * t
  | TUntil of Side.t * Interval.t * t * t

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
  | Exists (x, _, f) -> TExists (x, of_formula f)
  | Forall (x, _, f) -> TForall (x, of_formula f)
  | Prev (i, f) -> TPrev (i, of_formula f)
  | Next (i, f) -> TNext (i, of_formula f)
  | Once (i, f) -> TOnce (i, of_formula f)
  | Eventually (i, f) -> TEventually (i, of_formula f)
  | Historically (i, f) -> THistorically (i, of_formula f)
  | Always (i, f) -> TAlways (i, of_formula f)
  | Since (s, i, f, g) -> TSince (s, i, of_formula f, of_formula g)
  | Until (s, i, f, g) -> TUntil (s, i, of_formula f, of_formula g)

 and of_formula f = { f = core_of_formula f; enftype = EnfType.Obs }

let rec to_string_core_rec l = function
  | TTT -> Printf.sprintf "⊤"
  | TFF -> Printf.sprintf "⊥"
  | TEqConst (x, c) -> Printf.sprintf "%s = %s" x (Dom.to_string c)
  | TPredicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | TNeg f -> Printf.sprintf "¬%a" (fun x -> to_string_rec 5) f
  | TAnd (s, f, g) -> Printf.sprintf (Etc.paren l 4 "%a ∧%a %a") (fun x -> to_string_rec 4) f (fun x -> Side.string_of) s (fun x -> to_string_rec 4) g
  | TOr (s, f, g) -> Printf.sprintf (Etc.paren l 3 "%a ∨%a %a") (fun x -> to_string_rec 3) f (fun x -> Side.string_of) s (fun x -> to_string_rec 4) g
  | TImp (s, f, g) -> Printf.sprintf (Etc.paren l 5 "%a →%a %a") (fun x -> to_string_rec 5) f (fun x -> Side.string_of) s (fun x -> to_string_rec 5) g
  | TIff (s, t, f, g) -> Printf.sprintf (Etc.paren l 5 "%a ↔%a %a") (fun x -> to_string_rec 5) f (fun x -> Side.string_of2) (s, t) (fun x -> to_string_rec 5) g
  | TExists (x, f) -> Printf.sprintf (Etc.paren l 5 "∃%s. %a") x (fun x -> to_string_rec 5) f
  | TForall (x, f) -> Printf.sprintf (Etc.paren l 5 "∀%s. %a") x (fun x -> to_string_rec 5) f
  | TPrev (i, f) -> Printf.sprintf (Etc.paren l 5 "●%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
  | TNext (i, f) -> Printf.sprintf (Etc.paren l 5 "○%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
  | TOnce (i, f) -> Printf.sprintf (Etc.paren l 5 "⧫%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
  | TEventually (i, f) -> Printf.sprintf (Etc.paren l 5 "◊%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
  | THistorically (i, f) -> Printf.sprintf (Etc.paren l 5 "■%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
  | TAlways (i, f) -> Printf.sprintf (Etc.paren l 5 "□%a %a") (fun x -> Interval.to_string) i (fun x -> to_string_rec 5) f
  | TSince (s, i, f, g) -> Printf.sprintf (Etc.paren l 0 "%a S%a%a %a") (fun x -> to_string_rec 5) f
                         (fun x -> Interval.to_string) i (fun x -> Side.string_of) s (fun x -> to_string_rec 5) g
  | TUntil (s, i, f, g) -> Printf.sprintf (Etc.paren l 0 "%a U%a%a %a") (fun x -> to_string_rec 5) f
                         (fun x -> Interval.to_string) i (fun x -> Side.string_of) s (fun x -> to_string_rec 5) g
and to_string_rec l form =
  if form.enftype == EnfType.Obs then
    Printf.sprintf "%a" (fun x -> to_string_core_rec 5) form.f
  else
    Printf.sprintf (Etc.paren l 0 "%a : %s") (fun x -> to_string_core_rec 5) form.f (EnfType.to_string form.enftype)

let to_string = to_string_rec 0
