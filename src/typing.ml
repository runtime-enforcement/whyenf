(*******************************************************************)
(*     This is part of WhyEnf, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2024:                                                *)
(*  François Hublet (ETH Zurich)                                   *)
(*******************************************************************)

open Base
open Formula
open Pred

let rec is_past_guarded x p f =
  let r =
  match f with
  | TT | FF -> false
  | EqConst (y, _) -> p && (Term.Var x == y)
  | Predicate (_, ts) when p -> List.exists ~f:(Term.equal (Term.Var x)) ts
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
  | Exists (y, _, f) | Forall (y, _, f) -> x != y && is_past_guarded x p f
  | Prev (_, f) -> p && is_past_guarded x p f
  | Once (_, f) | Eventually (_, f) when p -> is_past_guarded x p f
  | Once (i, f) | Eventually (i, f) -> Interval.mem 0 i && is_past_guarded x p f
  | Historically (_, f) | Always (_, f) when not p -> is_past_guarded x p f
  | Historically (i, f) | Eventually (i, f) -> Interval.mem 0 i && is_past_guarded x p f
  | Since (_, i, f, g) when p -> not (Interval.mem 0 i) && is_past_guarded x p f
                                 || is_past_guarded x p g
  | Until (_, i, f, g) when p -> not (Interval.mem 0 i) && is_past_guarded x p f
                                 || is_past_guarded x p f && is_past_guarded x p g
  | Since (_, i, f, g) | Until (_, i, f, g) -> Interval.mem 0 i && is_past_guarded x p g
  | _ -> false
  in r

module Errors = struct

  type error =
    | ECast of string * EnfType.t * EnfType.t
    | EFormula of string option * t * EnfType.t
    | EConj of error * error
    | EDisj of error * error

  let rec to_string ?(n=0) e =
    let sp = Etc.spaces (2*n) in
    let lb = "\n" ^ sp in
    (match e with
     | ECast (e, t', t) -> "make "
                           ^ e
                           ^ " "
                           ^ EnfType.to_string t
                           ^ " (currently, it has type "
                           ^ EnfType.to_string t'
                           ^ ")"
     | EFormula (None, f, t) -> "make "
                                ^ Formula.to_string f
                                ^ " "
                                ^ EnfType.to_string t
                                ^ ", but this is impossible"
     | EFormula (Some s, f, t) -> "make "
                                ^ Formula.to_string f
                                ^ " "
                                ^ EnfType.to_string t
                                ^ ", but this is impossible"
                                ^ " (" ^ s ^ ")"
     | EConj (f, g) -> "both" ^ lb ^ "* "
                       ^ to_string ~n:(n+1) f
                       ^ lb ^ "and" ^ lb ^ "* "
                       ^ to_string ~n:(n+1) g
     | EDisj (f, g) -> "either" ^ lb ^ "* "
                       ^ to_string ~n:(n+1) f
                       ^ lb ^ "or" ^ lb ^ "* "
                       ^ to_string ~n:(n+1) g
    )

end

module Constraints = struct

  type constr =
    | CTT
    | CFF
    | CEq of string * EnfType.t
    | CConj of constr * constr
    | CDisj of constr * constr [@@deriving compare, sexp_of]

  type verdict = Possible of constr | Impossible of Errors.error

  let tt = CTT
  let ff = CFF
  let eq s t = CEq (s, t)

  let conj c d = match c, d with
    | Possible CTT, _ -> d
    | _, Possible CTT -> c
    | Impossible c, Impossible d -> Impossible (EConj (c, d))
    | Impossible c, _ | _, Impossible c -> Impossible c
    | Possible c, Possible d -> Possible (CConj (c, d))

  let disj c d = match c, d with
    | Impossible c, Impossible d -> Impossible (EDisj (c, d))
    | Impossible c, _ -> d
    | _, Impossible d -> c
    | Possible CTT, _ | _, Possible CTT -> Possible CTT
    | Possible c, Possible d -> Possible (CDisj (c, d))

  let rec cartesian a = function
      [] -> []
    | h::t -> (List.map a ~f:(fun x -> (x,h))) @ cartesian a t

  exception CannotMerge

  let merge_aux ~key = function
    | `Left t | `Right t -> Some t
    | `Both (t, u) -> if t == u then Some t else raise CannotMerge

  let try_merge (a, b) =
    try Some (Map.merge a b ~f:merge_aux)
    with CannotMerge -> None

  let rec solve = function
    | CTT -> [Map.empty (module String)]
    | CFF -> []
    | CEq (s, t) -> [Map.singleton (module String) s t]
    | CConj (c, d) -> List.filter_map (cartesian (solve c) (solve d)) ~f:try_merge
    | CDisj (c, d) -> (solve c) @ (solve d)

  let rec to_string_rec l = function
    | CTT -> Printf.sprintf "⊤"
    | CFF -> Printf.sprintf "⊥"
    | CEq (s, t) -> Printf.sprintf "t(%s) = %s" s (EnfType.to_string t)
    | CConj (c, d) -> Printf.sprintf (Etc.paren l 4 "%a ∧ %a") (fun x -> to_string_rec 4) c (fun x -> to_string_rec 4) d
    | CDisj (c, d) -> Printf.sprintf (Etc.paren l 3 "%a ∨ %a") (fun x -> to_string_rec 3) c (fun x -> to_string_rec 4) d

  let to_string = to_string_rec 0

end

open EnfType
open Constraints
open Option

(* todo: ensure that there is no shadowing *)

let types_predicate t e =
  let t' = Pred.Sig.enftype_of_pred e in
  match t', t with
  | _, _ when t == t' -> Possible CTT
  | CauSup, _         -> Possible (eq e t)
  | _, _              -> Impossible (ECast (e, t', t))

let rec types t f =
  let error s = Impossible (EFormula (Some s, f, t)) in
  match t with
    Cau -> begin
      match f with
      | TT -> Possible CTT
      | Predicate (e, _) -> types_predicate Cau e
      | Neg f -> types Sup f
      | And (_, f, g) -> conj (types Cau f) (types Cau g)
      | Or (L, f, g) -> types Cau f
      | Or (R, f, g) -> types Cau g
      | Or (_, f, g) -> disj (types Cau f) (types Cau g)
      | Imp (L, f, g) -> types Sup f
      | Imp (R, f, g) -> types Cau g
      | Imp (_, f, g) -> disj (types Sup f) (types Cau g)
      | Iff (L, L, f, g) -> conj (types Sup f) (types Cau f)
      | Iff (L, R, f, g) -> conj (types Sup f) (types Sup g)
      | Iff (R, L, f, g) -> conj (types Cau g) (types Cau f)
      | Iff (R, R, f, g) -> conj (types Cau g) (types Sup g)
      | Iff (_, _, f, g) -> conj (disj (types Sup f) (types Cau g))
                              (disj (types Cau f) (types Sup g))
      | Exists (_, _, f) -> types Cau f
      | Forall (x, _, f) when is_past_guarded x false f -> types Cau f
      | Forall (x, _, f) -> error ("for causability " ^ x ^ " must be past-guarded")
      | Next (i, f) when i == Interval.full -> types Cau f
      | Next _ -> error "○ with non-[0,∞) interval is never Cau"
      | Once (i, g) | Since (_, i, _, g) when Interval.mem 0 i -> types Cau g
      | Once _ | Since _ -> error "⧫[a,b) or S[a,b) with a > 0 is never Cau"
      | Eventually (_, f) | Always (_, f) -> types Cau f
      | Until (LR, B _, f, g) -> conj (types Cau f) (types Cau g)
      | Until (_, i, f, g) when Interval.mem 0 i -> types Cau g
      | Until (_, _, f, g) -> conj (types Cau f) (types Cau g)
      | Prev _ -> error "● is never Cau"
      | _ -> Impossible (EFormula (None, f, t))
    end
  | Sup -> begin
      match f with
      | FF -> Possible CTT
      | Predicate (e, _) -> types_predicate Sup e
      | Neg f -> types Cau f
      | And (L, f, g) -> types Sup f
      | And (R, f, g) -> types Sup g
      | And (_, f, g) -> disj (types Sup f) (types Sup g)
      | Or (_, f, g) -> conj (types Sup f) (types Sup g)
      | Imp (_, f, g) -> conj (types Cau f) (types Sup g)
      | Iff (L, _, f, g) -> conj (types Cau f) (types Sup g)
      | Iff (R, _, f, g) -> conj (types Sup f) (types Cau g)
      | Iff (_, _, f, g) -> disj (conj (types Cau f) (types Sup g))
                              (conj (types Sup f) (types Cau g))
      | Exists (x, _, f) when is_past_guarded x true f -> types Sup f
      | Exists (x, _, _) -> error ("for suppressability " ^ x ^ " must be past-guarded")
      | Forall (_, _, f) -> types Sup f
      | Next (_, f) -> types Sup f
      | Historically (i, f) when Interval.mem 0 i -> types Sup f
      | Historically _ -> error "■[a,b) with a > 0 is never Sup"
      | Since (_, i, f, _) when not (Interval.mem 0 i) -> types Sup f
      | Since (_, i, f, g) -> conj (types Sup f) (types Sup g)
      | Eventually (_, f) | Always (_, f) -> types Sup f
      | Until (L, i, f, g) when not (Interval.mem 0 i) -> types Sup f
      | Until (R, i, f, g) when not (Interval.mem 0 i) -> types Sup g
      | Until (_, i, f, g) when not (Interval.mem 0 i) -> disj (types Sup f) (types Sup g)
      | Until (_, _, _, g) -> types Sup g
      | Prev _ -> error "● is never Sup"
      | _ -> Impossible (EFormula (None, f, t))
    end
  | Obs -> Possible CTT
  | CauSup -> Impossible (EFormula (None, f, t))

let rec convert b enftype form : Tformula.t option =
  let convert = convert b in
  let default_L (s: Side.t) = if Side.equal s R then Side.R else L in
  let set_b = function
    | Interval.U (UI a) -> Interval.B (BI (a, b))
    | B _ as i -> i in
  let f =
    match enftype with
      Cau -> begin
        match form with
        | TT -> Some (Tformula.TTT)
        | Predicate (e, t) when Pred.Sig.enftype_of_pred e == Cau -> Some (Tformula.TPredicate (e, t))
        | Neg f -> (convert Sup f) >>| (fun f' -> Tformula.TNeg f')
        | And (s, f, g) ->
           (convert Cau f)
           >>= (fun f' -> (convert Cau g) >>| (fun g' -> Tformula.TAnd (default_L s, f', g')))
        | Or (L, f, g) -> (convert Cau f) >>| (fun f' -> Tformula.TOr(L, f', Tformula.of_formula g))
        | Or (R, f, g) -> (convert Cau g) >>| (fun g' -> Tformula.TOr(R, Tformula.of_formula f, g'))
        | Or (_, f, g) ->
           begin
             match convert Cau f with
             | Some f' -> Some (Tformula.TOr (L, f', Tformula.of_formula g))
             | None    -> (convert Cau g) >>| (fun g' -> Tformula.TOr (R, Tformula.of_formula f, g'))
           end
        | Imp (L, f, g) -> (convert Sup f) >>| (fun f' -> Tformula.TImp(L, f', Tformula.of_formula g))
        | Imp (R, f, g) -> (convert Cau g) >>| (fun g' -> Tformula.TImp(R, Tformula.of_formula f, g'))
        | Imp (_, f, g) ->
           begin
             match convert Sup f with
             | Some f' -> Some (Tformula.TImp (L, f', Tformula.of_formula g))
             | None    -> (convert Cau g) >>| (fun g' -> Tformula.TImp (R, Tformula.of_formula f, g'))
           end
        | Iff (L, L, f, g) -> (convert Sup f) >>| (fun f' -> Tformula.TIff (L, L, f', Tformula.of_formula g))
        | Iff (L, R, f, g) -> (convert Sup f) >>= (fun f' -> (convert Sup g)
                                                             >>| (fun g' -> Tformula.TIff (L, R, f', g')))
        | Iff (R, L, f, g) -> (convert Cau g) >>= (fun g' -> (convert Cau f)
                                                             >>| (fun f' -> Tformula.TIff (R, L, f', g')))
        | Iff (R, R, f, g) -> (convert Cau g) >>| (fun g' -> Tformula.TIff (R, R, Tformula.of_formula f, g'))
        | Iff (_, _, f, g) ->
           begin
             match convert Sup f with
             | Some f' ->
                begin
                  match convert Cau f with
                  | Some f' -> Some (Tformula.TIff (L, L, f', Tformula.of_formula g))
                  | None    -> (convert Sup g) >>| (fun g' -> Tformula.TIff (L, R, f', g'))
                end
             | None -> (convert Cau g)
                       >>= (fun g' ->
                 match convert Cau f with
                 | Some f' -> Some (Tformula.TIff (R, L, f', g'))
                 | None    -> (convert Sup g) >>| (fun g' -> Tformula.TIff (R, R, Tformula.of_formula f, g')))
           end
        | Exists (x, tt, f) -> (convert Cau f) >>| (fun f' -> Tformula.TExists (x, tt, f'))
        | Forall (x, tt, f) when is_past_guarded x false f -> (convert Cau f) >>| (fun f' -> Tformula.TForall (x, tt, f'))
        | Next (i, f) when i == Interval.full ->
           (convert Cau f) >>| (fun f' -> Tformula.TNext (i, f'))
        | Once (i, f) when Interval.mem 0 i ->
           (convert Cau f) >>| (fun f' -> Tformula.TOnce (i, f'))
        | Since (_, i, f, g) when Interval.mem 0 i ->
           (convert Cau g) >>| (fun g' -> Tformula.TSince (R, i, Tformula.of_formula f, g'))
        | Eventually (i, f) -> (convert Cau f) >>| (fun f' -> Tformula.TEventually (set_b i, Interval.is_bounded i, f'))
        | Always (i, f) -> (convert Cau f) >>| (fun f' -> Tformula.TAlways (i, true, f'))
        | Until (LR, i, f, g) ->
           (convert Cau f) >>= (fun f' -> (convert Cau g) >>| (fun g' -> Tformula.TUntil (LR, set_b i, Interval.is_bounded i, f', g')))
        | Until (_, i, f, g) when Interval.mem 0 i ->
           (convert Cau g) >>| (fun g' -> Tformula.TUntil (LR, set_b i, Interval.is_bounded i, Tformula.of_formula f, g'))
        | Until (L, i, f, g) ->
           (convert Cau g) >>| (fun g' -> Tformula.TUntil (LR, set_b i, Interval.is_bounded i, Tformula.of_formula f, g'))
        | _ -> None
      end
    | Sup -> begin
        match form with
        | FF -> Some (Tformula.TFF)
        | Predicate (e, t) when Pred.Sig.enftype_of_pred e == Sup -> Some (Tformula.TPredicate (e, t))
        | Neg f -> (convert Cau f) >>| (fun f' -> Tformula.TNeg f')
        | And (L, f, g) -> (convert Sup f) >>| (fun f' -> Tformula.TAnd (L, f', Tformula.of_formula g))
        | And (R, f, g) -> (convert Sup g) >>| (fun g' -> Tformula.TAnd (R, Tformula.of_formula f, g'))
        | And (_, f, g) ->
           begin
              match convert Sup f with
             | Some f' -> Some (Tformula.TAnd (L, f', Tformula.of_formula g))
             | None    -> (convert Sup g) >>| (fun g' -> Tformula.TAnd (R, Tformula.of_formula f, g'))
           end
        | Or (s, f, g) -> (convert Sup f) >>= (fun f' -> (convert Sup g)
                                                         >>| (fun g' -> Tformula.TOr (default_L s, f', g')))
        | Imp (s, f, g) -> (convert Cau f) >>= (fun f' -> (convert Sup g)
                                                          >>| (fun g' -> Tformula.TImp (default_L s, f', g')))
        | Iff (L, _, f, g) -> (convert Cau f) >>= (fun f' -> (convert Sup g)
                                                             >>| (fun g' -> Tformula.TIff (L, N, f', g')))
        | Iff (R, _, f, g) -> (convert Sup f) >>= (fun f' -> (convert Cau g)
                                                             >>| (fun g' -> Tformula.TIff (R, N, f', g')))
        | Iff (_, _, f, g) ->
           begin
             match convert Cau f, convert Sup g with
             | Some f', Some g' -> Some (Tformula.TIff (L, R, f', g'))
             | _, _ -> match convert Sup f, convert Cau g with
                       | Some f', Some g' -> Some (Tformula.TIff(R, L, f', g'))
                       | _, _ -> None
           end
        | Exists (x, tt, f) when is_past_guarded x true f ->
           (convert Sup f) >>| (fun f' -> Tformula.TExists (x, tt, f'))
        | Forall (x, tt, f) ->  (convert Sup f) >>| (fun f' -> Tformula.TForall (x, tt, f'))
        | Next (i, f) -> (convert Sup f) >>= (fun f' -> Some (Tformula.TNext (i, f')))
        | Historically (i, f) when Interval.mem 0 i ->
           (convert Sup f) >>| (fun f' -> Tformula.THistorically (i, f'))
        | Since (_, i, f, g) when not (Interval.mem 0 i) ->
           (convert Sup f) >>| (fun f' -> Tformula.TSince (L, i, f', Tformula.of_formula g))
        | Since (_, i, f, g) -> (convert Sup f) >>= (fun f' -> (convert Sup g)
                                                               >>| (fun g' -> Tformula.TSince (LR, i, f', g')))
        | Eventually (i, f) -> (convert Sup f) >>| (fun f' -> Tformula.TEventually (i, true, f'))
        | Always (i, f) -> (convert Sup f) >>| (fun f' -> Tformula.TAlways (set_b i, Interval.is_bounded i, f'))
        | Until (L, i, f, g) when not (Interval.mem 0 i) ->
           (convert Sup f) >>| (fun f' -> Tformula.TUntil (L, i, true, f', Tformula.of_formula g))
        | Until (R, i, f, g) when not (Interval.mem 0 i) ->
           (convert Sup g) >>| (fun g' -> Tformula.TUntil (R, i, true, Tformula.of_formula f, g'))
        | Until (_, i, f, g) when not (Interval.mem 0 i) ->
           begin
             match convert Sup f with
             | Some f' -> Some (Tformula.TUntil (L, i, true, f', Tformula.of_formula g))
             | None -> (convert Sup g) >>| (fun g' -> Tformula.TUntil (R, i, true, Tformula.of_formula f, g'))
           end
        | Until (_, i, f, g) -> (convert Sup g) >>| (fun g' -> Tformula.TUntil (R, i, true, Tformula.of_formula f, g'))
        | _ -> None
      end
    | Obs -> Some (Tformula.of_formula form).f
    | CauSup -> assert false
  in
  (*Stdio.print_string (EnfType.to_string enftype ^ " " ^ Formula.to_string form ^ " -> ");*)
  match f with Some f -> Some Tformula.{ f; enftype } | None -> None

let do_type f b =
  Formula.check_types f;
  if not (Set.is_empty (Formula.fv f)) then
    ignore (raise (Invalid_argument (Printf.sprintf "formula %s is not closed" (Formula.to_string f))));
  match types Cau f with
  | Possible c ->
     begin
       match Constraints.solve c with
       | sol::_ ->
          begin
            Map.iteri sol ~f:(fun ~key ~data -> Pred.Sig.update_enftype key data);
            match convert b Cau f with
              Some f' -> Stdio.print_endline ("The formula\n "
                                              ^ Formula.to_string f
                                              ^ "\nis enforceable and types to\n "
                                              ^ Tformula.to_string f');
                         f'
            | None    -> raise (Invalid_argument (Printf.sprintf "formula %s cannot be converted" (Formula.to_string f)))
          end
       | _ -> Stdio.print_endline ("The formula\n "
                                   ^ Formula.to_string f
                                   ^ "\nis not enforceable because the constraint\n "
                                   ^ Constraints.to_string c
                                   ^ "\nhas no solution");
              raise (Invalid_argument (Printf.sprintf "formula %s is not enforceable" (Formula.to_string f)))
     end
  | Impossible e ->
     Stdio.print_endline ("The formula\n "
                          ^ Formula.to_string f
                          ^ "\nis not enforceable. To make it enforceable, you would need to\n "
                          ^ Errors.to_string e);
     raise (Invalid_argument (Printf.sprintf "formula %s is not enforceable" (Formula.to_string f)))

let rec relative_interval (f: Tformula.t) =
  match f.f with
  | TTT | TFF | TEqConst (_, _) | TPredicate (_, _) -> Zinterval.singleton 0
  | TNeg f | TExists (_, _, f) | TForall (_, _, f) -> relative_interval f
  | TAnd (_, f1, f2) | TOr (_, f1, f2) | TImp (_, f1, f2) | TIff (_, _, f1, f2)
    -> Zinterval.lub (relative_interval f1) (relative_interval f2)
  | TPrev (i, f) | TOnce (i, f) | THistorically (i, f)
    -> let i' = Zinterval.inv (Zinterval.of_interval i) in
       Zinterval.lub (Zinterval.to_zero i') (Zinterval.sum i' (relative_interval f))
  | TNext (i, f) | TEventually (i, _, f) | TAlways (i, _, f)
    -> let i = Zinterval.of_interval i in
       Zinterval.lub (Zinterval.to_zero i) (Zinterval.sum i (relative_interval f))
  | TSince (_, i, f1, f2) ->
     let i' = Zinterval.inv (Zinterval.of_interval i) in
     (Zinterval.lub (Zinterval.sum (Zinterval.to_zero i') (relative_interval f1))
        (Zinterval.sum i' (relative_interval f2)))
  | TUntil (_, i, _, f1, f2) ->
     let i' = Zinterval.of_interval i in
     (Zinterval.lub (Zinterval.sum (Zinterval.to_zero i') (relative_interval f1))
        (Zinterval.sum i' (relative_interval f2)))


let strict f =
  let rec _strict itv fut (f: Tformula.t) =
    ((Zinterval.mem 0 itv) && fut)
    || (match f.f with
        | TEqConst (_, _) | TPredicate _ -> false
        | TNeg f | TExists (_, _, f) | TForall (_, _, f) -> _strict itv fut f
        | TAnd (_, f1, f2) | TOr (_, f1, f2) | TImp (_, f1, f2) | TIff (_, _, f1, f2)
          -> (_strict itv fut f1) || (_strict itv fut f2)
        | TPrev (i, f) | TOnce (i, f) | THistorically (i, f)
          -> _strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) fut f
        | TNext (i, f) | TEventually (i, _, f) | TAlways (i, _, f)
          -> _strict (Zinterval.sum (Zinterval.of_interval i) itv) true f
        | TSince (_, i, f1, f2)
          -> (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) fut f1)
             || (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) fut f2)
        | TUntil (_, i, _, f1, f2)
          -> (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) true f1)
             || (_strict (Zinterval.sum (Zinterval.inv (Zinterval.of_interval i)) itv) true f2))
  in not (_strict (Zinterval.singleton 0) false f)

let relative_past f =
  Zinterval.is_nonpositive (relative_interval f)

let strictly_relative_past f =
  (relative_past f) && (strict f)

let is_transparent (f: Tformula.t) =
  let rec aux (f: Tformula.t) =
    match f.enftype with
    | Cau -> begin
        match f.f with
        | TTT | TPredicate (_, _) -> true
        | TNeg f | TExists (_, _, f) | TForall (_, _, f)
          | TOnce (_, f) | TNext (_, f) | THistorically (_, f)
           | TAlways (_, _, f) -> aux f
        | TEventually (_, b, f) -> b && aux f
        | TOr (L, f, g) | TImp (L, f, g) | TIff (L, L, f, g)
          -> print_endline (string_of_bool (strictly_relative_past g));
             aux f && strictly_relative_past g
        | TOr (R, f, g) | TImp (R, f, g) | TIff (R, R, f, g)
          -> aux g && strictly_relative_past f
        | TAnd (_, f, g) | TIff (_, _, f, g)
          -> aux f && aux g
        | TSince (_, _, f, g) -> aux f && strictly_relative_past g
        | TUntil (R, _, b, f, g) -> b && aux f && strictly_relative_past g
        | TUntil (LR, _, b, f, g) -> b && aux f && aux g
        | _ -> false
      end
    | Sup -> begin
        match f.f with
        | TFF | TPredicate (_, _) -> true
        | TNeg f | TExists (_, _, f) | TForall (_, _, f)
          | TOnce (_, f) | TNext (_, f) | THistorically (_, f)
          | TEventually (_, _, f) -> aux f
        | TAlways (_, b, f) -> b && aux f
        | TAnd (L, f, g) | TIff (L, L, f, g)
          -> aux f && strictly_relative_past g
        | TAnd (R, f, g) | TIff (R, R, f, g)
          -> aux g && strictly_relative_past f
        | TOr (_, f, g) | TIff (_, _, f, g)
          -> aux f && aux g
        | TSince (L, _, f, g) -> aux f && strictly_relative_past g
        | TSince (R, _, f, g) -> aux f && aux g
        | TUntil (R, _, _, f, g) -> aux f && strictly_relative_past g
        | TUntil (_, _, _, f, g) -> aux g && strictly_relative_past f
        | _ -> false
      end
  in
  if aux f then
    true
  else
    raise (Invalid_argument (Printf.sprintf "Warning: this formula cannot be transparently enforced"))
