open Base
open Formula
open Pred

let rec is_past_guarded x p = function
  | TT | FF -> false
  | EqConst (y, _) -> p && (x == y)
  | Predicate (_, ts) -> List.exists ~f:(Term.equal (Term.Var x)) ts
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

module Errors = struct

  type error =
    | ECast of string * EnfType.t * EnfType.t
    | EFormula of string option * t * EnfType.t
    | EConj of error * error
    | EDisj of error * error

  let rec to_string ?(n=0) e =
    let sp = Etc.spaces (4*n) in
    let lb = "\n" ^ sp in
    (match e with
     | ECast (e, t', t) -> e
                           ^ " has type "
                           ^ EnfType.to_string t'
                           ^ " ⊀ "
                           ^ EnfType.to_string t
     | EFormula (None, f, t) ->  Formula.to_string f
                                 ^ " cannot be "
                                 ^ EnfType.to_string t
     | EFormula (Some s, f, t) ->  Formula.to_string f
                                   ^ " cannot be "
                                   ^ EnfType.to_string t
                                   ^ " (" ^ s ^ ")"
     | EConj (f, g) -> "either" ^ lb ^ "|" ^ lb ^ "--> "
                       ^ to_string ~n:(n+1) f
                       ^ lb ^ "|" ^ lb ^ "or" ^ lb ^ "|" ^ lb ^ "--> "
                       ^ to_string ~n:(n+1) g
     | EDisj (f, g) -> "both" ^ lb ^ "|" ^ lb ^ "--> "
                       ^ to_string ~n:(n+1) f
                       ^ lb ^ "|" ^ lb ^ "and" ^ lb ^ "|" ^ lb ^ "--> "
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
  let t' = Pred.Sig.enftype e in
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
      | Next (i, f) when i == Interval.full -> types Cau f
      | Next (i, f) -> error "○ with non-[0,∞) interval is never Cau"
      | Once (i, g) | Since (_, i, _, g) when Interval.mem 0 i -> types Cau g
      | Once (i, g) | Since (_, i, _, g) ->
         error "⧫[a,b) or S[a,b) with a > 0 is never Cau"
      | Eventually (B _, f) | Always (_, f) -> types Cau f
      | Eventually (_, _) -> error "◊ with unbounded interval is never Cau"
      | Until (_, B _, f, g) -> conj (types Cau f) (types Cau g)
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
      | Exists (x, _, f) ->  error ("for suppressability " ^ x ^ " must be past-guarded")
      | Next (_, f) -> types Sup f
      | Historically (i, f) when Interval.mem 0 i -> types Sup f
      | Historically (i, f) -> error "■[a,b) with a > 0 is never Sup"
      | Since (_, i, f, _) when not (Interval.mem 0 i) -> types Sup f
      | Since (_, i, f, g) -> conj (types Sup f) (types Sup g)
      | Eventually (_, f) | Always (B _, f) -> types Sup f
      | Always (_, _) -> error "□ with unbounded interval is never Sup"
      | Until (L, i, f, g) when not (Interval.mem 0 i) -> types Sup f
      | Until (R, i, f, g) when not (Interval.mem 0 i) -> types Sup g
      | Until (_, i, f, g) when not (Interval.mem 0 i) -> disj (types Sup f) (types Sup g)
      | Until (_, _, _, g) -> types Sup g
      | Prev _ -> error "● is never Sup"
      | _ -> Impossible (EFormula (None, f, t))
    end
  | Obs -> Possible CTT
  | CauSup -> Impossible (EFormula (None, f, t))

let rec convert enftype form : Tformula.t option =
  (*Stdio.print_endline (Formula.to_string form);*)
  let default_L (s: Side.t) = if Side.equal s R then Side.R else L in
  let f =
    match enftype with
      Cau -> begin
        match form with
        | TT -> Some (Tformula.TTT)
        | Predicate (e, t) when Pred.Sig.enftype e == Cau -> Some (Tformula.TPredicate (e, t))
        | Neg f -> (convert Sup f) >>= (fun f' -> Some (Tformula.TNeg f'))
        | And (s, f, g) ->
           (convert Cau f)
           >>= (fun f' -> (convert Cau g)
                          >>= (fun g' -> Some (Tformula.TAnd (default_L s, f', g'))))
        | Or (L, f, g) -> (convert Cau f) >>= (fun f' -> Some (Tformula.TOr(L, f', Tformula.of_formula g)))
        | Or (R, f, g) -> (convert Cau g) >>= (fun g' -> Some (Tformula.TOr(R, Tformula.of_formula f, g')))
        | Or (_, f, g) ->
           begin
             match convert Cau f with
             | Some f' -> Some (Tformula.TOr (L, f', Tformula.of_formula g))
             | None    -> (convert Cau g)
                          >>= (fun g' -> Some (Tformula.TOr (R, Tformula.of_formula f, g')))
           end
        | Imp (L, f, g) -> (convert Sup f) >>= (fun f' -> Some (Tformula.TImp(L, f', Tformula.of_formula g)))
        | Imp (R, f, g) -> (convert Cau g) >>= (fun g' -> Some (Tformula.TImp(R, Tformula.of_formula f, g')))
        | Imp (_, f, g) ->
           begin
             match convert Sup f with
             | Some f' -> Some (Tformula.TImp (L, f', Tformula.of_formula g))
             | None    -> (convert Cau g)
                          >>= (fun g' -> Some (Tformula.TImp (R, Tformula.of_formula f, g')))
           end
        | Iff (L, L, f, g) -> (convert Sup f) >>= (fun f' -> Some (Tformula.TIff (L, L, f', Tformula.of_formula g)))
        | Iff (L, R, f, g) -> (convert Sup f) >>= (fun f' -> (convert Sup g)
                                                             >>= (fun g' -> Some (Tformula.TIff (L, R, f', g'))))
        | Iff (R, L, f, g) -> (convert Cau g) >>= (fun g' -> (convert Cau f)
                                                             >>= (fun f' -> Some (Tformula.TIff (R, L, f', g'))))
        | Iff (R, R, f, g) -> (convert Cau g) >>= (fun g' -> Some (Tformula.TIff (R, R, Tformula.of_formula f, g')))
        | Iff (_, _, f, g) ->
           begin
             match convert Sup f with
             | Some f' ->
                begin
                  match convert Cau f with
                  | Some f' -> Some (Tformula.TIff (L, L, f', Tformula.of_formula g))
                  | None    -> (convert Sup g)
                               >>= (fun g' -> Some (Tformula.TIff (L, R, f', g')))
                end
             | None -> (convert Cau g)
                       >>= (fun g' ->
                 match convert Cau f with
                 | Some f' -> Some (Tformula.TIff (R, L, f', g'))
                 | None    -> (convert Sup g)
                              >>= (fun g' -> Some (Tformula.TIff (R, R, Tformula.of_formula f, g'))))
           end
        | Exists (x, _, f) -> (convert Cau f) >>= (fun f' -> Some (Tformula.TExists (x, f')))
        | Next (i, f) when i == Interval.full ->
           (convert Cau f) >>= (fun f' -> Some (Tformula.TNext (i, f')))
        | Once (i, f) when Interval.mem 0 i ->
           (convert Cau f) >>= (fun f' -> Some (Tformula.TOnce (i, f')))
        | Since (_, i, f, g) when Interval.mem 0 i ->
           (convert Cau g) >>= (fun g' -> Some (Tformula.TSince (R, i, Tformula.of_formula f, g')))
        | Eventually (B b, f) -> (convert Cau f) >>= (fun f' -> Some (Tformula.TEventually (B b, f')))
        | Always (i, f) -> (convert Cau f) >>= (fun f' -> Some (Tformula.TAlways (i, f')))
        | Until (_, B b, f, g) ->
           (convert Cau f) >>= (fun f' -> (convert Cau g)
                                          >>= (fun g' -> Some (Tformula.TUntil (LR, B b, f', g'))))
        | _ -> None
      end
    | Sup -> begin
        match form with
        | FF -> Some (Tformula.TFF)
        | Predicate (e, t) when Pred.Sig.enftype e == Sup -> Some (Tformula.TPredicate (e, t))
        | Neg f -> (convert Cau f) >>= (fun f' -> Some (Tformula.TNeg f'))
        | And (L, f, g) -> (convert Sup f) >>= (fun f' -> Some (Tformula.TAnd (L, f', Tformula.of_formula g)))
        | And (R, f, g) -> (convert Sup g) >>= (fun g' -> Some (Tformula.TAnd (L, Tformula.of_formula f, g')))
        | And (_, f, g) ->
           begin
             match convert Sup f with
             | Some f' -> Some (Tformula.TAnd (L, f', Tformula.of_formula g))
             | None    -> (convert Sup g)
                          >>= (fun g' -> Some (Tformula.TAnd (R, Tformula.of_formula f, g')))
           end
        | Or (s, f, g) -> (convert Sup f) >>= (fun f' -> (convert Sup g)
                                                         >>= (fun g' -> Some (Tformula.TOr (default_L s, f', g'))))
        | Imp (s, f, g) -> (convert Cau f) >>= (fun f' -> (convert Sup g)
                                                          >>= (fun g' -> Some (Tformula.TImp (default_L s, f', g'))))
        | Iff (L, _, f, g) -> (convert Cau f) >>= (fun f' -> (convert Sup g)
                                                             >>= (fun g' -> Some (Tformula.TIff (L, N, f', g'))))
        | Iff (R, _, f, g) -> (convert Sup f) >>= (fun f' -> (convert Cau g)
                                                             >>= (fun g' -> Some (Tformula.TIff (R, N, f', g'))))
        | Iff (_, _, f, g) ->
           begin
             match convert Cau f, convert Sup g with
             | Some f', Some g' -> Some (Tformula.TIff (L, R, f', g'))
             | _, _ -> match convert Sup f, convert Cau g with
                       | Some f', Some g' -> Some (Tformula.TIff(R, L, f', g'))
                       | _, _ -> None
           end
        | Exists (x, _, f) when is_past_guarded x true f ->
           (convert Sup f) >>= (fun f' -> Some (Tformula.TExists (x, Tformula.of_formula f)))
        | Next (i, f) -> (convert Sup f) >>= (fun f' -> Some (Tformula.TNext (i, f')))
        | Historically (i, f) when Interval.mem 0 i ->
           (convert Sup f) >>= (fun f' -> Some (Tformula.THistorically (i, f')))
        | Since (_, i, f, g) when not (Interval.mem 0 i) ->
           (convert Sup f) >>= (fun f' -> Some (Tformula.TSince (L, i, f', Tformula.of_formula g)))
        | Since (_, i, f, g) -> (convert Sup f) >>= (fun f' -> (convert Sup g)
                                                               >>= (fun g' -> Some (Tformula.TSince (LR, i, f', g'))))
        | Eventually (i, f) -> (convert Cau f) >>= (fun f' -> Some (Tformula.TEventually (i, f')))
        | Always (B b, f) -> (convert Cau f) >>= (fun f' -> Some (Tformula.TAlways (B b, f')))
        | Until (L, i, f, g) when not (Interval.mem 0 i) ->
           (convert Sup f) >>= (fun f' -> Some (Tformula.TUntil (L, i, f', Tformula.of_formula g)))
        | Until (R, i, f, g) when not (Interval.mem 0 i) ->
           (convert Sup g) >>= (fun g' -> Some (Tformula.TUntil (R, i, Tformula.of_formula f, g')))
        | Until (_, i, f, g) when not (Interval.mem 0 i) ->
           begin
             match convert Sup f with
             | Some f' -> Some (Tformula.TUntil (L, i, f', Tformula.of_formula g))
             | None -> (convert Sup g)
                       >>= (fun g' -> Some (Tformula.TUntil (R, i, Tformula.of_formula f, g')))
           end
        | Until (_, i, f, g) -> (convert Sup g)
                                >>= (fun g' -> Some (Tformula.TUntil (R, i, Tformula.of_formula f, g')))
        | _ -> None
      end
    | Obs -> Some (Tformula.of_formula form).f
    | CauSup -> assert false
  in match f with Some f -> Some Tformula.{ f; enftype } | None -> None

let do_type f =
  match types Cau f with
  | Possible c ->
     begin
       match Constraints.solve c with
       | sol::_ ->
          begin
            Map.iteri sol ~f:(fun ~key ~data -> Pred.Sig.update_enftype key data);
            match convert Cau f with
              Some f' -> Stdio.print_endline ("The formula\n "
                                              ^ Formula.to_string f
                                              ^ "\nis enforceable and types to\n "
                                              ^ Tformula.to_string f');
                         f'
            | None    -> failwith "formula cannot be converted"
          end
       | _ -> Stdio.print_endline ("The formula\n "
                                   ^ Formula.to_string f
                                   ^ "\nis not enforceable because the constraint\n "
                                   ^ Constraints.to_string c
                                   ^ "\nhas no solution");
              failwith "formula is not enforceable"
     end
  | Impossible e ->
     Stdio.print_endline ("The formula\n "
                          ^ Formula.to_string f
                          ^ "\nis not enforceable because\n "
                          ^ Errors.to_string e);
     failwith "formula is not enforceable"
