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
    | CGeq of string * EnfType.t
    | CNLeqNCau of string * EnfType.t
    | CConj of constr list
    | CDisj of constr list [@@deriving equal, compare, sexp_of]

  type verdict = Possible of constr | Impossible of Errors.error

  let tt = CTT
  let ff = CFF
  let geq s t = CGeq (s, t)
  let nleqncau s t = CNLeqNCau (s, t)

  let rec ac_simplify = function
    | CConj cs ->
       let cs = List.map ~f:ac_simplify cs in
       let f_has_ff = function CFF -> true | _ -> false in
       (if List.exists cs ~f:f_has_ff then
          CFF
        else
          let f_conjs = function CConj cs' -> Some cs' | _ -> None in
          let f_not_conjs = function CConj cs' -> false | CTT -> false | _ -> true in
          let cs_conjs = List.concat (List.filter_map cs ~f:f_conjs) in
          let cs_not_conjs = List.filter cs ~f:f_not_conjs in
          let cs' = Etc.dedup ~equal:equal_constr (cs_conjs @ cs_not_conjs) in
          CConj cs')
    | CDisj cs ->
       let cs = List.map ~f:ac_simplify cs in
       let f_has_tt = function CTT -> true | _ -> false in
       (if List.exists cs ~f:f_has_tt then
          CTT
        else
          let f_disjs = function CDisj cs' -> Some cs' | _ -> None in
          let f_not_disjs = function CDisj cs' -> false | CFF -> false | _ -> true in
          let cs_disjs = List.concat (List.filter_map cs ~f:f_disjs) in
          let cs_not_disjs = List.filter cs ~f:f_not_disjs in
          let cs' = Etc.dedup ~equal:equal_constr (cs_disjs @ cs_not_disjs) in
          CDisj cs')
    | c -> c

  let conj c d = match c, d with
    | Possible CTT, _ -> d
    | _, Possible CTT -> c
    | Impossible c, Impossible d -> Impossible (EConj (c, d))
    | Impossible c, _ | _, Impossible c -> Impossible c
    | Possible c, Possible d -> Possible (ac_simplify (CConj [c; d]))

  let disj c d = match c, d with
    | Impossible c, Impossible d -> Impossible (EDisj (c, d))
    | Impossible c, _ -> d
    | _, Impossible d -> c
    | Possible CTT, _ | _, Possible CTT -> Possible CTT
    | Possible c, Possible d -> Possible (ac_simplify (CDisj [c; d]))

  let rec conjs = function
    | [] -> Possible CTT
    | c::cs -> List.fold_left ~init:c ~f:conj cs
      
  let rec disjs = function
    | [] -> Possible CFF
    | c::cs -> List.fold_left ~init:c ~f:disj cs

  let rec cartesian a = function
      [] -> []
    | h::t -> (List.map a ~f:(fun x -> (x, h))) @ cartesian a t

  exception CannotMerge

  let merge_aux ~key = function
    | `Left t | `Right t -> Some t
    | `Both ((t, t'), (u, u')) ->
       let v  = EnfType.join t u in
       let v' = Option.merge ~f:EnfType.meet t' u' in
       match v' with
       | Some v' when EnfType.leq v' v ->
          (*print_endline (Printf.sprintf "merge_aux key=%s t=%s t'=%s u=%s, u'=%s"
                           key
                           (EnfType.to_string t)
                           (Option.fold t' ~init:"None" ~f:(fun _ v -> EnfType.to_string v))
                           (EnfType.to_string u)
                           (Option.fold u' ~init:"None" ~f:(fun _ v -> EnfType.to_string v)));*)
          raise CannotMerge
       | _ ->  Some (v, v')

  let try_merge (a, b) =
    try Some (Map.merge a b ~f:merge_aux)
    with CannotMerge -> None

  let rec solve = function
    | CTT -> [Map.empty (module String)]
    | CFF -> []
    | CGeq (s, t) -> [Map.singleton (module String) s (t, Some EnfType.Obs)]
    | CNLeqNCau (s, t) -> [Map.singleton (module String) s (EnfType.join EnfType.SCau t, None);
                           Map.singleton (module String) s (EnfType.join EnfType.Sup t,  None)]
    | CConj [] -> [Map.empty (module String)]
    | CConj (c::cs) ->
       let f sol d = List.filter_map (cartesian sol (solve d)) ~f:try_merge in
       List.fold_left cs ~init:(solve c) ~f
    | CDisj cs -> List.concat_map cs ~f:solve

  let rec to_string_rec l = function
    | CTT -> Printf.sprintf "⊤"
    | CFF -> Printf.sprintf "⊥"
    | CGeq (s, t) -> Printf.sprintf "t(%s) ⋡ Obs ∧ t(%s) ≽ %s" s s (EnfType.to_string t)
    | CNLeqNCau (s, t) -> Printf.sprintf "NCau ⋡ t(%s)" s 
    | CConj cs -> Printf.sprintf (Etc.paren l 4 "%s")
                    (String.concat ~sep:" ∧ " (List.map ~f:(to_string_rec 4) cs))
    | CDisj cs -> Printf.sprintf (Etc.paren l 3 "%s")
                    (String.concat ~sep:" ∨ " (List.map ~f:(to_string_rec 3) cs))

  let to_string = to_string_rec 0

  let verdict_to_string = function
    | Possible c -> Printf.sprintf "Possible(%s)" (to_string c)
    | Impossible e -> Printf.sprintf "Impossible(%s)" (Errors.to_string e)

end

open EnfType
open Constraints
open Option

(* todo: ensure that there is no shadowing *)

let types_predicate t e =
  let t' = Pred.Sig.enftype_of_pred e in
  if EnfType.geq t t' then
    Possible (geq e t)
  else
    Impossible (ECast (e, t', t))

type pg_map = (string, (string, String.comparator_witness) Set.t list, String.comparator_witness) Map.t

let rec types (t: EnfType.t) (pgs: pg_map) (f: Formula.t) =
  let error s = Impossible (EFormula (Some s, f, t)) in
  match t with
    Cau -> begin
      match f with
      | TT -> Possible CTT
      | Predicate (e, ts) ->
         let fvs = Etc.dedup ~equal:String.equal (Term.fv_list ts) in
         let es  = List.map fvs ~f:(fun x -> Option.value (Map.find pgs x) ~default:[]) in
         (match List.map ~f:(Set.union_list (module String)) (Etc.cartesian es) with
          | [] -> Impossible (EFormula (None, f, t))            
          | es_ncau_list ->
             (*print_endline (Printf.sprintf "types.es_ncau_list=[%s]"
               (String.concat ~sep:"; " (List.map es_ncau_list ~f:(fun s -> Printf.sprintf "[%s]" ((String.concat ~sep:", " (Set.elements s)))))));*)
             let c =
               (if Sig.is_strict ts then
                  disjs (List.map es_ncau_list ~f:(fun es_ncau ->
                             conj (types_predicate Cau e)
                               (conjs (List.map (Set.elements es_ncau)
                                         ~f:(fun e ->
                                           Possible (nleqncau e (Pred.Sig.enftype_of_pred e)))))))
                else
                  disjs (List.map es_ncau_list ~f:(fun es_ncau ->
                             conj (types_predicate NCau e)
                               (conjs (List.map (Set.elements es_ncau)
                                         ~f:(fun e ->
                                           Possible (nleqncau e (Pred.Sig.enftype_of_pred e))))))))
             in c)
      | Neg f -> types Sup pgs f
      | And (_, f, g) -> conj (types Cau pgs f) (types Cau pgs g)
      | Or (L, f, g) -> types Cau pgs f
      | Or (R, f, g) -> types Cau pgs g
      | Or (_, f, g) -> disj (types Cau pgs f) (types Cau pgs g)
      | Imp (L, f, g) -> types Sup pgs f
      | Imp (R, f, g) -> types Cau pgs g
      | Imp (_, f, g) -> disj (types Sup pgs f) (types Cau pgs g)
      | Iff (L, L, f, g) -> conj (types Sup pgs f) (types Cau pgs f)
      | Iff (L, R, f, g) -> conj (types Sup pgs f) (types Sup pgs g)
      | Iff (R, L, f, g) -> conj (types Cau pgs g) (types Cau pgs f)
      | Iff (R, R, f, g) -> conj (types Cau pgs g) (types Sup pgs g)
      | Iff (_, _, f, g) -> conj (disj (types Sup pgs f) (types Cau pgs g))
                              (disj (types Cau pgs f) (types Sup pgs g))
      | Exists (_, f) -> types Cau pgs f
      | Forall (x, f) ->
         let es = Formula.solve_past_guarded x false f in
         (match es with
          | [] -> error ("for causability " ^ x ^ " must be past-guarded")
          | _  -> types Cau (Map.update pgs x (fun _ -> es)) f)
      | Next (i, f) when Interval.has_zero i && not (Interval.is_zero i) -> types Cau pgs f
      | Next _ -> error "○ with non-[0,a) interval, a > 0, is never Cau"
      | Once (i, g) | Since (_, i, _, g) when Interval.has_zero i -> types Cau pgs g
      | Once _ | Since _ -> error "⧫[a,b) or S[a,b) with a > 0 is never Cau"
      | Eventually (_, f) | Always (_, f) -> types Cau pgs f
      | Until (LR, B _, f, g) -> conj (types Cau pgs f) (types Cau pgs g)
      | Until (_, i, f, g) when Interval.has_zero i -> types Cau pgs g
      | Until (_, _, f, g) -> conj (types Cau pgs f) (types Cau pgs g)
      | Prev _ -> error "● is never Cau"
      | _ -> Impossible (EFormula (None, f, t))
    end
  | Sup -> begin
      match f with
      | FF -> Possible CTT
      | Predicate (e, _) -> types_predicate Sup e
      | Neg f -> types Cau pgs f
      | And (L, f, g) -> types Sup pgs f
      | And (R, f, g) -> types Sup pgs g
      | And (_, f, g) -> disj (types Sup pgs f) (types Sup pgs g)
      | Or (_, f, g) -> conj (types Sup pgs f) (types Sup pgs g)
      | Imp (_, f, g) -> conj (types Cau pgs f) (types Sup pgs g)
      | Iff (L, _, f, g) -> conj (types Cau pgs f) (types Sup pgs g)
      | Iff (R, _, f, g) -> conj (types Sup pgs f) (types Cau pgs g)
      | Iff (_, _, f, g) -> disj (conj (types Cau pgs f) (types Sup pgs g))
                              (conj (types Sup pgs f) (types Cau pgs g))
      | Exists (x, f) ->
         let es = Formula.solve_past_guarded x true f in
         (match es with
          | [] -> error ("for suppressability " ^ x ^ " must be past-guarded")
          | _  -> types Sup (Map.update pgs x (fun _ -> es)) f)
      | Forall (_, f) -> types Sup pgs f
      | Next (_, f) -> types Sup pgs f
      | Historically (i, f) when Interval.has_zero i -> types Sup pgs f
      | Historically _ -> error "■[a,b) with a > 0 is never Sup"
      | Since (_, i, f, _) when not (Interval.has_zero i) -> types Sup pgs f
      | Since (_, i, f, g) -> conj (types Sup pgs f) (types Sup pgs g)
      | Eventually (_, f) | Always (_, f) -> types Sup pgs f
      | Until (L, i, f, g) when not (Interval.has_zero i) -> types Sup pgs f
      | Until (R, _, _, g) -> types Sup pgs g
      | Until (_, i, f, g) when not (Interval.has_zero i) -> types Sup pgs f
      | Until (_, _, _, g) -> types Sup pgs g
      | Prev _ -> error "● is never Sup"
      | _ -> Impossible (EFormula (None, f, t))
    end
  | Obs -> Possible CTT
  | CauSup -> Impossible (EFormula (None, f, t))



let rec convert b enftype form (types: Ctxt.t) : Ctxt.t * Tformula.t option =
  let convert = convert b in
  let default_L (s: Side.t) = if Side.equal s R then Side.R else L in
  let opt_filter = function
    | Some x -> Tformula.(x.filter)
    | None   -> Filter._true in
  let conj_filter ?(b=true) ?(neg=false) f g =
    (Filter.conj (Filter.present_filter ~b f) (Filter.present_filter ~b:(if neg then not b else b) g)) in
  let set_b = function
    | Interval.U a -> Interval.B (a, b)
    | B _ as i -> i in
  let apply1 ?(temporal=false) f comb types  =
    let types, x = f types in
    types, Option.map x ~f:comb, if temporal then Filter._true else opt_filter x in
  let apply1' ?(new_filter=None) f comb types =
    let types, (x: Tformula.t) = f types in
    types, Some (comb x), Option.fold new_filter ~init:x.filter ~f:Filter.conj  in
  let apply2 ?(temporal=false) f g comb types =
    let types, x = f types in
    let types, y = g types in
    types, Option.map2 x y ~f:comb, if temporal then Filter._true else Filter.disj (opt_filter x) (opt_filter y) in
  let apply2' ?(temporal=false) f g comb types new_filter =
    let types, x = f types in
    let types, (y: Tformula.t) = g types in
    types, Option.map x ~f:(fun x -> comb x y), if temporal then Filter._true else Filter.conj (opt_filter x) new_filter in
  let types, f, filter =
    (*print_endline "-- convert";
    print_endline (Formula.to_string form);
    print_endline (EnfType.to_string enftype);*)
    match enftype with
    | Cau | NCau | SCau -> begin
        match form with
        | TT -> types, Some (Tformula.TTT), Filter._true
        | Predicate (e, trms) when EnfType.is_causable (Pred.Sig.enftype_of_pred e) ->
           let types, _ = Sig.check_terms types e trms in
           types, Some (Tformula.TPredicate (e, trms)), Filter._true
        | Neg f -> apply1 (convert Sup f) (fun mf -> Tformula.TNeg mf) types 
        | And (s, f, g) -> apply2 (convert Cau f) (convert Cau g)
                             (fun mf mg -> Tformula.TAnd (default_L s, [mf; mg])) types
        | Or (L, f, g) -> apply2' (convert Cau f) (Tformula.of_formula g)
                            (fun mf mg -> Tformula.TOr (L, [mf; mg])) types
                            (conj_filter ~b:false f g)
        | Or (R, f, g) -> apply2' (convert Cau g) (Tformula.of_formula f)
                            (fun mg mf -> Tformula.TOr (R, [mf; mg])) types
                            (conj_filter ~b:false f g)
        | Or (_, f, g) ->
           begin
             match convert Cau f types with
             | types, Some mf -> apply1'
                                   ~new_filter:(Some (conj_filter ~b:false f g))
                                   (Tformula.of_formula g)
                                   (fun mg -> Tformula.TOr (L, [mf; mg])) types
             | types, None    -> apply2' (convert Cau g) (Tformula.of_formula f)
                                   (fun mg mf -> Tformula.TOr (R, [mf; mg])) types
                                   (conj_filter ~b:false f g)
           end
        | Imp (L, f, g) -> apply2' (convert Sup f) (Tformula.of_formula g)
                             (fun mf mg -> Tformula.TImp (L, mf, mg)) types
                             (conj_filter ~neg:true f g)
        | Imp (R, f, g) -> apply2' (convert Cau g) (Tformula.of_formula f)
                             (fun mg mf -> Tformula.TImp (R, mf, mg)) types
                             (conj_filter ~neg:true f g)
        | Imp (_, f, g) ->
           begin
             match convert Sup f types with
             | types, Some mf -> apply1'
                                   ~new_filter:(Some (conj_filter ~neg:true f g))
                                   (Tformula.of_formula g)
                                   (fun mg -> Tformula.TImp (L, mf, mg)) types
             | types, None    -> apply2' (convert Cau g) (Tformula.of_formula f)
                                   (fun mg mf -> Tformula.TImp (R, mf, mg)) types
                                   (conj_filter ~neg:true f g)
           end
        | Iff (L, L, f, g) -> apply2' (convert Sup f) (Tformula.of_formula g)
                                (fun mf mg -> Tformula.TIff (L, L, mf, mg)) types
                                Filter._true
        | Iff (L, R, f, g) -> apply2 (convert Sup f) (convert Sup g)
                                (fun mf mg -> Tformula.TIff (L, R, mf, mg)) types
        | Iff (R, L, f, g) -> apply2 (convert Cau g) (convert Cau f)
                                (fun mg mf -> Tformula.TIff (R, L, mf, mg)) types
        | Iff (R, R, f, g) -> apply2' (convert Cau g) (Tformula.of_formula f)
                                (fun mg mf -> Tformula.TIff (R, R, mf, mg)) types
                                Filter._true
        | Iff (_, _, f, g) ->
           begin
             match convert Sup f types with
             | types, Some mf ->
                begin
                  match convert Cau f types with
                  | types, Some mf -> apply1' (Tformula.of_formula g)
                                        (fun mg -> Tformula.TIff (L, L, mf, mg)) types
                  | types, None    -> apply1 (convert Sup g)
                                        (fun mg -> Tformula.TIff (L, R, mf, mg)) types
                end
             | types, None ->
                begin
                  match convert Cau g types with
                  | types, Some mg ->
                     begin
                       match convert Cau f types with
                       | types, Some mf -> types, Some (Tformula.TIff (R, L, mf, mg)),
                                           Filter.disj mf.filter mg.filter
                       | types, None    -> apply2' (convert Sup g) (Tformula.of_formula f)
                                             (fun mg mf -> Tformula.TIff (R, R, mf, mg)) types
                                             Filter._true
                     end
                  | types, None    -> types, None, Filter._true
                end
           end
        | Exists (x, f) ->
           begin
             match convert Cau f types with
             | types, Some mf -> types, Some (Tformula.TExists (x, Ctxt.get_tt_exn x types, true, mf)), mf.filter
             | types, None    -> types, None, Filter._true
           end
        | Forall (x, f) when is_past_guarded x false f ->
           begin
             match convert Cau f types with
             | types, Some mf -> types, Some (Tformula.TForall (x, Ctxt.get_tt_exn x types, false, mf)), mf.filter
             | types, None    -> types, None, Filter._true
           end
        | Next (i, f) when Interval.has_zero i && not (Interval.is_zero i) -> 
           apply1 ~temporal:true (convert Cau f) (fun mf -> Tformula.TNext (i, mf)) types
        | Once (i, f) when Interval.has_zero i ->
           apply1 (convert Cau f) (fun mf -> Tformula.TOnce (i, mf)) types
        | Since (_, i, f, g) when Interval.has_zero i ->
           apply2' (convert Cau g) (Tformula.of_formula f)
             (fun mg mf -> Tformula.TSince (R, i, mf, mg)) types
             Filter._true
        | Eventually (i, f) ->
           apply1 ~temporal:true (convert Cau f)
             (fun mf -> Tformula.TEventually (set_b i, Interval.is_bounded i, mf)) types
        | Always (i, f) ->
           apply1 ~temporal:true (convert Cau f) (fun mf -> Tformula.TAlways (i, true, mf)) types
        | Until (LR, i, f, g) ->
           apply2 ~temporal:true (convert Cau f) (convert Cau g)
             (fun mf mg -> Tformula.TUntil (LR, set_b i, Interval.is_bounded i, mf, mg)) types
        | Until (_, i, f, g) when Interval.has_zero i ->
           apply2' ~temporal:true (convert Cau g) (Tformula.of_formula f)
             (fun mg mf -> Tformula.TUntil (R, set_b i, Interval.is_bounded i, mf, mg)) types
             Filter._true
        | Until (_, i, f, g) ->
           apply2 ~temporal:true (convert Cau f) (convert Cau g)
             (fun mf mg -> Tformula.TUntil (LR, set_b i, Interval.is_bounded i, mf, mg)) types
        | _ -> types, None, Filter._true
      end
    | Sup -> begin
        match form with
        | FF -> types, Some (Tformula.TFF), Filter._true
        | Predicate (e, trms) when EnfType.is_suppressable (Pred.Sig.enftype_of_pred e) ->
           let types, _ = Sig.check_terms types e trms in
           types, Some (Tformula.TPredicate (e, trms)), Filter.An e
        | Neg f -> apply1 (convert Cau f) (fun mf -> Tformula.TNeg mf) types
        | And (L, f, g) -> apply2' (convert Sup f) (Tformula.of_formula g)
                             (fun mf mg -> Tformula.TAnd (L, [mf; mg])) types
                             (conj_filter f g)
        | And (R, f, g) -> apply2' (convert Sup g) (Tformula.of_formula f)
                             (fun mg mf -> Tformula.TAnd (R, [mf; mg])) types
                             (conj_filter f g)
        | And (_, f, g) ->
           begin
              match convert Sup f types with
              | types, Some mf -> apply1' ~new_filter:(Some (conj_filter f g))
                                    (Tformula.of_formula g)
                                    (fun mg -> Tformula.TAnd (L, [mf; mg])) types
              | types, None    -> apply2' (convert Sup g) (Tformula.of_formula f)
                                    (fun mg mf -> Tformula.TAnd (R, [mf; mg])) types
                                    (conj_filter f g)
           end
        | Or (s, f, g) -> apply2 (convert Sup f) (convert Sup g)
                            (fun mf mg -> Tformula.TOr (default_L s, [mf; mg])) types
        | Imp (s, f, g) -> apply2 (convert Cau f) (convert Sup g)
                             (fun mf mg -> Tformula.TImp (default_L s, mf, mg)) types
        | Iff (L, _, f, g) -> apply2 (convert Cau f) (convert Sup g)
                                (fun mf mg -> Tformula.TIff (L, N, mf, mg)) types
        | Iff (R, _, f, g) -> apply2 (convert Sup f) (convert Cau g)
                                (fun mf mg -> Tformula.TIff (R, N, mf, mg)) types
        | Iff (_, _, f, g) ->
           begin
             match convert Cau f types with
             | types, Some mf ->
                begin
                  match convert Sup g types with
                  | types, Some mg -> types, Some (Tformula.TIff (L, R, mf, mg)),
                                      Filter.disj mf.filter mg.filter
                  | types, None    -> types, None, Filter._true
                end
             | types, None    -> types, None, Filter._true
           end
        | Exists (x, f) when is_past_guarded x true f ->
           begin
             match convert Sup f types with
             | types, Some mf -> types, Some (Tformula.TExists (x, Ctxt.get_tt_exn x types, true, mf)), mf.filter
             | types, None    -> types, None, Filter._true
           end
        | Forall (x, f) ->
           begin
             match convert Sup f types with
             | types, Some mf -> types, Some (Tformula.TForall (x, Ctxt.get_tt_exn x types, false, mf)), mf.filter
             | types, None    -> types, None, Filter._true
           end
        | Next (i, f) -> apply1 ~temporal:true (convert Sup f) (fun mf -> Tformula.TNext (i, mf)) types
        | Historically (i, f) when Interval.has_zero i ->
           apply1 (convert Sup f) (fun mf -> Tformula.THistorically (i, mf)) types
        | Since (_, i, f, g) when not (Interval.has_zero i) ->
           apply2' (convert Sup f) (Tformula.of_formula g)
             (fun mf mg -> Tformula.TSince (L, i, mf, mg)) types
             Filter._true
        | Since (_, i, f, g) ->
           let types, since_f = Tformula.of_formula (Since (N, i, f, g)) types in
           apply2 (convert Sup f) (convert Sup g)
             (fun mf mg ->
               let f = Tformula.TAnd (L, [mf; since_f]) in
               Tformula.TOr (L, [mg; {f; enftype = Sup; filter = Filter._true}])) types
        | Eventually (i, f) ->
           apply1 ~temporal:true (convert Sup f)
             (fun mf -> Tformula.TEventually (i, true, mf)) types
        | Always (i, f) ->
           apply1 ~temporal:true (convert Sup f)
             (fun mf -> Tformula.TAlways (set_b i, Interval.is_bounded i, mf)) types
        | Until (L, i, f, g) when not (Interval.has_zero i) ->
           apply2' ~temporal:true (convert Sup f) (Tformula.of_formula g)
             (fun mf mg -> Tformula.TUntil (L, i, true, mf, mg)) types
             Filter._true
        | Until (R, i, f, g) ->
           apply2' ~temporal:true (convert Sup g) (Tformula.of_formula f)
             (fun mg mf -> Tformula.TUntil (R, i, true, mf, mg)) types
             Filter._true
        | Until (_, i, f, g) when not (Interval.has_zero i) ->
           begin
             match convert Sup f types with
             | types, None    ->
                apply2' ~temporal:true (convert Sup g) (Tformula.of_formula f)
                  (fun mg mf -> Tformula.TUntil (R, i, true, mf, mg)) types
                  Filter._true
             | types, Some mf ->
                apply1' (Tformula.of_formula g)
                  (fun mg -> Tformula.TUntil (L, i, true, mf, mg)) types
           end
        | Until (_, i, f, g) ->
           apply2' ~temporal:true (convert Sup g) (Tformula.of_formula f)
             (fun mg mf -> Tformula.TUntil (R, i, true, mf, mg)) types
             Filter._true
        | _ -> types, None, Filter._true
      end
    | Obs -> let types, f = Tformula.of_formula form types in
             types, Some f.f, Filter._true
    | CauSup -> assert false
  in
  let r = (match f with Some f -> Some Tformula.{ f; enftype; filter } | None -> None) in
  (*Stdio.printf "convert %s (%s) = (%s, %s)\n\n"
    (EnfType.to_string enftype)
    (Formula.to_string form)
    (match r with Some r -> Tformula.to_string r | None -> "")
    (Filter.to_string filter);*)
  types, r

let convert' b enftype f =
  snd (convert b Cau f Ctxt.empty)

let do_type f b =
  let f = Formula.unroll_let f in
  (*print_endline (Formula.to_string f);*)
  if not (Set.is_empty (Formula.fv f)) then (
    Stdio.print_endline ("The formula\n "
                         ^ Formula.to_string f
                         ^ "\nis not closed: free variables are "
                         ^ String.concat ~sep:", " (Set.elements (Formula.fv f)));
    ignore (raise (Invalid_argument (Printf.sprintf "formula %s is not closed" (Formula.to_string f)))));
  match types Cau (Map.empty (module String)) f with
  | Possible c ->
     begin
       let c = Constraints.ac_simplify c in
       match Constraints.solve c with
       | sol::_ ->
          begin
            Map.iteri sol ~f:(fun ~key ~data -> (*print_endline ("key=" ^ key ^ "; data="^ EnfType.to_string (fst data)); *)Pred.Sig.update_enftype key (fst data));
            match convert' b Cau f with
            | Some f' -> Stdio.print_endline ("The formula\n "
                                              ^ Formula.to_string f
                                              ^ "\nis enforceable and types to\n "
                                              ^ Tformula.to_string f');
                         Tformula.ac_simplify f'
            | None    -> raise (Invalid_argument (Printf.sprintf "formula %s cannot be converted" (Formula.to_string f)))
          end
       | _ -> Stdio.print_endline ("The formula\n "
                                   ^ Formula.to_string f
                                   ^ "\nis not enforceable because the constraint\n "
                                   ^ Constraints.to_string c
                                   ^ "\nhas no solution.");
              raise (Invalid_argument (Printf.sprintf "formula %s is not enforceable" (Formula.to_string f)))
     end
  | Impossible e ->
     Stdio.print_endline ("The formula\n "
                          ^ Formula.to_string f
                          ^ "\nis not enforceable. To make it enforceable, you would need to\n "
                          ^ Errors.to_string e);
     raise (Invalid_argument (Printf.sprintf "formula %s is not enforceable" (Formula.to_string f)))

let rec relative_interval (f: Tformula.t) =
  let i = 
  match f.f with
  | TTT | TFF | TEqConst (_, _) | TPredicate (_, _) -> Zinterval.singleton (Zinterval.Z.zero)
  | TNeg f | TExists (_, _, _, f) | TForall (_, _, _, f) | TAgg (_, _, _, _, _, f) -> relative_interval f
  | TImp (_, f1, f2) | TIff (_, _, f1, f2)
    -> Zinterval.lub (relative_interval f1) (relative_interval f2)
  | TAnd (_, f :: fs) | TOr (_, f :: fs)
    -> List.fold ~init:(relative_interval f) ~f:(fun i g -> Zinterval.lub i (relative_interval g)) fs
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
  in i

let strict f =
  let rec _strict itv fut (f: Tformula.t) =
    ((Zinterval.has_zero itv) && fut)
    || (match f.f with
        | TTT | TFF | TEqConst (_, _) | TPredicate _ -> false
        | TNeg f | TExists (_, _, _, f) | TForall (_, _, _, f) | TAgg (_, _, _, _, _, f) -> _strict itv fut f
        | TImp (_, f1, f2) | TIff (_, _, f1, f2)
          -> (_strict itv fut f1) || (_strict itv fut f2)
        | TAnd (_, fs) | TOr (_, fs)
          -> List.exists ~f:(_strict itv fut) fs
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
  in not (_strict (Zinterval.singleton (Zinterval.Z.zero)) false f)

let relative_past f =
  Zinterval.is_nonpositive (relative_interval f)

let strictly_relative_past f =
  (relative_past f) && (strict f)

let is_transparent (f: Tformula.t) =
  let rec aux (f: Tformula.t) =
    (*print_endline ("aux " ^ Tformula.to_string f);*)
    let b =
    match f.enftype with
    | Cau -> begin
        match f.f with
        | TTT | TPredicate (_, _) -> true
        | TNeg f | TExists (_, _, _, f) | TForall (_, _, _, f)
          | TOnce (_, f) | TNext (_, f) | THistorically (_, f)
           | TAlways (_, _, f) -> aux f
        | TEventually (_, b, f) -> b && aux f
        | TOr (L, [f; g]) | TImp (L, f, g) | TIff (L, L, f, g)
          -> aux f && strictly_relative_past g
        | TOr (R, [f; g]) | TImp (R, f, g) | TIff (R, R, f, g)
          -> aux g && strictly_relative_past f
        | TIff (_, _, f, g)
          -> aux f && aux g
        | TAnd (_, fs) -> List.for_all ~f:strictly_relative_past fs
        | TSince (_, _, f, g) -> aux g && strictly_relative_past f
        | TUntil (R, _, b, f, g) -> b && aux g && strictly_relative_past f
        | TUntil (LR, _, b, f, g) -> b && aux f && aux g
        | _ -> false
      end
    | Sup -> begin
        match f.f with
        | TFF | TPredicate (_, _) -> true
        | TNeg f | TExists (_, _, _, f) | TForall (_, _, _, f)
          | TOnce (_, f) | TNext (_, f) | THistorically (_, f)
          | TEventually (_, _, f) -> aux f
        | TAlways (_, b, f) -> b && aux f
        | TAnd (L, f :: gs) 
          -> aux f && List.for_all ~f:strictly_relative_past gs
        | TIff (L, L, f, g) -> aux f && strictly_relative_past g
        | TAnd (R, (_::_ as fs)) ->
           aux (List.last_exn fs) && List.for_all ~f:strictly_relative_past (List.drop_last_exn fs)
        | TIff (R, R, f, g) -> aux g && strictly_relative_past f
        | TIff (_, _, f, g)
          -> aux f && aux g
        | TOr (_, fs) -> List.for_all ~f:strictly_relative_past fs
        | TSince (L, _, f, g) -> aux f && strictly_relative_past g
        | TUntil (R, _, _, f, g) -> aux g && strictly_relative_past f
        | TUntil (_, _, _, f, g) -> aux f && strictly_relative_past g
        | _ -> false
      end
    in b
  in
  if aux f then
    true
  else
    raise (Invalid_argument (Printf.sprintf "Warning: this formula cannot be transparently enforced"))
