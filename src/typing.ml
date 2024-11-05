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


module Errors = struct

  type error =
    | ECast of string * Enftype.t * Enftype.t
    | EFormula of string option * t * Enftype.t
    | EConj of error list
    | EDisj of error list [@@deriving equal]

  let rec to_string ?(n=0) e =
    let sp = Etc.spaces (2*n) in
    let lb = "\n" ^ sp in
    (match e with
     | ECast (e, t', t) -> "make "
                           ^ e
                           ^ " "
                           ^ Enftype.to_string t
                           ^ " (currently, it has type "
                           ^ Enftype.to_string t'
                           ^ ")"
     | EFormula (None, f, t) -> "make "
                                ^ Formula.to_string f
                                ^ " "
                                ^ Enftype.to_string t
                                ^ ", but this is impossible"
     | EFormula (Some s, f, t) -> "make "
                                ^ Formula.to_string f
                                ^ " "
                                ^ Enftype.to_string t
                                ^ ", but this is impossible"
                                ^ " (" ^ s ^ ")"
     | EConj es -> "at the same time"
                   ^ String.concat (List.map ~f:(fun e -> lb ^ "* " ^ to_string ~n:(n+1) e) es)
     | EDisj es -> "either"
                   ^ String.concat (List.map ~f:(fun e -> lb ^ "* " ^ to_string ~n:(n+1) e) es))

  let rec ac_simplify = function
    | EConj es  ->
       let es = List.map ~f:ac_simplify es in
       let e_conjs = function EConj es' -> Some es' | _ -> None in
       let e_not_conjs = function EConj es' -> false | _ -> true in
       let es_conjs = List.concat (List.filter_map es ~f:e_conjs) in
       let es_not_conjs = List.filter es ~f:e_not_conjs in
       let es' = Etc.dedup ~equal:equal_error (es_conjs @ es_not_conjs) in
       if List.length es' = 1 then List.hd_exn es' else EConj es'
    | EDisj es ->
       let e_disjs = function EDisj cs' -> Some cs' | _ -> None in
       let e_not_disjs = function EDisj cs' -> false | _ -> true in
       let es_disjs = List.concat (List.filter_map es ~f:e_disjs) in
       let es_not_disjs = List.filter es ~f:e_not_disjs in
       let es' = Etc.dedup ~equal:equal_error (es_disjs @ es_not_disjs) in
       if List.length es' = 1 then List.hd_exn es' else EDisj es'
    | e -> e

end

module Constraints = struct

  type constr =
    | CTT
    | CFF
    | CGeq of string * Enftype.t
    | CNLeqNCau of string * Enftype.t
    | CConj of constr list
    | CDisj of constr list [@@deriving equal, compare, sexp_of]

  type verdict = Possible of constr | Impossible of Errors.error

  let tt = CTT
  let ff = CFF
  let geq s t = CGeq (s, t)

  let nleqncau s = CNLeqNCau (s, Sig.enftype_of_pred s)

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
    | Impossible c, Impossible d -> Impossible (Errors.ac_simplify (EConj [c; d]))
    | Impossible c, _ | _, Impossible c -> Impossible c
    | Possible c, Possible d -> Possible (ac_simplify (CConj [c; d]))

  let disj c d = match c, d with
    | Impossible c, Impossible d -> Impossible (Errors.ac_simplify (EDisj [c; d]))
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
       let v  = Enftype.join t u in
       let v' = Option.merge ~f:Enftype.meet t' u' in
       match v' with
       | Some v' when Enftype.leq v' v ->
          (*print_endline (Printf.sprintf "merge_aux.no key=%s t=%s t'=%s u=%s, u'=%s"
                           key
                           (Enftype.to_string t)
                           (Option.fold t' ~init:"None" ~f:(fun _ v -> Enftype.to_string v))
                           (Enftype.to_string u)
                           (Option.fold u' ~init:"None" ~f:(fun _ v -> Enftype.to_string v)));*)
          raise CannotMerge
       | _ ->
          (*print_endline (Printf.sprintf "merge_aux.yes key=%s t=%s t'=%s u=%s, u'=%s"
                           key
                           (Enftype.to_string t)
                           (Option.fold t' ~init:"None" ~f:(fun _ v -> Enftype.to_string v))
                           (Enftype.to_string u)
                           (Option.fold u' ~init:"None" ~f:(fun _ v -> Enftype.to_string v)));*)
          Some (v, v')

  let try_merge (a, b) =
    try Some (Map.merge a b ~f:merge_aux)
    with CannotMerge -> None

  let rec to_string_rec l = function
    | CTT -> Printf.sprintf "⊤"
    | CFF -> Printf.sprintf "⊥"
    | CGeq (s, t) -> Printf.sprintf "t(%s) ⋡ Obs ∧ t(%s) ≽ %s" s s (Enftype.to_string t)
    | CNLeqNCau (s, t) -> Printf.sprintf "NCau ⋡ t(%s)" s 
    | CConj cs -> Printf.sprintf (Etc.paren l 4 "%s")
                    (String.concat ~sep:" ∧ " (List.map ~f:(to_string_rec 4) cs))
    | CDisj cs -> Printf.sprintf (Etc.paren l 3 "%s")
                    (String.concat ~sep:" ∨ " (List.map ~f:(to_string_rec 3) cs))

  let to_string = to_string_rec 0

  let verdict_to_string = function
    | Possible c -> Printf.sprintf "Possible(%s)" (to_string c)
    | Impossible e -> Printf.sprintf "Impossible(%s)" (Errors.to_string e)

  let rec solve c =
    let r = match c with
    | CTT -> [Map.empty (module String)]
    | CFF (*| CGeq (_, Obs)*) -> []
    | CGeq (s, t) -> [Map.singleton (module String) s (t, Some Enftype.Obs)]
    | CNLeqNCau (s, t) -> [Map.singleton (module String) s (Enftype.join Enftype.SCau t, None);
                           Map.singleton (module String) s (Enftype.join Enftype.Sup t,  None)]
    | CConj [] -> [Map.empty (module String)]
    | CConj (c::cs) ->
       let f sol d = List.filter_map (cartesian sol (solve d)) ~f:try_merge in
       List.fold_left cs ~init:(solve c) ~f
    | CDisj cs -> List.concat_map cs ~f:solve
    in(* Stdio.printf "solve(%s)=[%s]\n" (to_string c) (String.concat ~sep:"; " (List.map r ~f:(fun m -> String.concat ~sep:", " (List.map (Map.to_alist m) ~f:(fun (key, (lower, upper_obs)) -> key ^ " ≽ " ^ Enftype.to_string lower ^ (match upper_obs with None -> "" | Some upper -> " ∧ " ^ key ^ " ⋡ " ^ Enftype.to_string upper))))));*)
       r
    


end

open Enftype
open Constraints
open Option

type pg_map = (string, (string, String.comparator_witness) Set.t list, String.comparator_witness) Map.t
type t_map  = (string, Enftype.t * int list, String.comparator_witness) Map.t


let types_predicate (ts: t_map) (t: Enftype.t) (e: string) =
  let t', _ = Map.find_exn ts e in
  let t'' = Enftype.join t t' in
  if not (Enftype.geq t'' Obs) then
    Possible (geq e t'')
  else
    Impossible (ECast (e, t', t))

let rec types (t: Enftype.t) (pgs: pg_map) (f: Formula.t) =
  let error s = Impossible (EFormula (Some s, f, t)) in
  let ts = Sig.pred_enftype_map () in
  let rec aux (t: Enftype.t) (pgs: pg_map) (ts: t_map) (f: Formula.t) =
    let aux' t f = aux t pgs ts f in
    let r = match t with
      Cau | NCau | SCau -> begin
        match f with
        | TT -> Possible CTT
        | Predicate (e, terms) ->
           let _, is = Map.find_exn ts e in
           let terms = List.filteri terms ~f:(fun i _ -> List.mem is i ~equal:Int.equal) in
           let fvs   = Etc.dedup ~equal:String.equal (Term.fv_list terms) in
           let es    = List.map fvs ~f:(fun x -> Option.value (Map.find pgs x) ~default:[]) in
           let unguarded = List.filter_map (List.zip_exn fvs es) ~f:(fun (x, e) ->
                               if List.is_empty e then Some x else None) in
           (match List.map ~f:(Set.union_list (module String)) (Etc.cartesian es) with
            | [] -> Impossible (EFormula (Some ("no guards found for " ^ String.concat ~sep:", " unguarded), f, t))
            | es_ncau_list ->
               (*print_endline (Printf.sprintf "aux.es_ncau_list=[%s]"
                 (String.concat ~sep:"; " (List.map es_ncau_list ~f:(fun s -> Printf.sprintf "[%s]" ((String.concat ~sep:", " (Set.elements s)))))));*)
               let c =
                 (if Sig.is_strict terms && Enftype.leq t SCau then
                    disjs (List.map es_ncau_list ~f:(fun es_ncau ->
                               conj (types_predicate ts t e)
                                 (conjs (List.map (Set.elements es_ncau)
                                           ~f:(fun e ->
                                             Possible (nleqncau e))))))
                  else if Enftype.geq t SCau then
                    error ("the predicate " ^ Formula.to_string f
                           ^ " cannot be SCau since it has non-strict terms")
                  else
                    disjs (List.map es_ncau_list ~f:(fun es_ncau ->
                               conj (types_predicate ts NCau e)
                                 (conjs (List.map (Set.elements es_ncau)
                                           ~f:(fun e ->
                                             Possible (nleqncau e)))))))
               in c) 
        | Let (e, enftype_opt, vars, f, g) ->
           let f_unguarded i x = if not (Formula.is_past_guarded x false f) then Some (x, i) else None in
           let unguarded_x, unguarded_i = List.unzip (List.filter_mapi vars ~f:f_unguarded) in
           let pgs' = List.fold_left unguarded_x ~init:pgs ~f:(Map.update ~f:(fun _ -> [Set.empty (module String)])) in
           (match enftype_opt with
            | Some enftype ->
               conj (aux enftype pgs' ts f) (aux t pgs (Map.update ts e ~f:(fun _ -> NCau, unguarded_i)) g)
            | None ->
               disjs [conj (aux NCau pgs' ts f) (aux t pgs (Map.update ts e ~f:(fun _ -> NCau, unguarded_i)) g);
                      conj (aux NSup pgs' ts f) (aux t pgs (Map.update ts e ~f:(fun _ -> NSup, unguarded_i)) g);
                      conj (aux SCau pgs' ts f) (aux t pgs (Map.update ts e ~f:(fun _ -> SCau, unguarded_i)) g);
                      conj (aux SSup pgs' ts f) (aux t pgs (Map.update ts e ~f:(fun _ -> SSup, unguarded_i)) g);
                      aux t pgs (Map.update ts e ~f:(fun _ -> Obs, unguarded_i)) g])
        | Neg f -> aux' (Enftype.neg t) f
        | And (_, f, g) -> conj (aux' t f) (aux' t g)
        | Or (L, f, g) -> aux' t f
        | Or (R, f, g) -> aux' t g
        | Or (_, f, g) -> disj (aux' t f) (aux' t g)
        | Imp (L, f, g) -> aux' (Enftype.neg t) f
        | Imp (R, f, g) -> aux' t g
        | Imp (_, f, g) -> disj (aux' (Enftype.neg t) f) (aux' t g)
        | Iff (L, L, f, g) -> conj (aux' (Enftype.neg t) f) (aux' t f)
        | Iff (L, R, f, g) -> conj (aux' (Enftype.neg t) f) (aux' (Enftype.neg t) g)
        | Iff (R, L, f, g) -> conj (aux' t g) (aux' t f)
        | Iff (R, R, f, g) -> conj (aux' t g) (aux' (Enftype.neg t) g)
        | Iff (_, _, f, g) -> conj (disj (aux' (Enftype.neg t) f) (aux' t g))
                                (disj (aux' t f) (aux' (Enftype.neg t) g))
        | Exists (_, f) -> aux' t f
        | Forall (x, f) ->
           let es = Formula.solve_past_guarded x false f in
           (match es with
            | [] -> error ("for causability " ^ x ^ " must be past-guarded")
            | _  -> aux t (Map.update pgs x (fun _ -> es)) ts f)
        | Next (i, f) when Interval.has_zero i && not (Interval.is_zero i) -> aux' t f
        | Next _ -> error "○ with non-[0,a) interval, a > 0, is never Cau"
        | Once (i, g) | Since (_, i, _, g) when Interval.has_zero i -> aux' t g
        | Once _ | Since _ -> error "⧫[a,b) or S[a,b) with a > 0 is never Cau"
        | Eventually (_, f) | Always (_, f) -> aux' t f
        | Until (LR, B _, f, g) -> conj (aux' t f) (aux' t g)
        | Until (_, i, f, g) when Interval.has_zero i -> aux' t g
        | Until (_, _, f, g) -> conj (aux' t f) (aux' t g)
        | Prev _ -> error "● is never Cau"
        | _ -> Impossible (EFormula (None, f, t))
      end
    | Sup | NSup | SSup -> begin
        match f with
        | FF -> Possible CTT
        | Predicate (e, _) -> types_predicate ts t e
        | Let (e, enftype_opt, vars, f, g) ->
           let f_unguarded i x = if not (Formula.is_past_guarded x false f) then Some (x, i) else None in
           let unguarded_x, unguarded_i = List.unzip (List.filter_mapi vars ~f:f_unguarded) in
           let pgs' = List.fold_left unguarded_x ~init:pgs ~f:(Map.update ~f:(fun _ -> [Set.empty (module String)])) in
           (match enftype_opt with
            | Some enftype ->
               conj (aux enftype pgs' ts f) (aux t pgs (Map.update ts e ~f:(fun _ -> NCau, unguarded_i)) g)
            | None ->
               disjs [conj (aux NCau pgs' ts f) (aux t pgs (Map.update ts e ~f:(fun _ -> NCau, unguarded_i)) g);
                      conj (aux SCau pgs' ts f) (aux t pgs (Map.update ts e ~f:(fun _ -> SCau, unguarded_i)) g);
                      conj (aux NSup pgs' ts f) (aux t pgs (Map.update ts e ~f:(fun _ -> NSup, unguarded_i)) g);
                      conj (aux SSup pgs' ts f) (aux t pgs (Map.update ts e ~f:(fun _ -> SSup, unguarded_i)) g);
                      aux t pgs (Map.update ts e ~f:(fun _ -> Obs, unguarded_i)) g])
        | Agg (s, op, x, (_::_ as y), f) -> aux t pgs ts (Formula.exists_of_agg s op x y f)
        | Neg f -> aux' (Enftype.neg t) f
        | And (L, f, g) -> aux' t f
        | And (R, f, g) -> aux' t g
        | And (_, f, g) -> disj (aux' t f) (aux' t g)
        | Or (_, f, g) -> conj (aux' t f) (aux' t g)
        | Imp (_, f, g) -> conj (aux' (Enftype.neg t) f) (aux' t g)
        | Iff (L, _, f, g) -> conj (aux' (Enftype.neg t) f) (aux' t g)
        | Iff (R, _, f, g) -> conj (aux' t f) (aux' (Enftype.neg t) g)
        | Iff (_, _, f, g) -> disj (conj (aux' (Enftype.neg t) f) (aux' t g))
                                (conj (aux' t f) (aux' (Enftype.neg t) g))
        | Exists (x, f) ->
           let es = Formula.solve_past_guarded x true f in
           (match es with
            | [] -> error ("for suppressability " ^ x ^ " must be past-guarded")
            | _  -> aux t (Map.update pgs x (fun _ -> es)) ts f)
        | Forall (_, f) -> aux' t f
        | Next (_, f) -> aux' t f
        | Historically (i, f) when Interval.has_zero i -> aux' t f
        | Historically _ -> error "■[a,b) with a > 0 is never Sup"
        | Since (_, i, f, _) when not (Interval.has_zero i) -> aux' t f
        | Since (_, i, f, g) -> conj (aux' t f) (aux' t g)
        | Eventually (_, f) | Always (_, f) -> aux' t f
        | Until (L, i, f, g) when not (Interval.has_zero i) -> aux' t f
        | Until (R, _, _, g) -> aux' t g
        | Until (_, i, f, g) when not (Interval.has_zero i) -> aux' t f
        | Until (_, _, _, g) -> aux' t g
        | Prev _ -> error "● is never Sup"
        | _ -> Impossible (EFormula (None, f, t))
      end
    | Obs -> Possible CTT
    | CauSup -> Impossible (EFormula (Some (Formula.to_string f ^ " is never CauSup"), f, t))
    in
    (*Stdio.printf "types.aux(%s, %s)=%s\n" (Enftype.to_string t) (Formula.to_string f) (Constraints.verdict_to_string r);*)
    r
  in aux t pgs ts f


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
    print_endline (Enftype.to_string enftype);*)
    match enftype with
    | Cau | NCau | SCau -> begin
        match form with
        | TT -> types, Some (Tformula.TTT), Filter._true
        | Predicate (e, trms) when Enftype.is_causable (Sig.enftype_of_pred e) ->
           let types, _ = Sig.check_terms types e trms in
           types, Some (Tformula.TPredicate (e, trms)), Filter._true
        | Predicate' (e, trms, f) ->
           apply1 (convert enftype f) (fun mf -> Tformula.TPredicate' (e, trms, mf)) types
        | Let' (e, vars, f, g) ->
           let enftype' = Sig.enftype_of_pred e in
           apply2 (convert enftype f) (convert enftype g)
             (fun mf mg -> Tformula.TLet' (e, vars, mf, mg)) types
        | Neg f -> apply1 (convert (Enftype.neg enftype) f) (fun mf -> Tformula.TNeg mf) types 
        | And (s, f, g) -> apply2 (convert enftype f) (convert enftype g)
                             (fun mf mg -> Tformula.TAnd (default_L s, [mf; mg])) types
        | Or (L, f, g) -> apply2' (convert enftype f) (Tformula.of_formula g)
                            (fun mf mg -> Tformula.TOr (L, [mf; mg])) types
                            (conj_filter ~b:false f g)
        | Or (R, f, g) -> apply2' (convert enftype g) (Tformula.of_formula f)
                            (fun mg mf -> Tformula.TOr (R, [mf; mg])) types
                            (conj_filter ~b:false f g)
        | Or (_, f, g) ->
           begin
             match convert enftype f types with
             | types, Some mf -> apply1'
                                   ~new_filter:(Some (conj_filter ~b:false f g))
                                   (Tformula.of_formula g)
                                   (fun mg -> Tformula.TOr (L, [mf; mg])) types
             | types, None    -> apply2' (convert enftype g) (Tformula.of_formula f)
                                   (fun mg mf -> Tformula.TOr (R, [mf; mg])) types
                                   (conj_filter ~b:false f g)
           end
        | Imp (L, f, g) -> apply2' (convert (Enftype.neg enftype) f) (Tformula.of_formula g)
                             (fun mf mg -> Tformula.TImp (L, mf, mg)) types
                             (conj_filter ~neg:true f g)
        | Imp (R, f, g) -> apply2' (convert enftype g) (Tformula.of_formula f)
                             (fun mg mf -> Tformula.TImp (R, mf, mg)) types
                             (conj_filter ~neg:true f g)
        | Imp (_, f, g) ->
           begin
             match convert Sup f types with
             | types, Some mf -> apply1'
                                   ~new_filter:(Some (conj_filter ~neg:true f g))
                                   (Tformula.of_formula g)
                                   (fun mg -> Tformula.TImp (L, mf, mg)) types
             | types, None    -> apply2' (convert enftype g) (Tformula.of_formula f)
                                   (fun mg mf -> Tformula.TImp (R, mf, mg)) types
                                   (conj_filter ~neg:true f g)
           end
        | Iff (L, L, f, g) -> apply2' (convert (Enftype.neg enftype) f) (Tformula.of_formula g)
                                (fun mf mg -> Tformula.TIff (L, L, mf, mg)) types
                                Filter._true
        | Iff (L, R, f, g) -> apply2 (convert (Enftype.neg enftype) f)
                                (convert (Enftype.neg enftype) g)
                                (fun mf mg -> Tformula.TIff (L, R, mf, mg)) types
        | Iff (R, L, f, g) -> apply2 (convert enftype g) (convert enftype f)
                                (fun mg mf -> Tformula.TIff (R, L, mf, mg)) types
        | Iff (R, R, f, g) -> apply2' (convert enftype g) (Tformula.of_formula f)
                                (fun mg mf -> Tformula.TIff (R, R, mf, mg)) types
                                Filter._true
        | Iff (_, _, f, g) ->
           begin
             match convert (Enftype.neg enftype) f types with
             | types, Some mf ->
                begin
                  match convert enftype f types with
                  | types, Some mf -> apply1' (Tformula.of_formula g)
                                        (fun mg -> Tformula.TIff (L, L, mf, mg)) types
                  | types, None    -> apply1 (convert (Enftype.neg enftype) g)
                                        (fun mg -> Tformula.TIff (L, R, mf, mg)) types
                end
             | types, None ->
                begin
                  match convert enftype g types with
                  | types, Some mg ->
                     begin
                       match convert enftype f types with
                       | types, Some mf -> types, Some (Tformula.TIff (R, L, mf, mg)),
                                           Filter.disj mf.filter mg.filter
                       | types, None    -> apply2' (convert (Enftype.neg enftype) g)
                                             (Tformula.of_formula f)
                                             (fun mg mf -> Tformula.TIff (R, R, mf, mg)) types
                                             Filter._true
                     end
                  | types, None    -> types, None, Filter._true
                end
           end
        | Exists (x, f) ->
           begin
             match convert enftype f types with
             | types, Some mf -> types, Some (Tformula.TExists (x, Ctxt.get_tt_exn x types, true, mf)), mf.filter
             | types, None    -> types, None, Filter._true
           end
        | Forall (x, f) when is_past_guarded x false f ->
           begin
             match convert enftype f types with
             | types, Some mf -> types, Some (Tformula.TForall (x, Ctxt.get_tt_exn x types, false, mf)), mf.filter
             | types, None    -> types, None, Filter._true
           end
        | Next (i, f) when Interval.has_zero i && not (Interval.is_zero i) -> 
           apply1 ~temporal:true (convert enftype f) (fun mf -> Tformula.TNext (i, mf)) types
        | Once (i, f) when Interval.has_zero i ->
           apply1 (convert enftype f) (fun mf -> Tformula.TOnce (i, mf)) types
        | Since (_, i, f, g) when Interval.has_zero i ->
           apply2' (convert enftype g) (Tformula.of_formula f)
             (fun mg mf -> Tformula.TSince (R, i, mf, mg)) types
             Filter._true
        | Eventually (i, f) ->
           apply1 ~temporal:true (convert enftype f)
             (fun mf -> Tformula.TEventually (set_b i, Interval.is_bounded i, mf)) types
        | Always (i, f) ->
           apply1 ~temporal:true (convert enftype f)
             (fun mf -> Tformula.TAlways (i, true, mf)) types
        | Until (LR, i, f, g) ->
           apply2 ~temporal:true (convert enftype f) (convert enftype g)
             (fun mf mg -> Tformula.TUntil (LR, set_b i, Interval.is_bounded i, mf, mg)) types
        | Until (_, i, f, g) when Interval.has_zero i ->
           apply2' ~temporal:true (convert enftype g) (Tformula.of_formula f)
             (fun mg mf -> Tformula.TUntil (R, set_b i, Interval.is_bounded i, mf, mg)) types
             Filter._true
        | Until (_, i, f, g) ->
           apply2 ~temporal:true (convert enftype f) (convert Cau g)
             (fun mf mg -> Tformula.TUntil (LR, set_b i, Interval.is_bounded i, mf, mg)) types
        | _ -> types, None, Filter._true
      end
    | Sup | NSup | SSup -> begin
        match form with
        | FF -> types, Some (Tformula.TFF), Filter._true
        | Predicate (e, trms) when Enftype.is_suppressable (Sig.enftype_of_pred e) ->
           let types, _ = Sig.check_terms types e trms in
           types, Some (Tformula.TPredicate (e, trms)), Filter.An e
        | Predicate' (e, trms, f) ->
           apply1 (convert enftype f) (fun mf -> Tformula.TPredicate' (e, trms, mf)) types
        | Let' (e, vars, f, g) ->
           let enftype' = Sig.enftype_of_pred e in
           apply2 (convert enftype f) (convert enftype g)
             (fun mf mg -> Tformula.TLet' (e, vars, mf, mg)) types
        | Agg (s, op, x, y, f) ->
           begin
             match convert enftype (Formula.exists_of_agg s op x y f) types with
             | types, Some mf -> apply1' (Tformula.of_formula form)
                                   (fun mg -> Tformula.TAnd (L, [mf; mg])) types
             | types, None    -> types, None, Filter._true
           end
        | Neg f -> apply1 (convert (Enftype.neg enftype) f) (fun mf -> Tformula.TNeg mf) types
        | And (L, f, g) -> apply2' (convert enftype f) (Tformula.of_formula g)
                             (fun mf mg -> Tformula.TAnd (L, [mf; mg])) types
                             (conj_filter f g)
        | And (R, f, g) -> apply2' (convert enftype g) (Tformula.of_formula f)
                             (fun mg mf -> Tformula.TAnd (R, [mf; mg])) types
                             (conj_filter f g)
        | And (_, f, g) ->
           begin
              match convert enftype f types with
              | types, Some mf -> apply1' ~new_filter:(Some (conj_filter f g))
                                    (Tformula.of_formula g)
                                    (fun mg -> Tformula.TAnd (L, [mf; mg])) types
              | types, None    -> apply2' (convert enftype g) (Tformula.of_formula f)
                                    (fun mg mf -> Tformula.TAnd (R, [mf; mg])) types
                                    (conj_filter f g)
           end
        | Or (s, f, g) -> apply2 (convert enftype f) (convert enftype g)
                            (fun mf mg -> Tformula.TOr (default_L s, [mf; mg])) types
        | Imp (s, f, g) -> apply2 (convert (Enftype.neg enftype) f) (convert enftype g)
                             (fun mf mg -> Tformula.TImp (default_L s, mf, mg)) types
        | Iff (L, _, f, g) -> apply2 (convert (Enftype.neg enftype) f) (convert enftype g)
                                (fun mf mg -> Tformula.TIff (L, N, mf, mg)) types
        | Iff (R, _, f, g) -> apply2 (convert enftype f) (convert (Enftype.neg enftype) g)
                                (fun mf mg -> Tformula.TIff (R, N, mf, mg)) types
        | Iff (_, _, f, g) ->
           begin
             match convert (Enftype.neg enftype) f types with
             | types, Some mf ->
                begin
                  match convert enftype g types with
                  | types, Some mg -> types, Some (Tformula.TIff (L, R, mf, mg)),
                                      Filter.disj mf.filter mg.filter
                  | types, None    -> types, None, Filter._true
                end
             | types, None    -> types, None, Filter._true
           end
        | Exists (x, f) when is_past_guarded x true f ->
           begin
             match convert enftype f types with
             | types, Some mf -> types, Some (Tformula.TExists (x, Ctxt.get_tt_exn x types, true, mf)), mf.filter
             | types, None    -> types, None, Filter._true
           end
        | Forall (x, f) ->
           begin
             match convert enftype f types with
             | types, Some mf -> types, Some (Tformula.TForall (x, Ctxt.get_tt_exn x types, false, mf)), mf.filter
             | types, None    -> types, None, Filter._true
           end
        | Next (i, f) -> apply1 ~temporal:true (convert enftype f)
                           (fun mf -> Tformula.TNext (i, mf)) types
        | Historically (i, f) when Interval.has_zero i ->
           apply1 (convert enftype f) (fun mf -> Tformula.THistorically (i, mf)) types
        | Since (_, i, f, g) when not (Interval.has_zero i) ->
           apply2' (convert enftype f) (Tformula.of_formula g)
             (fun mf mg -> Tformula.TSince (L, i, mf, mg)) types
             Filter._true
        | Since (_, i, f, g) ->
           let types, since_f = Tformula.of_formula (Since (N, i, f, g)) types in
           apply2 (convert enftype f) (convert enftype g)
             (fun mf mg ->
               let f = Tformula.TAnd (L, [mf; since_f]) in
               Tformula.TOr (L, [mg; {f; enftype; filter = Filter._true}])) types
        | Eventually (i, f) ->
           apply1 ~temporal:true (convert enftype f)
             (fun mf -> Tformula.TEventually (i, true, mf)) types
        | Always (i, f) ->
           apply1 ~temporal:true (convert enftype f)
             (fun mf -> Tformula.TAlways (set_b i, Interval.is_bounded i, mf)) types
        | Until (L, i, f, g) when not (Interval.has_zero i) ->
           apply2' ~temporal:true (convert enftype f) (Tformula.of_formula g)
             (fun mf mg -> Tformula.TUntil (L, i, true, mf, mg)) types
             Filter._true
        | Until (R, i, f, g) ->
           apply2' ~temporal:true (convert enftype g) (Tformula.of_formula f)
             (fun mg mf -> Tformula.TUntil (R, i, true, mf, mg)) types
             Filter._true
        | Until (_, i, f, g) when not (Interval.has_zero i) ->
           begin
             match convert enftype f types with
             | types, None    ->
                apply2' ~temporal:true (convert enftype g) (Tformula.of_formula f)
                  (fun mg mf -> Tformula.TUntil (R, i, true, mf, mg)) types
                  Filter._true
             | types, Some mf ->
                apply1' (Tformula.of_formula g)
                  (fun mg -> Tformula.TUntil (L, i, true, mf, mg)) types
           end
        | Until (_, i, f, g) ->
           apply2' ~temporal:true (convert enftype g) (Tformula.of_formula f)
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
    (Enftype.to_string enftype)
    (Formula.to_string form)
    (match r with Some r -> Tformula.to_string r | None -> "")
    (Filter.to_string filter);*)
  types, r

let convert' b enftype f =
  snd (convert b Cau f Ctxt.empty)

let do_type f b =
  let orig_f = f in
  let f = Formula.convert_vars f in
  let f = Formula.convert_lets f in
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
       (*print_endline (Constraints.to_string c);*)
       match Constraints.solve c with
       | sol::_ ->
          begin
            let bound = Map.fold sol ~init:[] ~f:
                          (fun ~key ~data bound -> if Hashtbl.mem Sig.table key then
                                                     (Sig.update_enftype key (fst data); bound)
                                                   else
                                                     (Sig.add_letpred key []; key::bound)) in
            let f = Formula.unroll_let f in
            match convert' b Cau f with
            | Some f' -> Stdio.print_endline ("The formula\n "
                                              ^ Formula.to_string orig_f
                                              ^ "\nis enforceable and types to\n "
                                              ^ Tformula.to_string f');
                         Tformula.ac_simplify f'
            | None    -> raise (Invalid_argument (Printf.sprintf "formula %s cannot be converted" (Formula.to_string f)))
          end
       | _ -> Stdio.print_endline ("The formula\n "
                                   ^ Formula.to_string orig_f
                                   ^ "\nis not enforceable because the constraint\n "
                                   ^ Constraints.to_string c
                                   ^ "\nhas no solution.");
              raise (Invalid_argument (Printf.sprintf "formula %s is not enforceable" (Formula.to_string f)))
     end
  | Impossible e ->
     Stdio.print_endline ("The formula\n "
                          ^ Formula.to_string orig_f
                          ^ "\nis not enforceable. To make it enforceable, you would need to\n "
                          ^ Errors.to_string e);
     raise (Invalid_argument (Printf.sprintf "formula %s is not enforceable" (Formula.to_string f)))

let rec relative_interval (f: Tformula.t) =
  let i = 
  match f.f with
  | TTT | TFF | TEqConst (_, _) | TPredicate (_, _) -> Zinterval.singleton (Zinterval.Z.zero)
  | TNeg f | TExists (_, _, _, f) | TForall (_, _, _, f) | TAgg (_, _, _, _, _, f)
    | TPredicate' (_, _, f) | TLet' (_, _, _, f)
    -> relative_interval f
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
        | TNeg f | TExists (_, _, _, f) | TForall (_, _, _, f) | TAgg (_, _, _, _, _, f)
          | TPredicate' (_, _, f) | TLet' (_, _, _, f) -> _strict itv fut f
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
    | Cau | NCau | SCau -> begin
        match f.f with
        | TTT | TPredicate (_, _) -> true
        | TNeg f | TExists (_, _, _, f) | TForall (_, _, _, f)
          | TOnce (_, f) | TNext (_, f) | THistorically (_, f) | TAlways (_, _, f)
          | TPredicate' (_, _, f) | TLet' (_, _, _, f) -> aux f
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
    | Sup | NSup | SSup -> begin
        match f.f with
        | TFF | TPredicate (_, _) -> true
        | TNeg f | TExists (_, _, _, f) | TForall (_, _, _, f)
          | TOnce (_, f) | TNext (_, f) | THistorically (_, f) | TEventually (_, _, f)
          | TPredicate' (_, _, f) | TLet' (_, _, _, f) -> aux f
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
