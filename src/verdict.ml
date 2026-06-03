open Base
open MFOTL_lib

module type T = sig
  type t
  val equal : t -> t -> bool
  val to_string : t -> string
end

module MakeErrors (F: T) = struct

  type error =
    | ECast of string * Enftype.t * Enftype.t
    | EFormula of string option * F.t * Enftype.t
    | EConj of error list
    | EDisj of error list
    | ERule of string  [@@deriving equal]

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
                                ^ F.to_string f
                                ^ " "
                                ^ Enftype.to_string t
                                ^ ", but this is impossible"
     | EFormula (Some s, f, t) -> "make "
                                  ^ F.to_string f
                                  ^ " "
                                  ^ Enftype.to_string t
                                  ^ ", but this is impossible"
                                  ^ " (" ^ s ^ ")"
     | EConj es -> "at the same time"
                   ^ String.concat (List.map ~f:(fun e -> lb ^ "* " ^ to_string ~n:(n+1) e) es)
     | EDisj es -> "either"
                   ^ String.concat (List.map ~f:(fun e -> lb ^ "* " ^ to_string ~n:(n+1) e) es)
     | ERule s -> s)

  let rec ac_flatten = function
    | EConj es ->
      let es = List.map ~f:ac_flatten es in
      let es = List.concat_map es ~f:(function EConj xs -> xs | c -> [c]) in
      (match es with [c] -> c | _ -> EConj es)
    | EDisj es ->
      let es = List.map ~f:ac_flatten es in
      let es = List.concat_map es ~f:(function EDisj xs -> xs | c -> [c]) in
      (match es with [c] -> c | _ -> EDisj es)
    | c -> c

  let rec ac_simplify = function
    | EConj es ->
      let es = List.map ~f:ac_simplify es in
      let f_has_ff = function EDisj [] -> true | _ -> false in
      (if List.exists es ~f:f_has_ff then
         EDisj []
       else
         match ac_flatten (EConj es) with
         | EConj es' ->
           let es', _ =
             let is_weaker_clause c ds =
               (* All disjuncts in d' are in d, so d is unnecessary *)
               let isin d = List.for_all ~f:(List.mem d ~equal:equal_error) in
               let d = match c with EDisj d -> d | _ -> [c] in
               d, List.exists ds ~f:(isin d) in
             let f c (cs, ds) =
               let d, b = is_weaker_clause c ds in
               if b then (cs, ds) else (c::cs, d::ds) in
             List.fold_right es' ~init:([], []) ~f
           in
           EConj es'
         | c -> c)
    | EDisj es ->
      let es = List.map ~f:ac_simplify es in
      let f_has_tt = function EConj [] -> true | _ -> false in
      (if List.exists es ~f:f_has_tt then
         EConj []
       else
         match ac_flatten (EDisj es) with
         | EDisj es' ->
           let es', _ =
             let is_weaker_clause c ds =
               (* All conjuncts in d' are in d, so d is unnecessary *)
               let isin d = List.for_all ~f:(List.mem d ~equal:equal_error) in
               let d = match c with EConj d -> d | _ -> [c] in
               d, List.exists ds ~f:(isin d) in
             let f c (cs, ds) =
               let d, b = is_weaker_clause c ds in
               if b then (cs, ds) else (c::cs, d::ds) in
             List.fold_right es' ~init:([], []) ~f
           in
           EDisj es'
         | c -> c)
    | c -> c

end

(* ------------------------------------------------------------------ *)
(* Verdict module                                                        *)
(* ------------------------------------------------------------------ *)

module Make (F: T)  = struct

  module Errors = MakeErrors(F)

  type 'a v = Possible of 'a list | Impossible of Errors.error

  let conj ~f c d = match c, d with
    | Impossible c, Impossible d -> Impossible (Errors.ac_simplify (Errors.EConj [c; d]))
    | Impossible c, _ | _, Impossible c -> Impossible c
    | Possible c, Possible d -> Possible (f c d)

  let disj c d = match c, d with
    | Impossible c, Impossible d -> Impossible (Errors.ac_simplify (Errors.EDisj [c; d]))
    | Impossible _, _ -> d
    | _, Impossible _ -> c
    | Possible c, Possible d -> Possible (c @ d)

  let conjs ~f = function
    | c::cs -> List.fold_left ~init:c ~f:(conj ~f) cs

  let disjs = function
    | [] -> Impossible (Errors.EDisj [])
    | c::cs -> List.fold_left ~init:c ~f:disj cs

  let rec all = function
    | [] -> Possible []
    | (Possible c)::cs ->
      (match all cs with
       | Possible cs -> Possible (c::cs)
       | Impossible err -> Impossible err)
    | (Impossible c)::cs ->
      (match all cs with
       | Possible cs -> Impossible c
       | Impossible d -> Impossible (Errors.ac_simplify (Errors.EDisj [c; d])))

  let rec any = function
    | [] -> Impossible (Errors.EDisj [])
    | (Possible c)::cs ->
      (match all cs with
       | Possible cs -> Possible (c::cs)
       | Impossible _err -> Possible [c])
    | (Impossible c)::cs ->
      (match all cs with
       | Possible cs -> Possible cs
       | Impossible d -> Impossible (Errors.ac_simplify (Errors.EConj [c; d])))

  let (let*) x f = match x with
    | Possible sols -> Possible (f sols)
    | Impossible err -> Impossible err

  let (let**) x f = match x with
    | Possible sols -> f sols
    | Impossible err -> Impossible err

  let verdict_to_string ~to_string = function
    | Possible c -> Printf.sprintf "Possible(%s)" (to_string c)
    | Impossible e -> Printf.sprintf "Impossible(%s)" (Errors.to_string e)

  let map ~f = function
    | Possible sols -> Possible (f sols)
    | Impossible err -> Impossible err

end
