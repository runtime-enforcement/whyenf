(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Stdio

module Term = struct

  module T = struct

    type t = Var of string | Const of Dom.t | App of string * t list [@@deriving sexp_of, hash]

    let rec compare t t' =
      match t, t' with
      | Var s, Var s' -> String.compare s s'
      | Var _, _ -> -1
      | Const d, Const d' -> Dom.compare d d'
      | Const _, Var _ -> 1
      | Const _, App _ -> -1
      | App (s, [Var x; trm]), App (s', [Var x'; trm']) when Funcs.is_eq s && Funcs.is_eq s' ->
         Etc.lexicographic2 String.compare compare (x, trm) (x', trm')
      | App (s, [Var x; trm]), App _ when Funcs.is_eq s -> -1
      | App _, App (s', [Var x'; trm']) when Funcs.is_eq s' -> 1
      | App (s, ts), App (s', ts') ->
         Etc.lexicographic2 String.compare (Etc.lexicographics compare) (s, ts) (s', ts')
      | App _, _ -> 1

    let var x = Var x
    let const d = Const d
    let app f trms = App (f, trms)

    let is_var = function
      | Var x -> true
      | _ -> false

    let is_const = function
      | Const d -> true
      | _ -> false

    let unvar = function
      | Var x -> x
      | Const _ -> raise (Invalid_argument "unvar is undefined for Consts")
      | App _ -> raise (Invalid_argument "unvar is undefined for Apps")

    let unconst = function
      | Var _ -> raise (Invalid_argument "unconst is undefined for Vars")
      | App _ -> raise (Invalid_argument "unconst is undefined for Apps")
      | Const c -> c

    let rec fv_list = function
      | [] -> []
      | Const c :: trms -> fv_list trms
      | Var x :: trms -> x :: fv_list trms
      | App (_, trms) :: trms' -> fv_list trms @ fv_list trms'

    let rec fn_list = function
      | [] -> []
      | Const c :: trms -> fn_list trms
      | Var x :: trms -> fn_list trms
      | App (f, trms) :: trms' -> f :: fn_list (trms @ trms')

    let rec equal t t' = match t, t' with
      | Var x, Var x' -> String.equal x x'
      | Const d, Const d' -> Dom.equal d d'
      | App (f, ts), App (f', ts') ->
         String.equal f f' &&
           (match List.map2 ts ts' ~f:equal with
            | Ok b -> List.for_all b (fun x -> x)
            | Unequal_lengths -> false)
      | _ -> false

    let rec to_string = function
      | Var x -> Printf.sprintf "Var %s" x
      | Const d -> Printf.sprintf "Const %s" (Dom.to_string d)
      | App (f, ts) -> Printf.sprintf "App %s(%s)" f (String.concat ~sep:", " (List.map ts ~f:to_string))

    let rec value_to_string = function
      | Var x -> Printf.sprintf "%s" x
      | Const d -> Printf.sprintf "%s" (Dom.to_string d)
      | App (f, ts) -> Printf.sprintf "%s(%s)" f (String.concat ~sep:", " (List.map ts ~f:value_to_string))

    let rec list_to_string trms = String.concat ~sep:", " (List.map trms ~f:value_to_string)

    let filter_vars = List.filter_map ~f:(function Var x -> Some x | _ -> None)

    let rec reorder l = function
      | [] -> l
      | h::t when not (List.mem l (Var h) ~equal) -> reorder l t
      | h::t -> (Var h) :: (reorder (List.filter l (fun x -> not (equal x (Var h)))) t)

    let rec subst v = function
      | Var x -> (match Map.find v x with
                  | None -> Var x
                  | Some trm -> trm)
      | Const d -> Const d
      | App (f, ts) -> App (f, List.map ~f:(subst v) ts)

    let rec substs v = List.map ~f:(subst v)

  end

  include T
  include Comparator.Make(T)

end

module EnfType = struct

  type t = Cau | NCau | SCau | Sup | CauSup | Obs [@@deriving compare, sexp_of, hash, equal]

  let neg = function
    | Cau
      | NCau
      | SCau -> Sup
    | Sup    -> Cau 
    | CauSup -> CauSup
    | Obs    -> Obs

  let to_int = function
    | Cau    -> 1
    | NCau   -> 2
    | SCau   -> 3
    | Sup    -> 4
    | CauSup -> 5
    | Obs    -> 0

  let to_string = function
    | Cau    -> "Cau"
    | NCau   -> "NCau"
    | SCau   -> "SCau"
    | Sup    -> "Sup"
    | CauSup -> "CauSup"
    | Obs    -> "Obs"

  let meet a b = match a, b with
    | _, _ when a == b -> a
    | Obs, x | x, Obs -> x
    | Cau, NCau | NCau, Cau
      | Cau, SCau | SCau, Cau -> Cau
    | _, _ -> CauSup

  let join a b = match a, b with
    | _, _ when a == b -> a
    | CauSup, x | x, CauSup -> x
    | Cau, NCau | NCau, Cau -> NCau
    | Cau, SCau | SCau, Cau -> SCau
    | _, _ -> Obs

  let leq a b = (meet a b) == a
  let geq a b = (join a b) == a

  let is_causable = function
    | CauSup | Cau | NCau | SCau -> true
    | _ -> false

  let is_suppressable = function
    | CauSup | Sup -> true
    | _ -> false

end

let tilde_tp_event_name = "~tp"
let tick_event_name = "tick"
let tp_event_name = "tp"
let ts_event_name = "ts"


module Sig = struct

  type pred_kind = Trace | Predicate | External | Builtin | Let [@@deriving compare, sexp_of, hash, equal]

  type pred = { arity: int;
                arg_ttts: (string * Ctxt.ttt) list;
                enftype: EnfType.t;
                rank: int;
                kind: pred_kind } [@@deriving compare, sexp_of, hash]

  let string_of_pred name pred =
    let f acc (var, tt) = acc ^ "," ^ var ^ ":" ^ (Ctxt.ttt_to_string tt) in
    Printf.sprintf "%s(%s)" name
      (String.drop_prefix (List.fold pred.arg_ttts ~init:"" ~f) 1)


  type ty = Pred of pred | Func of Funcs.t (*[@@deriving compare, sexp_of, hash]*)

  let string_of_ty name = function
    | Pred pred -> string_of_pred name pred
    | Func func -> Funcs.to_string name func

  let arity = function
    | Pred pred -> pred.arity
    | Func func -> func.arity

  let arg_ttts = function
    | Pred pred -> pred.arg_ttts
    | Func func -> func.arg_ttts

  let unpred = function
    | Pred pred -> pred
    | Func func -> raise (Invalid_argument "unpred is undefined for Funs")

  let unfunc = function
    | Func func -> func
    | Pred pred -> raise (Invalid_argument "unfunc is undefined for Preds")

  type elt = string * ty (*[@@deriving compare, sexp_of, hash]*)

  type t = (string, ty) Hashtbl.t

  let table: t =
    let table = Hashtbl.of_alist_exn (module String)
                  (List.map Funcs.builtins ~f:(fun (k,v) -> (k, Func v))) in
    Hashtbl.add_exn table ~key:tilde_tp_event_name
      ~data:(Pred { arity = 0; arg_ttts = []; enftype = Cau; rank = 0; kind = Trace });
    Hashtbl.add_exn table ~key:tick_event_name
      ~data:(Pred { arity = 0; arg_ttts = []; enftype = Obs; rank = 0; kind = Trace });
    Hashtbl.add_exn table ~key:tp_event_name
      ~data:(Pred { arity = 1; arg_ttts = [("i", TConst TInt)]; enftype = Obs; rank = 0; kind = Builtin });
    Hashtbl.add_exn table ~key:ts_event_name
      ~data:(Pred { arity = 1; arg_ttts = [("t", TConst TInt)]; enftype = Obs; rank = 0; kind = Builtin });
    table

  let add_letpred p_name arg_ttts =
    Hashtbl.add_exn table ~key:p_name
      ~data:(Pred { arity = List.length arg_ttts; arg_ttts; enftype = Obs; rank = 0; kind = Let })

  let add_pred p_name arg_tts enftype rank kind =
    if equal_pred_kind kind Predicate then
      Hashtbl.add_exn table ~key:p_name
        ~data:(Func { arity = List.length arg_tts;
                      arg_ttts = List.map arg_tts ~f:(fun (x, tt) -> x, Ctxt.TConst tt);
                      ret_ttt = TConst TInt;
                      kind = External; strict = false })
    else
      Hashtbl.add_exn table ~key:p_name
        ~data:(Pred { arity = List.length arg_tts;
                      arg_ttts = List.map arg_tts ~f:(fun (x, tt) -> x, Ctxt.TConst tt);
                      enftype; rank; kind })

  let add_func f_name arg_tts ret_tt kind strict =
    Hashtbl.add_exn table ~key:f_name ~data:(
        Func { arity = List.length arg_tts;
               arg_ttts = List.map arg_tts ~f:(fun (x, tt) -> x, Ctxt.TConst tt);
               ret_ttt = Ctxt.TConst ret_tt;
               kind; strict })

  let update_enftype name enftype =
    Hashtbl.update table name ~f:(fun (Some (Pred x)) -> Pred { x with enftype })

  let vars_of_pred name = List.map (unpred (Hashtbl.find_exn table name)).arg_ttts ~f:fst

  let arg_ttts_of_pred name = List.map (unpred (Hashtbl.find_exn table name)).arg_ttts ~f:snd

  let arg_ttts_of_func name = List.map (unfunc (Hashtbl.find_exn table name)).arg_ttts ~f:snd

  let ret_ttt_of_func name = (unfunc (Hashtbl.find_exn table name)).ret_ttt

  let enftype_of_pred name = (unpred (Hashtbl.find_exn table name)).enftype

  let rank_of_pred name = (unpred (Hashtbl.find_exn table name)).rank

  let kind_of_pred name = (unpred (Hashtbl.find_exn table name)).kind

  let func ff ds =
    let the_func = unfunc (Hashtbl.find_exn table ff) in
    match the_func.kind with
    | Builtin f -> f ds
    | External -> Funcs.Python.call ff ds (Ctxt.unconst the_func.ret_ttt)

  let print_table () =
    Hashtbl.iteri table ~f:(fun ~key:n ~data:ps -> Stdio.printf "%s\n" (string_of_ty n ps))

  let rec eval (v: Etc.valuation) = function
    | Term.Var x ->
       (match Map.find v x with
        | Some d -> Term.Const d
        | None -> Var x)
    | Const c -> Const c
    | App (ff, trms) ->
       (*Stdio.printf "eval(App(%s, %s), %s)\n" ff (Term.list_to_string trms) (Etc.valuation_to_string v);*)
       let trms = List.map trms ~f:(eval v) in
       let f = function Term.Const d -> Some d | c -> None in
       match Option.all (List.map trms ~f) with
       | Some ds -> (*Stdio.printf "=%s\n" (Dom.to_string(func ff ds));*)
                    Const (func ff ds)
       | None -> (*Stdio.printf "=%s\n" (Term.to_string(App (ff, trms)));*)
                 App (ff, trms)

  let rec set_eval (v: Setc.valuation) = function
    | Term.Var x ->
       (match Map.find v x with
        | Some (Setc.Finite s) -> Setc.Finite (Set.map (module Term) s ~f:Term.const)
        | Some (Setc.Complement s) -> Setc.Complement (Set.map (module Term) s ~f:Term.const)
        | None -> Setc.singleton (module Term) (Var x))
    | Const c -> Setc.singleton (module Term) (Const c)
    | App (ff, trms) ->
       let trms' = List.map trms ~f:(set_eval v) in
       let f trms =
         match Option.all (List.map trms ~f:(function Term.Const d -> Some d | _ -> None)) with
         | Some ds -> Term.Const (func ff ds)
         | None -> Term.App (ff, trms) in
       match Option.all (List.map trms' ~f:(function Setc.Finite s -> Some s | _ -> None)) with
       | Some ds -> let prod   = Etc.cartesian (List.map ds ~f:Set.elements) in
                    let trms'' = List.map prod ~f in
                    Setc.Finite (Set.of_list (module Term) trms'')
       | None -> Setc.singleton (module Term) (Term.App (ff, trms))

  let rec var_tt_of_term x tt = function
    | Term.Var x' when String.equal x x' -> Some tt
    | Var x' -> None
    | App (f, trms) -> var_tt_of_terms x (arg_ttts_of_func f) trms
    | Const c -> None
  and var_tt_of_terms x tts trms =
    List.find_map (List.zip_exn tts trms)
      ~f:(fun (tt, trm) -> var_tt_of_term x tt trm)

  let is_strict trms =
    List.for_all (Term.fn_list trms) ~f:(fun name -> (unfunc (Hashtbl.find_exn table name)).strict)

  let check_const (types: Ctxt.t) c (ttt: Ctxt.ttt) : Ctxt.t * Ctxt.ttt =
    Ctxt.type_const c ttt types

  let check_var (types: Ctxt.t) v (ttt: Ctxt.ttt) : Ctxt.t * Ctxt.ttt =
    Ctxt.type_var v ttt types

  let rec check_app (types: Ctxt.t) f trms (ttt: Ctxt.ttt) : Ctxt.t * Ctxt.ttt =
    let arg_ttts, ret_ttt = arg_ttts_of_func f, ret_ttt_of_func f in
    let types, (ret_ttt :: arg_ttts) =
      Ctxt.convert_with_fresh_ttts types (ret_ttt :: arg_ttts) in
    let types, ret_var = Ctxt.fresh_var types in
    (*print_endline ("check_app(" ^ ret_var ^ ", " ^ f ^ ")");*)
    let types, _ = Ctxt.type_var ret_var ret_ttt types in
    let types, _ =
      List.fold2_exn trms arg_ttts ~init:(types, [])
        ~f:(fun (types, trms) trm tt -> let types, trm' = check_term types tt trm in
                                        (types, trms @ [trm'])) in
    let types, ret_ttt = check_var types ret_var ttt in
    types, ret_ttt

  and check_term (types: Ctxt.t) (ttt: Ctxt.ttt) trm : Ctxt.t * Ctxt.ttt =
    match trm with
    | Term.Var x    -> check_var types x ttt
    | Const c       -> check_const types c ttt
    | App (f, trms) -> check_app types f trms ttt

  and check_terms (types: Ctxt.t) p_name trms : Ctxt.t * Ctxt.ttt list =
    let sig_pred = Hashtbl.find_exn table p_name in
    if List.length trms = arity sig_pred then
      let ttts = arg_ttts_of_pred p_name in
      List.fold2_exn trms ttts ~init:(types, [])
        ~f:(fun (types, ttts) trm ttt -> let types, ttt = check_term types ttt trm in
                                         (types, ttts @ [ttt]))
    else raise (Invalid_argument (
                    Printf.sprintf "arity of %s is %d" p_name (arity sig_pred)))

  let tt_of_term_exn (types: Ctxt.t) trm : Dom.tt =
    let types, new_ttt = Ctxt.fresh_ttt types in
    let types, ttt = check_term types new_ttt trm in
    match ttt with
    | Ctxt.TConst tt -> tt
    | Ctxt.TVar _ -> raise (Invalid_argument (
                    Printf.sprintf "cannot determine concrete type for %s" (Term.to_string trm)))

end

module Lbl = struct

  module S = struct
    type t = (string, String.comparator_witness) Set.t
    let equal = Set.equal 
    let compare = Set.compare_direct 
    let sexp_of_t s = Sexp.List (List.map (Set.elements s) ~f:(fun x -> Sexp.Atom x))
    let empty = Set.empty (module String)
    let is_empty = Set.is_empty
    let mem = Set.mem
    let filter = Set.filter
    let singleton = Set.singleton (module String)
    let of_list = Set.of_list (module String)
    let length = Set.length
    let elements = Set.elements
    let to_string s =
      Printf.sprintf "{%s}" (String.concat ~sep:", " (elements s))
  end

  module T = struct
    
    type t =
      | LVar  of string
      | LEx   of string
      | LAll  of string
      | LClos of string * Term.t list * S.t [@@deriving equal, compare, sexp_of]

    let var s = LVar s
    let ex s = LEx s
    let all s = LAll s
    let clos s terms vars = LClos (s, terms, vars)

    let is_var = function
      | LVar _ -> true
      | _ -> false

    let term = function
      | LVar s -> Term.Var s
      | LClos (f, ts, v) -> App (f, ts)

    let of_term = function
      | Term.Var s -> LVar s
      | App (f, ts) -> LClos (f, ts, S.empty)

    let to_string = function
      | LVar x -> Printf.sprintf "LVar %s" x
      | LEx x -> Printf.sprintf "LEx %s" x
      | LAll x -> Printf.sprintf "LAll %s" x
      | LClos (f, ts, v) ->
         Printf.sprintf "LClos %s(%s; [%s])"
           f (String.concat ~sep:", " (List.map ts ~f:Term.to_string)) (S.to_string v)

    let to_string_list lbls =
      String.concat ~sep:", " (List.map ~f:to_string lbls)

    let rec fv = function
      | LVar s -> S.singleton s
      | LClos (f, ts, vars) ->
         S.filter (S.of_list (Term.fv_list ts)) ~f:(fun x -> not (S.mem vars x))

    let quantify ~forall x = function
      | LVar x' when String.equal x x' ->
         if forall then LAll x' else LEx x'
      | LClos (f, ts, vars) as lbl ->
         let fvs = fv lbl in
         (if S.mem fvs x then
            LClos (f, ts, Set.add vars x)
          else
            LClos (f, ts, vars))
      | lbl -> lbl

    let quantify_list ~forall x lbls =
      List.map lbls ~f:(quantify ~forall x)

    let rec unquantify_list x =
      let rec unquantify_list2 = function
        | [] -> []
        | (LAll x' as lbl) :: terms | (LEx x' as lbl) :: terms when String.equal x x'
          -> lbl :: terms
        | LClos (f, ts, vars) :: terms
          -> LClos (f, ts, Set.remove vars x) :: unquantify_list2 terms
        | lbl :: terms
          -> lbl :: unquantify_list2 terms in
      function
      | [] -> []
      | LAll x' :: terms | LEx x' :: terms when String.equal x x' ->
         LVar x' :: (unquantify_list2 terms)
      | lbl :: terms -> lbl :: (unquantify_list x terms)


    let rec eval (v: Etc.valuation) = function
      | LVar s when Map.mem v s -> Term.Const (Map.find_exn v s)
      | LVar s -> Var s
      | LClos (f, ts, _) ->
         let aux = function | `Left y | `Right y | `Both (y, _) -> Some y in
         Sig.eval v (App (f, ts))
      | _ -> assert false

  end

  include T
  include Comparator.Make(T)
  
end

