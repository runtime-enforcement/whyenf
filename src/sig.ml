open Base

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm
module Ctxt = Ctxt.Make(Dom)
module Valuation = ITerm.Valuation

let tilde_tp_event_name = "~tp"
let tick_event_name = "tick"
let tp_event_name = "tp"
let ts_event_name = "ts"

type term = Term.t

type pred_kind = Trace | Predicate | External | Builtin | Let [@@deriving compare, sexp_of, hash, equal]

type pred = { arity: int;
              arg_ttts: (string * Ctxt.ttt) list;
              enftype: Enftype.t;
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
  | Func _ -> raise (Errors.SigError "unpred is undefined for Funs")

let unfunc = function
  | Func func -> func
  | Pred _ -> raise (Errors.SigError "unfunc is undefined for Preds")

type elt = string * ty (*[@@deriving compare, sexp_of, hash]*)

type t = (string, ty) Hashtbl.t

let table: t =
  let table = Hashtbl.of_alist_exn (module String)
                (List.map Funcs.builtins ~f:(fun (k,v) -> (k, Func v))) in
  Hashtbl.add_exn table ~key:tilde_tp_event_name
    ~data:(Pred { arity = 0; arg_ttts = []; enftype = Enftype.cau; rank = 0; kind = Trace });
  Hashtbl.add_exn table ~key:tick_event_name
    ~data:(Pred { arity = 0; arg_ttts = []; enftype = Enftype.obs; rank = 0; kind = Trace });
  Hashtbl.add_exn table ~key:tp_event_name
    ~data:(Pred { arity = 1; arg_ttts = [("i", TConst TInt)]; enftype = Enftype.obs; rank = 0; kind = Builtin });
  Hashtbl.add_exn table ~key:ts_event_name
    ~data:(Pred { arity = 1; arg_ttts = [("t", TConst TInt)]; enftype = Enftype.obs; rank = 0; kind = Builtin });
  table

let pred_enftype_map () =
  Hashtbl.fold table ~init:(Map.empty (module String))
    ~f:(fun ~key ~data ->
      match data with
      | Pred pred -> Map.add_exn ~key ~data:(pred.enftype, List.init pred.arity ~f:(fun x -> x))
      | _ -> fun m -> m)

let add_letpred p_name arg_ttts =
  Hashtbl.add_exn table ~key:p_name
    ~data:(Pred { arity = List.length arg_ttts; arg_ttts; enftype = Enftype.obs; rank = 0; kind = Let })

let add_letpred_empty p_name = add_letpred p_name []

let add_pred p_name arg_tts enftype rank kind =
  (*print_endline (p_name ^ " " ^ Enftype.to_string enftype);*)
  if equal_pred_kind kind Predicate then
    Hashtbl.add_exn table ~key:p_name
      ~data:(Func { arity = List.length arg_tts;
                    arg_ttts = List.map arg_tts ~f:(fun (x, tt) -> x, Ctxt.TConst tt);
                    ret_ttts = [TConst TInt];
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
             ret_ttts = [Ctxt.TConst ret_tt];
             kind; strict })

let add_tfunc f_name arg_tts ret_tts =
  Hashtbl.add_exn table ~key:f_name ~data:(
      Func { arity = List.length arg_tts;
             arg_ttts = List.map arg_tts ~f:(fun (x, tt) -> x, Ctxt.TConst tt);
             ret_ttts = List.map ~f:(fun x -> Ctxt.TConst x) ret_tts;
             kind = Table; strict = false })

let update_enftype name enftype =
  if Hashtbl.mem table name then
    Hashtbl.update table name ~f:(
        function
        | Some (Pred x) -> Pred { x with enftype }
        | _ ->
           raise (Errors.SigError
                    (Printf.sprintf "cannot update enftype for %s: event does not exist" name)))

let vars_of_pred name = List.map (unpred (Hashtbl.find_exn table name)).arg_ttts ~f:fst

let arg_ttts_of_pred name = List.map (unpred (Hashtbl.find_exn table name)).arg_ttts ~f:snd

let arg_ttts_of_func name = List.map (unfunc (Hashtbl.find_exn table name)).arg_ttts ~f:snd

let ret_ttts_of_func name = (unfunc (Hashtbl.find_exn table name)).ret_ttts

let enftype_of_pred name = (unpred (Hashtbl.find_exn table name)).enftype

let rank_of_pred name = (unpred (Hashtbl.find_exn table name)).rank

let kind_of_pred name = (unpred (Hashtbl.find_exn table name)).kind

let mem name = Hashtbl.mem table name

let func ff ds =
  let the_func = unfunc (Hashtbl.find_exn table ff) in
  match the_func.kind with
  | Builtin f -> f ds
  | External -> Funcs.Python.call ff ds (Ctxt.unconst (List.hd_exn the_func.ret_ttts))
  | _ -> raise (Errors.SigError
                  (Printf.sprintf "cannot find function %s: not a function" ff))

let tfunc ff dss =
  let the_func = unfunc (Hashtbl.find_exn table ff) in
  match the_func.kind with
  | Table -> Funcs.Python.tcall ff dss (List.map ~f:Ctxt.unconst the_func.ret_ttts)
  | _ -> raise (Errors.SigError
                  (Printf.sprintf "cannot find table function %s: not a table function" ff))

let print_table () =
  Hashtbl.iteri table ~f:(fun ~key:n ~data:ps -> Stdio.printf "%s\n" (string_of_ty n ps))

let rec normalize (t: Term.t) : Term.t =
  let trm = match t.trm with
  | Term.Var x -> Term.Var x
  | Const c -> Const c
  | App (ff, trms) ->
    let trms = List.map ~f:normalize trms in
    let f (t: Term.t) = match t.trm with
      | Term.Const d -> Some d
      | _ -> None in
    (match Option.all (List.map trms ~f) with
     | Some ds ->
       Const (func ff ds)
     | None ->
       App (ff, trms))
  | _ -> raise (Errors.SigError (Printf.sprintf "cannot normalize %s" (Term.to_string t)))
  in { t with trm }

let rec normalize_list (t: Term.t list) : Term.t list =
  List.map ~f:normalize t

let rec teval (lbls: Lbl.t array) (v: Valuation.t) (t: Term.t) : Term.t =
  let trm = match t.trm with
  | Term.Var x ->
    (let i_opt =
       try Some (ITerm.of_var lbls x)
       with _ -> None in
     match i_opt with
     | None -> Term.Var x
     | Some i -> match Map.find v i with
       | Some d -> Const d
       | None -> Var x)
  | Const c -> Const c
  | App (ff, trms) ->
     let trms = List.map trms ~f:(teval lbls v) in
     let f (t: Term.t) = match t.trm with
       | Term.Const d -> Some d
       | _ -> None in
     (match Option.all (List.map trms ~f) with
     | Some ds ->
        Const (func ff ds)
     | None ->
        App (ff, trms))
  | _ -> raise (Errors.SigError (Printf.sprintf "cannot evaluate %s" (Term.to_string t)))
  in { t with trm }

let eval_lbl (lbls: Lbl.t array) (v: Valuation.t) (lbl: Lbl.t) : Term.t =
  teval lbls v (Lbl.term lbl)

let eval_lbl_to_lbl (lbls: Lbl.t array) (v: Valuation.t) (lbl: Lbl.t) : Lbl.t option =
  match lbl with
  | LAll _ | LEx _ -> Some lbl
  | LVar x -> (match Map.find v (ITerm.of_var lbls x) with Some v -> None | _ -> Some (LVar x))
  | LClos (ff, trms) ->
    (match (teval lbls v (Term.make_dummy (Term.App (ff, trms)))).trm with
     | Const _ -> None
     | App (ff, trms) -> Some (LClos (ff, trms))
     | _ -> assert false)

let rec eval (lbls: Lbl.t array) (v: Valuation.t) (t: ITerm.t) : ITerm.t =
  (*Stdio.printf "Sig.eval ([%s], %s, %s)\n" (String.concat ~sep:", " (List.map ~f:Lbl.to_string lbls)) (Valuation.to_string v) (ITerm.to_string t);*)
  match t.trm with
  | ITerm.Var i ->
    ITerm.init lbls (eval_lbl lbls v (Array.get lbls i))
  | Const c -> ITerm.make_dummy (Const c)

(*
let rec set_eval (v: Setc.valuation) (t: Term.t) =
  match t.trm with
  | Term.Var x ->
     (match Map.find v x with
      | Some (Setc.Finite s) -> Setc.Finite (Set.map (module Term) s ~f:(fun c -> Term.make_dummy (Term.const c)))
      | Some (Setc.Complement s) -> Setc.Complement (Set.map (module Term) s ~f:(fun c -> Term.make_dummy (Term.const c)))
      | None -> Setc.singleton (module Term) t)
  | Const _ -> Setc.singleton (module Term) t
  | App (ff, trms) ->
     let trms' = List.map trms ~f:(set_eval v) in
     let f trms =
       match Option.all (List.map trms ~f:(fun t -> match Term.(t.trm) with Term.Const d -> Some d | _ -> None)) with
       | Some ds -> { t with trm = Term.Const (func ff ds) }
       | None -> t in
     (match Option.all (List.map trms' ~f:(function Setc.Finite s -> Some s | _ -> None)) with
     | Some ds -> let prod   = Etc.cartesian (List.map ds ~f:Set.elements) in
                  let trms'' = List.map prod ~f in
                  Setc.Finite (Set.of_list (module Term) trms'')
     | None -> Setc.singleton (module Term) t)
  | _ -> raise (Errors.SigError (Printf.sprintf "cannot evaluate %s" (Term.to_string t)))
*)

let strict_of_func name =
  (unfunc (Hashtbl.find_exn table name)).strict

let check_const (types: Ctxt.t) c (ttt: Ctxt.ttt) : Ctxt.t * Ctxt.ttt =
  Ctxt.type_const c ttt types

let check_var (types: Ctxt.t) v (ttt: Ctxt.ttt) : Ctxt.t * Ctxt.ttt =
  Ctxt.type_var v ttt types

let rec check_app (types: Ctxt.t) f trms (ttt: Ctxt.ttt) : Ctxt.t * Ctxt.ttt =
  let arg_ttts, ret_ttt = arg_ttts_of_func f, ret_ttts_of_func f in
  let types, arg_ttts = Ctxt.convert_with_fresh_ttts types (ret_ttt @ arg_ttts) in
  let ret_ttt, arg_ttts = List.hd_exn arg_ttts, List.tl_exn arg_ttts in
  let types, ret_var = Ctxt.fresh_var types in
  (*print_endline ("check_app(" ^ ret_var ^ ", " ^ f ^ ")");*)
  let types, _ = Ctxt.type_var ret_var ret_ttt types in
  let types, _ =
    List.fold2_exn trms arg_ttts ~init:(types, [])
      ~f:(fun (types, trms) trm tt -> let types, trm' = check_term types tt trm in
                                      (types, trms @ [trm'])) in
  let types, ret_ttt = check_var types ret_var ttt in
  types, ret_ttt

and check_term (types: Ctxt.t) (ttt: Ctxt.ttt) (t: Term.t) : Ctxt.t * Ctxt.ttt =
  match t.trm with
  | Term.Var x    -> check_var types x ttt
  | Const c       -> check_const types c ttt
  | App (f, trms) -> check_app types f trms ttt
  | _ -> raise (Errors.SigError (Printf.sprintf "cannot check %s" (Term.to_string t)))

and check_terms (types: Ctxt.t) p_name trms : Ctxt.t * Ctxt.ttt list =
  let sig_pred = Hashtbl.find_exn table p_name in
  if List.length trms = arity sig_pred then
    let ttts = arg_ttts_of_pred p_name in
    List.fold2_exn trms ttts ~init:(types, [])
      ~f:(fun (types, ttts) trm ttt -> let types, ttt = check_term types ttt trm in
                                       (types, ttts @ [ttt]))
  else raise (Errors.SigError (
                  Printf.sprintf "arity of %s is %d" p_name (arity sig_pred)))

and check_terms_ttts (types: Ctxt.t) p_name (ttts: Ctxt.ttt list) trms : Ctxt.t * Ctxt.ttt list =
  let arity = List.length ttts in
  if List.length trms = arity then
    List.fold2_exn trms ttts ~init:(types, [])
      ~f:(fun (types, ttts) trm ttt -> let types, ttt = check_term types ttt trm in
                                       (types, ttts @ [ttt]))
  else raise (Errors.SigError (
                  Printf.sprintf "arity of let-bound predicate %s is %d" p_name arity))

let tt_of_term_exn (types: Ctxt.t) trm : Dom.tt =
  let types, new_ttt = Ctxt.fresh_ttt types in
  let _, ttt = check_term types new_ttt trm in
  match ttt with
  | Ctxt.TConst tt -> tt
  | Ctxt.TVar _ -> raise (Errors.SigError (
                              Printf.sprintf "cannot determine concrete type for %s" (Term.to_string trm)))
