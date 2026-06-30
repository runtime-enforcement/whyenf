open Base
open MFOTL_lib

(* ------------------------------------------------------------------ *)
(* Per-SCC SMT incompatibility check.                                   *)
(*                                                                      *)
(* For each event E in an SCC that is *both* caused (by some clauses)    *)
(* and suppressed (by others), enforceability requires the causing and   *)
(* suppressing conditions to be mutually incompatible *on the same        *)
(* event instance*.  For each (cause-clause c, suppress-clause d) we ask  *)
(* Z3 whether                                                            *)
(*     trigger_c  ∧  trigger_d  ∧  (args_c = args_d)                     *)
(* is satisfiable.  If UNSAT for every pair → E is fine.  If SAT for      *)
(* some pair → a genuine cause/suppress conflict (reported).             *)
(*                                                                      *)
(* The Z3 encoding is a SOUND OVER-APPROXIMATION of the real semantics:  *)
(* unknown constructs (temporal operators, quantifiers, aggregations,    *)
(* lets) become fresh free booleans, so the encoded formula has *at      *)
(* least* the models of the real one.  Hence an encoded-UNSAT implies a   *)
(* real-UNSAT — we only ever accept (declare "incompatible") when truly   *)
(* sure.  Only events from strictly-upstream SCCs are shared between the  *)
(* two triggers (same uninterpreted symbol); same/downstream events get   *)
(* side-private symbols so they cannot spuriously cancel.                *)
(* ------------------------------------------------------------------ *)

module TF      = Tyformula
module Clause  = Nformula.Clause
module Effect  = Nformula.Effect
module ES      = Splitting.EventSplit

type conflict = {
  event        : string;
  cause_clause : int;
  supp_clause  : int;
}

let ctx = lazy (Z3.mk_context [ ("model", "false"); ("proof", "false") ])

let int_sort  () = Z3.Arithmetic.Integer.mk_sort (Lazy.force ctx)
let real_sort () = Z3.Arithmetic.Real.mk_sort    (Lazy.force ctx)
let str_sort  () = Z3.Seq.mk_string_sort         (Lazy.force ctx)
let bool_sort () = Z3.Boolean.mk_sort            (Lazy.force ctx)

let sort_of_tt = function
  | Dom.TInt   -> int_sort ()
  | Dom.TFloat -> real_sort ()
  | Dom.TStr   -> str_sort ()

(* Best-effort result type of a term (for sorting Z3 symbols). *)
let rec tt_of_term (t : Tterm.t) : Dom.tt =
  match t.trm with
  | Var (_, tt)          -> tt
  | Const (Dom.Int _)    -> Dom.TInt
  | Const (Dom.Str _)    -> Dom.TStr
  | Const (Dom.Float _)  -> Dom.TFloat
  | App (f, args)        -> tt_of_func f args
  | _                    -> Dom.TInt
and tt_of_func f args =
  match f with
  | "eq" | "neq" | "lt" | "leq" | "gt" | "geq" | "feq" | "seq" | "not"
  | "add" | "sub" | "mul" | "div" | "pow" | "usub" -> Dom.TInt
  | "fadd" | "fsub" | "fmul" | "fdiv" | "fpow"      -> Dom.TFloat
  | "conc" | "substr"                               -> Dom.TStr
  | _ -> (match args with a :: _ -> tt_of_term a | [] -> Dom.TInt)

(* Mutable per-check encoder environment. *)
type env = {
  c        : Z3.context;
  vars     : (string, Z3.Expr.expr) Hashtbl.t;
  preds    : (string, Z3.FuncDecl.func_decl) Hashtbl.t;
  funs     : (string, Z3.FuncDecl.func_decl) Hashtbl.t;
  upstream : (string, String.comparator_witness) Set.t;
  mutable fresh : int;
}

let fresh_bool env =
  env.fresh <- env.fresh + 1;
  Z3.Boolean.mk_const_s env.c (Printf.sprintf "__op%d" env.fresh)

let const_of_dom env (d : Dom.t) : Z3.Expr.expr =
  match d with
  | Dom.Int i   -> Z3.Arithmetic.Integer.mk_numeral_i env.c i
  | Dom.Float f -> Z3.Arithmetic.Real.mk_numeral_s env.c (Float.to_string f)
  | Dom.Str s   -> Z3.Seq.mk_string env.c s

let zero env = Z3.Arithmetic.Integer.mk_numeral_i env.c 0
let one  env = Z3.Arithmetic.Integer.mk_numeral_i env.c 1
let bool_to_int env b = Z3.Boolean.mk_ite env.c b (one env) (zero env)

(* Encode a term to a Z3 expression (sorts: Int/Real/String). *)
let rec enc_term env ~side (t : Tterm.t) : Z3.Expr.expr =
  match t.trm with
  | Var (name, tt) ->
    let key = side ^ "$" ^ name in
    Hashtbl.find_or_add env.vars key
      ~default:(fun () -> Z3.Expr.mk_const_s env.c key (sort_of_tt tt))
  | Const d -> const_of_dom env d
  | App (f, args) -> enc_app env ~side f args
  | _ -> (* Unop/Binop/Proj/Record should not survive typing; be safe *)
    Z3.Expr.mk_const_s env.c
      (let k = env.fresh in env.fresh <- k + 1; Printf.sprintf "__t%d" k)
      (int_sort ())

and enc_app env ~side f args : Z3.Expr.expr =
  let e = enc_term env ~side in
  let bin g = match args with [a; b] -> g (e a) (e b) | _ -> fresh_bool env in
  let rel mk = match args with
    | [a; b] -> bool_to_int env (mk (e a) (e b))
    | _ -> zero env in
  match f with
  | "add" -> bin (fun a b -> Z3.Arithmetic.mk_add env.c [a; b])
  | "sub" -> bin (fun a b -> Z3.Arithmetic.mk_sub env.c [a; b])
  | "mul" -> bin (fun a b -> Z3.Arithmetic.mk_mul env.c [a; b])
  | "div" -> bin (fun a b -> Z3.Arithmetic.mk_div env.c a b)
  | "usub" -> (match args with [a] -> Z3.Arithmetic.mk_unary_minus env.c (e a) | _ -> zero env)
  | "fadd" -> bin (fun a b -> Z3.Arithmetic.mk_add env.c [a; b])
  | "fsub" -> bin (fun a b -> Z3.Arithmetic.mk_sub env.c [a; b])
  | "fmul" -> bin (fun a b -> Z3.Arithmetic.mk_mul env.c [a; b])
  | "fdiv" -> bin (fun a b -> Z3.Arithmetic.mk_div env.c a b)
  | "eq" | "feq" | "seq" -> rel (fun a b -> Z3.Boolean.mk_eq env.c a b)
  | "neq" -> rel (fun a b -> Z3.Boolean.mk_not env.c (Z3.Boolean.mk_eq env.c a b))
  | "lt"  -> rel (fun a b -> Z3.Arithmetic.mk_lt env.c a b)
  | "leq" -> rel (fun a b -> Z3.Arithmetic.mk_le env.c a b)
  | "gt"  -> rel (fun a b -> Z3.Arithmetic.mk_gt env.c a b)
  | "geq" -> rel (fun a b -> Z3.Arithmetic.mk_ge env.c a b)
  | "not" -> (match args with
      | [a] -> bool_to_int env (Z3.Boolean.mk_eq env.c (e a) (zero env))
      | _ -> zero env)
  | _ ->
    (* uninterpreted function symbol, sorted by inferred arg/return types *)
    let dom = List.map args ~f:(fun a -> sort_of_tt (tt_of_term a)) in
    let ret = sort_of_tt (tt_of_func f args) in
    let key = Printf.sprintf "fn$%s/%d" f (List.length args) in
    let fd = Hashtbl.find_or_add env.funs key
        ~default:(fun () ->
            Z3.FuncDecl.mk_func_decl_s env.c key dom ret) in
    Z3.FuncDecl.apply fd (List.map args ~f:e)

(* Encode a (sub)formula to a Z3 Bool.  [side] tags clause-private symbols. *)
let rec enc_form env ~side (f : TF.t) : Z3.Expr.expr =
  match f.form with
  | TT -> Z3.Boolean.mk_true env.c
  | FF -> Z3.Boolean.mk_false env.c
  | EqConst (t, d) ->
    Z3.Boolean.mk_eq env.c (enc_term env ~side t) (const_of_dom env d)
  | Predicate (name, args) | Predicate' (name, args, _) ->
    enc_atom env ~side name args
  | Neg g -> Z3.Boolean.mk_not env.c (enc_form env ~side g)
  | And (_, gs) -> Z3.Boolean.mk_and env.c (List.map gs ~f:(enc_form env ~side))
  | Or  (_, gs) -> Z3.Boolean.mk_or  env.c (List.map gs ~f:(enc_form env ~side))
  | Imp (_, g, h) ->
    Z3.Boolean.mk_implies env.c (enc_form env ~side g) (enc_form env ~side h)
  | Type (g, _) | Label (_, g) -> enc_form env ~side g
  (* over-approximate everything else by a fresh free boolean *)
  | Exists _ | Forall _
  | Prev _ | Next _ | Once _ | Eventually _ | Historically _ | Always _
  | Since _ | Until _ | Let _ | Let' _ | Agg _ -> fresh_bool env

and enc_atom env ~side name args : Z3.Expr.expr =
  (* upstream events are shared across the two triggers; everything else is
     clause-private so the two sides cannot spuriously correlate. *)
  let sym = if Set.mem env.upstream name then "ev$" ^ name
    else "ev$" ^ side ^ "$" ^ name in
  let key = Printf.sprintf "%s/%d" sym (List.length args) in
  let dom = List.map args ~f:(fun a -> sort_of_tt (tt_of_term a)) in
  let fd = Hashtbl.find_or_add env.preds key
      ~default:(fun () -> Z3.FuncDecl.mk_func_decl_s env.c key dom (bool_sort ())) in
  Z3.FuncDecl.apply fd (List.map args ~f:(enc_term env ~side))

(* All (action, args) effects on event [ev] in clause [c]. *)
let effects_on (ev : string) (c : Clause.t) : (ES.action * Tterm.t list) list =
  List.filter_map c.Clause.effects ~f:(fun eff ->
      match eff with
      | Effect.Cau (r, a) | Effect.EventuallyCau (_, r, a) | Effect.NextCau (_, r, a)
        when String.equal r ev -> Some (ES.Cau, a)
      | Effect.Sup (r, a) | Effect.EventuallySup (_, r, a) | Effect.NextSup (_, r, a)
        when String.equal r ev -> Some (ES.Sup, a)
      | _ -> None)

(* Is (cause_trigger ∧ supp_trigger ∧ cause_args = supp_args) satisfiable? *)
let pair_satisfiable ~upstream (cause : Clause.t) (cargs : Tterm.t list)
    (supp : Clause.t) (sargs : Tterm.t list) : bool =
  let c = Lazy.force ctx in
  let env = { c;
              vars  = Hashtbl.create (module String);
              preds = Hashtbl.create (module String);
              funs  = Hashtbl.create (module String);
              upstream; fresh = 0 } in
  let tc = enc_form env ~side:"c" (Nformula.Trigger.to_formula true cause.trigger) in
  let td = enc_form env ~side:"s" (Nformula.Trigger.to_formula true supp.trigger) in
  let eqs =
    match List.zip cargs sargs with
    | Ok pairs ->
      List.map pairs ~f:(fun (a, b) ->
          Z3.Boolean.mk_eq c (enc_term env ~side:"c" a) (enc_term env ~side:"s" b))
    | Unequal_lengths -> [] in
  let solver = Z3.Solver.mk_solver c None in
  Z3.Solver.add solver (tc :: td :: eqs);
  match Z3.Solver.check solver [] with
  | Z3.Solver.UNSATISFIABLE -> false
  | Z3.Solver.SATISFIABLE | Z3.Solver.UNKNOWN -> true   (* conservative *)

(* Run the check over every SCC of the EDG.  Returns the list of conflicts
   (empty ⇒ all cause/suppress conditions are provably incompatible). *)
let run (edg : Edg.t) : conflict list =
  let upstream_by_scc = Edg.upstream_events_by_scc edg in
  let conflicts = ref [] in
  for s = 0 to edg.Edg.scc_count - 1 do
    let upstream =
      Option.value (Hashtbl.find upstream_by_scc s) ~default:(Set.empty (module String)) in
    let events = List.map (Edg.scc_members edg s) ~f:(fun v -> edg.Edg.nodes.(v)) in
    List.iter events ~f:(fun ev ->
        (* clauses that cause / suppress ev (with the targeted arg list) *)
        let causes = ref [] and supps = ref [] in
        Array.iteri edg.Edg.clauses ~f:(fun k c ->
            List.iter (effects_on ev c) ~f:(fun (act, args) ->
                match act with
                | ES.Cau -> causes := (k, c, args) :: !causes
                | ES.Sup -> supps := (k, c, args) :: !supps));
        List.iter !causes ~f:(fun (kc, cc, cargs) ->
            List.iter !supps ~f:(fun (kd, cd, sargs) ->
                if pair_satisfiable ~upstream cc cargs cd sargs then
                  conflicts := { event = ev; cause_clause = kc; supp_clause = kd }
                               :: !conflicts)))
  done;
  List.rev !conflicts

let conflicts_to_string (cs : conflict list) : string =
  String.concat ~sep:"\n"
    (List.map cs ~f:(fun c ->
         Printf.sprintf
           "  event %s: clause #%d may cause it while clause #%d may suppress it \
            under a *compatible* condition (cause/suppress not provably exclusive)"
           c.event c.cause_clause c.supp_clause))
