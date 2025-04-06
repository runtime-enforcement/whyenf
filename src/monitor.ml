open Base
open Expl
open Option

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm

let print_debug s =
  if !Global.debug then
    Stdio.printf "\027[34m[monitor] %s\027[0m\n" s
  else ()

open Etc

module TS = struct

  type 'a t = { tp : timepoint; ts : timestamp ; data : 'a }

  let tp te = te.tp
  let ts te = te.ts
  let data te = te.data

  let map f te = { te with data = f te.data }

  let map2 f te te' = { te with data = f te.data te'.data }

  let map_list f tes =
    let tps, tss, datas = List.map tes ~f:tp, List.map tes ~f:ts, List.map tes ~f:data in
    { tp = List.hd_exn tps; ts = List.hd_exn tss; data = f datas }


  let make tp ts data = { tp; ts; data }

  let to_string f te =
    Printf.sprintf "%s@(%d, %s)" (f te.data) te.tp (Time.to_string te.ts)

end

module Buf2 = struct

  type ('a, 'b) t = 'a list * 'b list

  let add xs ys (l1, l2) = (l1 @ xs, l2 @ ys)

  let rec take f = function
    | [], ys -> ([], ([], ys))
    | xs, [] -> ([], (xs, []))
    | x::xs, y::ys -> let (zs, buf2') = take f (xs, ys) in
                      ((f x y)::zs, buf2')

  let map f1 f2 (l1, l2) = (List.map ~f:f1 l1, List.map ~f:f2 l2)

end

module Bufn = struct

  type 'a t = 'a list list

  let empty n = List.init n ~f:(fun _ -> [])

  let add xss ls = List.map2_exn xss ls ~f:(@)

  let rec take f xss =
    match Option.all (List.map xss ~f:List.hd) with
    | None -> ([], xss)
    | Some heads -> let tails = List.map xss ~f:List.tl_exn in
                    let (zs, buf2') = take f tails in
                    ((f heads)::zs, buf2')

  let map (f: 'a -> 'b) (ls: 'a t) : 'b t = List.map ~f:(List.map ~f) ls

end

module Buft = struct

  type ('a, 'b) t = 'a list * 'b list
  
  let to_string f g (xs, ys) =
    Printf.sprintf "Buft(%s, %s)"
      (Etc.list_to_string "" (fun _ -> f) xs)
      (Etc.list_to_string "" (fun _ -> g) ys)

  let add (xs, ys) tes =
    (xs @ List.map tes ~f:TS.data, ys @ List.map tes ~f:(fun te -> (te.ts, te.tp)))

  let rec another_take f = function
    | [], ys  -> ([], ([], ys))
    | xs, []  -> ([], (xs, []))
    | xs, [y] -> ([], (xs, [y]))
    | x::xs, y::y'::ys -> let (zs, buft') = another_take f (xs, y'::ys) in
                          ((f x y y')::zs, buft')
  let rec take f z = function
    | [], ys -> (z, [], ys)
    | xs, [] -> (z, xs, [])
    | x::xs, (a,b)::ys -> take f (f x a b z) (xs, ys)

  let rec get = function
    | [], [] -> None, ([], [])
    | x::xs, (a,b)::ys -> Some (x, (a, b)), (xs, ys)

  let map f1 f2 (l1, l2) = (List.map ~f:f1 l1, List.map ~f:f2 l2)

end

module Buf2t = struct

  type ('a, 'b, 'c) t = ('a list * 'b list) * 'c list

  let to_string f g h ((xs, ys), zs) =
    Printf.sprintf "Buf2t(%s, %s, %s)"
      (Etc.list_to_string "" (fun _ -> f) xs)
      (Etc.list_to_string "" (fun _ -> g) ys)
      (Etc.list_to_string "" (fun _ -> h) zs)

  let add ((xs, xs'), ys) tes tes' =
    let tp_last_opt  = Option.map ~f:TS.tp (List.last tes) in
    let tp_last_opt' = Option.map ~f:TS.tp (List.last tes') in
    match tp_last_opt, tp_last_opt' with
    | Some tp_last, Some tp_last' when tp_last >= tp_last' -> 
       ((xs @ List.map tes ~f:TS.data, xs' @ List.map tes' ~f:TS.data), ys @ List.map tes ~f:(fun te -> (te.ts, te.tp)))
    | Some tp_last, Some tp_last' ->
       ((xs @ List.map tes ~f:TS.data, xs' @ List.map tes' ~f:TS.data), ys @ List.map tes' ~f:(fun te -> (te.ts, te.tp)))
    | Some tp_last, None ->
       ((xs @ List.map tes ~f:TS.data, []), ys @ List.map tes ~f:(fun te -> (te.ts, te.tp)))
    | None, Some tp_last' ->
       (([], xs' @ List.map tes' ~f:TS.data), ys @ List.map tes' ~f:(fun te -> (te.ts, te.tp)))
    | None, None ->
       (([], []), [])

  let rec take f w (xs, ys) zs = match (xs, ys), zs with
    | ([], ys), zs -> (w, (([], ys), zs))
    | (xs, []), zs -> (w, ((xs, []), zs))
    | (xs, ys), [] -> (w, ((xs, ys), []))
    | (x::xs, y::ys), (a,b)::zs -> take f (f x y a b w) (xs, ys) zs

  let rec get = function
    | (x::xs, x'::xs'), (a,b)::ys -> Some ((x, x'), (a, b)), ((xs, xs'), ys)
    | (xs, xs'), ys -> None, ((xs, xs'), ys)

  let map f1 f2 f3 ((l1, l2), l3) = ((List.map ~f:f1 l1, List.map ~f:f2 l2), List.map ~f:f3 l3)

end

type polarity = POS | NEG [@@deriving compare, sexp_of, hash, equal]

let neg_polarity = function
  | POS -> NEG
  | NEG -> POS

type alpha_t = {
    alphas_in : Tdeque.t;
    alphas_out: Tdeque.t
  } [@@deriving compare, sexp_of, hash, equal]

type beta_alphas_t = {
    beta_alphas_in : Tdeque.t;
    beta_alphas_out: Tdeque.t
  } [@@deriving compare, sexp_of, hash, equal]

type alphas_beta_t = {
    not_alpha_in : Tdeque.t;
    not_alpha_out: Tdeque.t;
    beta_in  : Tdeque.t;
    beta_out : Tdeque.t
  } [@@deriving compare, sexp_of, hash, equal]

type binop_info = (bool Expl.t TS.t, bool Expl.t TS.t) Buf2.t

and nop_info = bool Expl.t TS.t Bufn.t

and prev_info = {
    first: bool;
    itv  : Interval.t;
    tstps: (timestamp * timepoint) list;
    buf  : bool Expl.t list
  }

and next_info = {
    itv       : Interval.t;
    tstps     : (timestamp * timepoint) list;
    tstps_todo: (timestamp * timepoint) list;
    buf       : bool Expl.t list
  }

and once_info = {
    oaux   : alpha_t Pdt.t;
    itv_in : Interval.t;
    itv_out: Interval.t option;
    buf    : (bool Expl.t, (timestamp * timepoint)) Buft.t;
    neg    : bool
  }

and eventually_info = {
    eaux      : alpha_t Pdt.t;
    itv_in    : Interval.t;
    itv_out   : Interval.t;
    tstps_todo: (timestamp * timepoint) list;
    buf       : (bool Expl.t, timestamp * timepoint) Buft.t;
    neg       : bool
  }

and historically_info = once_info

and always_info = eventually_info

and since_info = {
    saux   : beta_alphas_t Pdt.t;
    itv_in : Interval.t;
    itv_out: Interval.t option;
    buf    : (bool Expl.t, bool Expl.t, timestamp * timepoint) Buf2t.t
  }

and until_info = {
    uaux        : alphas_beta_t Pdt.t;
    itv_beta_in : Interval.t;
    itv_alpha_in: Interval.t;
    itv_out     : Interval.t;
    tstps_todo  : (timestamp * timepoint) list;
    buf         : (bool Expl.t, bool Expl.t, timestamp * timepoint) Buf2t.t
  }

and mf_core_t =
  | MTT
  | MFF
  | MEqConst      of Term.t * Dom.t
  | MPredicate    of string * Term.t list
  | MAgg          of string * Aggregation.op * Aggregation.op_fun * Term.t * string list * mf_t
  | MTop          of string list * string * Aggregation.op_tfun * Term.t list * string list * mf_t
  | MNeg          of mf_t
  | MAnd          of Side.t * mf_t list * nop_info
  | MOr           of Side.t * mf_t list * nop_info
  | MImp          of Side.t * mf_t * mf_t * binop_info
  | MExists       of string * Dom.tt * bool * mf_t
  | MForall       of string * Dom.tt * bool * mf_t
  | MPrev         of Interval.t * mf_t * prev_info
  | MNext         of Interval.t * mf_t * next_info
  | MENext        of Interval.t * timestamp option * mf_t
  | MOnce         of Interval.t * mf_t * once_info
  | MEventually   of Interval.t * mf_t * eventually_info
  | MEEventually  of Interval.t * timestamp option * mf_t
  | MHistorically of Interval.t * mf_t * historically_info
  | MAlways       of Interval.t * mf_t * always_info
  | MEAlways      of Interval.t * timestamp option * mf_t
  | MSince        of Side.t * Interval.t * mf_t * mf_t * since_info
  | MUntil        of Interval.t * mf_t * mf_t * until_info
  | MEUntil       of Side.t * Interval.t * timestamp option * mf_t * mf_t

and mf_t = {
    mf: mf_core_t;
    filter: Filter.t;
    events: (string, String.comparator_witness) Set.t option;
    obligations: (int, Int.comparator_witness) Set.t option;
    hash: int;
    lbls: Lbl.t list
  } 

and fo =
  | FFormula of mf_t * int * Etc.valuation
  | FInterval of timestamp * Interval.t * mf_t * int * Etc.valuation
  | FUntil of timestamp * Side.t * Interval.t * mf_t * mf_t * int * Etc.valuation
  | FAlways of timestamp * Interval.t * mf_t * int * Etc.valuation
  | FEventually of timestamp * Interval.t * mf_t * int * Etc.valuation

and fix =
  | FEvent of string * Term.t list * polarity * int
  | FOblig of fo * polarity

and fbool =
  | FTrue  of fix list
  | FFalse of fix list

let fix_is_oblig = function
  | FEvent _ -> false
  | FOblig _ -> true

let fix_is_event = function
  | FEvent _ -> true
  | FOblig _ -> false
  
let ts_i_to_string (ts, i) =
  match ts with
  | Some ts -> Printf.sprintf "(%s+%s)" (Time.to_string ts) (Interval.to_string i)
  | None -> Interval.to_string i

let rec value_to_string_rec l mf =
  match mf.mf with
  | MTT -> Printf.sprintf "⊤"
  | MFF -> Printf.sprintf "⊥"
  | MEqConst (trm, c) -> Printf.sprintf "%s = %s" (Term.value_to_string trm) (Dom.to_string c)
  | MPredicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | MAgg (s, op, _, x, y, f) -> Printf.sprintf (Etc.paren l (-1) "%s <- %s(%s; %s; %s)") s (Aggregation.op_to_string op) (Term.value_to_string x) (String.concat ~sep:", " y) (value_to_string_rec (-1) f)
  | MTop (s, op, _, x, y, f) -> Printf.sprintf (Etc.paren l (-1) "[%s] <- %s(%s; %s; %s)")
                                  (Etc.string_list_to_string s) op
                                  (Term.list_to_string x) (Etc.string_list_to_string y)
                                  (value_to_string_rec (-1) f)
  | MNeg f -> Printf.sprintf "¬%a" (fun _ -> value_to_string_rec 5) f
  | MAnd (_, fs, _) -> Printf.sprintf (Etc.paren l 4 "%s") (String.concat ~sep:"∧" (List.map fs ~f:(value_to_string_rec 4)))
  | MOr (_, fs, _) -> Printf.sprintf (Etc.paren l 3 "%s") (String.concat ~sep:"∨" (List.map fs ~f:(value_to_string_rec 4)))
  | MImp (_, f, g, _) -> Printf.sprintf (Etc.paren l 4 "%a → %a") (fun _ -> value_to_string_rec 4) f (fun _ -> value_to_string_rec 4) g
  | MExists (x, _, _, f) -> Printf.sprintf (Etc.paren l 5 "∃%s. %a") x (fun _ -> value_to_string_rec 5) f
  | MForall (x, _, _, f) -> Printf.sprintf (Etc.paren l 5 "∀%s. %a") x (fun _ -> value_to_string_rec 5) f
  | MPrev (i, f, _) -> Printf.sprintf (Etc.paren l 5 "●%a %a") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f
  | MNext (i, f, _) -> Printf.sprintf (Etc.paren l 5 "○%a %a") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f
  | MENext (i, ts, f) -> Printf.sprintf (Etc.paren l 5 "○*%a %a") (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) f
  | MOnce (i, f, _) -> Printf.sprintf (Etc.paren l 5 "⧫%a %a") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f
  | MEventually (i, f, _) -> Printf.sprintf (Etc.paren l 5 "◊%a %a") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f
  | MEEventually (i, ts, f) -> Printf.sprintf (Etc.paren l 5 "◊*%a %a") (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) f
  | MHistorically (i, f, _) -> Printf.sprintf (Etc.paren l 5 "■%a %a") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f
  | MAlways (i, f, _) -> Printf.sprintf (Etc.paren l 5 "□%a %a") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f
  | MEAlways (i, ts, f) -> Printf.sprintf (Etc.paren l 5 "□*%a %a") (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) f
  | MSince (_, i, f, g, _) -> Printf.sprintf (Etc.paren l 0 "%a S%a %a") (fun _ -> value_to_string_rec 5) f
                                (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) g
  | MUntil (i, f, g, _) -> Printf.sprintf (Etc.paren l 0 "%a U%a %a") (fun _ -> value_to_string_rec 5) f
                             (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) g
  | MEUntil (_, i, ts, f, g) -> Printf.sprintf (Etc.paren l 0 "%a U*%a %a") (fun _ -> value_to_string_rec 5) f
                                     (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) g

let value_to_string = value_to_string_rec 0

let polarity_to_string = function
  | POS -> "+"
  | NEG -> "-"

let rec fo_to_string = function
  | FFormula (f, h, v) ->
     Printf.sprintf "FFormula(%s, %d, %s)" (value_to_string f) h (Etc.valuation_to_string v)
  | FInterval (ts, i, mf, h, v) ->
     Printf.sprintf "FInterval(%s, %s, %s, %d, %s)"
       (Time.to_string ts) (Interval.to_string i) (value_to_string mf)
       h (Etc.valuation_to_string v)
  | FUntil (ts, s, i, mf, mg, h, v) ->
     Printf.sprintf "FUntil(%s, %s, %s, %s, %s, %d, %s)"
       (Time.to_string ts) (Side.to_string s)
       (Interval.to_string i) (value_to_string mf) (value_to_string mg)
       h (Etc.valuation_to_string v)
  | FAlways (ts, i, mf, h, v) ->
     Printf.sprintf "FAlways(%s, %s, %s, %d, %s)"
       (Time.to_string ts) (Interval.to_string i) (value_to_string mf)
       h (Etc.valuation_to_string v)
  | FEventually (ts, i, mf, h, v) ->
     Printf.sprintf "FEventually(%s, %s, %s, %d, %s)"
       (Time.to_string ts) (Interval.to_string i) (value_to_string mf)
       h (Etc.valuation_to_string v)

and fix_to_string = function
  | FEvent (e, trms, pol, _) -> Printf.sprintf "(%s(%s))%s" e
                                  (String.concat ~sep:", " (List.map ~f:Term.value_to_string trms))
                                  (polarity_to_string pol)
  | FOblig (fo, pol) -> Printf.sprintf "(%s)%s" (fo_to_string fo) (polarity_to_string pol)

and fbool_to_string = function
  | FTrue fix -> Printf.sprintf "⊤{%s}" (String.concat ~sep:"; " (List.map ~f:fix_to_string fix))
  | FFalse fix -> Printf.sprintf "⊥{%s}" (String.concat ~sep:"; " (List.map ~f:fix_to_string fix))

let fbool_of_bool = function
  | true -> FTrue []
  | false -> FFalse []

(*let corresp_proof tp pol _ fo =
  match pol with
  | POS -> FTrue [FOblig (fo, NEG)]
  | NEG -> FFalse [FOblig (fo, POS)]*)

let fbool_of_polarity = function
  | POS -> FTrue []
  | NEG -> FFalse []

let int_of_polarity = function
  | POS -> 1
  | NEG -> 0

let sat = function
  | FTrue _ -> true
  | FFalse _ -> false

let equal_fo k k' = match k, k' with
  | FFormula (_, h, v), FFormula (_, h', v') ->
     h = h' && Etc.equal_valuation v v'
  | FInterval (ts, i, _, h, v), FInterval (ts', i', _, h', v') ->
     Time.equal ts ts' && Interval.equal i i' && h = h' && Etc.equal_valuation v v'
  | FAlways (ts, i, _, h, v), FAlways (ts', i', _, h', v') ->
     Time.equal ts ts' && Interval.equal i i' && h = h' && Etc.equal_valuation v v'
  | FEventually (ts, i, _, h, v), FEventually (ts', i', _, h', v') ->
     Time.equal ts ts' && Interval.equal i i' && h = h' && Etc.equal_valuation v v'
  | FUntil (ts, s, i, _, _, h, v), FUntil (ts', s', i', _, _, h', v') ->
     Time.equal ts ts' && Side.equal s s' && Interval.equal i i' && h = h' && Etc.equal_valuation v v'
  | _ -> false

let compare_fo k k' = match k, k' with
  | FFormula (_, h, v), FFormula (_, h', v') ->
     Etc.lexicographic2 Int.compare Etc.compare_valuation (h, v) (h', v')
  | FFormula _, _ -> 1
  | _, FFormula _ -> -1
  | FInterval (ts, i, _, h, v), FInterval (ts', i', _, h', v') ->
     Etc.lexicographic4 Time.compare Interval.compare Int.compare Etc.compare_valuation
       (ts, i, h, v) (ts', i', h', v')
  | FInterval _, _ -> 1
  | _, FInterval _ -> -1
  | FAlways (ts, i, _, h, v), FAlways (ts', i', _, h', v') ->
     Etc.lexicographic4 Time.compare Interval.compare Int.compare Etc.compare_valuation
       (ts, i, h, v) (ts', i', h', v')
  | FAlways _, _ -> 1
  | _, FAlways _ -> -1
  | FEventually (ts, i, _, h, v), FEventually (ts', i', _, h', v') ->
     Etc.lexicographic4 Time.compare Interval.compare Int.compare Etc.compare_valuation
       (ts, i, h, v) (ts', i', h', v')
  | FEventually _, _ -> 1
  | _, FEventually _ -> -1
  | FUntil (ts, s, i, _, _, h, v), FUntil (ts', s', i', _, _, h', v') ->
     Etc.lexicographic5 Time.compare Side.compare Interval.compare Int.compare Etc.compare_valuation
       (ts, s, i, h, v) (ts', s', i', h', v')
  | FUntil _, _ -> -1

let equal_fix f f' = match f, f' with
  | FEvent (r, trms, pol, h), FEvent (r', trms', pol', h') ->
     h = h' && equal_polarity pol pol'
  | FOblig (fo, pol), FOblig (fo', pol') ->
     equal_fo fo fo' && equal_polarity pol pol'
  | _ -> false

let compare_fix f f' = match f, f' with
  | FEvent (r, trms, pol, h), FEvent (r', trms', pol', h') ->
     Etc.lexicographic2 Int.compare compare_polarity (h, pol) (h', pol')
  | FEvent _, _ -> 1
  | FOblig (fo, pol), FOblig (fo', pol') ->
     Etc.lexicographic2 compare_fo compare_polarity (fo, pol) (fo', pol')
  | FOblig _, _ -> -1

let equal_fbool b b' = match b, b' with
  | FTrue fs, FTrue fs'
    | FFalse fs, FFalse fs' ->
     (match List.for_all2 fs fs' equal_fix with
      | Base.List.Or_unequal_lengths.Ok b -> b
      | Base.List.Or_unequal_lengths.Unequal_lengths -> false)
  | _ -> false

let not_fbool = function
  | FTrue fix -> FFalse fix
  | FFalse fix -> FTrue fix


let and_fbool side b b' = match side, b, b' with
  | Side.R, FTrue fix,  FTrue fix'  -> FTrue  fix'
  | _,      FTrue fix,  FTrue fix'  -> FTrue  fix
  | _,      FTrue fix,  FFalse fix' -> FFalse fix'
  | _,      FFalse fix, FTrue fix'  -> FFalse fix
  | _,      FFalse fix, FFalse fix' -> FFalse fix
  (* FFalse (List.dedup_and_sort ~compare:compare_fix (fix @ fix'))*)
  | _ -> Stdio.printf "%s, %s, %s" (Side.to_string side) (fbool_to_string b) (fbool_to_string b');
         assert false

let and_fbools side bs = List.fold_left ~init:(List.hd_exn bs) ~f:(and_fbool side) (List.tl_exn bs)

let or_fbool side b b' = match side, b, b' with
  | _,      FTrue fix,  FTrue fix'  -> FTrue fix
  (*FTrue (List.dedup_and_sort ~compare:compare_fix (fix @ fix'))*)
  | _,      FTrue fix,  FFalse fix' -> FTrue fix
  | _,      FFalse fix, FTrue fix'  -> FTrue fix'
  | Side.R, FFalse fix, FFalse fix' -> FFalse fix'
  | _,      FFalse fix, FFalse fix' -> FFalse fix
  | _ -> assert false

let or_fbools side bs = List.fold_left ~init:(List.hd_exn bs) ~f:(or_fbool side) (List.tl_exn bs)

module Prev = struct

  type t = prev_info

  let init itv = { first = true; itv; tstps = []; buf = [] }

  let to_string aux =
    Printf.sprintf "{ first = %b; itv = %s; tstps = %s; buf = %s }"
      aux.first (Interval.to_string aux.itv)
      (Etc.list_to_string "" (fun _ (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.tstps)
      (Etc.list_to_string "" (fun _ -> Expl.to_string ~to_string:Bool.to_string) aux.buf)  

  let rec update (lbls : Lbl.t list) (aux : t) : t * bool Expl.t TS.t list =
    match aux.tstps, aux.buf with
    | [(ts, tp)], _ when aux.first ->
       { aux with first = false }, [TS.make tp ts (Pdt.Leaf false)]
    | (ts, tp) :: (ts', tp') :: tstps, buf_expl :: buf when Interval.diff_is_in ts ts' aux.itv ->
       let aux, bs = update lbls { aux with tstps = (ts', tp') :: tstps; buf } in
       aux, (TS.make tp ts buf_expl)::bs
    | (ts, tp) :: (ts', tp') :: tstps, buf_expl :: buf ->
       let aux, bs = update lbls { aux with tstps = (ts', tp') :: tstps; buf }  in
       aux, (TS.make tp ts (Pdt.Leaf false))::bs
    | _,  _ -> aux, []


  let map f aux = { aux with buf = List.map ~f aux.buf }

end

module Next = struct

  type t = next_info

  let init itv = { itv; tstps = []; tstps_todo = []; buf = [] }

  let to_string (aux: next_info) =
    Printf.sprintf "{ itv = %s; tstps = %s; tstps_todo = %s; buf = %s }"
      (Interval.to_string aux.itv)
      (Etc.list_to_string "" (fun _ (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.tstps)
      (Etc.list_to_string "" (fun _ (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.tstps_todo)
      (Etc.list_to_string "" (fun _ -> Expl.to_string ~to_string:Bool.to_string) aux.buf)

  let rec update (lbls : Lbl.t list) (aux : t) : t * bool Expl.t TS.t list = 
    match aux.tstps, aux.tstps_todo, aux.buf with
    | (ts', tp') :: tstps, (ts, tp) :: tstps_todo, buf_expl :: buf when tp' = tp + 1 ->
       let aux, bs = update lbls { aux with tstps = (ts', tp') :: tstps;
                                            tstps_todo = tstps_todo } in
       let b = TS.make tp ts (if Interval.diff_is_in ts ts' aux.itv
                              then buf_expl
                              else Pdt.Leaf false) in
       aux, b::bs
    | _ -> aux, []

  let map f aux = { aux with buf = List.map ~f aux.buf }

end

module Once = struct

  let equal_alpha_t_bool (oaux, b) (oaux', b') =
    equal_alpha_t oaux oaux' && Bool.equal b b'

  type t = once_info

  let init itv_in neg = { oaux    = Pdt.Leaf { alphas_in  = Tdeque.empty
                                             ; alphas_out = Tdeque.empty };
                          itv_in;
                          itv_out = Interval.out_left itv_in;
                          buf     = ([], []);
                          neg }
  let alpha_to_string =
    Pdt.to_string (fun o -> Printf.sprintf "{ alphas_in = %s; alphas_out = %s }"
                              (Tdeque.to_string o.alphas_in) (Tdeque.to_string o.alphas_out)) ""
  
  let to_string aux =
    Printf.sprintf "{ oaux = %s; itv_in = %s; itv_out = %s; buf = %s; neg = %b }"
      (alpha_to_string aux.oaux)
      (Interval.to_string aux.itv_in)
      (Etc.option_to_string Interval.to_string aux.itv_out)
      (Buft.to_string (Expl.to_string ~to_string:Bool.to_string) (fun (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.buf)
      aux.neg
  
  let rec update (lbls: Lbl.t list) (aux : t) : t * bool Expl.t TS.t list =
    let process (ts: timestamp) (tp: timepoint) (b: bool) (oaux : alpha_t) : alpha_t * bool =
      let alphas_out, alphas_in =
        match aux.itv_out with
        | Some itv_out -> 
           (* Insert timestamp into alphas_out *)
           let alphas_out = if Bool.equal aux.neg b
                            then Tdeque.enqueue_back oaux.alphas_out ts
                            else oaux.alphas_out in
           (* Move timestamps from alphas_out to alphas_in if they are outside of ts - i *)
           Tdeque.split_left alphas_out oaux.alphas_in ts itv_out 
        | None ->
           (* Insert timestamp into alphas_in *)
           let alphas_in = if Bool.equal aux.neg b && Option.is_none aux.itv_out
                           then Tdeque.enqueue_back oaux.alphas_in ts
                           else oaux.alphas_in in
           oaux.alphas_out, alphas_in
      in
      (* Remove timestamps from alphas_in when they are too old *)
      let alphas_in = Tdeque.clean_left alphas_in ts aux.itv_in in
      (* Return true iff alphas_in is not empty *)
      let b = not (Tdeque.is_empty alphas_in) in
      { oaux with alphas_in; alphas_out }, Bool.equal aux.neg b
    in
    match Buft.get aux.buf with
    | Some (expl_pdt, (ts, tp)), buf ->
       let oaux, b = Pdt.split_prod (Pdt.apply2_reduce equal_alpha_t_bool lbls (process ts tp)
                                       expl_pdt aux.oaux) in
       let aux = { aux with oaux; buf } in
       let aux, bs = update lbls aux in
       aux, (TS.make tp ts b)::bs
    | _ -> aux, []

  let approximate a b expl =
    (* Enforce b (expl is generally not enforceable) *)
    (or_fbool R expl (if Time.Span.is_zero a then b else FFalse []))

  let approximate_historically a b expl =
    (* Enforce b (expl is generally not enforceable) *)
    (and_fbool R expl (if Time.Span.is_zero a then b else FFalse []))

  let map f g (aux: t) =
    { aux with oaux = f aux.oaux; buf = Buft.map g (fun t -> t) aux.buf }
  
end

module Eventually = struct

  let equal_alpha_t_bool (eaux, b) (eaux', b') =
    equal_alpha_t eaux eaux' && Bool.equal b b'

  type t = eventually_info

  let init itv_in neg = { eaux       = Pdt.Leaf { alphas_in  = Tdeque.empty
                                            ; alphas_out = Tdeque.empty };
                          itv_in;
                          itv_out    = Option.value_exn (Interval.out_right itv_in);
                          tstps_todo = [];
                          buf        = ([], []);
                          neg }

  let alpha_to_string =
    Pdt.to_string (fun o -> Printf.sprintf "{ alphas_in = %s; alphas_out = %s }"
                              (Tdeque.to_string o.alphas_in) (Tdeque.to_string o.alphas_out)) ""

  let to_string aux =
    Printf.sprintf "{ eaux = %s; itv_in = %s; itv_out = %s; tstps_todo = %s; buf = %s; neg = %b }"
      (alpha_to_string aux.eaux)
      (Interval.to_string aux.itv_in)
      (Interval.to_string aux.itv_out)
      (Etc.list_to_string "" (fun _ (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.tstps_todo)
      (Buft.to_string (Expl.to_string ~to_string:Bool.to_string) (fun (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.buf)
      aux.neg
  
  let rec update (lbls: Lbl.t list) (aux : t) : t * bool Expl.t TS.t list =
    let process (ts: timestamp) (tp: timepoint) (eaux : alpha_t) : alpha_t * bool = 
      (* Move timestamps from alphas_out to alphas_in if they are outside of ts + i *)
      let alphas_out, alphas_in = Tdeque.split_right eaux.alphas_out eaux.alphas_in ts aux.itv_out in
      (* Remove timestamps from alphas_in when they are too old *)
      let alphas_in = Tdeque.clean_right alphas_in ts aux.itv_in in
      (* Return true iff alphas_in is not empty *)
      let b = not (Tdeque.is_empty alphas_in) in
      { eaux with alphas_in; alphas_out }, Bool.equal aux.neg b
    in
    let load1 ts tp b oaux =
      (* Insert timestamp into alphas_out *)
      let alphas_out = if Bool.equal aux.neg b
                       then Tdeque.enqueue_back oaux.alphas_out ts
                       else oaux.alphas_out in
      { oaux with alphas_out }
    in
    let rec load ?(ts_opt=None) (aux: eventually_info) =
      match Buft.get aux.buf with
      | Some (expl_pdt, (ts, tp)), buf ->
         let eaux = Pdt.apply2 lbls (load1 ts tp) expl_pdt aux.eaux in
         let aux = { aux with eaux; buf } in
         load ~ts_opt:(Some ts) aux
      | _ -> ts_opt, aux
    in
    let ts_opt, aux = load aux in
    match aux.tstps_todo, ts_opt with
    | (ts, tp)::tstps_todo, Some ts' when Interval.diff_right_of ts ts' aux.itv_in -> 
       let eaux, b = Pdt.split_prod (Pdt.apply1_reduce equal_alpha_t_bool lbls (process ts tp) aux.eaux) in
       let aux = { aux with eaux; tstps_todo } in
       let aux, bs = update lbls aux in
       aux, (TS.make tp ts b)::bs
    | _ -> aux, []

  let approximate ts ts' i b_next b_now =
    (* Enforce b_next for transparency *)
    (or_fbool L b_next (if Interval.diff_is_in ts ts' i then b_now else FFalse []))

  let approximate_always ts ts' i b_next b_now =
    (* Enforce b_next for transparency *)
    (and_fbool L b_next (if Interval.diff_is_in ts ts' i then b_now else FFalse []))
  
  let map f g (aux: t) =
    { aux with eaux = f aux.eaux; buf = Buft.map g (fun t -> t) aux.buf }
  
end

module Since = struct

  let equal_beta_alphas_t_bool (saux, b) (saux', b') =
    equal_beta_alphas_t saux saux' && Bool.equal b b'

  type t = since_info

  let init itv_in = { saux    = Pdt.Leaf { beta_alphas_in  = Tdeque.empty
                                         ; beta_alphas_out = Tdeque.empty };
                      itv_in;
                      itv_out = Interval.out_left itv_in;
                      buf     = (([], []), []) }
  
  let beta_alphas_to_string =
    Pdt.to_string
      (fun o -> Printf.sprintf "{ beta_alphas_in = %s; beta_alphas_out = %s }"
                  (Tdeque.to_string o.beta_alphas_in) (Tdeque.to_string o.beta_alphas_out)) ""

  let to_string aux =
    Printf.sprintf "{ saux = %s; itv_in = %s; itv_out = %s; buf = %s }"
      (beta_alphas_to_string aux.saux)
      (Interval.to_string aux.itv_in)
      (Etc.option_to_string Interval.to_string aux.itv_out)
      (Buf2t.to_string
         (Expl.to_string ~to_string:Bool.to_string) (Expl.to_string ~to_string:Bool.to_string)
         (fun (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.buf)
  
  let rec update (lbls: Lbl.t list) (aux : t) : t * bool Expl.t TS.t list =
    let process (ts: timestamp) (tp: timepoint) (b_alpha: bool) (b_beta: bool) (saux : beta_alphas_t) : beta_alphas_t * bool =
      let beta_alphas_out, beta_alphas_in =
        match aux.itv_out with
        | Some itv_out -> 
           (* Insert timestamp into beta_alphas_out *)
           let beta_alphas_out, beta_alphas_in = if b_alpha
                                                 then saux.beta_alphas_out, saux.beta_alphas_in
                                                 else Tdeque.empty, Tdeque.empty in
           let beta_alphas_out = if b_beta
                                 then Tdeque.enqueue_back beta_alphas_out ts
                                 else saux.beta_alphas_out in
           (* Move timestamps from beta_alphas_out to beta_alphas_in if they are outside of ts - i *)
           let beta_alphas_out, beta_alphas_in = Tdeque.split_left beta_alphas_out beta_alphas_in ts itv_out in
           beta_alphas_out, beta_alphas_in
        | None ->
           (* Interval starts at 0: insert timestamp directly into beta_alphas_in *)
           let beta_alphas_in = if b_alpha
                                then saux.beta_alphas_in
                                else Tdeque.empty in
           let beta_alphas_in = if b_beta
                                then Tdeque.enqueue_back beta_alphas_in ts
                                else beta_alphas_in in
           saux.beta_alphas_out, beta_alphas_in
      in
      (* Remove timestamps from beta_alphas_in when they are too old *)
      let beta_alphas_in = Tdeque.clean_left beta_alphas_in ts aux.itv_in in
      (* Return true iff beta_alphas_in is not empty *)
      let b = not (Tdeque.is_empty beta_alphas_in) in
      { saux with beta_alphas_in; beta_alphas_out }, b
    in
    match Buf2t.get aux.buf with
    | Some ((expl_alpha_pdt, expl_beta_pdt), (ts, tp)), buf ->
       let saux, b = Pdt.split_prod (Pdt.apply3_reduce equal_beta_alphas_t_bool lbls (process ts tp) expl_alpha_pdt expl_beta_pdt aux.saux) in
       let aux = { aux with saux; buf } in
       let aux, bs = update lbls aux in
       aux, (TS.make tp ts b)::bs
    | _ -> aux, []

  let approximate pol a b_alpha b_beta expl =
    (* Enforce b_beta or b_alpha (expl is generally not enforceable) *)
    match pol with
    | POS -> or_fbool R expl b_beta   (* only relevant side is R *)
    | NEG -> and_fbool R expl b_alpha (* only relevant side is L *)

  let map f g (aux: t) =
    { aux with saux = f aux.saux; buf = Buf2t.map g g (fun t -> t) aux.buf }
  
end

module Until = struct

  type t = until_info

  let beta_alphas_to_string =
    Pdt.to_string (fun o -> Printf.sprintf "{ not_alpha_in = %s; not_alpha_out = %s; beta_in = %s; beta_out = %s }"
                              (Tdeque.to_string o.not_alpha_in) (Tdeque.to_string o.not_alpha_out) (Tdeque.to_string o.beta_in) (Tdeque.to_string o.beta_out)) ""

  let to_string aux =
    Printf.sprintf "{ uaux = %s; itv_beta_in = %s; itv_alpha_in = %s; itv_out = %s; tstps_todo = %s; buf = %s }"
      (beta_alphas_to_string aux.uaux)
      (Interval.to_string aux.itv_beta_in)
      (Interval.to_string aux.itv_alpha_in)
      (Interval.to_string aux.itv_out)
      (Etc.list_to_string "" (fun _ (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.tstps_todo)
      (Buf2t.to_string
         (Expl.to_string ~to_string:Bool.to_string) (Expl.to_string ~to_string:Bool.to_string)
         (fun (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.buf)


  let init itv_beta_in = { uaux         = Pdt.Leaf { not_alpha_in  = Tdeque.empty
                                                   ; not_alpha_out = Tdeque.empty
                                                   ; beta_in   = Tdeque.empty
                                                   ; beta_out  = Tdeque.empty };
                           itv_beta_in;
                           itv_alpha_in = Interval.to_zero itv_beta_in;
                           itv_out      = Option.value_exn (Interval.out_right itv_beta_in);
                           tstps_todo   = [];
                           buf          = (([], []), []) }
  
  let rec update (lbls: Lbl.t list) (aux : t) : t * bool Expl.t TS.t list =
    let process (ts: timestamp) (tp: timepoint) (uaux : alphas_beta_t) : alphas_beta_t * bool = 
      (* Move timestamps from alpha_out to alpha_in if they are outside of ts + i *)
      let not_alpha_out, not_alpha_in = Tdeque.split_right uaux.not_alpha_out uaux.not_alpha_in ts aux.itv_out in
      (* Remove timestamps from alpha_in when they are too old *)
      let not_alpha_in = Tdeque.clean_right not_alpha_in ts aux.itv_alpha_in in
      (* Move timestamps from beta_out to beta_in if they are outside of ts + i *)
      let beta_out, beta_in = Tdeque.split_right uaux.beta_out uaux.beta_in ts aux.itv_out in
      (* Remove timestamps from beta_in when they are too old *)
      let beta_in = Tdeque.clean_right beta_in ts aux.itv_beta_in in
      let b = Tdeque.compute_until not_alpha_in beta_in in
      (* Return true iff alphas_in is not empty *)
      { uaux with not_alpha_in; not_alpha_out; beta_in; beta_out }, b
    in
    let load1 ts tp b_alpha b_beta uaux =
      (* Insert timestamp into alpha_out *)
      let not_alpha_out = if not b_alpha
                          then Tdeque.enqueue_back uaux.not_alpha_out ts
                          else uaux.not_alpha_out in
      (* Insert timestamp into beta_out *)
      let beta_out = if b_beta
                     then Tdeque.enqueue_back uaux.beta_out ts
                     else uaux.beta_out in
      { uaux with not_alpha_out; beta_out} 
    in
    let rec load ?(ts_opt=None) (uaux: until_info) =
      match Buf2t.get uaux.buf with
      | Some ((expl_alpha_pdt, expl_beta_pdt), (ts, tp)), buf ->
         let uaux = Pdt.apply3_reduce equal_alphas_beta_t lbls (load1 ts tp) expl_alpha_pdt expl_beta_pdt aux.uaux in
         let aux = { aux with uaux; buf } in
         load ~ts_opt:(Some ts) aux
      | _ -> ts_opt, aux
    in
    let ts_opt, aux = load aux in
    let rec loop (aux: until_info) = 
      match aux.tstps_todo, ts_opt with
      | (ts, tp)::tstps_todo, Some ts' when Interval.diff_right_of ts ts' aux.itv_beta_in ->
         let uaux, b = Pdt.split_prod (Pdt.apply1 lbls (process ts tp) aux.uaux) in
         let aux = { aux with uaux; tstps_todo } in
         let aux, bs = loop aux in
         aux, (TS.make tp ts b)::bs
      | _ -> aux, []
    in loop aux

  let approximate pol ts ts' s i b_next b_alpha b_beta =
    (* Enforce b_next and/or b_beta (for transparency) *)
    match pol, s with
    | POS, Side.LR
    | NEG, R ->
       (or_fbool L
          (and_fbool L b_next b_alpha)
          (if Interval.diff_is_in ts ts' i then b_beta else FFalse []))
    | POS, R ->
       (and_fbool L
          (or_fbool R (not_fbool b_alpha) b_next)
          (or_fbool R b_alpha (if Interval.diff_is_in ts ts' i then b_beta else FFalse [])))
    | _ -> assert false

  let map f g (aux: t) =
    { aux with uaux = f aux.uaux; buf = Buf2t.map g g (fun t -> t) aux.buf }

end


module MFormula = struct

  let empty_binop_info = ([], [])
  let empty_nop_info = Bufn.empty

  type core_t = mf_core_t and t = mf_t

  let subs mf = match mf.mf with
    | MTT | MFF | MEqConst _ | MPredicate _ -> []
    | MExists (_, _, _, f)
      | MForall (_, _, _, f) 
      | MNeg f
      | MPrev (_, f, _)
      | MOnce (_, f, _)
      | MHistorically (_, f, _)
      | MEventually (_, f, _)
      | MEEventually (_, _, f)
      | MAlways (_, f, _)
      | MEAlways (_, _, f)
      | MNext (_, f, _)
      | MENext (_, _, f)
      | MAgg (_, _, _, _, _, f)
      | MTop (_, _, _, _, _, f) -> [f]
    | MImp (_, f1, f2, _)
      | MSince (_, _, f1, f2, _)
      | MUntil (_, f1, f2, _)
      | MEUntil (_, _, _, f1, f2) -> [f1; f2]
    | MAnd (_, fs, _)
      | MOr (_, fs, _) -> fs

  let rec with_aux_to_string_rec l mf =
    match mf.mf with
    | MTT -> Printf.sprintf "⊤"
    | MFF -> Printf.sprintf "⊥"
    | MEqConst (trm, c) -> Printf.sprintf "%s = %s" (Term.value_to_string trm) (Dom.to_string c)
    | MPredicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
    | MAgg (s, op, _, x, y, f) -> Printf.sprintf (Etc.paren l (-1) "%s <- %s(%s; %s; %s)") s (Aggregation.op_to_string op) (Term.value_to_string x) (String.concat ~sep:", " y) (value_to_string_rec (-1) f)
    | MTop (s, op, _, x, y, f) -> Printf.sprintf (Etc.paren l (-1) "[%s] <- %s(%s; %s; %s)")
                                    (Etc.string_list_to_string s) op
                                    (Term.list_to_string x) (Etc.string_list_to_string y)
                                    (value_to_string_rec (-1) f)
    | MNeg f -> Printf.sprintf "¬%a" (fun _ -> value_to_string_rec 5) f
    | MAnd (_, fs, _) -> Printf.sprintf (Etc.paren l 4 "%s") (String.concat ~sep:"∧" (List.map fs ~f:(value_to_string_rec 4)))
    | MOr (_, fs, _) -> Printf.sprintf (Etc.paren l 3 "%s") (String.concat ~sep:"∨" (List.map fs ~f:(value_to_string_rec 4)))
    | MImp (_, f, g, _) -> Printf.sprintf (Etc.paren l 4 "%a → %a") (fun _ -> value_to_string_rec 4) f (fun _ -> value_to_string_rec 4) g
    | MExists (x, _, _, f) -> Printf.sprintf (Etc.paren l 5 "∃%s. %a") x (fun _ -> value_to_string_rec 5) f
    | MForall (x, _, _, f) -> Printf.sprintf (Etc.paren l 5 "∀%s. %a") x (fun _ -> value_to_string_rec 5) f
    | MPrev (i, f, aux) -> Printf.sprintf (Etc.paren l 5 "{ f = ●%a %a; aux = %a }") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f (fun _ -> Prev.to_string) aux
    | MNext (i, f, aux) -> Printf.sprintf (Etc.paren l 5 "{ f = ○%a %a; aux = %a }") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f (fun _ -> Next.to_string) aux
    | MENext (i, ts, f) -> Printf.sprintf (Etc.paren l 5 "○*%a %a") (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) f
    | MOnce (i, f, aux) -> Printf.sprintf (Etc.paren l 5 "{ f = ⧫%a %a; aux = %a }") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f (fun _ -> Once.to_string) aux
    | MEventually (i, f, aux) -> Printf.sprintf (Etc.paren l 5 "{ f = ◊%a %a; aux = %a }") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f (fun _ -> Eventually.to_string) aux
    | MEEventually (i, ts, f) -> Printf.sprintf (Etc.paren l 5 "◊*%a %a") (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) f
    | MHistorically (i, f, aux) -> Printf.sprintf (Etc.paren l 5 "{ f = ■%a %a; aux = %a }") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f (fun _ -> Once.to_string) aux
    | MAlways (i, f, aux) -> Printf.sprintf (Etc.paren l 5 "{ f = □%a %a; aux = %a }") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f (fun _ -> Eventually.to_string) aux
    | MEAlways (i, ts, f) -> Printf.sprintf (Etc.paren l 5 "□*%a %a") (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) f
    | MSince (_, i, f, g, aux) -> Printf.sprintf (Etc.paren l 0 "{ f = %a S%a %a; aux = %a }") (fun _ -> value_to_string_rec 5) f 
                                    (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) g
                                    (fun _ -> Since.to_string) aux
    | MUntil (i, f, g, aux) -> Printf.sprintf (Etc.paren l 0 "{ f = %a U%a %a; aux = %a }") (fun _ -> value_to_string_rec 5) f
                                 (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) g
                                 (fun _ -> Until.to_string) aux
    | MEUntil (_, i, ts, f, g) -> Printf.sprintf (Etc.paren l 0 "%a U*%a %a") (fun _ -> value_to_string_rec 5) f
                                       (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) g
  let with_aux_to_string = with_aux_to_string_rec 0

  (*    and t = { mf: core_t;
        filter: Filter.t;
        events: (string, String.comparator_witness) Set.t option;
        obligations: (int, Int.comparator_witness) Set.t option;
        hash: int;
        lbls: Lbl.t list
        }*)
  let rec to_string ?(l=0) mf =
    let n = "\n" ^ Etc.spaces (l*4) in
    Printf.sprintf  "%s{ mf = %s;%s  filter = %s;%s  events = %s;%s  obligations = %s;%s  hash = %d;%s  lbls = [%s];%s  subformulae = [%s] }"
      n
      (with_aux_to_string mf) n
      (Filter.to_string mf.filter) n
      (match mf.events with
       | None -> "None"
       | Some evs -> Printf.sprintf "[%s]" (String.concat ~sep:", " (Set.elements evs))) n
      (match mf.obligations with
       | None -> "None"
       | Some evs -> Printf.sprintf "[%s]" (String.concat ~sep:", "
                                              (List.map ~f:Int.to_string (Set.elements evs)))) n
      mf.hash n
      (Lbl.to_string_list mf.lbls) n
      (String.concat ~sep:";"
         (List.map ~f:(fun f -> Printf.sprintf "\n%s" (to_string ~l:(l+1) f)) (subs mf)))
  

  let rec core_op_to_string = function
    | MTT -> Printf.sprintf "⊤"
    | MFF -> Printf.sprintf "⊥"
    | MEqConst (_, _) -> Printf.sprintf "="
    | MPredicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
    | MAgg (s, op, _, x, y, _) -> Printf.sprintf "%s <- %s(%s; %s)" s
                                    (Aggregation.op_to_string op) (Term.to_string x)
                                    (Etc.string_list_to_string y)
    | MTop (s, op, _, x, y, _) -> Printf.sprintf "[%s] <- %s(%s; %s)"
                                    (Etc.string_list_to_string s) op
                                    (Term.list_to_string x) (Etc.string_list_to_string y)
    | MNeg _ -> Printf.sprintf "¬"
    | MAnd (_, _, _) -> Printf.sprintf "∧"
    | MOr (_, _, _) -> Printf.sprintf "∨"
    | MImp (_, _, _, _) -> Printf.sprintf "→"
    | MExists (x, _, _, _) -> Printf.sprintf "∃ %s." x
    | MForall (x, _, _, _) -> Printf.sprintf "∀ %s." x
    | MPrev (i, _, _) -> Printf.sprintf "●%s" (Interval.to_string i)
    | MNext (i, _, _) -> Printf.sprintf "○%s" (Interval.to_string i)
    | MENext (i, ts, _) -> Printf.sprintf "○*%s" (ts_i_to_string (ts, i))
    | MOnce (i, _, _) -> Printf.sprintf "⧫%s" (Interval.to_string i)
    | MEventually (i, _, _) -> Printf.sprintf "◊%s" (Interval.to_string i)
    | MEEventually (i, ts, _) -> Printf.sprintf "◊*%s" (ts_i_to_string (ts, i))
    | MHistorically (i, _, _) -> Printf.sprintf "■%s" (Interval.to_string i)
    | MAlways (i, _, _) -> Printf.sprintf "□%s" (Interval.to_string i)
    | MEAlways (i, ts, _) -> Printf.sprintf "□*%s" (ts_i_to_string (ts, i))
    | MSince (_, i, _, _, _) -> Printf.sprintf "S%s" (Interval.to_string i)
    | MUntil (i, _, _, _) -> Printf.sprintf "U%s" (Interval.to_string i)
    | MEUntil (_, i, ts, _, _) -> Printf.sprintf "U*%s" (ts_i_to_string (ts, i))

  and op_to_string mf = core_op_to_string mf.mf

  let side_to_string mf = match mf.mf with
    | MTT -> Printf.sprintf "N"
    | MFF -> Printf.sprintf "N"
    | MEqConst _ -> Printf.sprintf "N"
    | MPredicate _ -> Printf.sprintf "N"
    | MAgg _ -> Printf.sprintf "N"
    | MTop _ -> Printf.sprintf "N"
    | MNeg _ -> Printf.sprintf "N"
    | MAnd (s, _, _) -> Printf.sprintf "%s" (Side.to_string s)
    | MOr (s, _, _) -> Printf.sprintf "%s" (Side.to_string s)
    | MImp (s, _, _, _) -> Printf.sprintf "%s" (Side.to_string s)
    | MExists _ -> Printf.sprintf "N"
    | MForall _ -> Printf.sprintf "N"
    | MPrev _ -> Printf.sprintf "N"
    | MNext _ -> Printf.sprintf "N"
    | MENext _ -> Printf.sprintf "N"
    | MOnce _ -> Printf.sprintf "N"
    | MEventually _ -> Printf.sprintf "N"
    | MEEventually _ -> Printf.sprintf "N"
    | MHistorically _ -> Printf.sprintf "N"
    | MAlways _ -> Printf.sprintf "N"
    | MEAlways _ -> Printf.sprintf "N"
    | MSince (s, _, _, _, _) -> Printf.sprintf "%s" (Side.to_string s)
    | MUntil _ -> Printf.sprintf "N"
    | MEUntil (s, _, _, _, _) -> Printf.sprintf "%s" (Side.to_string s)

  let core_hash =
    let (+++) x y = x * 65599 + y in
    let rec ppp = function
      | [x; y] -> x.hash +++ y.hash
      | x :: ys -> x.hash +++ ppp ys
      | [] -> raise (Errors.MonitoringError "cannot apply ppp to less than two elements") in
    let list_hash f l = List.fold_left ~f:(+++) ~init:0 (List.map ~f l) in
    function
    | MTT -> String.hash "MTT"
    | MFF -> String.hash "MFF"
    | MEqConst (x, d) -> String.hash "MEqConst" +++ Term.hash x +++ Dom.hash d
    | MPredicate (e, t) ->
       (*print_endline "--core_hash";
         List.iter t ~f:(fun t -> print_endline (Int.to_string (Term.hash t)));*)
       String.hash "MPredicate" +++ String.hash e +++ list_hash Term.hash t
    | MAgg (s, op, _, x, y, f) ->
       String.hash "MAgg"
       +++ String.hash s +++ Aggregation.hash_op op +++ Term.hash x
       +++ list_hash String.hash y +++ f.hash
    | MTop (s, op, _, x, y, f) ->
       String.hash "MTop"
       +++ list_hash String.hash s +++ String.hash op
       +++ list_hash Term.hash x +++ list_hash String.hash y +++ f.hash
    | MNeg f ->
       String.hash "MNeg" +++ f.hash
    | MAnd (s, fs, _) ->
       String.hash "MAnd" +++ Side.hash s +++ ppp fs
    | MOr (s, fs, _) ->
       (*print_endline "--MOr ";
         print_endline ("hash('MOr')=" ^ Int.to_string (String.hash "MOr"));
         print_endline ("hash(s)=" ^ Int.to_string (Side.hash s));
         print_endline ("hash(f)=" ^ Int.to_string (f.hash));
         print_endline ("hash(g)=" ^ Int.to_string (g.hash));
         print_endline ("hash(MOr)=" ^ Int.to_string (String.hash "MOr" +++ Side.hash s +++ f.hash +++ g.hash));*)
       String.hash "MOr" +++ Side.hash s +++ ppp fs
    | MImp (s, f, g, _) ->
       String.hash "MImp" +++ Side.hash s +++ f.hash +++ g.hash
    | MExists (x, _, _, f) ->
       String.hash "MExists" +++ String.hash x +++ f.hash
    | MForall (x, _, _, f) ->
       String.hash "MForall" +++ String.hash x +++ f.hash
    | MPrev (i, f, _) ->
       String.hash "MPrev" +++ Interval.hash i +++ f.hash
    | MNext (i, f, _) ->
       String.hash "MNext" +++ Interval.hash i +++ f.hash
    | MENext (i, _, f) ->
       String.hash "MENext" +++ Interval.hash i +++ f.hash
    | MOnce (i, f, _) ->
       String.hash "MOnce" +++ Interval.hash i +++ f.hash
    | MEventually (i, f, _) ->
       String.hash "MEventually" +++ Interval.hash i +++ f.hash
    | MEEventually (i, _, f) ->
       String.hash "MEEventually" +++ Interval.hash i +++ f.hash
    | MHistorically (i, f, _) ->
       String.hash "MHistorically" +++ Interval.hash i +++ f.hash
    | MAlways (i, f, _) ->
       String.hash "MAlways" +++ Interval.hash i +++ f.hash
    | MEAlways (i, _, f) ->
       String.hash "MEAlways" +++ Interval.hash i +++ f.hash 
    | MSince (s, i, f, g, _) ->
       String.hash "MSince" +++ Side.hash s +++ Interval.hash i +++ f.hash +++ g.hash
    | MUntil (i, f, g, _) ->
       String.hash "MUntil" +++ Interval.hash i +++ f.hash +++ g.hash
    | MEUntil (s, i, _, f, g) ->
       String.hash "MEUntil" +++ Side.hash s +++ Interval.hash i +++ f.hash +++ g.hash

  (*and hash mf = core_hash mf.mf*)

  let rec set_events mf =
    let with_events mf events =
      { mf with events = Some events;
                obligations = Some (Set.empty (module Int)) } in
    let map1 f comb =
      let f = set_events f in
      { mf with mf          = comb f;
                events      = f.events;
                obligations = f.obligations } in
    let map2 f1 f2 comb =
      let f1 = set_events f1 in
      let f2 = set_events f2 in
      { mf with mf          = comb f1 f2;
                events      = Some (Set.union (Option.value_exn f1.events) (Option.value_exn f2.events));
                obligations = Some (Set.union (Option.value_exn f1.obligations) (Option.value_exn f2.obligations)) } in
    let mapn fs comb =
      let fs = List.map ~f:set_events fs in
      { mf with mf          = comb fs;
                events      = Some (Set.union_list (module String) (List.map ~f:(fun f -> Option.value_exn f.events) fs));
                obligations = Some (Set.union_list (module Int) (List.map ~f:(fun f -> Option.value_exn f.obligations) fs)) } in
    let add_hash mf =
      { mf with obligations = Some (Set.add (Option.value_exn mf.obligations) mf.hash) } in
    match mf.events with
    | Some _ -> mf
    | None ->
       match mf.mf with
       | MTT
         | MFF
         | MEqConst _ -> with_events mf (Set.empty (module String))
       | MPredicate (r, _) -> with_events mf (Set.singleton (module String) r)
       | MAgg (s, op, op_fun, x, y, f) -> map1 f (fun f -> MAgg (s, op, op_fun, x, y, f))
       | MTop (s, op, op_fun, x, y, f) -> map1 f (fun f -> MTop (s, op, op_fun, x, y, f))
       | MNeg f -> map1 f (fun f -> MNeg f)
       | MAnd (s, fs, inf) -> mapn fs (fun fs -> MAnd (s, fs, inf))
       | MOr (s, fs, inf) -> mapn fs (fun fs -> MOr (s, fs, inf))
       | MImp (s, f, g, inf) -> map2 f g (fun f g -> MImp (s, f, g, inf))
       | MExists (s, tt, b, f) -> map1 f (fun f -> MExists (s, tt, b, f))
       | MForall (s, tt, b, f) -> map1 f (fun f -> MForall (s, tt, b, f))
       | MPrev (i, f, inf) -> map1 f (fun f -> MPrev (i, f, inf))
       | MNext (i, f, inf) -> map1 f (fun f -> MNext (i, f, inf))
       | MENext (i, t_opt, f) -> add_hash (map1 f (fun f -> MENext (i, t_opt, f)))
       | MOnce (i, f, inf) -> map1 f (fun f -> MOnce (i, f, inf))
       | MEventually (i, f, inf) -> map1 f (fun f -> MEventually (i, f, inf))
       | MEEventually (i, t_opt, f) -> add_hash (map1 f (fun f -> MEEventually (i, t_opt, f)))
       | MHistorically (i, f, inf) -> map1 f (fun f -> MHistorically (i, f, inf))
       | MAlways (i, f, inf) -> map1 f (fun f -> MAlways (i, f, inf))
       | MEAlways (i, t_opt, f) -> add_hash (map1 f (fun f -> MEAlways (i, t_opt, f)))
       | MSince (s, i, f, g, inf) -> map2 f g (fun f g -> MSince (s, i, f, g, inf))
       | MUntil (i, f, g, inf) -> map2 f g (fun f g -> MUntil (i, f, g, inf))
       | MEUntil (s, i, t_opt, f, g) -> add_hash (map2 f g (fun f g -> MEUntil (s, i, t_opt, f, g)))

  let rec fv mf = match mf.mf with
    | MTT | MFF -> Set.empty (module String)
    | MEqConst (trm, _) -> Set.of_list (module String) (Term.fv_list [trm])
    | MPredicate (_, trms) -> Set.of_list (module String) (Term.fv_list trms)
    | MAgg (s, _, _, _, y, _) -> Set.of_list (module String) (s::y)
    | MTop (s, _, _, _, y, _) -> Set.of_list (module String) (s@y)
    | MNeg f -> fv f
    | MAnd (_, fs, _)
      | MOr (_, fs, _) -> Set.union_list (module String) (List.map fs ~f:fv)
    | MImp (_, f, g, _)
      | MSince (_, _, f, g, _)
      | MUntil (_, f, g, _)
      | MEUntil (_, _, _, f, g) -> Set.union (fv f) (fv g)
    | MExists (_, _, _, f)
      | MForall (_, _, _, f)
      | MPrev (_, f, _)
      | MNext (_, f, _)
      | MENext (_, _, f)
      | MOnce (_, f, _) 
      | MEventually (_, f, _)
      | MEEventually (_, _, f)
      | MHistorically (_, f, _)
      | MAlways (_, f, _)
      | MEAlways (_, _, f) -> fv f

  let rec set_lbls ?(fvs=[]) mf =
    let with_lbls mf lbls = { mf with lbls } in
    let order_lbls lbls fvs _ =
      let f (vars, quants, nonvars) = function
        | Lbl.LVar z when List.mem fvs z ~equal:String.equal -> (z :: vars, quants, nonvars)
        | LVar _ -> (vars, quants, nonvars)
        | LAll _ | LEx _ as t -> (vars, quants @ [t], nonvars)
        | t      -> (vars, quants, t :: nonvars) in
      let (vars, quants, nonvars) = List.fold_left lbls ~init:([], [], []) ~f in
      let vars = Etc.dedup ~equal:String.equal vars in
      let quants = Etc.dedup ~equal:Lbl.equal quants in
      let nonvars = Etc.dedup ~equal:Lbl.equal nonvars in
      let var_terms = List.map (Etc.reorder ~equal:String.equal vars fvs) ~f:Lbl.var in
      let nonvars = List.sort nonvars ~compare:Lbl.compare in
      (*print_endline (Printf.sprintf "order_lbls([%s], [%s]) = [%s]\n"
        (Lbl.to_string_list lbls)
        (String.concat ~sep:", " fvs)
        (Lbl.to_string_list (var_terms @ quants @ nonvars)));*)
      var_terms @ quants @ nonvars in
    let map1 fvs f comb flbls =
      let f = set_lbls ~fvs f in
      { mf with mf   = comb f;
                lbls = flbls f.lbls } in
    let map2 fvs f1 f2 comb flbls =
      let f1 = set_lbls ~fvs f1 in
      let f2 = set_lbls ~fvs f2 in
      { mf with mf   = comb f1 f2;
                lbls = flbls f1.lbls f2.lbls } in
    let mapn fvs fs comb flbls =
      let fs = List.map ~f:(set_lbls ~fvs) fs in
      { mf with mf   = comb fs;
                lbls = flbls (order_lbls
                                (List.concat (List.map ~f:(fun f -> f.lbls) fs)) fvs true) } in
    let id lbls = lbls in
    let id2 lbls1 lbls2 = order_lbls (lbls1 @ lbls2) fvs true in
    let imp lbls1 lbls2 = order_lbls ((List.map ~f:Lbl.exquant lbls1) @ lbls2) fvs true in
    let mf' = match mf.mf with
      | MTT | MFF -> with_lbls mf []
      | MAgg (s, op, op_fun, x, y, f) ->
         let y    = Etc.reorder_subset ~equal:String.equal y fvs in
         let sy   = Etc.reorder_subset ~equal:String.equal (s::y) fvs in
         let fvs' = Etc.reorder_subset ~equal:String.equal (Set.elements (fv f)) y in
         map1 fvs' f (fun f -> MAgg (s, op, op_fun, x, y, f)) (fun _ -> List.map ~f:Lbl.var sy)
      | MTop (s, op, op_fun, x, y, f) ->
         let y    = Etc.reorder_subset ~equal:String.equal y fvs in
         let sy   = Etc.reorder_subset ~equal:String.equal (s@y) fvs in
         let fvs' = Etc.reorder_subset ~equal:String.equal (Set.elements (fv f)) y in
         map1 fvs' f (fun f -> MTop (s, op, op_fun, x, y, f)) (fun _ -> List.map ~f:Lbl.var sy)
      | MEqConst (t, _) -> with_lbls mf [Lbl.of_term t]
      | MPredicate (_, ts) ->
         with_lbls mf (order_lbls (List.map (List.filter ~f:(fun t -> not (Term.is_const t)) ts)
                                     ~f:Lbl.of_term) fvs true)
      | MExists (x, tt, b, f) ->
         map1 (fvs @ [x]) f (fun f -> MExists (x, tt, b, f)) (Lbl.quantify_list ~forall:false x)
      | MForall (x, tt, b, f) ->
         map1 (fvs @ [x]) f (fun f -> MForall (x, tt, b, f)) (Lbl.quantify_list ~forall:true x)
      | MNeg f -> map1 fvs f (fun f -> MNeg f) (List.map ~f:Lbl.exquant)
      | MAnd (s, fs, inf) -> mapn fvs fs (fun fs -> MAnd (s, fs, inf)) id
      | MOr (s, fs, inf) -> mapn fvs fs (fun fs -> MOr (s, fs, inf)) id
      | MImp (s, f, g, inf) -> map2 fvs f g (fun f g -> MImp (s, f, g, inf)) imp
      | MPrev (i, f, inf) -> map1 fvs f (fun f -> MPrev (i, f, inf)) id
      | MNext (i, f, inf) -> map1 fvs f (fun f -> MNext (i, f, inf)) id
      | MENext (i, t_opt, f) -> map1 fvs f (fun f -> MENext (i, t_opt, f)) id
      | MOnce (i, f, inf) -> map1 fvs f (fun f -> MOnce (i, f, inf)) id
      | MEventually (i, f, inf) -> map1 fvs f (fun f -> MEventually (i, f, inf)) id
      | MEEventually (i, t_opt, f) -> map1 fvs f (fun f -> MEEventually (i, t_opt, f)) id
      | MHistorically (i, f, inf) -> map1 fvs f (fun f -> MHistorically (i, f, inf)) id
      | MAlways (i, f, inf) -> map1 fvs f (fun f -> MAlways (i, f, inf)) id
      | MEAlways (i, t_opt, f) -> map1 fvs f (fun f -> MEAlways (i, t_opt, f)) id
      | MSince (s, i, f, g, inf) -> map2 fvs f g (fun f g -> MSince (s, i, f, g, inf)) id2
      | MUntil (i, f, g, inf) -> map2 fvs f g (fun f g -> MUntil (i, f, g, inf)) id2
      | MEUntil (s, i, t_opt, f, g) -> map2 fvs f g (fun f g -> MEUntil (s, i, t_opt, f, g)) id2 in
    (*(match mf.mf with
      | MAgg _ -> 
      print_endline (Printf.sprintf "set_lbls([%s], %s)=%s\n\n\n"
      (String.concat ~sep:", " fvs)
      (to_string mf)
      (to_string mf'))
      | _ -> ());*)
    mf'


  let make mf filter =
    { mf; filter; events = None; obligations = None; hash = core_hash mf; lbls = [] }

  let set_make mf filter =
    set_lbls (set_events (make mf filter))

  let map_mf mf filter ?(exquant=false) f =
    let mf_mf = f mf in
    { mf          = mf_mf;
      filter;
      events      = mf.events;
      obligations = mf.obligations;
      hash        = core_hash mf_mf;
      lbls        = if exquant then List.map ~f:Lbl.exquant mf.lbls else mf.lbls }

  let map2_mf mf1 mf2 filter f =
    let mf_mf = f mf1 mf2 in
    { mf          = mf_mf;
      filter;
      events      = Option.map2 mf1.events mf2.events ~f:Set.union;
      obligations = Option.map2 mf1.obligations mf2.obligations ~f:Set.union;
      hash        = core_hash mf_mf;
      lbls        = Etc.dedup ~equal:Lbl.equal (mf1.lbls @ mf2.lbls) }

  let mapn_mf mfs filter f =
    let mf_mf = f mfs in
    { mf          = mf_mf;
      filter;
      events      = Option.map (Option.all (List.map ~f:(fun mf -> mf.events) mfs))
                      ~f:(Set.union_list (module String));
      obligations = Option.map (Option.all (List.map ~f:(fun mf -> mf.obligations) mfs))
                      ~f:(Set.union_list (module Int));
      hash        = core_hash mf_mf;
      lbls        = Etc.dedup ~equal:Lbl.equal (List.concat_map mfs ~f:(fun mf -> mf.lbls)) }
  
  let _tp     = set_make (MPredicate (Sig.tilde_tp_event_name, [])) Filter.tt
  let _neg_tp = set_make (MNeg _tp) Filter.tt
  let _tt     = set_make MTT Filter.tt
  let _ff     = set_make MFF Filter.tt

  let init (tf: Tformula.t) =
    let rec aux (tf: Tformula.t) = match tf.form with
      | Tformula.TT -> MTT
      | FF -> MFF
      | EqConst (x, c) -> MEqConst (Tterm.to_term x, c)
      | Predicate (r, trms) -> MPredicate (r, Tterm.to_terms trms)
      | Predicate' (_, _, f) | Let' (_, _, _, _, f) -> aux f
      | Agg ((s, tt), op, x, y, f) ->
         let op_fun = Aggregation.eval op tt in
         MAgg (s, op, op_fun, Tterm.to_term x, List.map ~f:fst y, make (aux f) Filter.tt)
      | Top (s, op, x, y, f) ->
         let op_fun = Sig.tfunc op in
         MTop (List.map ~f:fst s, op, op_fun, Tterm.to_terms x, List.map ~f:fst y, make (aux f) Filter.tt)
      | Neg f -> MNeg (make (aux f) tf.info.filter)
      | And (s, fs) ->
         MAnd (s, List.map2_exn ~f:make (List.map ~f:aux fs) (List.map fs ~f:(fun tf -> tf.info.filter)),
               empty_nop_info (List.length fs))
      | Or (s, fs) ->
         MOr (s, List.map2_exn ~f:make (List.map ~f:aux fs) (List.map fs ~f:(fun tf -> tf.info.filter)),
              empty_nop_info (List.length fs))
      | Imp (s, f, g) -> MImp (s, make (aux f) f.info.filter, make (aux g) g.info.filter, ([], []))
      | Exists ((x, tt), f) -> MExists (x, tt, tf.info.flag, make (aux f) f.info.filter)
      | Forall ((x, tt), f) -> MForall (x, tt, tf.info.flag, make (aux f) f.info.filter)
      | Prev (i, f) -> MPrev (i, make (aux f) f.info.filter, Prev.init i)
      | Next (i, f) when Enftype.is_only_observable tf.info.enftype -> MNext (i, make (aux f) f.info.filter, Next.init i)
      | Next (i, f) -> MENext (i, None, make (aux f) f.info.filter)
      | Once (i, f) -> MOnce (i, make (aux f) f.info.filter, Once.init i true)
      | Eventually (i, f) when Enftype.is_only_observable tf.info.enftype ->
         MEventually (i, make (aux f) f.info.filter, Eventually.init i true)
      | Eventually (i, f) -> MEEventually (i, None, make (aux f) f.info.filter)
      | Historically (i, f) -> MHistorically (i, make (aux f) f.info.filter, Once.init i false)
      | Always (i, f) when Enftype.is_only_observable tf.info.enftype ->
         MAlways (i, make (aux f) f.info.filter, Eventually.init i false)
      | Always (i, f) -> MEAlways (i, None, make (aux f) f.info.filter)
      | Since (s, i, f, g) ->
         MSince (s, i, make (aux f) f.info.filter, make (aux g) g.info.filter, Since.init i)
      | Until (_, i, f, g) when Enftype.is_only_observable tf.info.enftype ->
         MUntil (i, make (aux f) f.info.filter, make (aux g) g.info.filter, Until.init i)
      | Until (s, i, f, g) ->
         MEUntil (s, i, None, make (aux f) f.info.filter, make (aux g) g.info.filter)
      | Type (f, _) -> aux f
      | Let _ -> raise (Errors.MonitoringError "Let bindings must be unrolled to initialize MFormula")
    in set_make (aux tf) tf.info.filter


  let equal mf1 mf2 = mf1.hash = mf2.hash

  let rec rank mf = match mf.mf with
    | MTT | MFF -> 0
    | MEqConst _ -> 0
    | MPredicate (r, _) -> Sig.rank_of_pred r
    | MNeg f
      | MExists (_, _, _, f)
      | MForall (_, _, _, f)
      | MPrev (_, f, _)
      | MNext (_, f, _)
      | MENext (_, _, f)
      | MOnce (_, f, _)
      | MEventually (_, f, _)
      | MEEventually (_, _, f)
      | MHistorically (_, f, _)
      | MAlways (_, f, _)
      | MEAlways (_, _, f)
      | MAgg (_, _, _, _, _, f)
      | MTop (_, _, _, _, _, f) -> rank f
    | MImp (_, f, g, _)
      | MSince (_, _, f, g, _)
      | MUntil (_, f, g, _)
      | MEUntil (_, _, _, f, g) -> rank f + rank g
    | MAnd (_, fs, _)
      | MOr (_, fs, _) -> List.fold ~init:0 ~f:(+) (List.map fs ~f:rank)



  let rec apply_valuation (v: Etc.valuation) mf =
    let r = apply_valuation v in
    let av_term = Sig.eval in
    let spec t = Pdt.specialize_partial v t in
    let av_buf2 b = Buf2.map (TS.map spec) (TS.map spec) b in
    let av_bufn b = Bufn.map (TS.map spec) b in
    let av_buft b = Buft.map (spec) (fun t -> t) b in
    let av_buf2t b = Buf2t.map (spec) (spec) (fun t -> t) b in
    let av_pdt p = spec p in
    let mf_ = match mf.mf with
      | MTT -> MTT
      | MFF -> MFF
      | MEqConst (trm, d) ->
         (match (Sig.eval v trm).trm with
          | Const d' when Dom.equal d d' -> MTT
          | Const _ -> MFF
          | _ -> MEqConst (trm, d))
      | MPredicate (e, t) -> MPredicate (e, List.map t ~f:(av_term v))
      | MAgg (s, op, op_fun, x, y, f) -> MAgg (s, op, op_fun, x, y, r f)
      | MTop (s, op, op_fun, x, y, f) -> MTop (s, op, op_fun, x, y, r f)
      | MNeg f -> MNeg (r f)
      | MAnd (s, fs, bi) -> MAnd (s, List.map ~f:r fs, av_bufn bi)
      | MOr (s, fs, bi) -> MOr (s, List.map ~f:r fs, av_bufn bi)
      | MImp (s, f, g, bi) -> MImp (s, r f, r g, av_buf2 bi)
      | MExists (x, tt, b, f) -> MExists (x, tt, b, apply_valuation (Map.remove v x) f)
      | MForall (x, tt, b, f) -> MForall (x, tt, b, apply_valuation (Map.remove v x) f)
      | MPrev (i, f, pi) -> MPrev (i, r f, Prev.map spec pi)
      | MNext (i, f, si) -> MNext (i, r f, si)
      | MENext (i, ts, f) -> MENext (i, ts, r f)
      | MOnce (i, f, oi) -> MOnce (i, r f, Once.map spec spec oi)
      | MEventually (i, f, oi) -> MEventually (i, r f, Eventually.map spec spec oi)
      | MEEventually (i, ts, f) -> MEEventually (i, ts, r f)
      | MHistorically (i, f, oi) -> MHistorically (i, r f, Once.map spec spec oi)
      | MAlways (i, f, ai) -> MAlways (i, r f, Eventually.map spec spec ai)
      | MEAlways (i, ts, f) -> MEAlways (i, ts, r f)
      | MSince (s, i, f, g, si) -> MSince (s, i, r f, r g, Since.map spec spec si)
      | MUntil (i, f, g, ui) -> MUntil (i, r f, r g, Until.map spec spec ui)
      | MEUntil (s, i, ts, f, g) -> MEUntil (s, i, ts, r f, r g)
    in
    (*print_endline ("hash(apply_valuation(" ^ Etc.valuation_to_string v ^ ", " ^ to_string { mf; hash = 0 } ^ ")=" ^ (Int.to_string (make mf).hash));*)
    set_make mf_ mf.filter

end

module FObligation = struct

  include MFormula

  module T = struct

    let neg = function POS -> NEG | NEG -> POS

    type t = fo * polarity

    (*let is_fformula = function
      | FFormula _ -> true
      | _ -> false*)

    let is_finterval = function
      | FInterval _ -> true
      | _ -> false

    let is_funtil = function
      | FUntil _ -> true
      | _ -> false

    let is_falways = function
      | FAlways _ -> true
      | _ -> false

    let is_feventually = function
      | FEventually _ -> true
      | _ -> false

    let fold_map_kind f es = function
      | FFormula (mf, h, v) -> let es, mf = f es mf in es, FFormula (mf, h, v)
      | FInterval (ts, i, mf, h, v) -> let es, mf = f es mf in es, FInterval (ts, i, mf, h, v)
      | FUntil (ts, s, i, mf1, mf2, h, v) -> let es, mf1 = f es mf1 in
                                             let es, mf2 = f es mf2 in
                                             es, FUntil (ts, s, i, mf1, mf2, h, v)
      | FAlways (ts, i, mf, h, v) -> let es, mf = f es mf in es, FAlways (ts, i, mf, h, v)
      | FEventually (ts, i, mf, h, v) -> let es, mf = f es mf in es, FEventually (ts, i, mf, h, v)

    let fold_map f es (k, pol) = let es, k = fold_map_kind f es k in es, (k, pol)

    (*let kind_equal k1 k2 = match k1, k2 with
      | FFormula (_, h, v), FFormula (_, h', v') -> h = h' && Etc.equal_valuation v v'
      | FInterval (ts, i, _, h, v), FInterval (ts', i', _, h', v')
      | FAlways (ts, i, _, h, v), FAlways (ts', i', _, h', v')
      | FEventually (ts, i, _, h, v), FEventually (ts', i', _, h', v') ->
      Time.equal ts ts' && Interval.equal i i' && h = h' && Etc.equal_valuation v v'
      | FUntil (ts, s, i, _, _, h, v), FUntil (ts', s', i', _, _, h', v') ->
      Time.equal ts ts' && Side.equal s s' && Interval.equal i i' && h = h'
      && Etc.equal_valuation v v'
      | _ -> false*)

    let compare_kind k1 k2 = match k1, k2 with
      | FFormula (_, h, v), FFormula (_, h', v') ->
         Etc.lexicographic2 Int.compare Etc.compare_valuation (h, v) (h', v')
      | FFormula _, _ -> 1
      | FInterval _, FFormula _ -> -1
      | FInterval (ts, i, _, h, v), FInterval (ts', i', _, h', v') ->
         Etc.lexicographic4
           Time.compare Interval.compare Int.compare Etc.compare_valuation
           (ts, i, h, v) (ts', i', h', v')
      | FInterval _, _ -> 1
      | FAlways _, FFormula _ | FAlways _, FInterval _ -> -1
      | FAlways (ts, i, _, h, v), FAlways (ts', i', _, h', v') ->
         Etc.lexicographic4 Time.compare Interval.compare Int.compare Etc.compare_valuation
           (ts, i, h, v) (ts', i', h', v')
      | FAlways _, _ -> 1
      | FEventually _, FFormula _ | FEventually _, FInterval _ | FEventually _, FAlways _ -> -1
      | FEventually (ts, i, _, h, v), FEventually (ts', i', _, h', v') ->
         Etc.lexicographic4 Time.compare Interval.compare Int.compare Etc.compare_valuation
           (ts, i, h, v) (ts', i', h', v')
      | FEventually _, FUntil _ -> 1
      | FUntil (ts, s, i, _, _, h, v), FUntil (ts', s', i', _, _, h', v') ->
         Etc.lexicographic5 Time.compare Side.compare Interval.compare Int.compare Etc.compare_valuation
           (ts, s, i, h, v) (ts', s', i', h', v')
      | FUntil _, _ -> -1

    let compare =
      Etc.lexicographic2 compare_kind compare_polarity

    let sexp_of_t _ = Sexp.Atom "FObligation"
    (*let t_of_sexp _ = (FFormula (_tt, 0, Etc.empty_valuation), Etc.empty_valuation, POS)*)

    (*let equal (k, v, pol) (k', v', pol') =
      kind_equal k k' && Map.equal Dom.equal v v' && equal_polarity pol pol'*)

    let to_string ((kind, pol) : t) =
      Printf.sprintf "Kind: %s; " (fo_to_string kind) ^
          Printf.sprintf "Polarity: %s" (polarity_to_string pol)

    let eval_kind ts' _ k =
      let tp_filter mf = 
        Filter.conj mf.filter (Filter.An Sig.tilde_tp_event_name) in
      match k with
      | FFormula (mf, _, _) -> mf
      | FInterval (ts, i, mf, _, v) ->
         if Interval.diff_is_in ts ts' i then
           map_mf
             (map_mf mf Filter.tt (fun mf -> (MAnd (L, [_tp; mf], empty_nop_info 2))))
             Filter.tt
             (fun mf -> MEUntil (R, i, Some ts, _neg_tp, mf))
         else
           _tt
      | FUntil (ts, side, i, mf1, mf2, _, v) ->
         if not (Interval.diff_right_of ts ts' i) then
           let mf1' = match mf1.mf with
             | MImp (_, mf11, mf12, _) when MFormula.equal _tp mf11 -> mf12
             | _ -> mf1 in
           let mf2' = match mf2.mf with
             | MAnd (_, [mf21; mf22], _) when MFormula.equal _tp mf21 -> mf22
             | _ -> mf2 in
           map2_mf
             (if MFormula.equal mf1' _neg_tp then
                _neg_tp
              else
                map_mf mf1' (tp_filter mf1') (fun mf -> MImp (R, _tp, mf, empty_binop_info)))
             (map_mf mf2' Filter.tt (fun mf -> MAnd (R, [_tp; mf], empty_nop_info 2)))
             Filter.tt
             (fun mf1 mf2 -> MEUntil (side, i, Some ts, mf1, mf2))
         else
           _ff
      | FAlways (ts, i, mf, _, v) ->
         if not (Interval.diff_right_of ts ts' i) then
           let mf' = match mf.mf with
             | MImp (_, mf1, mf2, _) when MFormula.equal _tp mf1 -> mf2
             | _ -> mf in
           map_mf
             (map_mf mf' (tp_filter mf') (fun mf -> MImp (R, _tp, mf, empty_binop_info)))
             Filter.tt
             (fun mf -> MEAlways (i, Some ts, mf))
         else
           _tt
      | FEventually (ts, i, mf, _, v) ->
         if not (Interval.diff_right_of ts ts' i) then
           let mf' = match mf.mf with
             | MAnd (_, [mf1; mf2], _) when MFormula.equal _tp mf1 -> mf2
             | _ -> mf in
           map_mf
             (map_mf mf' Filter.tt (fun mf -> MAnd (L, [_tp; mf], empty_nop_info 2)))
             Filter.tt
             (fun mf -> MEEventually (i, Some ts, mf))
         else
           _ff

    let set_valuation v = function
      | FFormula (mf, h, _) -> FFormula (mf, h, v)
      | FInterval (ts, i, mf, h, _) -> FInterval (ts, i, mf, h, v)
      | FUntil (ts, s, i, mf, mg, h, _) -> FUntil (ts, s, i, mf, mg, h, v)
      | FAlways (ts, i, mf, h, _) -> FAlways (ts, i, mf, h, v)
      | FEventually (ts, i, mf, h, _) -> FEventually (ts, i, mf, h, v)

    let pop_valuation = function
      | FFormula (mf, h, v) -> FFormula (mf, h, Etc.empty_valuation), v
      | FInterval (ts, i, mf, h, v) -> FInterval (ts, i, mf, h, Etc.empty_valuation), v
      | FUntil (ts, s, i, mf, mg, h, v) -> FUntil (ts, s, i, mf, mg, h, Etc.empty_valuation), v
      | FAlways (ts, i, mf, h, v) -> FAlways (ts, i, mf, h, Etc.empty_valuation), v
      | FEventually (ts, i, mf, h, v) -> FEventually (ts, i, mf, h, Etc.empty_valuation), v

    let eval ts tp (k, pol) =
      let k, v = pop_valuation k in
      let mf = apply_valuation v (eval_kind ts tp k) in
      match pol with
      | POS -> (*print_endline (Printf.sprintf "eval()=%s" (MFormula.to_string mf)); *)mf
      | NEG -> match mf.mf with
               | MNeg mf -> mf
               | _       -> map_mf mf Filter.tt (fun mf -> MNeg mf) ~exquant:true


    let accepts_empty = function
      | (FFormula _, pol) -> equal_polarity pol NEG
      | (FInterval _, pol) -> equal_polarity pol NEG
      | (FUntil _, pol) -> equal_polarity pol NEG
      | (FAlways _, pol) -> equal_polarity pol POS
      | (FEventually _, pol) -> equal_polarity pol NEG

    let hv = function
      | FFormula (_, i, v) -> (i, v)
      | FInterval (_, _, _, i, v) -> (i, v)
      | FUntil (_, _, _, _, _, i, v) -> (i, v)
      | FAlways (_, _, _, i, v) -> (i, v)
      | FEventually (_, _, _, i, v) -> (i, v)

    let h (f, _) = fst (hv f)

  end

  include T
  include Comparable.Make(T)

end


module FObligations = struct

  type t = (FObligation.t, FObligation.comparator_witness) Set.t

  let to_string fobligations =
    Etc.string_list_to_string (List.map ~f:FObligation.to_string (Set.elements fobligations))

  let empty = Set.empty (module FObligation)

  let accepts_empty fobligations =
    Set.for_all fobligations ~f:FObligation.accepts_empty

end

include MFormula

let rec match_terms trms ds map =
  (*print_endline ("trms=" ^ Term.list_to_string trms);
    print_endline ("ds=" ^ String.concat ~sep:", " (List.map ~f:Dom.to_string ds));*)
  match trms, ds with
  | [], [] -> Some(map)
  | Term.Const c :: trms, d :: ds -> if Dom.equal c d then match_terms trms ds map else None
  | Var x :: trms, d :: ds ->
     (match match_terms trms ds map with
      | None -> None
      | Some map' ->
         (match Map.find map' (Lbl.LVar x) with
          | None -> let map'' = Map.add_exn map' ~key:(Lbl.LVar x) ~data:d in Some map''
          | Some z -> (if Dom.equal d z then Some map' else None)))
  | App (f, trms') :: trms, d :: ds ->
     (match match_terms trms ds map with
      | None -> None
      | Some map' -> Some (Map.add_exn map' ~key:(Lbl.LClos (f, trms', Set.empty (module String))) ~data:d))
  | _, _ -> raise (Errors.MonitoringError
                     (Printf.sprintf "Cannot match terms %s with domain elements %s"
                        (Term.list_to_string_core trms) (Dom.list_to_string ds)))

let default_pol = Option.value ~default:POS

let proof_false ?(fixes=None) = function
  | POS -> FFalse (Option.value ~default:[] fixes)
  | NEG -> FTrue  (Option.value ~default:[] fixes)

let apply_fbool lbls = Pdt.apply1 lbls fbool_of_bool
let apply_sat lbls = Pdt.apply1 lbls sat

(* Approximation functions, monitoring under assumptions *)

let approximate_false pol = Pdt.Leaf (proof_false pol)
let approximate_false_opt pol_opt = approximate_false (default_pol pol_opt)

let els pol_opt = function
  | Some p -> p
  | None -> approximate_false_opt pol_opt

let approximate_expl tp pol lbls (expls: bool Expl.t TS.t list) =
  match List.last expls with
  | Some expl when expl.tp = tp -> apply_fbool lbls expl.data
  | _ -> Leaf (proof_false pol)

let approximate_fobligs lbls fobligs (fo, pol) = (* TODO: Check how we match on ts etc. *)
  let h, _ = FObligation.hv fo in
  let f (k, pol') =
    let (h', v) = FObligation.hv k in
    if h = h' && equal_polarity pol pol' then
      Some (Pdt.from_valuation lbls v (fbool_of_polarity pol)
              (proof_false ~fixes:(Some [FOblig (fo, pol)]) pol))
    else
      None in
  match pol with
  | POS -> Pdt.applyN_reduce equal_fbool lbls
             (List.fold ~init:(FFalse [FOblig (fo, pol)]) ~f:(or_fbool L))
             (List.filter_map ~f (Set.elements fobligs))
  | NEG -> Pdt.applyN_reduce equal_fbool lbls
             (List.fold ~init:(FTrue [FOblig (fo, pol)]) ~f:(and_fbool L))
             (List.filter_map ~f (Set.elements fobligs))

let approximate_once lbls (expls: bool Expl.t TS.t list) aexpl i tp pol =
  let expl = approximate_expl tp pol lbls expls in
  Pdt.apply2_reduce equal_fbool lbls (Once.approximate (Interval.left i)) aexpl expl

let approximate_eventually lbls aexpl (fobligs: FObligations.t) ts ts' i mf h pol =
  let fo_expl = approximate_fobligs lbls fobligs
                  (FEventually (ts, i, mf, h, Etc.empty_valuation), pol) in
  Pdt.apply2_reduce equal_fbool lbls (Eventually.approximate ts ts' i) fo_expl aexpl

let approximate_historically lbls (expls: bool Expl.t TS.t list) aexpl i tp pol =
  let expl = approximate_expl tp pol lbls expls in
  Pdt.apply2_reduce equal_fbool lbls (Once.approximate_historically (Interval.left i)) aexpl expl

let approximate_always lbls aexpl (fobligs: FObligations.t) ts ts' i mf h pol = (*TODO*)
  let fo_expl = approximate_fobligs lbls fobligs
                  (FAlways (ts, i, mf, h, Etc.empty_valuation), pol) in
  Pdt.apply2_reduce equal_fbool lbls
    (Eventually.approximate_always ts ts' i) fo_expl aexpl

let approximate_since lbls (expls: bool Expl.t TS.t list) aexpl1 aexpl2 i tp pol =
  let expl = approximate_expl tp pol lbls expls in
  Pdt.apply3_reduce equal_fbool lbls (Since.approximate pol (Interval.left i)) aexpl1 aexpl2 expl

let approximate_quant aexpl x mf =
  match mf with
  | MExists _ -> Pdt.quantify ~forall:false x aexpl
  | MForall _ -> Pdt.quantify ~forall:true x aexpl
  | _ -> raise (Errors.MonitoringError
                  (Printf.sprintf "function is not defined for %s" (MFormula.core_op_to_string mf)))

let approximate_enext lbls (fobligs: FObligations.t) ts i mf h pol = (*TODO*)
  approximate_fobligs lbls fobligs (FInterval (ts, i, mf, h, Etc.empty_valuation), pol)

let approximate_until lbls aexpl1 aexpl2 (fobligs: FObligations.t) ts ts' s i mf mg h pol = (*TODO*)
  let fo_expl = approximate_fobligs lbls fobligs
                  (FUntil (ts, s, i, mf, mg, h, Etc.empty_valuation), pol) in
  Pdt.apply3_reduce equal_fbool lbls (Until.approximate pol ts ts' s i) fo_expl aexpl1 aexpl2

let inc_ts ts = Time.(ts + !Global.s_ref)

let meval_c = ref 0
(*let memo = Hashtbl.create (module Formula)*)


module Memo = struct

  type 'a t = { map: (int, 'a, Int.comparator_witness) Map.t;
                ex_events: (string, String.comparator_witness) Set.t;
                ex_obligations: (int, Int.comparator_witness) Set.t }

  let to_string (memo : 'a t) =
    Printf.sprintf "memo(map.keys = {%s};\n     ex_events = {%s};\n     ex_obligations = {%s})"
      (String.concat ~sep:", " (List.map (Map.keys memo.map) ~f:Int.to_string))
      (String.concat ~sep:", " (Set.elements memo.ex_events))
      (String.concat ~sep:", " (List.map ~f:Int.to_string (Set.elements memo.ex_obligations)))

  let find memo mf pol =
    let hash = mf.hash * 65599 + (int_of_polarity pol) in
    (*print_debug ("find " ^ Int.to_string hash);
    print_debug (to_string memo);*)
    match Map.find memo.map hash, mf.events, mf.obligations with
    | None, _, _  
      | _, None, _ 
      | _, _, None -> None
    | Some _, Some mf_events, _ when not (Set.are_disjoint mf_events memo.ex_events) ->
       None
    | Some _, _, Some mf_obligations when not (Set.are_disjoint mf_obligations memo.ex_obligations) ->
       None
    | Some res, _, _ -> Some res

  let add_event memo e = { memo with ex_events = Set.add memo.ex_events e }
  let add_obligation memo h = { memo with ex_obligations = Set.add memo.ex_obligations h }
  let empty = { map = Map.empty (module Int);
                ex_events = Set.empty (module String);
                ex_obligations = Set.empty (module Int) }
  
  let memoize memo mf pol res =
    let hash = mf.hash * 65599 + (int_of_polarity pol) in
    (*print_debug ("memoize " ^ Int.to_string hash);
    print_debug (to_string { memo with map = Map.update memo.map hash ~f:(fun _ -> res) });*)
    { memo with map = Map.update memo.map hash ~f:(fun _ -> res) }

  
end

let rec update_tstps tstps (expls: 'a TS.t list) : (timestamp * timepoint) list =
  let last_tp = Option.value (Option.map (List.last tstps) ~f:snd) ~default:(-1) in
  tstps @ List.filter_map expls ~f:(fun te -> if te.tp > last_tp then Some (te.ts, te.tp) else None) 

let rec update_tstps2 tstps expls1 expls2 =
  let tstps = update_tstps tstps expls1 in
  update_tstps tstps expls2

let default_ts ts ts'  =
  Option.value ts ~default:ts'

let rec filter_eval (db : Db.t) = function
  | Filter.An e -> Db.mem_trace db e
  | AllOf fis   -> List.for_all fis ~f:(filter_eval db)
  | OneOf fis   -> List.exists  fis ~f:(filter_eval db)

let can_skip db mformula =
  not (filter_eval db mformula.filter)
  
let meval (ts: timestamp) tp (db: Db.t) ~pol (fobligs: FObligations.t) nick mformula memo =
  let outer_tp = tp in
  let map_expl f (tp, (ts, x)) = (tp,  x) in
  let rec meval_rec (ts: timestamp) tp (db: Db.t) ~pol (fobligs: FObligations.t) memo mformula :
            'a *  (bool Expl.t TS.t list * fbool Expl.t * MFormula.t) =
    let nick_of_time f_ts ts i =
      Interval.diff_right_of (default_ts f_ts ts) (inc_ts ts) i && nick in
    (*print_endline "--meval_rec";
    print_endline ("mf=" ^ MFormula.to_string mformula);
    print_endline ("pol=" ^ Option.value_map pol ~default:"None" ~f:FObligation.polarity_to_string);*)
    (*print_endline "";*)
    (*print_debug ("memo=" ^ Memo.to_string memo);*)
    (*print_endline ("hash=" ^ Int.to_string mformula.hash);*)
    (*print_endline ("incr: " ^ MFormula.to_string mformula);*)
    Int.incr meval_c;
    match Memo.find memo mformula (default_pol pol), can_skip db mformula with
    | Some (expls, aexpl, mf), _ ->
       (print_debug (Printf.sprintf "meval:memo(%s, %d, %d)" (value_to_string mformula) mformula.hash tp);
        memo, (expls, aexpl, mf))
    | None, true ->
       (print_debug (Printf.sprintf "meval:skip(%s)" (value_to_string mformula));
        let pol   = default_pol pol in
        let expl  = Pdt.Leaf (equal_polarity pol POS) in
        let fexpl = Pdt.Leaf (fbool_of_polarity pol) in
        memo, ([TS.make tp ts expl], fexpl, mformula))
    | None, _ -> 
       let memo, (expls, aexpl, mf) =
         match mformula.mf with
         | MTT -> let expl  = Pdt.Leaf true in
                  let fexpl = Pdt.Leaf (FTrue []) in
                  memo, ([TS.make tp ts expl], fexpl, MTT)
         | MFF -> let expl  = Pdt.Leaf false in
                  let fexpl = Pdt.Leaf (FFalse []) in
                  memo, ([TS.make tp ts expl], fexpl, MFF)
         | MEqConst (trm, d) ->
            let expl =
              Pdt.Node (Lbl.of_term trm,
                        [(Setc.Complement (Set.of_list (module Dom) [d]), Pdt.Leaf false);
                         (Setc.Finite (Set.of_list (module Dom) [d]), Pdt.Leaf true)]) in
            let fexpl =
              Pdt.Node (Lbl.of_term trm,
                        [(Setc.Complement (Set.of_list (module Dom) [d]), Pdt.Leaf (FFalse []));
                         (Setc.Finite (Set.of_list (module Dom) [d]), Pdt.Leaf (FTrue []))]) in

            memo, ([TS.make tp ts expl], fexpl, MEqConst (trm, d))
         | MPredicate (r, trms) when not (Enftype.is_observable (Sig.enftype_of_pred r)) ->
            (*print_endline ("not observable: " ^ r);*)
            let expl = Pdt.Leaf (not (equal_polarity POS (default_pol pol))) in
            let fexpl = Pdt.Leaf (fbool_of_bool (not (equal_polarity POS (default_pol pol)))) in
            memo, ([TS.make tp ts expl], fexpl, MPredicate (r, trms))
         | MPredicate (r, trms) ->
            let db' = match Sig.kind_of_pred r with
              | Trace -> Db.filter db ~f:(fun evt -> String.equal r (fst(evt)))
              | External -> Db.retrieve_external r
              | Builtin -> Db.retrieve_builtin ts tp r
              | Predicate -> raise (Errors.MonitoringError "cannot evaluate Predicate")
              | Let -> raise (Errors.MonitoringError "cannot evaluate Let") in
            if List.is_empty trms then
              (let expl = Pdt.Leaf (not (Db.is_empty db')) in
               let fexpl = Pdt.Leaf (if not (Db.is_empty db') then
                                       FTrue [FEvent (r, [], NEG, mformula.hash)]
                                     else
                                       FFalse [FEvent (r, [], POS, mformula.hash)]) in
               memo, ([TS.make tp ts expl], fexpl, MPredicate (r, trms)))
            else
              let maps = List.filter_opt (
                             Set.fold (Db.events db') ~init:[]
                               ~f:(fun acc evt -> match_terms (List.map ~f:(fun x -> x.trm) trms) (snd evt)
                                                    (Map.empty (module Lbl)) :: acc)) in
              let enftype = Sig.enftype_of_pred r in
              let expl = if List.is_empty maps
                         then Pdt.Leaf false
                         else Expl.pdt_of tp r trms mformula.lbls maps
                                ~equal:Bool.equal ~tt:true ~ff:false in
              let fexpl = if List.is_empty maps
                          then Pdt.Leaf (FFalse (if Enftype.is_causable enftype
                                                 then [FEvent (r, trms, POS, mformula.hash)]
                                                 else []))
                          else Expl.pdt_of tp r trms mformula.lbls maps
                                 ~equal:equal_fbool
                                 ~tt:(FTrue (if Enftype.is_suppressable enftype
                                             then [FEvent (r, trms, NEG, mformula.hash)]
                                             else []))
                                 ~ff:(FFalse (if Enftype.is_causable enftype
                                              then [FEvent (r, trms, POS, mformula.hash)]
                                              else [])) in
              (*print_endline "--MPredicate";
              print_endline ("r=" ^ r);
              print_endline ("db'=" ^ Db.to_string db');
              print_endline ("maps=" ^ (String.concat ~sep:"; " (List.map maps ~f:(fun map -> String.concat ~sep:", " (List.map (Map.to_alist map) ~f:(fun (lbl, d) -> Lbl.to_string lbl ^ " -> " ^ Dom.to_string d))))));*)
              (*print_endline ("fexpl=" ^ Expl.to_string ~to_string:fbool_to_string fexpl);*)
              memo, ([TS.make tp ts expl], fexpl, MPredicate (r, trms))
         | MAgg (s, op, op_fun, x, y, mf) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db fobligs ~pol memo mf in
            (*print_endline ("--MAgg.aexpl=" ^ Expl.to_string aexpl);
              print_endline ("mf=" ^ MFormula.to_string mformula);
              print_endline ("aexpl=" ^ Expl.to_string aexpl);*)
            (*print_endline ("lbls="  ^ String.concat ~sep:", " (List.map ~f:Lbl.to_string mformula.lbls));
              print_endline ("lbls'=" ^ String.concat ~sep:", " (List.map ~f:Lbl.to_string mf.lbls));*)
            let aggregate = Expl.aggregate op_fun s tp x y mformula.lbls mf.lbls
                              ~sat:(fun x -> x) ~equal:Bool.equal ~tt:true ~ff:false in
            let faggregate = Expl.aggregate op_fun s tp x y mformula.lbls mf.lbls
                               ~sat ~equal:equal_fbool ~tt:(FTrue []) ~ff:(FFalse [])  in
            (*print_endline ("MAgg.aexpl=" ^ Expl.to_string aexpl);*)
            (*print_endline ("MAgg.mformula=" ^ MFormula.to_string mformula);*)
            let f_expls = List.map expls ~f:(TS.map aggregate) in
            let f_aexpl = faggregate aexpl in
            (*print_endline ("--MAgg.f_aexpl=" ^ Expl.to_string f_aexpl);*)
            memo, (f_expls, f_aexpl, MAgg (s, op, op_fun, x, y, mf'))
         | MTop (s, op, op_fun, x, y, mf) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db fobligs ~pol memo mf in
            (*print_endline ("--MAgg.aexpl=" ^ Expl.to_string aexpl);
              print_endline ("mf=" ^ MFormula.to_string mformula);
              print_endline ("aexpl=" ^ Expl.to_string aexpl);*)
            (*print_endline ("lbls="  ^ String.concat ~sep:", " (List.map ~f:Lbl.to_string mformula.lbls));
              print_endline ("lbls'=" ^ String.concat ~sep:", " (List.map ~f:Lbl.to_string mf.lbls));*)
            let aggregate = Expl.table_operator op_fun s tp x y mformula.lbls mf.lbls
                              ~sat:(fun x -> x) ~equal:Bool.equal ~tt:true ~ff:false in
            let faggregate = Expl.table_operator op_fun s tp x y mformula.lbls mf.lbls
                               ~sat ~equal:equal_fbool ~tt:(FTrue []) ~ff:(FFalse []) in
            (*print_endline ("MAgg.aexpl=" ^ Expl.to_string aexpl);*)
            (*print_endline ("MAgg.mformula=" ^ MFormula.to_string mformula);*)
            let f_expls = List.map expls ~f:(TS.map aggregate) in
            let f_aexpl = faggregate aexpl in
            (*print_endline ("--MTop.f_aexpl=" ^ Expl.to_string f_aexpl);*)
            memo, (f_expls, f_aexpl, MTop (s, op, op_fun, x, y, mf'))
         | MNeg (mf) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db fobligs ~pol:(pol >>| FObligation.neg) memo mf in
            let neg pdt =
              Pdt.apply1_reduce Bool.equal mformula.lbls (fun x -> not x) (Pdt.exquant pdt) in
            let fneg pdt =
              Pdt.apply1_reduce equal_fbool mformula.lbls not_fbool (Pdt.exquant pdt) in
            let f_expls = List.map expls ~f:(TS.map neg) in
            let f_aexpl = fneg aexpl in
            memo, (f_expls, f_aexpl, MNeg mf')
         | MAnd (s, mfs, bufn) -> 
            let memo, data = List.fold_map ~init:memo ~f:(meval_rec ts tp db ~pol fobligs) mfs in
            let expls_list, aexpl_list, mfs' = List.unzip3 data in
            let apply_ands = Pdt.applyN_reduce Bool.equal mformula.lbls
                               (List.fold_left ~init:true ~f:(&&)) in
            let fapply_ands = Pdt.applyN_reduce equal_fbool mformula.lbls (and_fbools s) in
            (*print_endline ("MAnd " ^ MFormula.to_string mformula);
            print_endline "and_a";
            List.iter expls_list ~f:(fun expl_list -> List.iter expl_list ~f:(fun expl -> print_endline (TS.to_string Expl.to_string expl)));
            print_endline "and_b";*)
            let (f_expls, bufn) = Bufn.take (TS.map_list apply_ands) (Bufn.add expls_list bufn) in
            let aexpl = fapply_ands aexpl_list in
            memo, (f_expls, aexpl, MAnd (s, mfs', bufn))
         | MOr (s, mfs, bufn) ->
            let memo, data = List.fold_map ~init:memo ~f:(meval_rec ts tp db ~pol fobligs) mfs in
            let expls_list, aexpl_list, mfs' = List.unzip3 data in
            let apply_ors = Pdt.applyN_reduce Bool.equal mformula.lbls
                              (List.fold_left ~init:false ~f:(||)) in
            let fapply_ors = Pdt.applyN_reduce equal_fbool mformula.lbls (or_fbools s) in
            (*print_endline ("MOr " ^ MFormula.to_string mformula);
            print_endline "or_a";
            List.iter expls_list ~f:(fun expl_list -> List.iter expl_list ~f:(fun expl -> print_endline (TS.to_string Expl.to_string expl)));*)
            let (f_expls, bufn) = Bufn.take (TS.map_list apply_ors) (Bufn.add expls_list bufn) in
            (*print_endline "or_b";*)
            (*List.iter ~f:(fun e -> print_endline (TS.to_string Expl.to_string e)) f_expls;*)
            let aexpl = fapply_ors aexpl_list in
            memo, (f_expls, aexpl, MOr (s, mfs', bufn))
         | MImp (s, mf1, mf2, buf2) ->
            let memo, (expls1, aexpl1, mf1') = meval_rec ts tp db ~pol:(pol >>| FObligation.neg) fobligs memo mf1 in
            let memo, (expls2, aexpl2, mf2') = meval_rec ts tp db ~pol fobligs memo mf2 in
            let imp pdt1 pdt2 =
              Pdt.apply2_reduce Bool.equal mformula.lbls
                (fun p1 p2 -> (not p1) || p2) (Pdt.exquant pdt1) pdt2 in
            let fimp pdt1 pdt2 =
              Pdt.apply2_reduce equal_fbool mformula.lbls
                (fun p1 p2 -> or_fbool s (not_fbool p1) p2) (Pdt.exquant pdt1) pdt2 in
            (*print_endline "--MImp";
            print_endline ("aexpl1=" ^ Expl.to_string aexpl1);
            print_endline ("aexpl2=" ^ Expl.to_string aexpl2);
            print_endline ("lbls=" ^ Lbl.to_string_list mformula.lbls);*)
            let (f_expls, buf2) = Buf2.take (TS.map2 imp) (Buf2.add expls1 expls2 buf2) in
            let aexpl = fimp aexpl1 aexpl2 in
            (*print_endline ("aexpl=" ^ Expl.to_string aexpl);*)
            memo, (f_expls, aexpl, MImp (s, mf1', mf2', buf2))
         | MExists (x, tc, b, mf) ->
            (*print_endline "--MExists";
              print_endline ("x =" ^ x);
              print_endline ("lbls =" ^ (Lbl.to_string_list lbls));
              print_endline ("lbls'=" ^ (Lbl.to_string_list lbls'));*)
            let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let quant expl = approximate_quant expl x mformula.mf in
            let expls = List.map expls ~f:(TS.map quant) in
            (*print_endline ("aexpl (before) = " ^ Expl.to_string aexpl);*)
            let aexpl = quant aexpl in
            (*print_endline ("aexpl (after) = " ^ Expl.to_string aexpl);*)
            memo, (expls, aexpl, MExists(x, tc, b, mf'))
         | MForall (x, tc, b, mf) ->
            (*print_endline "--MForall";
              print_endline ("x =" ^ x);*)
            (*print_endline ("lbls =" ^ (Lbl.to_string_list lbls));
              print_endline ("lbls'=" ^ (Lbl.to_string_list lbls'));*)
            let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let quant expl = approximate_quant expl x mformula.mf in
            let expls = List.map expls ~f:(TS.map quant) in
            (*print_endline ("aexpl (before) = " ^ Expl.to_string aexpl);*)
            let aexpl = quant aexpl in
            (*print_endline ("aexpl (after) = " ^ Expl.to_string aexpl);*)
            memo, (expls, aexpl, MForall(x, tc, b, mf'))
         | MPrev (i, mf, aux) -> 
            let memo, (expls, _, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = { aux with
                        tstps = aux.tstps @ (List.map expls ~f:(fun te -> (te.ts, te.tp)));
                        buf = aux.buf @ (List.map expls ~f:TS.data) } in
            let aux, f_expls = Prev.update mformula.lbls aux in
            memo, (f_expls, approximate_false_opt pol, MPrev (i, mf', aux))
         | MNext (i, mf, aux) ->
            let memo, (expls, _, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = { aux with
                        tstps = aux.tstps @ (List.map expls ~f:(fun te -> (te.ts, te.tp)));
                        tstps_todo = aux.tstps_todo @ (List.map expls ~f:(fun te -> (te.ts, te.tp)));
                        buf = aux.buf @ (List.map expls ~f:TS.data) } in
            let aux, f_expls = Next.update mformula.lbls aux in
            memo, (f_expls, approximate_false_opt pol, MNext (i, mf', aux))
         | MENext (i, f_ts, mf) ->
            let memo, (_, _, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aexpl = approximate_enext mformula.lbls fobligs (default_ts f_ts ts)
                          i mf mformula.hash (default_pol pol) in
            let bexpl = apply_sat mformula.lbls aexpl in
            memo, ([TS.make tp ts bexpl], aexpl, MENext (i, f_ts, mf'))
         | MOnce (i, mf, aux) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = { aux with buf = Buft.add aux.buf expls } in
            let aux, f_expls = Once.update mformula.lbls aux in
            let aexpl = approximate_once mformula.lbls f_expls aexpl i tp (default_pol pol) in
            (*print_endline ("aexpl=" ^ Expl.to_string aexpl);*)
            memo, (f_expls, aexpl, MOnce (i, mf', aux))
         | MEventually (i, mf, aux) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = { aux with
                        tstps_todo = aux.tstps_todo @ (List.map expls ~f:(fun te -> (te.ts, te.tp)));
                        buf = Buft.add aux.buf expls } in
            let aux, f_expls = Eventually.update mformula.lbls aux in
            memo, (f_expls, approximate_false_opt pol, MEventually (i, mf', aux))
         | MEEventually (i, f_ts, mf) ->
            let memo, (_, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aexpl =
              if nick_of_time f_ts ts i && equal_polarity (default_pol pol) POS then aexpl
              else approximate_eventually mformula.lbls aexpl fobligs
                     (default_ts f_ts ts) ts i mf mformula.hash (default_pol pol) in
            let bexpl = apply_sat mformula.lbls aexpl in
            memo, ([TS.make tp ts bexpl], aexpl, MEEventually (i, f_ts, mf'))
         | MHistorically (i, mf, aux) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = { aux with buf = Buft.add aux.buf expls } in
            let aux, f_expls = Once.update mformula.lbls aux in
            let aexpl =
              approximate_historically mformula.lbls f_expls aexpl i tp (default_pol pol) in
            memo, (f_expls, aexpl, MHistorically (i, mf', aux))
         | MAlways (i, mf, aux) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = { aux with
                        tstps_todo = aux.tstps_todo @ (List.map expls ~f:(fun te -> (te.ts, te.tp)));
                        buf = Buft.add aux.buf expls } in
            let aux, f_expls = Eventually.update mformula.lbls aux in
            memo, (f_expls, approximate_false_opt pol, MAlways (i, mf', aux))
         | MEAlways (i, f_ts, mf) ->
            let memo, (_, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            (*print_endline "--MEAlways";
              print_endline ("lbls = " ^ (Lbl.to_string_list mformula.lbls));*)
            let aexpl =
              if nick_of_time f_ts ts i && equal_polarity (default_pol pol) NEG then aexpl
              else approximate_always mformula.lbls aexpl fobligs (default_ts f_ts ts) ts
                     i mf mformula.hash (default_pol pol) in
            let bexpl = apply_sat mformula.lbls aexpl in
            memo, ([TS.make tp ts bexpl], aexpl, MEAlways (i, f_ts, mf'))
         | MSince (s, i, mf1, mf2, aux) ->
            let memo, (expls1, aexpl1, mf1') = meval_rec ts tp db ~pol fobligs memo mf1 in
            let memo, (expls2, aexpl2, mf2') = meval_rec ts tp db ~pol fobligs memo mf2 in
            (*print_endline "-- MSince (before)";
            print_endline (Since.to_string aux);
            print_endline (Expl.to_string aexpl1);
            print_endline (Expl.to_string aexpl2);*)
            (*print_endline ("expls1=" ^ Etc.list_to_string "" (fun _ -> TS.to_string Expl.to_string) expls1);
            print_endline ("expls2=" ^ Etc.list_to_string "" (fun _ -> TS.to_string Expl.to_string) expls2);*)
            let aux = { aux with buf = Buf2t.add aux.buf expls1 expls2 } in
            let aux, f_expls = Since.update mformula.lbls aux in
            let aexpl = approximate_since mformula.lbls f_expls aexpl1 aexpl2 i tp (default_pol pol) in
            (*print_endline "-- MSince (after)";
            print_endline (Since.to_string aux);*)
            memo, (f_expls, aexpl, MSince (s, i, mf1', mf2', aux))
         | MUntil (i, mf1, mf2, aux) ->
            let memo, (expls1, aexpl1, mf1') = meval_rec ts tp db ~pol fobligs memo mf1 in
            let memo, (expls2, aexpl2, mf2') = meval_rec ts tp db ~pol fobligs memo mf2 in
            let tstps_todo = update_tstps2 aux.tstps_todo expls1 expls2 in
            let aux = { aux with
                        tstps_todo;
                        buf = Buf2t.add aux.buf expls1 expls2 } in
            let aux, f_expls = Until.update mformula.lbls aux in
            memo, (f_expls, approximate_false_opt pol, MUntil (i, mf1', mf2', aux))
         | MEUntil (s, i, f_ts, mf1, mf2) ->
            let memo, (_, aexpl1, mf1') = meval_rec ts tp db ~pol fobligs memo mf1 in
            let memo, (_, aexpl2, mf2') = meval_rec ts tp db ~pol fobligs memo mf2 in
            let aexpl =
              if nick_of_time f_ts ts i && equal_polarity (default_pol pol) POS then aexpl2
              else approximate_until mformula.lbls aexpl1 aexpl2 fobligs (default_ts f_ts ts) ts
                     s i mf1 mf2 mformula.hash (default_pol pol) in
            let bexpl = apply_sat mformula.lbls aexpl in
            memo, ([TS.make tp ts bexpl], aexpl, MEUntil (s, i, f_ts, mf1', mf2'))
       in let mf = { mformula with mf } in
          print_debug (Printf.sprintf "meval(%s, %d, %d, %s) = %s"
                         (value_to_string mf) tp mformula.hash (Option.value ~default:"None" (Option.map ~f:polarity_to_string pol))
                         (Expl.to_string ~to_string:fbool_to_string aexpl));
          let memo = if tp = outer_tp then Memo.memoize memo mformula (default_pol pol) (expls, aexpl, mf) else memo in
          memo, (expls, aexpl, mf)
  in meval_rec ts tp db ~pol fobligs memo mformula


module MState = struct

  type t = { mf: MFormula.t
           ; tp_cur: timepoint                        (* current time-point evaluated    *)
           ; tp_out: timepoint                        (* last time-point that was output *)
           ; ts_waiting: timestamp Queue.t
           ; tsdbs: (timestamp * Db.t) Queue.t
           ; tpts: (timepoint, timestamp) Hashtbl.t }

  let init mf = { mf = mf
                ; tp_cur = 0
                ; tp_out = -1
                ; ts_waiting = Queue.create ()
                ; tsdbs = Queue.create ()
                ; tpts = Hashtbl.create (module Int) }

  let tp_cur ms = ms.tp_cur

  let tsdbs ms = ms.tsdbs

  let to_string indent { mf
                       ; tp_cur
                       ; tp_out
                       ; ts_waiting
                       ; tsdbs
                       ; tpts } =
    "\nMState: \n\n" ^
      Printf.sprintf "%smf = %s\n" indent (MFormula.to_string mf) ^
        Printf.sprintf "%stp_cur = %d\n" indent tp_cur ^
          Printf.sprintf "%stp_out = %d\n" indent tp_out ^
            Printf.sprintf "\n%sts_waiting = [" indent ^ (String.concat ~sep:", "
                                                            (Queue.to_list
                                                               (Queue.map ts_waiting ~f:Time.to_string))) ^ "]\n" ^
              Printf.sprintf "\n%stsdbs = [" indent ^ (String.concat ~sep:", "
                                                         (Queue.to_list (Queue.map tsdbs ~f:(fun (ts, db) ->
                                                                             Printf.sprintf "(%s):\n %s\n" 
                                                                               (Time.to_string ts) (Db.to_string db))))) ^ "]\n" ^
                Printf.sprintf "\n%stpts = [" indent ^ (String.concat ~sep:", "
                                                          (Hashtbl.fold tpts ~init:[] ~f:(fun ~key:tp ~data:ts acc ->
                                                               acc @ [Printf.sprintf "(%d, %s)" tp (Time.to_string ts)]))) ^ "]\n"

end

type res = bool Expl.t TS.t list * fbool Expl.t * MFormula.t

let mstep _ ts db approx (ms: MState.t) (fobligs: FObligations.t) nick (memo : res Memo.t) =
  let pol_opt = if approx then Some POS else None in
  let memo, (_, aexpl, mf') = meval ts ms.tp_cur db ~pol:pol_opt fobligs nick ms.mf memo in
  let tsdbs = ms.tsdbs in
  let ts_waiting = ms.ts_waiting in
  memo, (aexpl,
         { ms with
           mf = mf'
         ; tp_cur = ms.tp_cur + 1
         ; ts_waiting
         ; tsdbs = tsdbs })

