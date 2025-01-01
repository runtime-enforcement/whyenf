open Base
open Expl
open Option

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm

open Etc

module type MonitorT = sig

  module MFormula : sig

    type binop_info
    type nop_info
    type prev_info
    type once_info
    type next_info
    type eventually_info
    type historically_info
    type always_info
    type since_info
    type until_info

    val empty_binop_info: binop_info
    val empty_nop_info: int -> nop_info

    type core_t =
      | MTT
      | MFF
      | MEqConst      of Term.t * Dom.t
      | MPredicate    of string * Term.t list
      | MAgg          of string * Aggregation.op * Aggregation.op_fun * Term.t * string list * t
      | MTop          of string list * string * Aggregation.op_tfun * Term.t list * string list * t
      | MNeg          of t
      | MAnd          of Side.t * t list * nop_info
      | MOr           of Side.t * t list * nop_info
      | MImp          of Side.t * t * t * binop_info
      | MExists       of string * Dom.tt * bool * t
      | MForall       of string * Dom.tt * bool *  t
      | MPrev         of Interval.t * t * prev_info
      | MNext         of Interval.t * t * next_info
      | MENext        of Interval.t * timestamp option * t * Etc.valuation
      | MOnce         of Interval.t * t * once_info
      | MEventually   of Interval.t * t * eventually_info
      | MEEventually  of Interval.t * timestamp option * t * Etc.valuation
      | MHistorically of Interval.t * t * historically_info
      | MAlways       of Interval.t * t * always_info
      | MEAlways      of Interval.t * timestamp option * t * Etc.valuation
      | MSince        of Side.t * Interval.t * t * t * since_info
      | MUntil        of Interval.t * t * t * until_info
      | MEUntil       of Side.t * Interval.t * timestamp option * t * t * Etc.valuation

    and t = { mf: core_t;
              filter: Filter.t;
              events: (string, String.comparator_witness) Set.t option;
              obligations: (int, Int.comparator_witness) Set.t option;
              hash: int;
              lbls: Lbl.t list }

    val make: core_t -> Filter.t -> t
    val set_make: core_t -> Filter.t -> t
    val map_mf: t -> Filter.t -> ?exquant:bool -> (t -> core_t) -> t
    val map2_mf: t -> t -> Filter.t -> (t -> t -> core_t) -> t
    val mapn_mf: t list -> Filter.t -> (t list -> core_t) -> t

    val _tt : t
    val _ff : t

    val init: Tformula.t -> t
    val rank: t -> int


    val apply_valuation : Etc.valuation -> t -> t

    val fv: t -> (String.t, Base.String.comparator_witness) Base.Set.t
    (*val terms: t -> (Term.t, Term.comparator_witness) Base.Set.t*)

    val to_string: ?l:int -> t -> string
    val op_to_string: t -> string
    val side_to_string: t -> string

  end

  module FObligation : sig

    type polarity = POS | NEG

    type kind =
      | FFormula of MFormula.t * int * Etc.valuation                         (* fun _ -> f *)
      | FInterval of timestamp * Interval.t * MFormula.t * int * Etc.valuation  (* fun t -> if mem t i then f else Formula.TT *)
      | FUntil of timestamp * Side.t * Interval.t * MFormula.t * MFormula.t * int * Etc.valuation (* fun t -> Until (s, sub2 i (t-t0), f1, f2) *)
      | FAlways of timestamp * Interval.t * MFormula.t * int * Etc.valuation     (* fun t -> Always (sub2 i (t-t0), f1) *)
      | FEventually of timestamp * Interval.t * MFormula.t * int * Etc.valuation (* fun t -> Eventually (sub2 i (t-t0), f1) *)

    type t = kind * Etc.valuation * polarity

    (*val equal: t -> t -> bool*)
    val eval: timestamp -> int -> t -> MFormula.t
    val to_string: t -> string
    val h: t -> int

    include Comparable.S with type t := t

  end

  module FObligations : sig

    type t = (FObligation.t, FObligation.comparator_witness) Set.t

    val to_string: t -> string
    val empty: t
    val accepts_empty: t -> bool

  end


  module MState : sig

    type t = { mf: MFormula.t
             ; tp_cur: timepoint
             ; tp_out: timepoint
             ; ts_waiting: timestamp Queue.t
             ; tsdbs: (timestamp * Db.t) Queue.t
             ; tpts: (timepoint, timestamp) Hashtbl.t }

    val tp_cur: t -> timepoint

    val tsdbs: t -> (timestamp * Db.t) Queue.t

    val init: MFormula.t -> t

    val to_string: string -> t -> string

  end

  module Memo : sig

    type 'a t
    
    val find : 'a t -> MFormula.t -> 'a option
    val add_event : 'a t -> string -> 'a t
    val add_obligation : 'a t -> int -> 'a t
    val empty : 'a t
    
  end

  type res = Expl.t list * Expl.t * MFormula.t

  val mstep: timepoint -> timestamp -> Db.t -> bool -> MState.t -> FObligations.t ->
             res Memo.t -> res Memo.t * (((timepoint * timestamp) * Expl.t) list * Expl.t * MState.t)

  val meval_c: int ref

end

open Expl

(* let minp_list = Proof.Size.minp_list *)
(* let minp_bool = Proof.Size.minp_bool *)
(* let minp = Proof.Size.minp *)
let minp_list = List.hd_exn
let minp_bool = fun _ _ -> true
(*let minp = fun p1 _ -> p1*)

let s_append_deque sp1 d =
  Fdeque.map d ~f:(fun (ts, ssp) ->
      match ssp with
      | true -> (ts, true)
      | false -> raise (Errors.MonitoringError "found V proof in S deque"))

(*let v_append_deque vp2 d =
  Fdeque.map d ~f:(fun (ts, vvp) ->
  match vvp with
  | Proof.V vp -> (ts, Proof.V (Proof.v_append vp vp2))
  | S _ -> raise (Invalid_argument "found S proof in V deque"))*)

let remove_cond_front f deque =
  let rec remove_cond_front_rec d = match Fdeque.dequeue_front d with
    | None -> d
    | Some(el', d') -> if (f el') then remove_cond_front_rec d'
                       else Fdeque.enqueue_front d' el' in
  remove_cond_front_rec deque

let remove_cond_back f deque =
  let rec remove_cond_back_rec d = match Fdeque.dequeue_back d with
    | None -> d
    | Some(el', d') -> if (f el') then remove_cond_back_rec d'
                       else Fdeque.enqueue_back d' el' in
  remove_cond_back_rec deque

let remove_cond_front_ne f deque =
  let rec remove_cond_front_ne_rec d =
    if (Fdeque.length d) > 1 then
      (match Fdeque.dequeue_front d with
       | None -> d
       | Some(el', d') -> if (f el') then remove_cond_front_ne_rec d'
                          else Fdeque.enqueue_front d' el')
    else d in
  remove_cond_front_ne_rec deque

let sorted_append new_in deque =
  Fdeque.fold new_in ~init:deque ~f:(fun d (ts, p) ->
      let d' = remove_cond_back (fun (_, p') -> minp_bool p p') d in
      Fdeque.enqueue_back d' (ts, p))

let sorted_enqueue (ts, p) deque =
  let d' = remove_cond_back (fun (_, p') -> minp_bool p p') deque in
  Fdeque.enqueue_back d' (ts, p)



let etp tstps_in tstps_out tp =
  match Fdeque.peek_front tstps_in with
  | None -> (match Fdeque.peek_front tstps_out with
             | None -> tp
             | Some (_, tp') -> tp')
  | Some (_, tp') -> tp'

let ready_tstps b nts tstps_out tstps_in =
  let tstps' = Fdeque.fold tstps_out ~init:Fdeque.empty ~f:(fun tstps (ts, tp) ->
                   if Time.(ts + b < nts) then Fdeque.enqueue_back tstps (ts, tp) else tstps) in
  Fdeque.fold tstps_in ~init:tstps' ~f:(fun tstps (ts, tp) ->
      if Time.(ts + b < nts) then Fdeque.enqueue_back tstps (ts, tp) else tstps)

let first_ts_tp tstps_out tstps_in =
  match Fdeque.peek_front tstps_out with
  | None -> (match Fdeque.peek_front tstps_in with
             | None -> None
             | Some(ts, tp) -> Some(ts, tp))
  | Some(ts, tp) -> Some(ts, tp)

let drop_first_ts_tp tstps_out tstps_in =
  match Fdeque.peek_front tstps_out with
  | None -> (tstps_out, Fdeque.drop_front_exn tstps_in)
  | Some _ -> (Fdeque.drop_front_exn tstps_out, tstps_in)

let add_tstp_future a _ nts ntp tstps_out tstps_in =
  (* (ts, tp) update is performed differently if the queues are not empty *)
  if not (Fdeque.is_empty tstps_out) || not (Fdeque.is_empty tstps_in) then
    let first_ts = match first_ts_tp tstps_out tstps_in with
      | None -> raise (Errors.MonitoringError "tstps deques are empty")
      | Some(ts', _) -> ts' in
    if Time.(nts < first_ts + a) then (Fdeque.enqueue_back tstps_out (nts, ntp), tstps_in)
    else (tstps_out, Fdeque.enqueue_back tstps_in (nts, ntp))
  else
    (if Time.Span.is_zero a then (tstps_out, Fdeque.enqueue_back tstps_in (nts, ntp))
     else (Fdeque.enqueue_back tstps_out (nts, ntp), tstps_in))

let shift_tstps_future a first_ts ntp tstps_out tstps_in =
  let tstps_out' = Fdeque.fold tstps_in ~init:tstps_out ~f:(fun tstps_out' (ts', tp') ->
                       if Time.(ts' < first_ts + a) && (tp' < ntp) then
                         Fdeque.enqueue_back tstps_out' (ts', tp')
                       else tstps_out') in
  (remove_cond_front (fun (ts', tp') -> Time.(ts' < first_ts) && (tp' < ntp)) tstps_out',
   remove_cond_front (fun (ts', tp') -> Time.(ts' < first_ts + a) && (tp' < ntp)) tstps_in)

let shift_tstps_past (l, r) a ts tp tstps_in tstps_out =
  if Time.Span.is_zero a then
    (remove_cond_front (fun (ts', _) -> Time.(ts' < l)) (Fdeque.enqueue_back tstps_in (ts, tp)), tstps_out)
  else
    let tstps_out' = Fdeque.enqueue_back tstps_out (ts, tp) in
    (remove_cond_front (fun (ts', _) -> Time.(ts' < l))
       (Fdeque.fold tstps_out' ~init:tstps_in ~f:(fun tstps_in' (ts', tp') ->
            if Time.(ts' <= r) then Fdeque.enqueue_back tstps_in' (ts', tp')
            else tstps_in')),
     remove_cond_front (fun (ts', _) -> Time.(ts' <= r)) tstps_out')


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

module Prev = struct

  type t = { first: bool;
             itv  : Interval.t;
             tstps: (timestamp * timepoint) list;
             buf  : Expl.t list }

  let init itv = { first = true; itv; tstps = []; buf = [] }

  let to_string aux =
    Printf.sprintf "{ first = %b; itv = %s; tstps = %s; buf = %s }"
      aux.first (Interval.to_string aux.itv)
      (Etc.list_to_string "" (fun _ (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.tstps)
      (Etc.list_to_string "" (fun _ -> Expl.to_string) aux.buf)  

  let rec update (lbls : Lbl.t list) (aux : t) : t * Expl.t TS.t list =
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

  let approximate tp expls =
    match List.last expls with
    | Some te when TS.tp te = tp -> Some te.data
    | _ -> None

  let map f aux = { aux with buf = List.map ~f aux.buf }

end

module Next = struct

  type t = { itv       : Interval.t;
             tstps     : (timestamp * timepoint) list;
             tstps_todo: (timestamp * timepoint) list;
             buf       : Expl.t list }

  let init itv = { itv; tstps = []; tstps_todo = []; buf = [] }

  let to_string aux =
    Printf.sprintf "{ itv = %s; tstps = %s; tstps_todo = %s; buf = %s }"
      (Interval.to_string aux.itv)
      (Etc.list_to_string "" (fun _ (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.tstps)
      (Etc.list_to_string "" (fun _ (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.tstps_todo)
      (Etc.list_to_string "" (fun _ -> Expl.to_string) aux.buf)

  let rec update (lbls : Lbl.t list) (aux : t) : t * Expl.t TS.t list = 
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

  type alpha_t = { alphas_in : Tdeque.t;
                   alphas_out: Tdeque.t } [@@deriving compare, sexp_of, hash, equal]

  let equal_alpha_t_bool (oaux, b) (oaux', b') =
    equal_alpha_t oaux oaux' && Bool.equal b b'

  type t = { oaux   : alpha_t Pdt.t;
             itv_in : Interval.t;
             itv_out: Interval.t option;
             buf    : (Expl.t, (timestamp * timepoint)) Buft.t;
             neg    : bool }

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
      (Buft.to_string Expl.to_string (fun (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.buf)
      aux.neg
  
  let rec update (lbls: Lbl.t list) (aux : t) : t * Expl.t TS.t list =
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
       let oaux, b = Pdt.split_prod (Pdt.apply2_reduce equal_alpha_t_bool lbls (process ts tp) expl_pdt aux.oaux) in
       let aux = { aux with oaux; buf } in
       let aux, bs = update lbls aux in
       aux, (TS.make tp ts b)::bs
    | _ -> aux, []

  let approximate i b neg =
    Bool.equal neg (b && Interval.has_zero i)

  let map f g (aux: t) =
    { aux with oaux = f aux.oaux; buf = Buft.map g (fun t -> t) aux.buf }
  
end

module Eventually = struct

  type alpha_t = { alphas_in : Tdeque.t;
                   alphas_out: Tdeque.t } [@@deriving compare, sexp_of, hash, equal]

  let equal_alpha_t_bool (eaux, b) (eaux', b') =
    equal_alpha_t eaux eaux' && Bool.equal b b'

  type t = { eaux      : alpha_t Pdt.t;
             itv_in    : Interval.t;
             itv_out   : Interval.t;
             tstps_todo: (timestamp * timepoint) list;
             buf       : (Expl.t, timestamp * timepoint) Buft.t;
             neg       : bool }

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
      (Buft.to_string Expl.to_string (fun (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.buf)
      aux.neg
  
  let rec update (lbls: Lbl.t list) (aux : t) : t * Expl.t TS.t list =
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
    let rec load ?(ts_opt=None) aux =
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

  let approximate tp i is_pos b_next b_now =
    (*print_endline (Proof.to_string "pnext=" p_next);
      print_endline (Proof.to_string "pnow=" p_now);
      print_endline (Interval.to_string i);
      print_endline (Bool.to_string is_pos);*)
    match b_next, b_now, Interval.left i, is_pos with
    | _    , true , a, true when Time.Span.is_zero a        -> true
    | true , _    , a, true when not (Time.Span.is_zero a)  -> true
    | _    , _    , _, true                                 -> false
    | false, false, a, false when Time.Span.is_zero a       -> false
    | false, _    , a, false when not (Time.Span.is_zero a) -> false
    | _    , _    , _, false                                -> true

  let approximate_always tp i is_pos b_next b_now =
    match b_next, b_now, Interval.left i, is_pos with
    | _    , false, a, false when Time.Span.is_zero a       -> false
    | false, _    , a, false when not (Time.Span.is_zero a) -> false
    | _    , _    , _, false                                -> false
    | true , true , a, true when Time.Span.is_zero a        -> true
    | true , _    , a, true when not (Time.Span.is_zero a)  -> true
    | _    , _    , _, true                                 -> false

  let map f g (aux: t) =
    { aux with eaux = f aux.eaux; buf = Buft.map g (fun t -> t) aux.buf }
  
end

module Since = struct

  type beta_alphas_t = { beta_alphas_in : Tdeque.t;
                         beta_alphas_out: Tdeque.t } [@@deriving compare, sexp_of, hash, equal]

  let equal_beta_alphas_t_bool (saux, b) (saux', b') =
    equal_beta_alphas_t saux saux' && Bool.equal b b'

  type t = { saux   : beta_alphas_t Pdt.t;
             itv_in : Interval.t;
             itv_out: Interval.t option;
             buf    : (Expl.t, Expl.t, timestamp * timepoint) Buf2t.t }

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
      (Buf2t.to_string Expl.to_string Expl.to_string (fun (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.buf)
  
  let rec update (lbls: Lbl.t list) (aux : t) : t * Expl.t TS.t list =
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

  let approximate tp a pol b_alpha b_beta =
    match b_alpha, b_beta, pol with
      | _    , true, true when Time.Span.is_zero a        -> true
      | _    , _   , true                                 -> false
      | false, _   , false when not (Time.Span.is_zero a) -> false
      | _    , _   , false                                -> true

  let map f g (aux: t) =
    { aux with saux = f aux.saux; buf = Buf2t.map g g (fun t -> t) aux.buf }
  
end

module Until = struct

  type alphas_beta_t = { alpha_in : Tdeque.t;
                         alpha_out: Tdeque.t;
                         beta_in  : Tdeque.t;
                         beta_out : Tdeque.t } [@@deriving compare, sexp_of, hash, equal]

  type t = { uaux        : alphas_beta_t Pdt.t;
             itv_beta_in : Interval.t;
             itv_alpha_in: Interval.t;
             itv_out     : Interval.t;
             tstps_todo  : (timestamp * timepoint) list;
             buf         : (Expl.t, Expl.t, timestamp * timepoint) Buf2t.t }

  let beta_alphas_to_string =
    Pdt.to_string (fun o -> Printf.sprintf "{ alpha_in = %s; alpha_out = %s; beta_in = %s; beta_out = %s }"
                              (Tdeque.to_string o.alpha_in) (Tdeque.to_string o.alpha_out) (Tdeque.to_string o.beta_in) (Tdeque.to_string o.beta_out)) ""

  let to_string aux =
    Printf.sprintf "{ uaux = %s; itv_beta_in = %s; itv_alpha_in = %s; itv_out = %s; tstps_todo = %s; buf = %s }"
      (beta_alphas_to_string aux.uaux)
      (Interval.to_string aux.itv_beta_in)
      (Interval.to_string aux.itv_alpha_in)
      (Interval.to_string aux.itv_out)
      (Etc.list_to_string "" (fun _ (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.tstps_todo)
      (Buf2t.to_string Expl.to_string Expl.to_string (fun (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.buf)


  let init itv_beta_in = { uaux         = Pdt.Leaf { alpha_in  = Tdeque.empty
                                                   ; alpha_out = Tdeque.empty
                                                   ; beta_in   = Tdeque.empty
                                                   ; beta_out  = Tdeque.empty };
                           itv_beta_in;
                           itv_alpha_in = Interval.to_zero itv_beta_in;
                           itv_out      = Option.value_exn (Interval.out_right itv_beta_in);
                           tstps_todo   = [];
                           buf          = (([], []), []) }
  
  let rec update (lbls: Lbl.t list) (aux : t) : t * Expl.t TS.t list =
    let process (ts: timestamp) (tp: timepoint) (uaux : alphas_beta_t) : alphas_beta_t * bool = 
      (* Move timestamps from alpha_out to alpha_in if they are outside of ts + i *)
      let alpha_out, alpha_in = Tdeque.split_right uaux.alpha_out uaux.alpha_in ts aux.itv_out in
      (* Remove timestamps from alpha_in when they are too old *)
      let alphas_in = Tdeque.clean_right alpha_in ts aux.itv_alpha_in in
      (* Move timestamps from beta_out to beta_in if they are outside of ts + i *)
      let beta_out, beta_in = Tdeque.split_right uaux.beta_out uaux.beta_in ts aux.itv_out in
      (* Remove timestamps from beta_in when they are too old *)
      let beta_in = Tdeque.clean_right beta_in ts aux.itv_beta_in in
      let b = Tdeque.compute_until alpha_in beta_in in
      (* Return true iff alphas_in is not empty *)
      { uaux with alpha_in; alpha_out; beta_in; beta_out }, b
    in
    let load1 ts tp b_alpha b_beta uaux =
      (* Insert timestamp into alpha_out *)
      let alpha_out = if not b_alpha
                      then Tdeque.enqueue_back uaux.alpha_out ts
                      else uaux.alpha_out in
      (* Insert timestamp into beta_out *)
      let beta_out = if b_beta
                     then Tdeque.enqueue_back uaux.beta_out ts
                     else uaux.beta_out in
      { uaux with alpha_out; beta_out }
    in
    let rec load ?(ts_opt=None) uaux =
      match Buf2t.get uaux.buf with
      | Some ((expl_alpha_pdt, expl_beta_pdt), (ts, tp)), buf ->
         let uaux = Pdt.apply3_reduce equal_alphas_beta_t lbls (load1 ts tp) expl_alpha_pdt expl_beta_pdt aux.uaux in
         let aux = { aux with uaux; buf } in
         load ~ts_opt:(Some ts) aux
      | _ -> ts_opt, aux
    in
    let ts_opt, aux = load aux in
    match aux.tstps_todo, ts_opt with
    | (ts, tp)::tstps_todo, Some ts' when Interval.diff_right_of ts ts' aux.itv_beta_in -> 
       let uaux, b = Pdt.split_prod (Pdt.apply1 lbls (process ts tp) aux.uaux) in
       let aux = { aux with uaux; tstps_todo } in
       let aux, bs = update lbls aux in
       aux, (TS.make tp ts b)::bs
    | _ -> aux, []

  let approximate tp i pol b_alpha b_beta b_next =
    match b_alpha, b_beta, b_next, pol with
    | _    , true , _    , true when Interval.has_zero i        -> true
    | true , _    , true , true                                 -> true
    | _    , _    , _    , true                                 -> false
    | false, _    , _    , false when not (Interval.has_zero i) -> false
    | false, false, _    , false                                -> false
    | _    , _    , _    , false                                -> true

  let map f g (aux: t) =
    { aux with uaux = f aux.uaux; buf = Buf2t.map g g (fun t -> t) aux.buf }

end


module MFormula = struct

  type binop_info         = (Expl.t TS.t, Expl.t TS.t) Buf2.t
  type nop_info           = Expl.t TS.t Bufn.t
  type prev_info          = Prev.t
  type next_info          = Next.t
  type once_info          = Once.t
  type eventually_info    = Eventually.t
  type historically_info  = Once.t
  type always_info        = Eventually.t
  type since_info         = Since.t
  type until_info         = Until.t

  let empty_binop_info = ([], [])
  let empty_nop_info = Bufn.empty

  type core_t =
    | MTT
    | MFF
    | MEqConst      of Term.t * Dom.t
    | MPredicate    of string * Term.t list
    | MAgg          of string * Aggregation.op * Aggregation.op_fun * Term.t * string list * t
    | MTop          of string list * string * Aggregation.op_tfun * Term.t list * string list * t
    | MNeg          of t
    | MAnd          of Side.t * t list * nop_info
    | MOr           of Side.t * t list * nop_info
    | MImp          of Side.t * t * t * binop_info
    | MExists       of string * Dom.tt * bool * t
    | MForall       of string * Dom.tt * bool * t
    | MPrev         of Interval.t * t * prev_info
    | MNext         of Interval.t * t * next_info
    | MENext        of Interval.t * timestamp option * t * Etc.valuation
    | MOnce         of Interval.t * t * once_info
    | MEventually   of Interval.t * t * eventually_info
    | MEEventually  of Interval.t * timestamp option * t * Etc.valuation
    | MHistorically of Interval.t * t * historically_info
    | MAlways       of Interval.t * t * always_info
    | MEAlways      of Interval.t * timestamp option * t * Etc.valuation
    | MSince        of Side.t * Interval.t * t * t * since_info
    | MUntil        of Interval.t * t * t * until_info
    | MEUntil       of Side.t * Interval.t * timestamp option *  t * t * Etc.valuation

  and t = { mf: core_t;
            filter: Filter.t;
            events: (string, String.comparator_witness) Set.t option;
            obligations: (int, Int.comparator_witness) Set.t option;
            hash: int;
            lbls: Lbl.t list
          }

  let subs mf = match mf.mf with
    | MTT | MFF | MEqConst _ | MPredicate _ -> []
    | MExists (_, _, _, f)
      | MForall (_, _, _, f) 
      | MNeg f
      | MPrev (_, f, _)
      | MOnce (_, f, _)
      | MHistorically (_, f, _)
      | MEventually (_, f, _)
      | MEEventually (_, _, f, _)
      | MAlways (_, f, _)
      | MEAlways (_, _, f, _)
      | MNext (_, f, _)
      | MENext (_, _, f, _)
      | MAgg (_, _, _, _, _, f)
      | MTop (_, _, _, _, _, f) -> [f]
    | MImp (_, f1, f2, _)
      | MSince (_, _, f1, f2, _)
      | MUntil (_, f1, f2, _)
      | MEUntil (_, _, _, f1, f2, _) -> [f1; f2]
    | MAnd (_, fs, _)
      | MOr (_, fs, _) -> fs

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
    | MENext (i, ts, f, _) -> Printf.sprintf (Etc.paren l 5 "○*%a %a") (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) f
    | MOnce (i, f, _) -> Printf.sprintf (Etc.paren l 5 "⧫%a %a") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f
    | MEventually (i, f, _) -> Printf.sprintf (Etc.paren l 5 "◊%a %a") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f
    | MEEventually (i, ts, f, _) -> Printf.sprintf (Etc.paren l 5 "◊*%a %a") (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) f
    | MHistorically (i, f, _) -> Printf.sprintf (Etc.paren l 5 "■%a %a") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f
    | MAlways (i, f, _) -> Printf.sprintf (Etc.paren l 5 "□%a %a") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f
    | MEAlways (i, ts, f, _) -> Printf.sprintf (Etc.paren l 5 "□*%a %a") (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) f
    | MSince (_, i, f, g, _) -> Printf.sprintf (Etc.paren l 0 "%a S%a %a") (fun _ -> value_to_string_rec 5) f
                                  (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) g
    | MUntil (i, f, g, _) -> Printf.sprintf (Etc.paren l 0 "%a U%a %a") (fun _ -> value_to_string_rec 5) f
                               (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) g
    | MEUntil (_, i, ts, f, g, _) -> Printf.sprintf (Etc.paren l 0 "%a U*%a %a") (fun _ -> value_to_string_rec 5) f
                                       (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) g
  let value_to_string = value_to_string_rec 0

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
    | MENext (i, ts, f, _) -> Printf.sprintf (Etc.paren l 5 "○*%a %a") (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) f
    | MOnce (i, f, aux) -> Printf.sprintf (Etc.paren l 5 "{ f = ⧫%a %a; aux = %a }") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f (fun _ -> Once.to_string) aux
    | MEventually (i, f, aux) -> Printf.sprintf (Etc.paren l 5 "{ f = ◊%a %a; aux = %a }") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f (fun _ -> Eventually.to_string) aux
    | MEEventually (i, ts, f, _) -> Printf.sprintf (Etc.paren l 5 "◊*%a %a") (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) f
    | MHistorically (i, f, aux) -> Printf.sprintf (Etc.paren l 5 "{ f = ■%a %a; aux = %a }") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f (fun _ -> Once.to_string) aux
    | MAlways (i, f, aux) -> Printf.sprintf (Etc.paren l 5 "{ f = □%a %a; aux = %a }") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f (fun _ -> Eventually.to_string) aux
    | MEAlways (i, ts, f, _) -> Printf.sprintf (Etc.paren l 5 "□*%a %a") (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) f
    | MSince (_, i, f, g, aux) -> Printf.sprintf (Etc.paren l 0 "{ f = %a S%a %a; aux = %a }") (fun _ -> value_to_string_rec 5) f 
                                    (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) g
                                    (fun _ -> Since.to_string) aux
    | MUntil (i, f, g, aux) -> Printf.sprintf (Etc.paren l 0 "{ f = %a U%a %a; aux = %a }") (fun _ -> value_to_string_rec 5) f
                                 (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) g
                                 (fun _ -> Until.to_string) aux
    | MEUntil (_, i, ts, f, g, _) -> Printf.sprintf (Etc.paren l 0 "%a U*%a %a") (fun _ -> value_to_string_rec 5) f
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
    | MENext (i, ts, _, _) -> Printf.sprintf "○*%s" (ts_i_to_string (ts, i))
    | MOnce (i, _, _) -> Printf.sprintf "⧫%s" (Interval.to_string i)
    | MEventually (i, _, _) -> Printf.sprintf "◊%s" (Interval.to_string i)
    | MEEventually (i, ts, _, _) -> Printf.sprintf "◊*%s" (ts_i_to_string (ts, i))
    | MHistorically (i, _, _) -> Printf.sprintf "■%s" (Interval.to_string i)
    | MAlways (i, _, _) -> Printf.sprintf "□%s" (Interval.to_string i)
    | MEAlways (i, ts, _, _) -> Printf.sprintf "□*%s" (ts_i_to_string (ts, i))
    | MSince (_, i, _, _, _) -> Printf.sprintf "S%s" (Interval.to_string i)
    | MUntil (i, _, _, _) -> Printf.sprintf "U%s" (Interval.to_string i)
    | MEUntil (_, i, ts, _, _, _) -> Printf.sprintf "U*%s" (ts_i_to_string (ts, i))

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
    | MEUntil (s, _, _, _, _, _) -> Printf.sprintf "%s" (Side.to_string s)

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
    | MENext (i, _, f, _) ->
       String.hash "MENext" +++ Interval.hash i +++ f.hash
    | MOnce (i, f, _) ->
       String.hash "MOnce" +++ Interval.hash i +++ f.hash
    | MEventually (i, f, _) ->
       String.hash "MEventually" +++ Interval.hash i +++ f.hash
    | MEEventually (i, _, f, v) ->
       String.hash "MEEventually" +++ Interval.hash i +++ f.hash +++ Etc.hash_valuation v
    | MHistorically (i, f, _) ->
       String.hash "MHistorically" +++ Interval.hash i +++ f.hash
    | MAlways (i, f, _) ->
       String.hash "MAlways" +++ Interval.hash i +++ f.hash
    | MEAlways (i, _, f, v) ->
       String.hash "MEAlways" +++ Interval.hash i +++ f.hash +++ Etc.hash_valuation v
    | MSince (s, i, f, g, _) ->
       String.hash "MSince" +++ Side.hash s +++ Interval.hash i +++ f.hash +++ g.hash
    | MUntil (i, f, g, _) ->
       String.hash "MUntil" +++ Interval.hash i +++ f.hash +++ g.hash
    | MEUntil (s, i, _, f, g, v) ->
       String.hash "MEUntil" +++ Side.hash s +++ Interval.hash i +++ f.hash
       +++ g.hash +++ Etc.hash_valuation v

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
       | MENext (i, t_opt, f, v) -> add_hash (map1 f (fun f -> MENext (i, t_opt, f, v)))
       | MOnce (i, f, inf) -> map1 f (fun f -> MOnce (i, f, inf))
       | MEventually (i, f, inf) -> map1 f (fun f -> MEventually (i, f, inf))
       | MEEventually (i, t_opt, f, v) -> add_hash (map1 f (fun f -> MEEventually (i, t_opt, f, v)))
       | MHistorically (i, f, inf) -> map1 f (fun f -> MHistorically (i, f, inf))
       | MAlways (i, f, inf) -> map1 f (fun f -> MAlways (i, f, inf))
       | MEAlways (i, t_opt, f, inf) -> add_hash (map1 f (fun f -> MEAlways (i, t_opt, f, inf)))
       | MSince (s, i, f, g, inf) -> map2 f g (fun f g -> MSince (s, i, f, g, inf))
       | MUntil (i, f, g, inf) -> map2 f g (fun f g -> MUntil (i, f, g, inf))
       | MEUntil (s, i, t_opt, f, g, v) -> add_hash (map2 f g (fun f g -> MEUntil (s, i, t_opt, f, g, v)))

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
      | MEUntil (_, _, _, f, g, _) -> Set.union (fv f) (fv g)
    | MExists (_, _, _, f)
      | MForall (_, _, _, f)
      | MPrev (_, f, _)
      | MNext (_, f, _)
      | MENext (_, _, f, _)
      | MOnce (_, f, _) 
      | MEventually (_, f, _)
      | MEEventually (_, _, f, _)
      | MHistorically (_, f, _)
      | MAlways (_, f, _)
      | MEAlways (_, _, f, _) -> fv f

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
      (*print_endline (Printf.sprintf "filter_lbls_vars([%s], [%s], %b) = [%s]\n"
        (Lbl.to_string_list lbls)
        (String.concat ~sep:", " fvs)
        keep_nonvars
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
      | MENext (i, t_opt, f, v) -> map1 fvs f (fun f -> MENext (i, t_opt, f, v)) id
      | MOnce (i, f, inf) -> map1 fvs f (fun f -> MOnce (i, f, inf)) id
      | MEventually (i, f, inf) -> map1 fvs f (fun f -> MEventually (i, f, inf)) id
      | MEEventually (i, t_opt, f, v) -> map1 fvs f (fun f -> MEEventually (i, t_opt, f, v)) id
      | MHistorically (i, f, inf) -> map1 fvs f (fun f -> MHistorically (i, f, inf)) id
      | MAlways (i, f, inf) -> map1 fvs f (fun f -> MAlways (i, f, inf)) id
      | MEAlways (i, t_opt, f, inf) -> map1 fvs f (fun f -> MEAlways (i, t_opt, f, inf)) id
      | MSince (s, i, f, g, inf) -> map2 fvs f g (fun f g -> MSince (s, i, f, g, inf)) id2
      | MUntil (i, f, g, inf) -> map2 fvs f g (fun f g -> MUntil (i, f, g, inf)) id2
      | MEUntil (s, i, t_opt, f, g, v) -> map2 fvs f g (fun f g -> MEUntil (s, i, t_opt, f, g, v)) id2 in
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
      | Next (i, f) -> MENext (i, None, make (aux f) f.info.filter, Etc.empty_valuation)
      | Once (i, f) -> MOnce (i, make (aux f) f.info.filter, Once.init i true)
      | Eventually (i, f) when Enftype.is_only_observable tf.info.enftype ->
         MEventually (i, make (aux f) f.info.filter, Eventually.init i true)
      | Eventually (i, f) -> MEEventually (i, None, make (aux f) f.info.filter, Etc.empty_valuation)
      | Historically (i, f) -> MHistorically (i, make (aux f) f.info.filter, Once.init i false)
      | Always (i, f) when Enftype.is_only_observable tf.info.enftype ->
         MAlways (i, make (aux f) f.info.filter, Eventually.init i false)
      | Always (i, f) -> MEAlways (i, None, make (aux f) f.info.filter, Etc.empty_valuation)
      | Since (s, i, f, g) ->
         MSince (s, i, make (aux f) f.info.filter, make (aux g) g.info.filter, Since.init i)
      | Until (_, i, f, g) when Enftype.is_only_observable tf.info.enftype ->
         MUntil (i, make (aux f) f.info.filter, make (aux g) g.info.filter, Until.init i)
      | Until (s, i, f, g) ->
         MEUntil (s, i, None, make (aux f) f.info.filter, make (aux g) g.info.filter, Etc.empty_valuation)
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
      | MENext (_, _, f, _)
      | MOnce (_, f, _)
      | MEventually (_, f, _)
      | MEEventually (_, _, f, _)
      | MHistorically (_, f, _)
      | MAlways (_, f, _)
      | MEAlways (_, _, f, _)
      | MAgg (_, _, _, _, _, f)
      | MTop (_, _, _, _, _, f) -> rank f
    | MImp (_, f, g, _)
      | MSince (_, _, f, g, _)
      | MUntil (_, f, g, _)
      | MEUntil (_, _, _, f, g, _) -> rank f + rank g
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
      | MExists (x, tt, b, f) -> MExists (x, tt, b, r f)
      | MForall (x, tt, b, f) -> MForall (x, tt, b, r f)
      | MPrev (i, f, pi) -> MPrev (i, r f, Prev.map spec pi)
      | MNext (i, f, si) -> MNext (i, r f, si)
      | MENext (i, ts, f, vv) -> MENext (i, ts, r f, Etc.extend_valuation v vv)
      | MOnce (i, f, oi) -> MOnce (i, r f, Once.map spec spec oi)
      | MEventually (i, f, oi) -> MEventually (i, r f, Eventually.map spec spec oi)
      | MEEventually (i, ts, f, vv) -> MEEventually (i, ts, r f, Etc.extend_valuation v vv)
      | MHistorically (i, f, oi) -> MHistorically (i, r f, Once.map spec spec oi)
      | MAlways (i, f, ai) -> MAlways (i, r f, Eventually.map spec spec ai)
      | MEAlways (i, ts, f, vv) -> MEAlways (i, ts, r f, Etc.extend_valuation v vv)
      | MSince (s, i, f, g, si) -> MSince (s, i, r f, r g, Since.map spec spec si)
      | MUntil (i, f, g, ui) -> MUntil (i, r f, r g, Until.map spec spec ui)
      | MEUntil (s, i, ts, f, g, vv) -> MEUntil (s, i, ts, r f, r g, Etc.extend_valuation v vv)
    in
    (*print_endline ("hash(apply_valuation(" ^ Etc.valuation_to_string v ^ ", " ^ to_string { mf; hash = 0 } ^ ")=" ^ (Int.to_string (make mf).hash));*)
    set_make mf_ mf.filter

end

module FObligation = struct

  include MFormula

  module T = struct

    type polarity = POS | NEG [@@deriving compare, sexp_of, hash]

    let neg = function POS -> NEG | NEG -> POS

    type kind =
      | FFormula of MFormula.t * int * Etc.valuation
      | FInterval of timestamp * Interval.t * MFormula.t * int * Etc.valuation
      | FUntil of timestamp * Side.t * Interval.t * MFormula.t * MFormula.t * int * Etc.valuation
      | FAlways of timestamp * Interval.t * MFormula.t * int * Etc.valuation
      | FEventually of timestamp * Interval.t * MFormula.t * int * Etc.valuation

    type t = kind * Etc.valuation * polarity

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

    let fold_map f es (k, v, pol) = let es, k = fold_map_kind f es k in es, (k, v, pol)

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
      Etc.lexicographic3 compare_kind Etc.compare_valuation compare_polarity

    let sexp_of_t _ = Sexp.Atom "FObligation"
    (*let t_of_sexp _ = (FFormula (_tt, 0, Etc.empty_valuation), Etc.empty_valuation, POS)*)

    let equal_polarity pol1 pol2 = match pol1, pol2 with
      | POS, POS -> true
      | NEG, NEG -> true
      | _ -> false

    (*let equal (k, v, pol) (k', v', pol') =
      kind_equal k k' && Map.equal Dom.equal v v' && equal_polarity pol pol'*)

    let corresp_proof tp pol _ = function
      | FFormula _ -> true
      | FInterval _ when equal_polarity pol POS -> true
      | FInterval (_, i, _, _, _) -> false
      | FUntil _ when equal_polarity pol POS -> true
      | FUntil _ -> false
      | FEventually _ when equal_polarity pol POS -> true
      | FEventually _ -> false
      | FAlways _ when equal_polarity pol POS -> true
      | FAlways _ -> false
    

    let polarity_to_string = function
      | POS -> "+"
      | NEG -> "-"

    let kind_to_string = function
      | FFormula (f, h, v) ->
         Printf.sprintf "FFormula(%s, %d, %s)" (to_string f) h (Etc.valuation_to_string v)
      | FInterval (ts, i, mf, h, v) ->
         Printf.sprintf "FInterval(%s, %s, %s, %d, %s)"
           (Time.to_string ts) (Interval.to_string i) (to_string mf)
           h (Etc.valuation_to_string v)
      | FUntil (ts, s, i, mf, mg, h, v) ->
         Printf.sprintf "FUntil(%s, %s, %s, %s, %s, %d, %s)"
           (Time.to_string ts) (Side.to_string s)
           (Interval.to_string i) (to_string mf) (to_string mg) h (Etc.valuation_to_string v)
      | FAlways (ts, i, mf, h, v) ->
         Printf.sprintf "FAlways(%s, %s, %s, %d, %s)"
           (Time.to_string ts) (Interval.to_string i) (to_string mf)
           h (Etc.valuation_to_string v)
      | FEventually (ts, i, mf, h, v) ->
         Printf.sprintf "FEventually(%s, %s, %s, %d, %s)"
           (Time.to_string ts) (Interval.to_string i) (to_string mf)
           h (Etc.valuation_to_string v)

    let to_string ((kind, valuation, pol) : t) =
      Printf.sprintf "Kind: %s; " (kind_to_string kind) ^
        Printf.sprintf "Valuation: %s; " (Etc.dom_map_to_string valuation) ^
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
             (fun mf -> MEUntil (R, i, Some ts, _neg_tp, mf, v))
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
             (fun mf1 mf2 -> MEUntil (side, i, Some ts, mf1, mf2, v))
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
             (fun mf -> MEAlways (i, Some ts, mf, v))
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
             (fun mf -> MEEventually (i, Some ts, mf, v))
         else
           _ff

    let eval ts tp (k, v, pol) =
      let mf = apply_valuation v (eval_kind ts tp k) in
      match pol with
      | POS -> (*print_endline (Printf.sprintf "eval()=%s" (MFormula.to_string mf)); *)mf
      | NEG -> match mf.mf with
               | MNeg mf -> mf
               | _       -> map_mf mf Filter.tt (fun mf -> MNeg mf) ~exquant:true


    let accepts_empty = function
      | (FFormula _, _, pol) -> equal_polarity pol NEG
      | (FInterval _, _, pol) -> equal_polarity pol NEG
      | (FUntil _, _, pol) -> equal_polarity pol NEG
      | (FAlways _, _, pol) -> equal_polarity pol POS
      | (FEventually _, _, pol) -> equal_polarity pol NEG

    let hv = function
      | FFormula (_, i, v) -> (i, v)
      | FInterval (_, _, _, i, v) -> (i, v)
      | FUntil (_, _, _, _, _, i, v) -> (i, v)
      | FAlways (_, _, _, i, v) -> (i, v)
      | FEventually (_, _, _, i, v) -> (i, v)

    let h (f, _, _) = fst (hv f)


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


(*let print_maps maps =
  Stdio.print_endline "> Map:";
  List.iter maps ~f:(fun map -> Map.iteri map ~f:(fun ~key:k ~data:v ->
  Stdio.printf "%s -> %s\n" (Term.to_string k) (Dom.to_string v)))*)

let pol_value = Option.value ~default:FObligation.POS

let proof_false = function
  | FObligation.POS -> false
  | NEG -> true

let approximate_false pol = Pdt.Leaf (proof_false pol)

let approximate_false_opt pol_opt =
  Pdt.Leaf (proof_false (pol_value pol_opt))

let els pol_opt = function
  | Some p -> p
  | None -> approximate_false (Option.value ~default:FObligation.POS pol_opt)

let approximate_once lbls (expls: Expl.t TS.t list) aexpl moaux tp pol =
  match List.last expls, pol with
  | Some expl, _ when expl.tp = tp -> expl.data
  | _, FObligation.POS ->
     Pdt.apply1_reduce Bool.equal lbls (Once.approximate moaux true) aexpl
  | _, _ -> approximate_false pol

let relevant_fobligs fobligs test h vv pol =
  let f (k, _, pol') =
    let (h', v') = FObligation.hv k in
    h = h' && Etc.equal_valuation v' vv && FObligation.equal_polarity pol pol' && test k
  in Set.elements (Set.filter fobligs ~f)

let expls_approx test tp pol vars fobligs h vv =
  let f (k, v, _) =  
    let p = FObligation.corresp_proof tp pol None k in
    let p' = proof_false pol in
    Pdt.from_valuation vars v p p' in
  List.map (relevant_fobligs fobligs test h vv pol) ~f

let approximate_eventually lbls aexpl (fobligs: FObligations.t) i h_opt tp pol =
  let aexpl_new = aexpl in
  let expls = match h_opt with
    | None -> []
    | Some (h, vv) -> begin
        (*let relevant_fobligs =
          Set.elements (Set.filter fobligs ~f:(fun (k, v, pol') ->
          match k with
          | FEventually (_, _, _, h', v') ->
          h = h' && Etc.equal_valuation vv v'
          && FObligation.polarity_equal pol pol'
          | _ -> false)) in*)
        (*let f (k, v, pol) =
          let p = FObligation.corresp_proof tp pol None k in
          let p' = proof_false tp pol in
          try
          Some (Pdt.from_valuation vars v p p')
          with Invalid_argument _ -> None in
          List.filter_map (relevant_fobligs fobligs FObligation.is_feventually h vv pol)  ~f*)
        expls_approx FObligation.is_feventually tp pol lbls fobligs h vv
      end in
  let aexpl_next = Pdt.applyN_reduce Bool.equal lbls (List.fold ~init:false ~f:(||)) expls in
  (*print_endline ("approx_eventually aexpl_new=" ^ Expl.to_string aexpl_new);
    print_endline ("approx_eventually aexpl_next=" ^ Expl.to_string aexpl_next);
    print_endline ("approx_eventually pol=" ^ FObligation.polarity_to_string pol);
    print_endline ("approx_eventually i=" ^ Interval.to_string i);*)
  Pdt.apply2_reduce Bool.equal lbls
    (fun p1 p2 -> Eventually.approximate tp i (FObligation.equal_polarity pol POS) p1 p2)
    aexpl_next aexpl_new

let approximate_historically vars (expls: Expl.t TS.t list) aexpl i tp pol =
  match List.last expls, pol with
  | Some expl, _ when expl.tp = tp -> expl.data
  | _, FObligation.NEG ->
     Pdt.apply1_reduce Bool.equal vars (Once.approximate i false) aexpl
  | _, _ -> approximate_false pol

let approximate_always lbls aexpl (fobligs: FObligations.t) i h_opt tp pol = (*TODO*)
  let aexpl_new = aexpl in
  let expls = match h_opt with
    | None -> []
    | Some (h, vv) -> begin
        (*let relevant_fobligs =
          Set.elements (Set.filter fobligs ~f:(fun (k, v, pol') ->
          match k with
          | FAlways (_, _, _, h', v') ->
          h = h' && Etc.equal_valuation vv v'
          && FObligation.polarity_equal pol pol'
          | _ -> false)) in*)
        expls_approx FObligation.is_falways tp pol lbls fobligs h vv
      end in
  let aexpl_next = Pdt.applyN_reduce Bool.equal lbls (List.fold ~init:false ~f:(||)) expls in
  Pdt.apply2_reduce Bool.equal lbls
    (fun p1 p2 -> Eventually.approximate_always tp i (FObligation.equal_polarity pol POS) p1 p2)
    aexpl_next aexpl_new 


let approximate_since lbls (expls: Expl.t TS.t list) aexpl1 aexpl2 i tp pol =
  match List.last expls, pol with
  | Some expl, _ when expl.tp = tp -> expl.data
  | _ -> Pdt.apply2_reduce Bool.equal lbls
           (Since.approximate tp (Interval.left i) (FObligation.equal_polarity pol FObligation.POS)) aexpl1 aexpl2

let approximate_quant aexpl x mf =
  match mf with
  | MExists _ -> Pdt.quantify ~forall:false x aexpl
  | MForall _ -> Pdt.quantify ~forall:true x aexpl
  | _ -> raise (Errors.MonitoringError
                  (Printf.sprintf "function is not defined for %s" (MFormula.core_op_to_string mf)))

let approximate_enext lbls (fobligs: FObligations.t) (h, vv) tp pol_opt = (*TODO*)
  let expls = expls_approx FObligation.is_finterval tp (pol_value pol_opt) lbls fobligs h vv in
  (*let relevant_fobligs =
    Set.elements (Set.filter fobligs ~f:(fun (k, _, pol') ->
    match k with
    | FInterval (_, _, _, h', v') ->
    h = h' && Etc.equal_valuation v' vv && FObligation.polarity_equal pol pol'
    | _ -> false)) in*)
  Pdt.applyN_reduce Bool.equal lbls (List.fold ~init:false ~f:(||)) expls 

let approximate_until lbls aexpl1 aexpl2 (fobligs: FObligations.t) i h_opt tp pol = (*TODO*)
  let aexpl_new1 = aexpl1 in
  let aexpl_new2 = aexpl2 in
  let expls = match h_opt with
    | None -> []
    | Some (h, vv) -> begin
        (*let relevant_fobligs =
          Set.elements (Set.filter fobligs ~f:(fun (k, v, pol') ->
          match k with
          | FUntil (_, s, _, _, _, h', v') ->
          h = h' && Etc.equal_valuation vv v'
          && FObligation.polarity_equal pol pol'
          | _ -> false)) in*)
        (*let f (k, v, _) =
          let p = FObligation.corresp_proof tp pol None k in
          let p' = proof_false tp pol in
          Pdt.from_valuation vars v p p' in
          List.map (relevant_fobligs fobligs FObligation.is_funtil h vv pol) ~f*)
        expls_approx FObligation.is_funtil tp pol lbls fobligs h vv
      end in
  let aexpl_next = Pdt.applyN_reduce Bool.equal lbls (List.fold ~init:false ~f:(||)) expls in
  (*print_endline ("approx_until aexpl_new1=" ^ Expl.to_string aexpl_new1);
    print_endline ("approx_until aexpl_new2=" ^ Expl.to_string aexpl_new2);
    print_endline ("approx_until aexpl_next=" ^ Expl.to_string aexpl_next);
    print_endline ("approx_until pol=" ^ FObligation.polarity_to_string pol);
    print_endline ("approx_until i=" ^ Interval.to_string i);
    print_endline ( CI.Expl.to_string (   Pdt.apply3_reduce Proof.equal vars
    (fun p1 p2 p3 -> Until.do_until_base tp i (pol == POS) p1 p2 p3)
    aexpl_new1 aexpl_new2 aexpl_next));*)
  Pdt.apply3_reduce Bool.equal lbls
    (fun p1 p2 p3 -> Until.approximate tp i (FObligation.equal_polarity pol POS) p1 p2 p3)
    aexpl_new1 aexpl_new2 aexpl_next

let meval_c = ref 0

(*let memo = Hashtbl.create (module Formula)*)


module Memo = struct

  type 'a t = { map: (int, 'a, Int.comparator_witness) Map.t;
                ex_events: (string, String.comparator_witness) Set.t;
                ex_obligations: (int, Int.comparator_witness) Set.t }

  let find memo mf =
    match Map.find memo.map mf.hash, mf.events, mf.obligations with
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
  let memoize memo mf res = { memo with map = Map.update memo.map mf.hash ~f:(fun _ -> res) }

(*let to_string (memo : 'a t) =
  Printf.sprintf "memo(map.keys = {%s};\n     ex_events = {%s};\n     ex_obligations = {%s}y)"
  (String.concat ~sep:", " (List.map (Map.keys memo.map) ~f:Int.to_string))
  (String.concat ~sep:", " (Set.elements memo.ex_events))
  (String.concat ~sep:", " (List.map ~f:Int.to_string (Set.elements memo.ex_obligations)))*)
  
end

let rec update_tstps tstps (expls: 'a TS.t list) : (timestamp * timepoint) list =
  let last_tp = Option.value (Option.map (List.last tstps) ~f:snd) ~default:(-1) in
  tstps @ List.filter_map expls ~f:(fun te -> if te.tp > last_tp then Some (te.ts, te.tp) else None) 

let rec update_tstps2 tstps expls1 expls2 =
  let tstps = update_tstps tstps expls1 in
  update_tstps tstps expls2


let meval (ts: timestamp) tp (db: Db.t) ~pol (fobligs: FObligations.t) mformula memo =
  let outer_tp = tp in
  let map_expl f (tp, (ts, x)) = (tp,  x) in
  let rec meval_rec (ts: timestamp) tp (db: Db.t) ~pol (fobligs: FObligations.t) memo mformula :
    'a *  (Expl.t TS.t list * Expl.t * MFormula.t) =
    (*print_endline "--meval_rec";
    print_endline ("mf=" ^ MFormula.to_string mformula);*)
    (*print_endline ("pol=" ^ Option.value_map pol ~default:"None" ~f:FObligation.polarity_to_string);*)
    (*print_endline "";*)
    (*print_endline ("memo=" ^ Memo.to_string memo);*)
    (*print_endline ("hash=" ^ Int.to_string mformula.hash);*)
    (*print_endline ("incr: " ^ MFormula.to_string mformula);*)
    Int.incr meval_c;
    match Memo.find memo mformula with
    | Some (expls, aexpl, mf) -> ((*print_endline ("meval:memo(" ^ Int.to_string mf.hash ^ ", " ^ Int.to_string tp ^ ")");*) (memo, (expls, aexpl, mf)))
    | None -> 
       let memo, (expls, aexpl, mf) =
         match mformula.mf with
         | MTT -> let expl = Pdt.Leaf true in
                  memo, ([TS.make tp ts expl], expl, MTT)
         | MFF -> let expl = Pdt.Leaf false in
                  memo, ([TS.make tp ts expl], expl, MFF)
         | MEqConst (trm, d) ->
            let expl = Pdt.Node (Lbl.of_term trm,
                                 [(Setc.Complement (Set.of_list (module Dom) [d]), Pdt.Leaf false);
                                  (Setc.Finite (Set.of_list (module Dom) [d]), Pdt.Leaf true)]) in
            memo, ([TS.make tp ts expl], expl, MEqConst (trm, d))
         | MPredicate (r, trms) when not (Enftype.is_observable (Sig.enftype_of_pred r)) ->
            (*print_endline ("not observable: " ^ r);*)
            let expl = Pdt.Leaf (not (FObligation.equal_polarity FObligation.POS
                                      (pol_value pol))) in
            memo, ([TS.make tp ts expl], expl, MPredicate (r, trms))
         | MPredicate (r, trms) ->
            let db' = match Sig.kind_of_pred r with
              | Trace -> Db.filter db ~f:(fun evt -> String.equal r (fst(evt)))
              | External -> Db.retrieve_external r
              | Builtin -> Db.retrieve_builtin ts tp r
              | Predicate -> raise (Errors.MonitoringError "cannot evaluate Predicate")
              | Let -> raise (Errors.MonitoringError "cannot evaluate Let") in
            if List.is_empty trms then
              (let expl = Pdt.Leaf (not (Db.is_empty db')) in
               memo, ([TS.make tp ts expl], expl, MPredicate (r, trms)))
            else
              let maps = List.filter_opt (
                             Set.fold (Db.events db') ~init:[]
                               ~f:(fun acc evt -> match_terms (List.map ~f:(fun x -> x.trm) trms) (snd evt)
                                                    (Map.empty (module Lbl)) :: acc)) in
              let expl = if List.is_empty maps
                         then Pdt.Leaf false
                         else Expl.pdt_of tp r trms mformula.lbls maps in
              (*print_endline "--MPredicate";
              print_endline ("r=" ^ r);
              print_endline ("db'=" ^ Db.to_string db');
              print_endline ("maps=" ^ (String.concat ~sep:"; " (List.map maps ~f:(fun map -> String.concat ~sep:", " (List.map (Map.to_alist map) ~f:(fun (lbl, d) -> Lbl.to_string lbl ^ " -> " ^ Dom.to_string d))))));
              print_endline ("expl=" ^ Expl.to_string expl);*)
              memo, ([TS.make tp ts expl], expl, MPredicate (r, trms))
         | MAgg (s, op, op_fun, x, y, mf) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db fobligs ~pol memo mf in
            (*print_endline ("--MAgg.aexpl=" ^ Expl.to_string aexpl);
              print_endline ("mf=" ^ MFormula.to_string mformula);
              print_endline ("aexpl=" ^ Expl.to_string aexpl);*)
            (*print_endline ("lbls="  ^ String.concat ~sep:", " (List.map ~f:Lbl.to_string mformula.lbls));
              print_endline ("lbls'=" ^ String.concat ~sep:", " (List.map ~f:Lbl.to_string mf.lbls));*)
            let aggregate = Expl.aggregate op_fun s tp x y mformula.lbls mf.lbls in
            (*print_endline ("MAgg.aexpl=" ^ Expl.to_string aexpl);*)
            (*print_endline ("MAgg.mformula=" ^ MFormula.to_string mformula);*)
            let f_expls = List.map expls ~f:(TS.map aggregate) in
            let f_aexpl = aggregate aexpl in
            (*print_endline ("--MAgg.f_aexpl=" ^ Expl.to_string f_aexpl);*)
            memo, (f_expls, f_aexpl, MAgg (s, op, op_fun, x, y, mf'))
         | MTop (s, op, op_fun, x, y, mf) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db fobligs ~pol memo mf in
            (*print_endline ("--MAgg.aexpl=" ^ Expl.to_string aexpl);
              print_endline ("mf=" ^ MFormula.to_string mformula);
              print_endline ("aexpl=" ^ Expl.to_string aexpl);*)
            (*print_endline ("lbls="  ^ String.concat ~sep:", " (List.map ~f:Lbl.to_string mformula.lbls));
              print_endline ("lbls'=" ^ String.concat ~sep:", " (List.map ~f:Lbl.to_string mf.lbls));*)
            let aggregate = Expl.table_operator op_fun s tp x y mformula.lbls mf.lbls in
            (*print_endline ("MAgg.aexpl=" ^ Expl.to_string aexpl);*)
            (*print_endline ("MAgg.mformula=" ^ MFormula.to_string mformula);*)
            let f_expls = List.map expls ~f:(TS.map aggregate) in
            let f_aexpl = aggregate aexpl in
            (*print_endline ("--MTop.f_aexpl=" ^ Expl.to_string f_aexpl);*)
            memo, (f_expls, f_aexpl, MTop (s, op, op_fun, x, y, mf'))
         | MNeg (mf) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db fobligs ~pol:(pol >>| FObligation.neg) memo mf in
            let f_neg pdt = Pdt.apply1_reduce Bool.equal mformula.lbls (fun b -> not b) (Pdt.exquant pdt) in
            let f_expls = List.map expls ~f:(TS.map f_neg) in
            let f_aexpl = f_neg aexpl in
            memo, (f_expls, f_aexpl, MNeg mf')
         | MAnd (s, mfs, bufn) ->
            let memo, data = List.fold_map ~init:memo ~f:(meval_rec ts tp db ~pol fobligs) mfs in
            let expls_list, aexpl_list, mfs' = List.unzip3 data in
            let apply_ands = Pdt.applyN_reduce Bool.equal mformula.lbls (List.fold_left ~init:true ~f:(&&)) in            
            let (f_expls, bufn) = Bufn.take (TS.map_list apply_ands) (Bufn.add expls_list bufn) in
            let aexpl = apply_ands aexpl_list in
            memo, (f_expls, aexpl, MAnd (s, mfs', bufn))
         | MOr (s, mfs, bufn) ->
            let memo, data = List.fold_map ~init:memo ~f:(meval_rec ts tp db ~pol fobligs) mfs in
            let expls_list, aexpl_list, mfs' = List.unzip3 data in
            let apply_ors = Pdt.applyN_reduce Bool.equal mformula.lbls (List.fold_left ~init:false ~f:(||)) in
            let (f_expls, bufn) = Bufn.take (TS.map_list apply_ors) (Bufn.add expls_list bufn) in
            let aexpl = apply_ors aexpl_list in
            memo, (f_expls, aexpl, MOr (s, mfs', bufn))
         | MImp (s, mf1, mf2, buf2) ->
            let memo, (expls1, aexpl1, mf1') = meval_rec ts tp db ~pol:(pol >>| FObligation.neg) fobligs memo mf1 in
            let memo, (expls2, aexpl2, mf2') = meval_rec ts tp db ~pol fobligs memo mf2 in
            let f_imp pdt1 pdt2 =
              Pdt.apply2_reduce Bool.equal mformula.lbls (fun p1 p2 -> (not p1) || p2) (Pdt.exquant pdt1) pdt2 in
            (*print_endline "--MImp";
            print_endline ("aexpl1=" ^ Expl.to_string aexpl1);
            print_endline ("aexpl2=" ^ Expl.to_string aexpl2);
            print_endline ("lbls=" ^ Lbl.to_string_list mformula.lbls);*)
            let (f_expls, buf2) = Buf2.take (TS.map2 f_imp) (Buf2.add expls1 expls2 buf2) in
            let aexpl = f_imp aexpl1 aexpl2 in
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
            let aexpl = els pol (Prev.approximate tp f_expls) in
            memo, (f_expls, aexpl, MPrev (i, mf', aux))
         | MNext (i, mf, aux) ->
            let memo, (expls, _, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = { aux with
                        tstps = aux.tstps @ (List.map expls ~f:(fun te -> (te.ts, te.tp)));
                        tstps_todo = aux.tstps_todo @ (List.map expls ~f:(fun te -> (te.ts, te.tp)));
                        buf = aux.buf @ (List.map expls ~f:TS.data) } in
            let aux, f_expls = Next.update mformula.lbls aux in
            let aexpl = approximate_false_opt pol in
            memo, (f_expls, approximate_false_opt pol, MNext (i, mf', aux))
         | MENext (i, f_ts, mf, v) ->
            let memo, (_, _, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aexpl = approximate_enext mformula.lbls fobligs (mformula.hash, v) tp pol in
            memo, ([TS.make tp ts aexpl], aexpl, MENext (i, f_ts, mf', v))
         | MOnce (i, mf, aux) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = { aux with buf = Buft.add aux.buf expls } in
            let aux, f_expls = Once.update mformula.lbls aux in
            (*print_endline ("--MOnce");
            print_endline ("aux=" ^ Once.to_string aux);*)
            let aexpl = approximate_once mformula.lbls f_expls aexpl i tp (pol_value pol) in
                (*print_endline ("aexpl=" ^ Expl.to_string aexpl);*)
            memo, (f_expls, aexpl, MOnce (i, mf', aux))
         | MEventually (i, mf, aux) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = { aux with
                        tstps_todo = aux.tstps_todo @ (List.map expls ~f:(fun te -> (te.ts, te.tp)));
                        buf = Buft.add aux.buf expls } in
            let aux, f_expls = Eventually.update mformula.lbls aux in
            let aexpl = approximate_eventually mformula.lbls aexpl fobligs i None tp (pol_value pol) in
            memo, (f_expls, aexpl, MEventually (i, mf', aux))
         | MEEventually (i, f_ts, mf, v) ->
            let memo, (_, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aexpl = approximate_eventually mformula.lbls aexpl fobligs i (Some (mformula.hash, v)) tp (pol_value pol) in
            memo, ([TS.make tp ts aexpl], aexpl, MEEventually (i, f_ts, mf', v))
         | MHistorically (i, mf, aux) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = { aux with buf = Buft.add aux.buf expls } in
            let aux, f_expls = Once.update mformula.lbls aux in
            let aexpl = approximate_historically mformula.lbls f_expls aexpl i tp (pol_value pol) in
            memo, (f_expls, aexpl, MHistorically (i, mf', aux))
         | MAlways (i, mf, aux) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = { aux with
                        tstps_todo = aux.tstps_todo @ (List.map expls ~f:(fun te -> (te.ts, te.tp)));
                        buf = Buft.add aux.buf expls } in
            let aux, f_expls = Eventually.update mformula.lbls aux in
            let aexpl = approximate_always mformula.lbls aexpl fobligs i None tp (pol_value pol) in
            memo, (f_expls, aexpl, MAlways (i, mf', aux))
         | MEAlways (i, f_ts, mf, v) ->
            let memo, (_, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            (*print_endline "--MEAlways";
              print_endline ("lbls = " ^ (Lbl.to_string_list mformula.lbls));
              print_endline ("aexpl = " ^ Expl.to_string aexpl);*)
            let aexpl = approximate_always mformula.lbls aexpl fobligs i (Some (mformula.hash, v)) tp (pol_value pol) in
            memo, ([TS.make tp ts aexpl], aexpl, MEAlways (i, f_ts, mf', v))
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
            let aexpl = approximate_since mformula.lbls f_expls aexpl1 aexpl2 i tp (pol_value pol) in
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
            let aexpl = approximate_until mformula.lbls aexpl1 aexpl2 fobligs i None tp (pol_value pol) in
            memo, (f_expls, aexpl, MUntil (i, mf1', mf2', aux))
         | MEUntil (s, i, f_ts, mf1, mf2, v) ->
            let memo, (_, aexpl1, mf1') = meval_rec ts tp db ~pol fobligs memo mf1 in
            let memo, (_, aexpl2, mf2') = meval_rec ts tp db ~pol fobligs memo mf2 in
            let aexpl = approximate_until mformula.lbls aexpl1 aexpl2 fobligs i (Some (mformula.hash, v)) tp (pol_value pol) in
            memo, ([TS.make tp ts aexpl], aexpl, MEUntil (s, i, f_ts, mf1', mf2', v))
       in let mf = { mformula with mf } in
          (*print_endline ("add memo: " ^ " (" ^ MFormula.to_string mf ^ ", " ^ Int.to_string tp ^ ", " ^ Int.to_string mformula.hash ^ ") -> " ^ Expl.to_string aexpl);*)
          let memo = if tp = outer_tp then Memo.memoize memo mformula (expls, aexpl, mf) else memo in
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

type res = Expl.t TS.t list * Expl.t * MFormula.t

let mstep _ ts db approx (ms: MState.t) (fobligs: FObligations.t) (memo : res Memo.t) =
  let pol_opt = if approx then Some FObligation.POS else None in
  let memo, (_, aexpl, mf') = meval ts ms.tp_cur db ~pol:pol_opt fobligs ms.mf memo in
  let expls, tstps = [aexpl], [(ms.tp_cur, ts)] in
  let tsdbs = ms.tsdbs in
  let ts_waiting = ms.ts_waiting in
  memo, (List.zip_exn tstps expls,
         aexpl,
         { ms with
           mf = mf'
         ; tp_cur = ms.tp_cur + 1
         ; ts_waiting
         ; tsdbs = tsdbs })

