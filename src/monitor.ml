open Base
open Expl
open Option

module Dom = MFOTL_lib.Dom
module Aggregation = MFOTL_lib.Aggregation
module Side = MFOTL_lib.Side
module Interval = MFOTL_lib.Interval
module Time = MFOTL_lib.Time
module MFOTL = MFOTL_lib.MFOTL
module Enftype = MFOTL_lib.Enftype
module Etc = MFOTL_lib.Etc
module Filter = MFOTL_lib.Filter

open Etc

module type MonitorT = sig

  module E : Expl.ExplT

  module MFormula : sig

    type binop_info
    type nop_info
    type prev_info
    type tp_info
    type buft_info
    type once_info
    type next_info
    type eventually_info
    type historically_info
    type always_info
    type buf2t_info
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
      | MIff          of Side.t * Side.t * t * t * binop_info
      | MExists       of string * Dom.tt * bool * t
      | MForall       of string * Dom.tt * bool *  t
      | MPrev         of Interval.t * t * bool * prev_info
      | MNext         of Interval.t * t * bool * next_info
      | MENext        of Interval.t * Time.t option * t * Etc.valuation
      | MOnce         of Interval.t * t * tp_info * once_info
      | MEventually   of Interval.t * t * buft_info * eventually_info
      | MEEventually  of Interval.t * Time.t option * t * Etc.valuation
      | MHistorically of Interval.t * t * tp_info * historically_info
      | MAlways       of Interval.t * t * buft_info * always_info
      | MEAlways      of Interval.t * Time.t option * t * Etc.valuation
      | MSince        of Side.t * Interval.t * t * t * buf2t_info * since_info
      | MUntil        of Interval.t * t * t * buf2t_info * until_info
      | MEUntil       of Side.t * Interval.t * Time.t option * t * t * Etc.valuation

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
      | FInterval of Time.t * Interval.t * MFormula.t * int * Etc.valuation  (* fun t -> if mem t i then f else Formula.TT *)
      | FUntil of Time.t * Side.t * Interval.t * MFormula.t * MFormula.t * int * Etc.valuation (* fun t -> Until (s, sub2 i (t-t0), f1, f2) *)
      | FAlways of Time.t * Interval.t * MFormula.t * int * Etc.valuation     (* fun t -> Always (sub2 i (t-t0), f1) *)
      | FEventually of Time.t * Interval.t * MFormula.t * int * Etc.valuation (* fun t -> Eventually (sub2 i (t-t0), f1) *)

    type t = kind * Etc.valuation * polarity

    (*val equal: t -> t -> bool*)
    val eval: Time.t -> int -> t -> MFormula.t
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

  type res = E.t list * E.t * MFormula.t

  val mstep: timepoint -> timestamp -> Db.t -> bool -> MState.t -> FObligations.t ->
             res Memo.t -> res Memo.t * (((timepoint * timestamp) * E.t) list * E.t * MState.t)

  val meval_c: int ref

end

module Make (E: Expl.ExplT) = struct

  module E = E

  open E

  (* let minp_list = Proof.Size.minp_list *)
  (* let minp_bool = Proof.Size.minp_bool *)
  (* let minp = Proof.Size.minp *)
  let minp_list = List.hd_exn
  let minp_bool = fun _ _ -> true
  (*let minp = fun p1 _ -> p1*)

  let s_append_deque sp1 d =
    Fdeque.map d ~f:(fun (ts, ssp) ->
        match ssp with
        | Proof.S sp -> (ts, Proof.S (Proof.s_append sp sp1))
        | V _ -> raise (Invalid_argument "found V proof in S deque"))

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

  (* split_in_out considers a closed interval [l, r] *)
  let split_in_out get_ts (l, r) deque =
    let new_in = Fdeque.empty in
    let rec split_in_out_rec d nd =
      match Fdeque.dequeue_front d with
      | None -> (d, nd)
      | Some(el', d') -> let ts = get_ts el' in
                         if Time.(ts <= r) then
                           (if Time.(l <= ts) then
                              split_in_out_rec d' (Fdeque.enqueue_back nd el')
                            else split_in_out_rec d' nd)
                         else (d, nd) in
    split_in_out_rec deque new_in

  (* split_out_in considers an interval of the form [z, l) *)
  let split_out_in get_ts (z, l) deque =
    let new_out = Fdeque.empty in
    let rec split_out_in_rec d nd =
      match Fdeque.dequeue_front d with
      | None -> (nd, d)
      | Some(el', d') -> let ts = get_ts el' in
                         if Time.(ts < l) then
                           (if Time.(z <= ts) then
                              split_out_in_rec d' (Fdeque.enqueue_back nd el')
                            else split_out_in_rec d' nd)
                         else (nd, d) in
    split_out_in_rec deque new_out

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
        | None -> raise (Failure "tstps deques are empty")
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

  (*let tstps_to_string (ts_zero: Time.t option) tstps_in tstps_out =
    (match ts_zero with
     | None -> ""
     | Some(ts) -> Printf.sprintf "\n\tts_zero = (%s)\n" (Time.to_string ts)) ^
      Fdeque.fold tstps_in ~init:"\n\ttstps_in = ["
        ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%s, %d);" (Time.to_string ts) tp)) ^
        (Printf.sprintf "]\n") ^
          Fdeque.fold tstps_out ~init:"\n\ttstps_out = ["
            ~f:(fun acc (ts, tp) -> acc ^ (Printf.sprintf "(%s, %d);" (Time.to_string ts) tp)) ^
            (Printf.sprintf "]\n")*)

  module Buf2 = struct

    type ('a, 'b) t = 'a list * 'b list

    let add xs ys (l1, l2) = (l1 @ xs, l2 @ ys)

    let rec take f = function
      | [], ys -> ([], ([], ys))
      | xs, [] -> ([], (xs, []))
      | x::xs, y::ys -> let (zs, buf2') = take f (xs, ys) in
                        ((f x y)::zs, buf2')

    (*let rec pdt_equal b1 b2 = match b1, b2 with
      | ([], []), ([], []) -> true
      | (x1::x1s, y1::y1s), (x2::x2s, y2::y2s) ->
         Int.equal (List.length x1s) (List.length x2s) && Int.equal (List.length y1s) (List.length y2s) &&
           Pdt.eq Proof.equal x1 x2 && Pdt.eq Proof.equal y1 y2 &&
             pdt_equal (x1s, y1s) (x2s, y2s)
      | _, _ -> false*)

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

    (*let rec pdt_equal b1 b2 = match b1, b2 with
      | ([], []), ([], []) -> true
      | (x1::x1s, (y11, y12)::y1s), (x2::x2s, (y21, y22)::y2s) ->
         Int.equal (List.length x1s) (List.length x2s) && Int.equal (List.length y1s) (List.length y2s) &&
           Pdt.eq Proof.equal x1 x2 && Int.equal y11 y21 && Int.equal y12 y22 &&
             pdt_equal (x1s, y1s) (x2s, y2s)
      | _, _ -> false*)

    let map f1 f2 (l1, l2) = (List.map ~f:f1 l1, List.map ~f:f2 l2)

  end

  module Buf2t = struct

    type ('a, 'b, 'c) t = ('a list * 'b list) * 'c list

    (*let add xs ys (l1, l2) = (l1 @ xs, l2 @ ys)*)

    let rec take f w (xs, ys) zs = match (xs, ys), zs with
      | ([], ys), zs -> (w, (([], ys), zs))
      | (xs, []), zs -> (w, ((xs, []), zs))
      | (xs, ys), [] -> (w, ((xs, ys), []))
      | (x::xs, y::ys), (a,b)::zs -> take f (f x y a b w) (xs, ys) zs

    (*let rec pdt_equal b1 b2 = match b1, b2 with
      | (([], []), []), (([], []), []) -> true
      | ((x1::x1s, y1::y1s), (z11, z12)::z1s), ((x2::x2s, y2::y2s), (z21, z22)::z2s) ->
         Int.equal (List.length x1s) (List.length x2s) && Int.equal (List.length y1s) (List.length y2s) &&
           Int.equal (List.length z1s) (List.length z2s) && Pdt.eq Proof.equal x1 x2 &&
             Pdt.eq Proof.equal y1 y2 && Int.equal z11 z21 && Int.equal z12 z22 &&
               pdt_equal ((x1s, y1s), z1s) ((x2s, y2s), z2s)
      | _, _ -> false*)

    let map f1 f2 f3 ((l1, l2), l3) = ((List.map ~f:f1 l1, List.map ~f:f2 l2), List.map ~f:f3 l3)

  end

  module Once = struct

    type t = { ts_zero: Time.t option
             ; tstps_out: (Time.t * timepoint) Fdeque.t
             ; s_alphas_in: (Time.t * Proof.t) Fdeque.t
             ; s_alphas_out: (Time.t * Proof.t) Fdeque.t
             ; v_alphas_in: (Time.t * Proof.vp) Fdeque.t
             ; v_alphas_out: (Time.t * Proof.vp) Fdeque.t }

    let init () = { ts_zero = None
                  ; tstps_out = Fdeque.empty
                  ; s_alphas_in = Fdeque.empty
                  ; s_alphas_out = Fdeque.empty
                  ; v_alphas_in = Fdeque.empty
                  ; v_alphas_out = Fdeque.empty }

    (*let to_string { ts_zero
                  ; tstps_in
                  ; tstps_out
                  ; s_alphas_in
                  ; s_alphas_out
                  ; v_alphas_in
                  ; v_alphas_out } =
      ("\n\nOnce state: " ^ (tstps_to_string ts_zero tstps_in tstps_out) ^
         Fdeque.fold s_alphas_in ~init:"\ns_alphas_in = "
           ~f:(fun acc (ts, p) ->
             acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.to_string "" p) ^
           Fdeque.fold s_alphas_out ~init:"\ns_alphas_out = "
             ~f:(fun acc (ts, p) ->
               acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.to_string "" p) ^
             Fdeque.fold v_alphas_in ~init:"\nv_alphas_in = "
               ~f:(fun acc (ts, p) ->
                 acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.v_to_string "" p) ^
               Fdeque.fold v_alphas_out ~init:"\nv_alphas_out = "
                 ~f:(fun acc (ts, p) ->
                   acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.v_to_string "" p))
     *)
    
    let update_s_alphas_in new_in_sat s_alphas_in =
      if not (Fdeque.is_empty new_in_sat) then
        sorted_append new_in_sat s_alphas_in
      else s_alphas_in

    (*let update_v_alphas_in new_in_vio v_alphas_in =
      Fdeque.fold new_in_vio ~init:v_alphas_in ~f:(fun v_alphas_in' (ts, vp) ->
          Fdeque.enqueue_back v_alphas_in' (ts, vp))*)

    (*let add_subps ts p1 moaux = match p1 with
      | Proof.S sp1 -> { moaux with s_alphas_out = Fdeque.enqueue_back moaux.s_alphas_out (ts, (Proof.S sp1)) }
      | V vp1 -> { moaux with v_alphas_out = Fdeque.enqueue_back moaux.v_alphas_out (ts, vp1) }*)

    let clean (l, r) moaux =
      { moaux with s_alphas_in = remove_cond_front (fun (ts, _) -> Time.(ts < l)) moaux.s_alphas_in
                 ; s_alphas_out = remove_cond_front (fun (ts, _) -> Time.(ts <= r)) moaux.s_alphas_out
                 ; v_alphas_in = remove_cond_front (fun (ts, _) -> Time.(ts < l)) moaux.v_alphas_in
                 ; v_alphas_out = remove_cond_front (fun (ts, _) -> Time.(ts <= r)) moaux.v_alphas_out }

    let shift_sat (l, r) s_alphas_out s_alphas_in =
      let (s_alphas_out', new_in_sat) = split_in_out (fun (ts, _) -> ts) (l, r) s_alphas_out in
      (s_alphas_out', update_s_alphas_in new_in_sat s_alphas_in)

    (*let shift_vio (l, r) v_alphas_out v_alphas_in =
      let (v_alphas_out', new_in_vio) = split_in_out (fun (ts, _) -> ts) (l, r) v_alphas_out in
      (v_alphas_out', update_v_alphas_in new_in_vio v_alphas_in)*)

    (*let shift (l, r) a ts tp moaux =
      let (tstps_in, tstps_out) = shift_tstps_past (l, r) a ts tp moaux.tstps_in moaux.tstps_out in
      let (s_alphas_out, s_alphas_in) = shift_sat (l,r) moaux.s_alphas_out moaux.s_alphas_in in
      let (v_alphas_out, v_alphas_in) = shift_vio (l,r) moaux.v_alphas_out moaux.v_alphas_in in
      clean (l, r) { moaux with tstps_in
                              ; tstps_out
                              ; s_alphas_out
                              ; s_alphas_in
                              ; v_alphas_out
                              ; v_alphas_in }*)

    (*let eval tp moaux =
      if not (Fdeque.is_empty moaux.s_alphas_in) then
        [Proof.S (Proof.make_sonce tp (Proof.unS (snd (Fdeque.peek_front_exn moaux.s_alphas_in))))]
      else
        let etp = match Fdeque.is_empty moaux.v_alphas_in with
          | true -> etp moaux.tstps_in moaux.tstps_out tp
          | false -> Proof.v_at (snd(Fdeque.peek_front_exn moaux.v_alphas_in)) in
        [Proof.V (Proof.make_vonce tp etp (Fdeque.map moaux.v_alphas_in ~f:snd))]*)

    let add_subps_enforce ts p1 moaux = match p1 with
      | Proof.S sp1 -> { moaux with s_alphas_out = Fdeque.enqueue_back moaux.s_alphas_out (ts, (Proof.S sp1)) }
      | V _ -> moaux

    let shift_enforce (l, r) _ _ _ moaux =
      let (s_alphas_out, s_alphas_in) = shift_sat (l,r) moaux.s_alphas_out moaux.s_alphas_in in
      clean (l, r) { moaux with s_alphas_out
                              ; s_alphas_in }

    let eval_enforce tp moaux =
      if not (Fdeque.is_empty moaux.s_alphas_in) then
        [Proof.S (Proof.make_sonce tp (Proof.unS(snd(Fdeque.peek_front_exn moaux.s_alphas_in))))]
      else
        [Proof.V (Proof.make_vff tp)]

    let update i ts tp p1 moaux =
      let a = Interval.left i in
      let moaux_z = if Option.is_none moaux.ts_zero then
                      { moaux with ts_zero = Some ts }
                    else
                      moaux in
      let moaux_subps = add_subps_enforce ts p1 moaux_z in
      if Time.(ts < Option.value_exn moaux_subps.ts_zero + a) then
        ({ moaux_subps with tstps_out = Fdeque.enqueue_back moaux_subps.tstps_out (ts, tp) },
         [Proof.V (Proof.make_vonceout tp)])
      else
        let b = Interval.right i in
        let l =
          if Option.is_some b then
            Time.max Time.zero Time.(ts - Option.value_exn b)
          else
            Option.value_exn moaux_subps.ts_zero in
        let r = Time.(ts - a) in
        let moaux_shifted = shift_enforce (l, r) a ts tp moaux_subps in
        let ps = eval_enforce tp moaux_shifted in
        (moaux_shifted, ps)

    (* Only used for approximation (enforcement related) *)
    let do_once_base tp a (p: Proof.t) =
      match p, Time.Span.is_zero a with
      | S sp, true -> Proof.S (Proof.make_sonce tp sp)
      | _ -> Proof.V (Proof.make_vff tp)

  end


  module Eventually = struct

    type t = { tstps_out: (Time.t * timepoint) Fdeque.t
             ; tstps_in: (Time.t * timepoint) Fdeque.t
             ; s_alphas_in: (Time.t * Proof.t) Fdeque.t
             ; v_alphas_in: (Time.t * Proof.vp) Fdeque.t
             ; optimal_proofs: (Time.t * Proof.t) Fdeque.t }

    let init () = { tstps_out = Fdeque.empty
                  ; tstps_in = Fdeque.empty
                  ; s_alphas_in = Fdeque.empty
                  ; v_alphas_in = Fdeque.empty
                  ; optimal_proofs = Fdeque.empty }

    (*let to_string { tstps_out
                  ; tstps_in
                  ; s_alphas_in
                  ; v_alphas_in
                  ; optimal_proofs } =
      ("\n\nEventually state: " ^ (tstps_to_string None tstps_in tstps_out) ^
         Fdeque.fold s_alphas_in ~init:"\ns_alphas_in = "
           ~f:(fun acc (ts, p) ->
             acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.to_string "" p) ^
           Fdeque.fold v_alphas_in ~init:"\nv_alphas_in = "
             ~f:(fun acc (ts, p) ->
               acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.v_to_string "" p) ^
             Fdeque.fold optimal_proofs ~init:"\noptimal_proofs = "
               ~f:(fun acc (ts, p) ->
                 acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.to_string "" p))*)

    let adjust a (nts, ntp) meaux =
      let (tstps_out, tstps_in) = drop_first_ts_tp meaux.tstps_out meaux.tstps_in in
      let (first_ts, first_tp) = match first_ts_tp tstps_out tstps_in with
        | None -> (nts, ntp)
        | Some(ts', tp') -> (ts', tp') in
      let (tstps_out', tstps_in') = shift_tstps_future a first_ts ntp tstps_out tstps_in in
      let s_alphas_in' = remove_cond_front (fun (ts', p) ->
                             Time.(ts' < first_ts + a) || (Proof.p_at p < first_tp)) meaux.s_alphas_in in
      let v_alphas_in' = remove_cond_front (fun (ts', vp) ->
                             Time.(ts' < first_ts + a) || (Proof.v_at vp < first_tp)) meaux.v_alphas_in in
      { meaux with tstps_out = tstps_out'
                 ; tstps_in = tstps_in'
                 ; s_alphas_in = s_alphas_in'
                 ; v_alphas_in = v_alphas_in' }

    let eval_step a (nts, ntp) ts tp meaux =
      let optimal_proofs =
        (if not (Fdeque.is_empty meaux.s_alphas_in) then
           (match Fdeque.peek_front_exn meaux.s_alphas_in with
            | (_, S _) -> Fdeque.enqueue_back meaux.optimal_proofs
                             (ts, S (Proof.make_seventually tp (Proof.unS(snd(Fdeque.peek_front_exn meaux.s_alphas_in)))))
            | _ -> raise (Invalid_argument "found V proof in S deque"))
         else
           (let ltp = match Fdeque.peek_back meaux.v_alphas_in with
              | None -> snd(Fdeque.peek_back_exn meaux.tstps_out)
              | Some (_, vp2) -> Proof.v_at vp2 in
            Fdeque.enqueue_back meaux.optimal_proofs
              (ts, V (Proof.make_veventually tp ltp (Fdeque.map meaux.v_alphas_in ~f:snd))))) in
      { (adjust a (nts, ntp) meaux) with optimal_proofs }

    let shift (a, b) (nts, ntp) meaux =
      let tstps = ready_tstps b nts meaux.tstps_out meaux.tstps_in in
      Fdeque.fold tstps ~init:meaux ~f:(fun meaux' (ts, tp) ->
          eval_step a (nts, ntp) ts tp meaux')

    let add_subp a (ts, _) (p1: Proof.t) meaux =
      let first_ts = match first_ts_tp meaux.tstps_out meaux.tstps_in with
        | None -> Time.zero
        | Some(ts', _) -> ts' in
      match p1 with
      | S sp1 -> if Time.(first_ts + a <= ts) then
                   { meaux with s_alphas_in = sorted_enqueue (ts, (Proof.S sp1)) meaux.s_alphas_in }
                 else meaux
      | V vp1 -> if Time.(first_ts + a <= ts) then
                   { meaux with v_alphas_in = Fdeque.enqueue_back meaux.v_alphas_in (ts, vp1) }
                 else meaux

    let update i (nts: Time.t) ntp p meaux =
      let a = Interval.left i in
      let b = match Interval.right i with
        | None -> Time.Span.infty
        | Some(b') -> b' in
      let meaux_shifted = shift (a, b) (nts, ntp) meaux in
      let (tstps_out, tstps_in) = add_tstp_future a b nts
                                    ntp meaux_shifted.tstps_out meaux_shifted.tstps_in in
      add_subp a (nts, ntp) p { meaux_shifted with tstps_out; tstps_in }

    let rec eval i nts ntp (meaux, ops) =
      let a = Interval.left i in
      match Interval.right i with
      | None -> (meaux, ops)
      | Some(b) ->
         let meaux_shifted = shift (a, b) (nts, ntp) meaux in
         match Fdeque.peek_back meaux_shifted.optimal_proofs with
         | None -> (meaux, ops)
         | Some(ts, _) -> if Time.(ts + b < nts) then
                            let ((_, op), optimal_proofs) = Fdeque.dequeue_back_exn meaux_shifted.optimal_proofs in
                            let (meaux', ops') = eval i nts ntp ({ meaux_shifted with optimal_proofs }, ops) in
                            (meaux', ops' @ [op])
                          else (meaux, ops)

    let do_eventually_base tp i is_pos (p_next: Proof.t) (p_now: Proof.t) =
      (*print_endline (Proof.to_string "pnext=" p_next);
      print_endline (Proof.to_string "pnow=" p_now);
      print_endline (Interval.to_string i);
      print_endline (Bool.to_string is_pos);*)
      match p_next, p_now, Interval.left i, is_pos with
      | _  , S sp_now, a, true when Time.Span.is_zero a -> Proof.S (Proof.make_seventuallynow sp_now i)
      | S _, _       , a, true when not (Time.Span.is_zero a) -> Proof.S (Proof.make_seventuallyassm tp i)
      | _  , _       , _, true  -> Proof.V (Proof.make_vff tp)
      | V _, V vp_now, a, false when Time.Span.is_zero a -> Proof.V (Proof.make_veventuallyassm tp (Some vp_now) i)
      | V _, _       , a, false when not (Time.Span.is_zero a) -> Proof.V (Proof.make_veventuallyassm tp None i)
      | _  , _       , _, false -> Proof.S (Proof.make_stt tp)

  end


  module Historically = struct

    type t = { ts_zero: Time.t option
             ; tstps_in: (Time.t * timepoint) Fdeque.t
             ; tstps_out: (Time.t * timepoint) Fdeque.t
             ; s_alphas_in: (Time.t * Proof.sp) Fdeque.t
             ; s_alphas_out: (Time.t * Proof.sp) Fdeque.t
             ; v_alphas_in: (Time.t * Proof.t) Fdeque.t
             ; v_alphas_out: (Time.t * Proof.t) Fdeque.t }

    let init () = { ts_zero = None
                  ; tstps_in = Fdeque.empty
                  ; tstps_out = Fdeque.empty
                  ; s_alphas_in = Fdeque.empty
                  ; s_alphas_out = Fdeque.empty
                  ; v_alphas_in = Fdeque.empty
                  ; v_alphas_out = Fdeque.empty }

    (*let to_string { ts_zero
                  ; tstps_in
                  ; tstps_out
                  ; s_alphas_in
                  ; s_alphas_out
                  ; v_alphas_in
                  ; v_alphas_out } =
      ("\n\nHistorically state: " ^ (tstps_to_string ts_zero tstps_in tstps_out) ^
         Fdeque.fold s_alphas_in ~init:"\ns_alphas_in = "
           ~f:(fun acc (ts, sp) ->
             acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.s_to_string "" sp) ^
           Fdeque.fold s_alphas_out ~init:"\ns_alphas_out = "
             ~f:(fun acc (ts, sp) ->
               acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.s_to_string "" sp) ^
             Fdeque.fold v_alphas_in ~init:"\nv_alphas_in = "
               ~f:(fun acc (ts, p) ->
                 acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.to_string "" p) ^
               Fdeque.fold v_alphas_in ~init:"\nv_alphas_out = "
                 ~f:(fun acc (ts, p) ->
                   acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.to_string "" p))*)

    let update_s_alphas_in new_in_sat s_alphas_in =
      Fdeque.fold new_in_sat ~init:s_alphas_in ~f:(fun s_alphas_in' (ts, sp) ->
          Fdeque.enqueue_back s_alphas_in' (ts, sp)) 

    let update_v_alphas_in new_in_vio v_alphas_in =
      if not (Fdeque.is_empty new_in_vio) then
        sorted_append new_in_vio v_alphas_in
      else v_alphas_in

    let add_subps ts (p1: Proof.t) mhaux = match p1 with
      | S sp1 -> { mhaux with s_alphas_out = Fdeque.enqueue_back mhaux.s_alphas_out (ts, sp1) }
      | V vp1 -> { mhaux with v_alphas_out = Fdeque.enqueue_back mhaux.v_alphas_out (ts, (V vp1)) }

    let shift_sat (l, r) s_alphas_out s_alphas_in =
      let (s_alphas_out', new_in_sat) = split_in_out (fun (ts, _) -> ts) (l, r) s_alphas_out in
      (s_alphas_out', update_s_alphas_in new_in_sat s_alphas_in)

    let shift_vio (l, r) v_alphas_out v_alphas_in =
      let (v_alphas_out', new_in_viol) = split_in_out (fun (ts, _) -> ts) (l, r) v_alphas_out in
      (v_alphas_out', update_v_alphas_in new_in_viol v_alphas_in)

    let clean (l, r) mhaux =
      { mhaux with s_alphas_in = remove_cond_front (fun (ts, _) -> Time.(ts < l)) mhaux.s_alphas_in
                 ; s_alphas_out = remove_cond_front (fun (ts, _) -> Time.(ts <= r)) mhaux.s_alphas_out
                 ; v_alphas_in = remove_cond_front (fun (ts, _) -> Time.(ts < l)) mhaux.v_alphas_in
                 ; v_alphas_out = remove_cond_front (fun (ts, _) -> Time.(ts <= r)) mhaux.v_alphas_out }

    let shift (l, r) a ts tp mhaux =
      let (tstps_in, tstps_out) = shift_tstps_past (l, r) a ts tp mhaux.tstps_in mhaux.tstps_out in
      let (s_alphas_out, s_alphas_in) = shift_sat (l,r) mhaux.s_alphas_out mhaux.s_alphas_in in
      let (v_alphas_out, v_alphas_in) = shift_vio (l,r) mhaux.v_alphas_out mhaux.v_alphas_in in
      clean (l, r) { mhaux with tstps_in
                              ; tstps_out
                              ; s_alphas_out
                              ; s_alphas_in
                              ; v_alphas_out
                              ; v_alphas_in }

    let eval tp mhaux =
      if not (Fdeque.is_empty mhaux.v_alphas_in) then
        [Proof.V (Proof.make_vhistorically tp (Proof.unV(snd(Fdeque.peek_front_exn mhaux.v_alphas_in))))]
      else
        let etp = match Fdeque.is_empty mhaux.s_alphas_in with
          | true -> etp mhaux.tstps_in mhaux.tstps_out tp
          | false -> Proof.s_at (snd(Fdeque.peek_front_exn mhaux.s_alphas_in)) in
        [S (Proof.make_shistorically tp etp (Fdeque.map mhaux.s_alphas_in ~f:snd))]

    let update i ts tp p1 mhaux =
      let a = Interval.left i in
      let mhaux_z = if Option.is_none mhaux.ts_zero then
                      { mhaux with ts_zero = Some(ts) }
                    else mhaux in
      let mhaux_subps = add_subps ts p1 mhaux_z in
      if Time.(ts < (Option.value_exn mhaux_subps.ts_zero) + a) then
        ({ mhaux_subps with tstps_out = Fdeque.enqueue_back mhaux_subps.tstps_out (ts, tp) },
         [Proof.S (Proof.make_shistoricallyout tp)])
      else
        let b = Interval.right i in
        let l = if (Option.is_some b) then
                  Time.max Time.zero Time.(ts - (Option.value_exn b))
                else
                  (Option.value_exn mhaux_subps.ts_zero) in
        let r = Time.(ts - a) in
        let mhaux_shifted = shift (l, r) a ts tp mhaux_subps in
        (mhaux_shifted, eval tp mhaux_shifted)

    (* Only used for approximation (enforcement related) *)
    let do_historically_base tp a (p: Proof.t) =
      match p, Time.Span.is_zero a with
      | V vp, true -> Proof.V (Proof.make_vhistorically tp vp)
      | _ -> Proof.S (Proof.make_stt tp)

  end

  module Always = struct

    type t = { tstps_out: (Time.t * timepoint) Fdeque.t
             ; tstps_in: (Time.t * timepoint) Fdeque.t
             ; v_alphas_in: (Time.t * Proof.t) Fdeque.t
             ; s_alphas_in: (Time.t * Proof.sp) Fdeque.t
             ; optimal_proofs: (Time.t * Proof.t) Fdeque.t }

    let init () = { tstps_out = Fdeque.empty
                  ; tstps_in = Fdeque.empty
                  ; v_alphas_in = Fdeque.empty
                  ; s_alphas_in = Fdeque.empty
                  ; optimal_proofs = Fdeque.empty }

    (*let to_string { tstps_out
                  ; tstps_in
                  ; v_alphas_in
                  ; s_alphas_in
                  ; optimal_proofs } =
      ("\n\nAlways state: " ^ (tstps_to_string None tstps_in tstps_out) ^
         Fdeque.fold v_alphas_in ~init:"\nv_alphas_in = "
           ~f:(fun acc (ts, p) ->
             acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.to_string "" p) ^
           Fdeque.fold s_alphas_in ~init:"\ns_alphas_in = "
             ~f:(fun acc (ts, sp) ->
               acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.s_to_string "" sp) ^
             Fdeque.fold optimal_proofs ~init:"\noptimal_proofs = "
               ~f:(fun acc (ts, p) ->
                 acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.to_string "" p))*)

    let adjust a (nts, ntp) maaux =
      let (tstps_out, tstps_in) = drop_first_ts_tp maaux.tstps_out maaux.tstps_in in
      let (first_ts, first_tp) = match first_ts_tp tstps_out tstps_in with
        | None -> (nts, ntp)
        | Some(ts', tp') -> (ts', tp') in
      let (tstps_out', tstps_in') = shift_tstps_future a first_ts ntp tstps_out tstps_in in
      let s_alphas_in' = remove_cond_front (fun (ts', sp) ->
                             Time.(ts' < first_ts + a) || (Proof.s_at sp < first_tp)) maaux.s_alphas_in in
      let v_alphas_in' = remove_cond_front (fun (ts', p) ->
                             Time.(ts' < first_ts + a) || (Proof.p_at p < first_tp)) maaux.v_alphas_in in
      { maaux with tstps_out = tstps_out'
                 ; tstps_in = tstps_in'
                 ; v_alphas_in = v_alphas_in'
                 ; s_alphas_in = s_alphas_in' }

    let eval_step a (nts, ntp) ts tp maaux =
      let optimal_proofs =
        (if not (Fdeque.is_empty maaux.v_alphas_in) then
           (match Fdeque.peek_front_exn maaux.v_alphas_in with
            | (_, V _) -> Fdeque.enqueue_back maaux.optimal_proofs
                             (ts, V (Proof.make_valways tp (Proof.unV(snd(Fdeque.peek_front_exn maaux.v_alphas_in)))))
            | _ -> raise (Invalid_argument "found S proof in V deque"))
         else
           (let ltp = match Fdeque.peek_back maaux.s_alphas_in with
              | None -> snd(Fdeque.peek_back_exn maaux.tstps_out)
              | Some (_, sp) -> Proof.s_at sp in
            Fdeque.enqueue_back maaux.optimal_proofs (ts, S (Proof.make_salways tp ltp (Fdeque.map maaux.s_alphas_in ~f:snd))))) in
      { (adjust a (nts, ntp) maaux) with optimal_proofs }

    let shift (a, b) (nts, ntp) maaux =
      let tstps = ready_tstps b nts maaux.tstps_out maaux.tstps_in in
      Fdeque.fold tstps ~init:maaux ~f:(fun maaux' (ts, tp) ->
          eval_step a (nts, ntp) ts tp maaux')

    let add_subp a (ts, _) (p1: Proof.t) maaux =
      let first_ts = match first_ts_tp maaux.tstps_out maaux.tstps_in with
        | None -> Time.zero
        | Some(ts', _) -> ts' in
      match p1 with
      | V vp1 -> if Time.(first_ts + a <= ts) then
                   { maaux with v_alphas_in = sorted_enqueue (ts, (Proof.V vp1)) maaux.v_alphas_in }
                 else maaux
      | S sp1 -> if Time.(first_ts + a <= ts) then
                   { maaux with s_alphas_in = Fdeque.enqueue_back maaux.s_alphas_in (ts, sp1) }
                 else maaux

    let update i nts ntp p maaux =
      let a = Interval.left i in
      let b = match Interval.right i with
        | None -> Time.Span.infty
        | Some(b') -> b' in
      let maaux_shifted = shift (a, b) (nts, ntp) maaux in
      let (tstps_out, tstps_in) = add_tstp_future a b nts ntp maaux_shifted.tstps_out maaux_shifted.tstps_in in
      add_subp a (nts, ntp) p { maaux_shifted with tstps_out; tstps_in }

    let rec eval i nts ntp (maaux, ops) =
      let a = Interval.left i in
      match Interval.right i with
      | None -> (maaux, ops)
      | Some (b) ->
         let maaux_shifted = shift (a, b) (nts, ntp) maaux in
         match Fdeque.peek_back maaux_shifted.optimal_proofs with
         | None -> (maaux, ops)
         | Some(ts, _) -> if Time.(ts + b < nts) then
                            let ((_, op), optimal_proofs) = Fdeque.dequeue_back_exn maaux_shifted.optimal_proofs in
                            let (maaux', ops') = eval i nts ntp ({ maaux_shifted with optimal_proofs }, ops) in
                            (maaux', ops' @ [op])
                          else (maaux, ops)

    let do_always_base tp i is_pos (p_next: Proof.t) (p_now: Proof.t) =
      match p_next, p_now, Interval.left i, is_pos with
      | _  , V vp_now, a, false when Time.Span.is_zero a -> Proof.V (Proof.make_valwaysnow vp_now i)
      | V _, _       , a, false when not (Time.Span.is_zero a) -> Proof.V (Proof.make_valwaysassm tp i)
      | _  , _       , _, false -> Proof.S (Proof.make_stt tp)
      | S _, S sp_now, a, true when Time.Span.is_zero a  -> Proof.S (Proof.make_salwaysassm tp (Some sp_now) i)
      | S _, _       , a, true when not (Time.Span.is_zero a) -> Proof.S (Proof.make_salwaysassm tp None i)
      | _  , _       , _, true  -> Proof.V (Proof.make_vff tp)

  end

  module Since = struct

    type t = { ts_zero: Time.t option
             ; tstps_out: (Time.t * timepoint) Fdeque.t
             ; s_beta_alphas_in: (Time.t * Proof.t) Fdeque.t
             ; s_beta_alphas_out: (Time.t * Proof.t) Fdeque.t
             ; v_alpha_betas_in: (Time.t * Proof.t) Fdeque.t
             ; v_alphas_out: (Time.t * Proof.t) Fdeque.t
             ; v_betas_in: (Time.t * Proof.vp) Fdeque.t }

    let init () = { ts_zero = None
                  ; tstps_out = Fdeque.empty
                  ; s_beta_alphas_in = Fdeque.empty
                  ; s_beta_alphas_out = Fdeque.empty
                  ; v_alpha_betas_in = Fdeque.empty
                  ; v_alphas_out = Fdeque.empty
                  ; v_betas_in = Fdeque.empty }

    (*let to_string { ts_zero
                  ; tstps_in
                  ; tstps_out
                  ; s_beta_alphas_in
                  ; s_beta_alphas_out
                  ; v_alpha_betas_in
                  ; v_alphas_out
                  ; v_betas_in
                  ; v_alphas_betas_out } =
      ("\n\nSince state: " ^ (tstps_to_string ts_zero tstps_in tstps_out) ^
         Fdeque.fold s_beta_alphas_in ~init:"\ns_beta_alphas_in = "
           ~f:(fun acc (ts, p) ->
             acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.to_string "" p) ^
           Fdeque.fold s_beta_alphas_out ~init:"\ns_beta_alphas_out = "
             ~f:(fun acc (ts, p) ->
               acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.to_string "" p) ^
             Fdeque.fold v_alpha_betas_in ~init:"\nv_alpha_betas_in = "
               ~f:(fun acc (ts, p) ->
                 acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.to_string "" p) ^
               Fdeque.fold v_alphas_out ~init:"\nv_alphas_out = "
                 ~f:(fun acc (ts, p) ->
                   acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.to_string "" p) ^
                 Fdeque.fold v_betas_in ~init:"\nv_betas_in = "
                   ~f:(fun acc (ts, p) ->
                     acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.v_to_string "" p) ^
                   Fdeque.fold v_alphas_betas_out ~init:"\nv_alphas_betas_out = "
                     ~f:(fun acc (ts, p1_opt, p2_opt) ->
                       match p1_opt, p2_opt with
                       | None, None -> acc
                       | Some(p1), None -> acc ^ (Printf.sprintf "\n(%s)\nalpha = " (Time.to_string ts)) ^ Proof.v_to_string "" p1
                       | None, Some(p2) -> acc ^ (Printf.sprintf "\n(%s)\nbeta = " (Time.to_string ts)) ^ Proof.v_to_string "" p2
                       | Some(p1), Some(p2) -> acc ^ (Printf.sprintf "\n(%s)\nalpha = " (Time.to_string ts)) ^ Proof.v_to_string "" p1 ^
                                                 (Printf.sprintf "\n(%s)\nbeta = " (Time.to_string ts)) ^ Proof.v_to_string "" p2))*)

    let update_s_beta_alphas_in new_in s_beta_alphas_in =
      if not (Fdeque.is_empty new_in) then
        sorted_append new_in s_beta_alphas_in
      else s_beta_alphas_in

    (*let update_v_betas_in new_in v_betas_in =
      Fdeque.fold new_in ~init:v_betas_in ~f:(fun v_betas_in' (ts, _, vp2_opt) ->
          match vp2_opt with
          | None -> Fdeque.empty
          | Some(vp2) -> Fdeque.enqueue_back v_betas_in' (ts, vp2))*)

    (*let construct_vsinceps tp new_in =
      Fdeque.fold new_in ~init:Fdeque.empty
        ~f:(fun acc (ts, vp1_opt, vp2_opt) ->
          match vp1_opt with
          | None -> (match vp2_opt with
                     | None -> Fdeque.empty
                     | Some(vp2) -> v_append_deque vp2 acc)
          | Some(vp1) -> (match vp2_opt with
                          | None -> Fdeque.empty
                          | Some(vp2) -> let acc' = v_append_deque vp2 acc in
                                         let vp2s = Fdeque.enqueue_back Fdeque.empty vp2 in
                                         let vp = Proof.V (Proof.make_vsince tp vp1 vp2s) in
                                         Fdeque.enqueue_back acc' (ts, vp)))*)

    (*let add_new_ps_v_alpha_betas_in tp new_in v_alpha_betas_in =
      let new_vsinceps_in = construct_vsinceps tp new_in in
      if not (Fdeque.is_empty new_vsinceps_in) then
        sorted_append new_vsinceps_in v_alpha_betas_in
      else v_alpha_betas_in*)

    (*let update_v_alpha_betas_in_tps tp v_alpha_betas_in =
      Fdeque.map v_alpha_betas_in ~f:(fun (ts, vvp) ->
          match vvp with
          | Proof.V vp -> (match Proof.decompose_vsince vp with
                           | Some (vp1, vp2s) -> (ts, Proof.V (Proof.make_vsince tp vp1 vp2s))
                           | None -> raise (Invalid_argument "found S proof in V deque"))
          | _ -> raise (Invalid_argument "found S proof in V deque"))*)

    (*let update_v_alpha_betas_in tp new_in v_alpha_betas_in =
      let v_alpha_betas_in_vapp = Fdeque.fold new_in ~init:v_alpha_betas_in ~f:(fun v_alpha_betas_in' (_, _, vp2_opt) ->
                                      match vp2_opt with
                                      | None -> Fdeque.empty
                                      | Some(vp2) -> v_append_deque vp2 v_alpha_betas_in') in
      let v_alpha_betas_in' = add_new_ps_v_alpha_betas_in tp new_in v_alpha_betas_in_vapp in
      update_v_alpha_betas_in_tps tp v_alpha_betas_in'*)

    (*let add_subps ts (p1: Proof.t) (p2: Proof.t) msaux =
      match p1, p2 with
      | S sp1, S sp2 ->
         let s_beta_alphas_in = s_append_deque sp1 msaux.s_beta_alphas_in in
         let s_beta_alphas_out = s_append_deque sp1 msaux.s_beta_alphas_out in
         let s_beta_alphas_out' = Fdeque.enqueue_back s_beta_alphas_out (ts, Proof.S (Proof.make_ssince sp2 Fdeque.empty)) in
         let v_alphas_betas_out = Fdeque.enqueue_back msaux.v_alphas_betas_out (ts, None, None) in
         { msaux with s_beta_alphas_in; s_beta_alphas_out = s_beta_alphas_out'; v_alphas_betas_out }
      | S sp1, V vp2 ->
         let s_beta_alphas_in = s_append_deque sp1 msaux.s_beta_alphas_in in
         let s_beta_alphas_out = s_append_deque sp1 msaux.s_beta_alphas_out in
         let v_alphas_betas_out = Fdeque.enqueue_back msaux.v_alphas_betas_out (ts, None, Some(vp2)) in
         { msaux with s_beta_alphas_in; s_beta_alphas_out; v_alphas_betas_out }
      | V vp1, S sp2 ->
         let s_beta_alphas_out = Fdeque.enqueue_back Fdeque.empty (ts, Proof.S (Proof.make_ssince sp2 Fdeque.empty)) in
         let v_alphas_out = sorted_enqueue (ts, (Proof.V vp1)) msaux.v_alphas_out in
         let v_alphas_betas_out = Fdeque.enqueue_back msaux.v_alphas_betas_out (ts, Some(vp1), None) in
         { msaux with s_beta_alphas_in = Fdeque.empty; s_beta_alphas_out; v_alphas_out; v_alphas_betas_out }
      | V vp1, V vp2 ->
         let v_alphas_out = sorted_enqueue (ts, (Proof.V vp1)) msaux.v_alphas_out in
         let v_alphas_betas_out = Fdeque.enqueue_back msaux.v_alphas_betas_out (ts, Some(vp1), Some(vp2)) in
         { msaux with s_beta_alphas_in = Fdeque.empty; s_beta_alphas_out = Fdeque.empty; v_alphas_out; v_alphas_betas_out }*)

    let shift_sat (l, r) s_beta_alphas_out s_beta_alphas_in =
      let (s_beta_alphas_out', new_in_sat) = split_in_out (fun (ts, _) -> ts) (l, r) s_beta_alphas_out in
      (s_beta_alphas_out', update_s_beta_alphas_in new_in_sat s_beta_alphas_in)

    (*let shift_vio (l, r) tp v_alphas_betas_out v_alpha_betas_in v_betas_in =
      let (v_alphas_betas_out', new_in_vio) = split_in_out (fun (ts, _, _) -> ts) (l, r) v_alphas_betas_out in
      let v_betas_in = update_v_betas_in new_in_vio v_betas_in in
      (v_alphas_betas_out', update_v_alpha_betas_in tp new_in_vio v_alpha_betas_in, v_betas_in)*)

    let clean (l, r) msaux =
      { msaux with s_beta_alphas_in = remove_cond_front (fun (ts, _) -> Time.(ts < l)) msaux.s_beta_alphas_in
                 ; v_alpha_betas_in = remove_cond_front (fun (ts, _) -> Time.(ts < l)) msaux.v_alpha_betas_in
                 ; v_alphas_out = remove_cond_front (fun (ts, _) -> Time.(ts <= r)) msaux.v_alphas_out
                 ; v_betas_in = remove_cond_front (fun (ts, _) -> Time.(ts < l)) msaux.v_betas_in }

    (*let shift (l, r) a ts tp msaux =
      let (tstps_in, tstps_out) = shift_tstps_past (l, r) a ts tp msaux.tstps_in msaux.tstps_out in
      let (s_beta_alphas_out, s_beta_alphas_in) = shift_sat (l,r) msaux.s_beta_alphas_out msaux.s_beta_alphas_in in
      let (v_alphas_betas_out, v_alpha_betas_in, v_betas_in) =
        shift_vio (l, r) tp msaux.v_alphas_betas_out msaux.v_alpha_betas_in msaux.v_betas_in in
      clean (l, r) ({ msaux with
                      tstps_in
                    ; tstps_out
                    ; s_beta_alphas_in
                    ; s_beta_alphas_out
                    ; v_alpha_betas_in
                    ; v_betas_in
                    ; v_alphas_betas_out })*)

    (*let eval tp msaux =
      if not (Fdeque.is_empty msaux.s_beta_alphas_in) then
        [snd(Fdeque.peek_front_exn msaux.s_beta_alphas_in)]
      else
        let cp1 = if not (Fdeque.is_empty msaux.v_alpha_betas_in) then
                    [snd(Fdeque.peek_front_exn msaux.v_alpha_betas_in)]
                  else [] in
        let cp2 = if not (Fdeque.is_empty msaux.v_alphas_out) then
                    let vp_f2 = snd(Fdeque.peek_front_exn msaux.v_alphas_out) in
                    match vp_f2 with
                    | V f2 -> [Proof.V (Proof.make_vsince tp f2 Fdeque.empty)]
                    | S _ -> raise (Invalid_argument "found S proof in V deque")
                  else [] in
        let cp3 = if Int.equal (Fdeque.length msaux.v_betas_in) (Fdeque.length msaux.tstps_in) then
                    let etp = match Fdeque.is_empty msaux.v_betas_in with
                      | true -> etp msaux.tstps_in msaux.tstps_out tp
                      | false -> Proof.v_at (snd(Fdeque.peek_front_exn msaux.v_betas_in)) in
                    [Proof.V (Proof.make_vsinceinf tp etp (Fdeque.map msaux.v_betas_in ~f:snd))]
                  else [] in
        [minp_list (cp1 @ cp2 @ cp3)]*)

    let add_subps_enforce ts (p1: Proof.t) (p2: Proof.t) msaux =
      match p1, p2 with
      | S sp1, S sp2 ->
         let s_beta_alphas_in = s_append_deque sp1 msaux.s_beta_alphas_in in
         let s_beta_alphas_out = s_append_deque sp1 msaux.s_beta_alphas_out in
         let s_beta_alphas_out' = Fdeque.enqueue_back s_beta_alphas_out (ts, Proof.S (Proof.make_ssince sp2 Fdeque.empty)) in
         { msaux with s_beta_alphas_in; s_beta_alphas_out = s_beta_alphas_out' }
      | S sp1, V _ ->
         let s_beta_alphas_in = s_append_deque sp1 msaux.s_beta_alphas_in in
         let s_beta_alphas_out = s_append_deque sp1 msaux.s_beta_alphas_out in
         { msaux with s_beta_alphas_in; s_beta_alphas_out }
      | V vp1, S sp2 ->
         let s_beta_alphas_out = Fdeque.enqueue_back Fdeque.empty (ts, Proof.S (Proof.make_ssince sp2 Fdeque.empty)) in
         let v_alphas_out = sorted_enqueue (ts, (Proof.V vp1)) msaux.v_alphas_out in
         { msaux with s_beta_alphas_in = Fdeque.empty; s_beta_alphas_out; v_alphas_out }
      | V _, V _ ->
         { msaux with s_beta_alphas_in = Fdeque.empty; s_beta_alphas_out = Fdeque.empty }

    let shift_enforce (l, r) _ _ _ msaux =
      let (s_beta_alphas_out, s_beta_alphas_in) = shift_sat (l,r) msaux.s_beta_alphas_out msaux.s_beta_alphas_in in
      clean (l, r) ({ msaux with s_beta_alphas_in
                               ; s_beta_alphas_out })

    let eval_enforce tp msaux =
      if not (Fdeque.is_empty msaux.s_beta_alphas_in) then
        [snd(Fdeque.peek_front_exn msaux.s_beta_alphas_in)]
      else
        [Proof.V (Proof.make_vff tp)]

    let update i ts tp p1 p2 msaux =
      let a = Interval.left i in
      let msaux_z = if Option.is_none msaux.ts_zero then
                      { msaux with ts_zero = Some(ts) }
                    else msaux in
      let msaux_subps = add_subps_enforce ts p1 p2 msaux_z in
      if Time.(ts < Option.value_exn msaux_subps.ts_zero + a) then
        ({ msaux_subps with tstps_out = Fdeque.enqueue_back msaux_subps.tstps_out (ts, tp) },
         [Proof.V (Proof.make_vsinceout tp)])
      else
        (let b = Interval.right i in
         let l = if (Option.is_some b) then Time.max Time.zero Time.(ts - (Option.value_exn b))
                 else (Option.value_exn msaux_subps.ts_zero) in
         let r = Time.(ts - a) in
         let msaux_shifted = shift_enforce (l, r) a ts tp msaux_subps in
         let ps = eval_enforce tp msaux_shifted in
         (msaux_shifted, ps))

    (* Only used for approximation (enforcement related) *)
    let do_since_base tp a pol (p1: Proof.t) (p2: Proof.t) =
      match p1, p2, pol with
      | _    , S sp2, true when Time.Span.is_zero a -> Proof.S (Proof.make_ssince sp2 Fdeque.empty)
      | _    , _    , true -> Proof.V (Proof.make_vff tp)
      | V vp1, _    , false when not (Time.Span.is_zero a) -> Proof.V (Proof.make_vsince tp vp1 (Fdeque.empty))
      | _    , _    , false -> Proof.S (Proof.make_stt tp)

  end

  module Until = struct

    type t = { tstps_in: (Time.t * timepoint) Fdeque.t
             ; tstps_out: (Time.t * timepoint) Fdeque.t
             ; s_alphas_beta: ((Time.t * Proof.t) Fdeque.t) Fdeque.t
             ; s_alphas_suffix: (Time.t * Proof.sp) Fdeque.t
             ; v_betas_alpha: ((Time.t * Proof.t) Fdeque.t) Fdeque.t
             ; v_alphas_out: (Time.t * Proof.t) Fdeque.t
             ; v_alphas_in: (Time.t * Proof.t) Fdeque.t
             ; v_betas_suffix_in: (Time.t * Proof.vp) Fdeque.t
             ; optimal_proofs: (Time.t * Proof.t) Fdeque.t }

    let init () = { tstps_in = Fdeque.empty
                  ; tstps_out = Fdeque.empty
                  ; s_alphas_beta = Fdeque.enqueue_back Fdeque.empty Fdeque.empty
                  ; s_alphas_suffix = Fdeque.empty
                  ; v_betas_alpha = Fdeque.enqueue_back Fdeque.empty Fdeque.empty
                  ; v_alphas_out = Fdeque.empty
                  ; v_alphas_in = Fdeque.empty
                  ; v_betas_suffix_in = Fdeque.empty
                  ; optimal_proofs = Fdeque.empty }

    (*let to_string { tstps_in
                  ; tstps_out
                  ; s_alphas_beta
                  ; s_alphas_suffix
                  ; v_betas_alpha
                  ; v_alphas_out
                  ; v_alphas_in
                  ; v_betas_suffix_in
                  ; optimal_proofs } =
      ("\n\nUntil state: " ^ (tstps_to_string None tstps_in tstps_out) ^
         Fdeque.fold s_alphas_beta ~init:"\ns_alphas_beta = \n"
           ~f:(fun acc1 d ->
             acc1 ^ "\n" ^
               Fdeque.fold d ~init:"[" ~f:(fun acc2 (ts, p) ->
                   acc2 ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.to_string "" p) ^ "\n]\n") ^
           Fdeque.fold s_alphas_suffix ~init:"\ns_alphas_suffix = "
             ~f:(fun acc (ts, p) ->
               acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.s_to_string "" p) ^
             Fdeque.fold v_betas_alpha ~init:"\nv_betas_alpha = \n"
               ~f:(fun acc1 d ->
                 acc1 ^ "\n" ^
                   Fdeque.fold d ~init:"[" ~f:(fun acc2 (ts, p) ->
                       acc2 ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.to_string "" p) ^ "\n]\n") ^
               Fdeque.fold v_alphas_out ~init:"\nv_alphas_out = "
                 ~f:(fun acc (ts, p) ->
                   acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.to_string "" p) ^
                 Fdeque.fold v_alphas_in ~init:"\nv_alphas_in = "
                   ~f:(fun acc (ts, p) ->
                     acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.to_string "" p) ^
                   Fdeque.fold v_betas_suffix_in ~init:"\nv_betas_suffix_in = "
                     ~f:(fun acc (ts, p) ->
                       acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.v_to_string "" p) ^
                     Fdeque.fold optimal_proofs ~init:"\noptimal_proofs = "
                       ~f:(fun acc (ts, p) ->
                         acc ^ (Printf.sprintf "\n(%s)\n" (Time.to_string ts)) ^ Proof.to_string "" p))*)

    let ts_of_tp tp tstps_in tstps_out =
      match (Fdeque.find tstps_out ~f:(fun (_, tp') -> tp = tp')) with
      | None -> (match (Fdeque.find tstps_in ~f:(fun (_, tp') -> tp = tp')) with
                 | None -> raise (Failure "ts not found")
                 | Some(ts, _) -> ts)
      | Some(ts, _) -> ts

    (* TODO: Rewrite this function with map instead of fold *)
    let step_sdrop_tp tp s_alphas_beta =
      Fdeque.fold s_alphas_beta ~init:Fdeque.empty
        ~f:(fun s_alphas_beta' (ts, ssp) ->
          match ssp with
          | Proof.S sp -> if tp = (Proof.s_at sp) then
                            (match Proof.s_drop sp with
                             | None -> s_alphas_beta'
                             | Some(sp') -> Fdeque.enqueue_back s_alphas_beta' (ts, Proof.S sp'))
                          else (Fdeque.enqueue_back s_alphas_beta' (ts, ssp))
          | V _ -> raise (Invalid_argument "found V proof in S deque"))

    let step_vdrop_ts a first_ts v_betas_alpha tstps_in =
      let rec vdrop_until vp =
        let is_out = match Fdeque.find ~f:(fun (_, tp') -> (Proof.v_etp vp) = tp') tstps_in with
          | None -> true
          | Some(ts', _) -> Time.(ts' < (first_ts + a)) in
        if is_out then
          (match Proof.v_drop vp with
           | None -> None
           | Some(vp') -> vdrop_until vp')
        else Some(vp) in
      Fdeque.fold v_betas_alpha ~init:Fdeque.empty
        ~f:(fun v_betas_alpha' (ts, vvp) ->
          (match vvp with
           | Proof.V vp -> (match vdrop_until vp with
                            | None -> v_betas_alpha'
                            | Some (vp') -> Fdeque.enqueue_back v_betas_alpha' (ts, Proof.V vp'))
           | S _ -> raise (Invalid_argument "found S proof in V deque")))

    (*let remove_out_less2_lts lim d =
      remove_cond_front_ne (fun d' -> Fdeque.is_empty d')
        (Fdeque.map d ~f:(fun d' ->
             (Fdeque.fold d' ~init:Fdeque.empty ~f:(fun acc (ts, p) ->
                  if Time.(lim <= ts) then
                    Fdeque.enqueue_back acc (ts, p)
                  else acc))))*)

    let add_subps a (ts, tp) (p1: Proof.t) (p2: Proof.t) muaux =
      let first_ts = match first_ts_tp muaux.tstps_out muaux.tstps_in with
        | None -> Time.zero
        | Some(ts', _) -> ts' in
      match p1, p2 with
      | S sp1, S sp2 ->
         let s_alphas_beta = if Time.(first_ts + a <= ts) then
                               let cur_s_alphas_beta = Fdeque.peek_back_exn muaux.s_alphas_beta in
                               let sp = Proof.S (Proof.make_suntil sp2 (Fdeque.map muaux.s_alphas_suffix ~f:snd)) in
                               let cur_s_alphas_beta_add = sorted_enqueue (ts, sp) cur_s_alphas_beta in
                               Fdeque.enqueue_back (Fdeque.drop_back_exn muaux.s_alphas_beta) cur_s_alphas_beta_add
                             else muaux.s_alphas_beta in
         let v_betas_alpha = if not (Fdeque.is_empty (Fdeque.peek_back_exn muaux.v_betas_alpha)) then
                               Fdeque.enqueue_back muaux.v_betas_alpha Fdeque.empty
                             else muaux.v_betas_alpha in
         let s_alphas_suffix = Fdeque.enqueue_back muaux.s_alphas_suffix (ts, sp1) in
         let v_betas_suffix_in = if Time.(first_ts + a <= ts) then Fdeque.empty
                                 else muaux.v_betas_suffix_in in
         { muaux with s_alphas_beta; v_betas_alpha; s_alphas_suffix; v_betas_suffix_in }
      | S sp1, V vp2 ->
         let s_alphas_suffix = Fdeque.enqueue_back muaux.s_alphas_suffix (ts, sp1) in
         let v_betas_suffix_in = if Time.(first_ts + a <= ts) then
                                   Fdeque.enqueue_back muaux.v_betas_suffix_in (ts, vp2)
                                 else muaux.v_betas_suffix_in in
         { muaux with s_alphas_suffix; v_betas_suffix_in }
      | V vp1, S sp2 ->
         let s_alphas_beta = if Time.(first_ts + a <= ts) then
                               (let cur_s_alphas_beta = Fdeque.peek_back_exn muaux.s_alphas_beta in
                                let ssp = Proof.S (Proof.make_suntil sp2 (Fdeque.map muaux.s_alphas_suffix ~f:snd)) in
                                let cur_s_alphas_beta_add = sorted_enqueue (ts, ssp) cur_s_alphas_beta in
                                let s_alphas_beta' = Fdeque.enqueue_back (Fdeque.drop_back_exn muaux.s_alphas_beta)
                                                       cur_s_alphas_beta_add in
                                if not (Fdeque.is_empty (Fdeque.peek_back_exn s_alphas_beta')) then
                                  Fdeque.enqueue_back s_alphas_beta' Fdeque.empty
                                else s_alphas_beta')
                             else muaux.s_alphas_beta in
         let v_betas_alpha = if not (Fdeque.is_empty (Fdeque.peek_back_exn muaux.v_betas_alpha)) then
                               Fdeque.enqueue_back muaux.v_betas_alpha Fdeque.empty
                             else muaux.v_betas_alpha in
         let s_alphas_suffix = Fdeque.empty in
         let (v_alphas_in, v_alphas_out) = if Time.(first_ts + a <= ts) then
                                             (Fdeque.enqueue_back muaux.v_alphas_in (ts, Proof.V vp1),
                                              muaux.v_alphas_out)
                                           else (muaux.v_alphas_in, sorted_enqueue (ts, Proof.V vp1) muaux.v_alphas_out) in
         let v_betas_suffix_in = if Time.(first_ts + a <= ts) then Fdeque.empty
                                 else muaux.v_betas_suffix_in in
         { muaux with s_alphas_beta; v_betas_alpha; s_alphas_suffix; v_alphas_in; v_alphas_out; v_betas_suffix_in }
      | V vp1, V vp2 ->
         let s_alphas_beta = if not (Fdeque.is_empty (Fdeque.peek_back_exn muaux.s_alphas_beta)) then
                               Fdeque.enqueue_back muaux.s_alphas_beta Fdeque.empty
                             else muaux.s_alphas_beta in
         let s_alphas_suffix = Fdeque.empty in
         let v_betas_suffix_in = if Time.(first_ts + a <= ts) then
                                   Fdeque.enqueue_back muaux.v_betas_suffix_in (ts, vp2)
                                 else muaux.v_betas_suffix_in in
         let v_betas_alpha = if Time.(first_ts + a <= ts) then
                               (let cur_v_betas_alpha = Fdeque.peek_back_exn muaux.v_betas_alpha in
                                let vvp = Proof.V (Proof.make_vuntil tp vp1 (Fdeque.map v_betas_suffix_in ~f:snd)) in
                                let cur_v_betas_alpha_add = sorted_enqueue (ts, vvp) cur_v_betas_alpha in
                                Fdeque.enqueue_back (Fdeque.drop_back_exn muaux.v_betas_alpha)
                                  cur_v_betas_alpha_add)
                             else muaux.v_betas_alpha in
         let (v_alphas_in, v_alphas_out) = if Time.(first_ts + a <= ts) then
                                             (Fdeque.enqueue_back muaux.v_alphas_in (ts, Proof.V vp1),
                                              muaux.v_alphas_out)
                                           else (muaux.v_alphas_in, sorted_enqueue (ts, Proof.V vp1) muaux.v_alphas_out) in
         { muaux with s_alphas_beta; s_alphas_suffix; v_betas_suffix_in; v_betas_alpha; v_alphas_in; v_alphas_out }

    let drop_tp tp s_alphas_beta =
      match Fdeque.peek_front s_alphas_beta with
      | None -> raise (Etc.Empty_deque "alphas_beta")
      | Some(cur_s_alphas_beta) ->
         if not (Fdeque.is_empty cur_s_alphas_beta) then
           Fdeque.enqueue_front (Fdeque.drop_front_exn s_alphas_beta)
             (step_sdrop_tp tp cur_s_alphas_beta)
         else s_alphas_beta

    let drop_v_ts a ts v_betas_alpha tstps_in =
      Fdeque.map v_betas_alpha ~f:(fun d -> step_vdrop_ts a ts d tstps_in)

    let drop_v_single_ts cur_tp v_betas_alpha =
      let first_v_betas_alpha = Fdeque.fold (Fdeque.peek_front_exn v_betas_alpha) ~init:Fdeque.empty
                                  ~f:(fun first_v_betas_alpha' (ts', vvp) ->
                                    match vvp with
                                    | Proof.V vp -> if Proof.v_etp vp <= cur_tp then
                                                      (match Proof.v_drop vp with
                                                       | None -> first_v_betas_alpha'
                                                       | Some (vp') -> Fdeque.enqueue_back first_v_betas_alpha'
                                                                         (ts', Proof.V vp'))
                                                    else Fdeque.enqueue_back first_v_betas_alpha' (ts', Proof.V vp)
                                    | S _ -> raise (Invalid_argument "found S proof in V deque")) in
      Fdeque.enqueue_front (Fdeque.drop_front_exn v_betas_alpha) first_v_betas_alpha

    let adjust a (nts, ntp) { tstps_in
                            ; tstps_out
                            ; s_alphas_beta
                            ; s_alphas_suffix
                            ; v_betas_alpha
                            ; v_alphas_out
                            ; v_alphas_in
                            ; v_betas_suffix_in
                            ; optimal_proofs } =
      let eval_tp = match first_ts_tp tstps_out tstps_in with
        | None -> raise (Failure "tp not found")
        | Some(_, tp') -> tp' in
      let (tstps_out', tstps_in') = drop_first_ts_tp tstps_out tstps_in in
      let (first_ts, first_tp) = match first_ts_tp tstps_out' tstps_in' with
        | None -> (nts, ntp)
        | Some(ts', tp') -> (ts', tp') in
      (* v_betas_alpha *)
      let v_betas_alpha_step1 = Fdeque.map v_betas_alpha ~f:(fun d ->
                                    remove_cond_front (fun (ts', p) ->
                                        Time.(ts' < first_ts + a) || ((Proof.p_at p) < first_tp)) d) in
      let v_betas_alpha_step2 = if Time.Span.is_zero a then
                                  drop_v_single_ts eval_tp v_betas_alpha_step1
                                else drop_v_ts a first_ts v_betas_alpha_step1 tstps_in' in
      let v_betas_alpha_step3 = remove_cond_front_ne (fun d' -> Fdeque.is_empty d') v_betas_alpha_step2 in
      (* tstp_out and tstp_in *)
      let (tstps_out'', tstps_in'') = shift_tstps_future a first_ts ntp tstps_out' tstps_in' in
      (* s_alphas_beta *)
      let s_alphas_beta_step1 = drop_tp eval_tp s_alphas_beta in
      let s_alphas_beta_step2 = Fdeque.map s_alphas_beta_step1 ~f:(fun d ->
                                    (remove_cond_front (fun (_, p) ->
                                         match p with
                                         | Proof.S sp -> Time.((ts_of_tp (Proof.s_ltp sp)
                                                                  tstps_in'' tstps_out'') < (first_ts + a))
                                         | V _ -> raise (Invalid_argument "found V proof in S deque")) d)) in
      let s_alphas_beta_step3 = remove_cond_front_ne (fun d' -> Fdeque.is_empty d') s_alphas_beta_step2 in
      (* s_alphas_suffix *)
      let s_alphas_suffix' = remove_cond_front (fun (_, sp) -> (Proof.s_at sp) < first_tp) s_alphas_suffix in
      (* v_alphas_in and v_alphas_out *)
      let v_alphas_out_step1 = remove_cond_front (fun (_, p) -> (Proof.p_at p) < first_tp) v_alphas_out in
      let (new_out_v_alphas, v_alphas_in') = split_out_in (fun (ts', _) -> ts')
                                               (first_ts, Time.(first_ts + a)) v_alphas_in in
      let v_alphas_out' = sorted_append new_out_v_alphas v_alphas_out_step1 in
      (* v_betas_in *)
      let v_betas_suffix_in' = remove_cond_front (fun (_, vp) ->
                                   match Fdeque.peek_front tstps_in'' with
                                   | None -> (match Fdeque.peek_back tstps_out'' with
                                              | None -> (Proof.v_at vp) <= ntp
                                              | Some(_, tp') -> (Proof.v_at vp) <= tp')
                                   | Some (_, tp') -> (Proof.v_at vp) < tp') v_betas_suffix_in in
      { tstps_in = tstps_in''
      ; tstps_out = tstps_out''
      ; s_alphas_beta = s_alphas_beta_step3
      ; s_alphas_suffix = s_alphas_suffix'
      ; v_betas_alpha = v_betas_alpha_step3
      ; v_alphas_out = v_alphas_out'
      ; v_alphas_in = v_alphas_in'
      ; v_betas_suffix_in = v_betas_suffix_in'
      ; optimal_proofs }

    let eval_step a (nts, ntp) ts tp muaux =
      let cur_alphas_beta = Fdeque.peek_front_exn muaux.s_alphas_beta in
      let optimal_proofs_step1 = if not (Fdeque.is_empty cur_alphas_beta) then
                                   (match Fdeque.peek_front_exn cur_alphas_beta with
                                    | (_, S sp) -> if tp = Proof.s_at sp then
                                                     Fdeque.enqueue_back muaux.optimal_proofs (ts, S sp)
                                                   else muaux.optimal_proofs
                                    | _ -> raise (Invalid_argument "found V proof in S deque"))
                                 else muaux.optimal_proofs in
      let optimal_proofs_step2 =
        if Int.equal (Fdeque.length optimal_proofs_step1) (Fdeque.length muaux.optimal_proofs) then
          (let c1 = if not (Fdeque.is_empty muaux.v_betas_alpha) then
                      let cur_betas_alpha = Fdeque.peek_front_exn muaux.v_betas_alpha in
                      (if not (Fdeque.is_empty cur_betas_alpha) then
                         match Fdeque.peek_front_exn cur_betas_alpha with
                         | (_, V vp) -> (
                           match Proof.decompose_vuntil vp with
                           | Some (vp1, vp2s) ->
                              (match Fdeque.peek_front muaux.tstps_in with
                               | None -> []
                               | Some(_, first_tp_in) ->
                                  if Proof.v_etp (Proof.make_vuntil tp vp1 vp2s) = first_tp_in then
                                    [Proof.V (Proof.make_vuntil tp vp1 vp2s)]
                                  else [])
                           | None -> raise (Invalid_argument "proof should be VUntil"))
                         | _ -> raise (Invalid_argument "proof should be VUntil")
                       else [])
                    else [] in
           let c2 = if not (Fdeque.is_empty muaux.v_alphas_out) then
                      let vvp1 = snd(Fdeque.peek_front_exn muaux.v_alphas_out) in
                      match vvp1 with
                      | V vp1 -> [Proof.V (Proof.make_vuntil tp vp1 Fdeque.empty)]
                      | S _ -> raise (Invalid_argument "found S proof in V deque")
                    else [] in
           let c3 = if Int.equal (Fdeque.length muaux.v_betas_suffix_in) (Fdeque.length muaux.tstps_in) then
                      let ltp = match Fdeque.peek_back muaux.v_betas_suffix_in with
                        | None -> snd(Fdeque.peek_back_exn muaux.tstps_out)
                        | Some(_, vp2) -> (Proof.v_at vp2) in
                      [Proof.V (Proof.make_vuntilinf tp ltp (Fdeque.map muaux.v_betas_suffix_in ~f:snd))]
                    else [] in
           let cps = c1 @ c2 @ c3 in
           if List.length cps > 0 then
             Fdeque.enqueue_back muaux.optimal_proofs (ts, minp_list cps)
           else muaux.optimal_proofs)
        else optimal_proofs_step1 in
      adjust a (nts, ntp) { muaux with optimal_proofs = optimal_proofs_step2 }

    let shift (a, b) (nts, ntp) muaux =
      let tstps = ready_tstps b nts muaux.tstps_out muaux.tstps_in in
      Fdeque.fold tstps ~init:muaux ~f:(fun muaux' (ts, tp) ->
          eval_step a (nts, ntp) ts tp muaux')

    let update i nts ntp p1 p2 muaux =
      let a = Interval.left i in
      let b = match Interval.right i with
        | None -> Time.Span.infty
        | Some(b') -> b' in
      let muaux_shifted = shift (a, b) (nts, ntp) muaux in
      let (tstps_out, tstps_in) = add_tstp_future a b nts ntp muaux_shifted.tstps_out muaux_shifted.tstps_in in
      add_subps a (nts, ntp) p1 p2 { muaux_shifted with tstps_out; tstps_in }

    let rec eval i nts ntp (muaux, ops) =
      let a = Interval.left i in
      match Interval.right i with
      | None -> (muaux, ops)
      | Some(b) -> let muaux_shifted = shift (a, b) (nts, ntp) muaux in
                   (match Fdeque.peek_back muaux.optimal_proofs with
                    | None -> (muaux, ops)
                    | Some(ts, _) -> if Time.(ts + b < nts) then
                                       let ((_, op), optimal_proofs) = Fdeque.dequeue_back_exn muaux_shifted.optimal_proofs in
                                       let (muaux', ops') = eval i nts ntp ({ muaux_shifted with optimal_proofs }, ops) in
                                       (muaux', ops' @ [op])
                                     else (muaux, ops))

    (* Only used for approximation (enforcement related) *)
    let do_until_base tp i pol (p_new1: Proof.t) (p_new2: Proof.t) (p_next: Proof.t) =
      match p_new1, p_new2, p_next, pol with
      | _    , S sp2, _  , true when Interval.has_zero i -> Proof.S (Proof.make_suntilnow sp2 i)
      | S sp1, _    , S _, true -> Proof.S (Proof.make_suntilassm tp sp1 i)
      | _    , _    , _  , true -> Proof.V (Proof.make_vff tp)
      | V vp1, _    , _  , false when not (Interval.has_zero i) -> Proof.V (Proof.make_vuntilnow vp1 i)
      | V vp1, V   _, _  , false -> Proof.V (Proof.make_vuntilnow vp1 i)
      | _    , V vp2, V _, false -> Proof.V (Proof.make_vuntilassm tp vp2 i)
      | _    , _    , _  , false -> Proof.S (Proof.make_stt tp)

  end

  module Prev_Next = struct

    type operator = Prev | Next

    let update_eval op i p ts ts' =
      let c1 = (match p with
                | Proof.S sp -> if Interval.diff_is_in ts ts' i then
                                  (match op with
                                   | Prev -> [Proof.S (Proof.make_sprev sp)]
                                   | Next -> [S (Proof.make_snext sp)])
                                else []
                | V vp -> (match op with
                           | Prev -> [V (Proof.make_vprev vp)]
                           | Next -> [V (Proof.make_vnext vp)])) in
      let c2 = if Interval.diff_left_of ts ts' i then
                 (match op with
                  | Prev -> [Proof.V (Proof.make_vprevoutl ((Proof.p_at p)+1))]
                  | Next -> [V (Proof.make_vnextoutl ((Proof.p_at p)-1))])
               else [] in
      let c3 = if Interval.diff_right_of ts ts' i then
                 (match op with
                  | Prev -> [Proof.V (Proof.make_vprevoutr ((Proof.p_at p)+1))]
                  | Next -> [V (Proof.make_vnextoutr ((Proof.p_at p)-1))])
               else [] in
      minp_list (c1 @ c2 @ c3)

  end

  module MFormula = struct

    type binop_info         = (E.t, E.t) Buf2.t
    type nop_info           = E.t Bufn.t
    type prev_info          = (E.t, Time.t) Buft.t
    type next_info          = Time.t list
    type tp_info            = (Time.t * timepoint) list
    type buft_info          = (E.t, Time.t * timepoint) Buft.t
    type once_info          = Once.t Pdt.t
    type eventually_info    = Eventually.t Pdt.t
    type historically_info  = Historically.t Pdt.t
    type always_info        = Always.t Pdt.t
    type buf2t_info         = (E.t, E.t, Time.t * timepoint) Buf2t.t
    type since_info         = Since.t Pdt.t
    type until_info         = Until.t Pdt.t

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
      | MIff          of Side.t * Side.t * t * t * binop_info
      | MExists       of string * Dom.tt * bool * t
      | MForall       of string * Dom.tt * bool * t
      | MPrev         of Interval.t * t * bool * prev_info
      | MNext         of Interval.t * t * bool * next_info
      | MENext        of Interval.t * Time.t option * t * Etc.valuation
      | MOnce         of Interval.t * t * tp_info * once_info
      | MEventually   of Interval.t * t * buft_info * eventually_info
      | MEEventually  of Interval.t * Time.t option * t * Etc.valuation
      | MHistorically of Interval.t * t * tp_info * historically_info
      | MAlways       of Interval.t * t * buft_info * always_info
      | MEAlways      of Interval.t * Time.t option * t * Etc.valuation
      | MSince        of Side.t * Interval.t * t * t * buf2t_info * since_info
      | MUntil        of Interval.t * t * t * buf2t_info * until_info
      | MEUntil       of Side.t * Interval.t * Time.t option *  t * t * Etc.valuation

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
        | MPrev (_, f, _, _)
        | MOnce (_, f, _, _)
        | MHistorically (_, f, _, _)
        | MEventually (_, f, _, _)
        | MEEventually (_, _, f, _)
        | MAlways (_, f, _, _)
        | MEAlways (_, _, f, _)
        | MNext (_, f, _, _)
        | MENext (_, _, f, _)
        | MAgg (_, _, _, _, _, f)
        | MTop (_, _, _, _, _, f) -> [f]
      | MImp (_, f1, f2, _)
        | MIff (_, _, f1, f2, _)
        | MSince (_, _, f1, f2, _, _)
        | MUntil (_, f1, f2, _, _)
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
      | MIff (_, _, f, g, _) -> Printf.sprintf (Etc.paren l 4 "%a ↔ %a") (fun _ -> value_to_string_rec 4) f (fun _ -> value_to_string_rec 4) g
      | MExists (x, _, _, f) -> Printf.sprintf (Etc.paren l 5 "∃%s. %a") x (fun _ -> value_to_string_rec 5) f
      | MForall (x, _, _, f) -> Printf.sprintf (Etc.paren l 5 "∀%s. %a") x (fun _ -> value_to_string_rec 5) f
      | MPrev (i, f, _, _) -> Printf.sprintf (Etc.paren l 5 "●%a %a") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f
      | MNext (i, f, _, _) -> Printf.sprintf (Etc.paren l 5 "○%a %a") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f
      | MENext (i, ts, f, _) -> Printf.sprintf (Etc.paren l 5 "○*%a %a") (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) f
      | MOnce (i, f, _, _) -> Printf.sprintf (Etc.paren l 5 "⧫%a %a") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f
      | MEventually (i, f, _, _) -> Printf.sprintf (Etc.paren l 5 "◊%a %a") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f
      | MEEventually (i, ts, f, _) -> Printf.sprintf (Etc.paren l 5 "◊*%a %a") (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) f
      | MHistorically (i, f, _, _) -> Printf.sprintf (Etc.paren l 5 "■%a %a") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f
      | MAlways (i, f, _, _) -> Printf.sprintf (Etc.paren l 5 "□%a %a") (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) f
      | MEAlways (i, ts, f, _) -> Printf.sprintf (Etc.paren l 5 "□*%a %a") (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) f
      | MSince (_, i, f, g, _, _) -> Printf.sprintf (Etc.paren l 0 "%a S%a %a") (fun _ -> value_to_string_rec 5) f
                                       (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) g
      | MUntil (i, f, g, _, _) -> Printf.sprintf (Etc.paren l 0 "%a U%a %a") (fun _ -> value_to_string_rec 5) f
                                    (fun _ -> Interval.to_string) i (fun _ -> value_to_string_rec 5) g
      | MEUntil (_, i, ts, f, g, _) -> Printf.sprintf (Etc.paren l 0 "%a U*%a %a") (fun _ -> value_to_string_rec 5) f
                                         (fun _ -> ts_i_to_string) (ts, i) (fun _ -> value_to_string_rec 5) g
    let value_to_string = value_to_string_rec 0

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
        (value_to_string mf) n
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
      | MIff (_, _, _, _, _) -> Printf.sprintf "↔"
      | MExists (x, _, _, _) -> Printf.sprintf "∃ %s." x
      | MForall (x, _, _, _) -> Printf.sprintf "∀ %s." x
      | MPrev (i, _, _, _) -> Printf.sprintf "●%s" (Interval.to_string i)
      | MNext (i, _, _, _) -> Printf.sprintf "○%s" (Interval.to_string i)
      | MENext (i, ts, _, _) -> Printf.sprintf "○*%s" (ts_i_to_string (ts, i))
      | MOnce (i, _, _, _) -> Printf.sprintf "⧫%s" (Interval.to_string i)
      | MEventually (i, _, _, _) -> Printf.sprintf "◊%s" (Interval.to_string i)
      | MEEventually (i, ts, _, _) -> Printf.sprintf "◊*%s" (ts_i_to_string (ts, i))
      | MHistorically (i, _, _, _) -> Printf.sprintf "■%s" (Interval.to_string i)
      | MAlways (i, _, _, _) -> Printf.sprintf "□%s" (Interval.to_string i)
      | MEAlways (i, ts, _, _) -> Printf.sprintf "□*%s" (ts_i_to_string (ts, i))
      | MSince (_, i, _, _, _, _) -> Printf.sprintf "S%s" (Interval.to_string i)
      | MUntil (i, _, _, _, _) -> Printf.sprintf "U%s" (Interval.to_string i)
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
      | MIff (s, _, _, _, _) -> Printf.sprintf "%s" (Side.to_string s)
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
      | MSince (s, _, _, _, _, _) -> Printf.sprintf "%s" (Side.to_string s)
      | MUntil _ -> Printf.sprintf "N"
      | MEUntil (s, _, _, _, _, _) -> Printf.sprintf "%s" (Side.to_string s)


    (*let rec core_to_formula ts' =
      let sub i = function
      | Some ts -> Interval.sub i Time.(ts' - ts)
      | None -> i in
      function
      | MTT -> Formula.TT
      | MFF -> Formula.FF
      | MEqConst (x, d) -> Formula.TT
      | MEqConst (x, d) -> Formula.FF
      | MEqConst (x, d) -> Formula.EqConst (x, d)
      | MPredicate (e, t) -> Formula.Predicate (e, t)
      | MAgg (s, op, op_fun, _, _, x, y, f) ->
      Formula.Agg (s, op, x, y, to_formula f)
      | MNeg f -> Formula.Neg (to_formula f)
      | MAnd (s, f, g, bi) -> Formula.And (s, to_formula f, to_formula g)
      | MOr (s, f, g, bi) -> Formula.Or (s, to_formula f, to_formula g)
      | MImp (s, f, g, bi) -> Formula.Imp (s, to_formula f, to_formula g)
      | MIff (s, t, f, g, bi) -> Formula.Iff (s, t, to_formula f, to_formula g)
      | MExists (x, tt, _, _, _, f) -> Formula.Exists (x, to_formula f)
      | MForall (x, tt, _, _, _, f) -> Formula.Forall (x, to_formula f)
      | MPrev (i, f, b, pi) -> Formula.Prev (i, to_formula f)
      | MNext (i, f, b, si) -> Formula.Next (i, to_formula f)
      | MENext (i, ts, f, _) -> Formula.Next (sub i ts, to_formula f)
      | MOnce (i, f, ti, oi) -> Formula.Once (i, to_formula f)
      | MEventually (i, f, bi, oi) -> Formula.Eventually (i, to_formula f)
      | MEEventually (i, ts, f, _) -> Formula.Eventually (sub i ts, to_formula f)
      | MHistorically (i, f, ti, oi) -> Formula.Historically (i, to_formula f)
      | MAlways (i, f, bi, ai) -> Formula.Always (i, to_formula f)
      | MEAlways (i, ts, f, _) -> Formula.Always (sub i ts, to_formula f)
      | MSince (s, i, f, g, bi, si) -> Formula.Since (s, i, to_formula f, to_formula g)
      | MUntil (i, f, g, bi, ui) -> Formula.Until (N, i, to_formula f, to_formula g)
      | MEUntil (s, i, ts, f, g, _) -> Formula.Until (s, sub i ts, to_formula f, to_formula g)

      and to_formula ?(ts'=Time.zero) mf = core_to_formula ts' mf.mf*)

    let core_hash =
      let (+++) x y = x * 65599 + y in
      let rec ppp = function
        | [x; y] -> x.hash +++ y.hash
        | x :: ys -> x.hash +++ ppp ys
        | [] -> raise (Invalid_argument "cannot apply ppp to less than two elements") in
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
      | MIff (s, _, f, g, _) ->
         String.hash "MIff" +++ Side.hash s +++ f.hash +++ g.hash
      | MExists (x, _, _, f) ->
         String.hash "MExists" +++ String.hash x +++ f.hash
      | MForall (x, _, _, f) ->
         String.hash "MForall" +++ String.hash x +++ f.hash
      | MPrev (i, f, _, _) ->
         String.hash "MPrev" +++ Interval.hash i +++ f.hash
      | MNext (i, f, _, _) ->
         String.hash "MNext" +++ Interval.hash i +++ f.hash
      | MENext (i, _, f, _) ->
         String.hash "MENext" +++ Interval.hash i +++ f.hash
      | MOnce (i, f, _, _) ->
         String.hash "MOnce" +++ Interval.hash i +++ f.hash
      | MEventually (i, f, _, _) ->
         String.hash "MEventually" +++ Interval.hash i +++ f.hash
      | MEEventually (i, _, f, v) ->
         String.hash "MEEventually" +++ Interval.hash i +++ f.hash +++ Etc.hash_valuation v
      | MHistorically (i, f, _, _) ->
         String.hash "MHistorically" +++ Interval.hash i +++ f.hash
      | MAlways (i, f, _, _) ->
         String.hash "MAlways" +++ Interval.hash i +++ f.hash
      | MEAlways (i, _, f, v) ->
         String.hash "MEAlways" +++ Interval.hash i +++ f.hash +++ Etc.hash_valuation v
      | MSince (s, i, f, g, _, _) ->
         String.hash "MSince" +++ Side.hash s +++ Interval.hash i +++ f.hash +++ g.hash
      | MUntil (i, f, g, _, _) ->
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
         | MIff (s, t, f, g, inf) -> map2 f g (fun f g -> MIff (s, t, f, g, inf))
         | MExists (s, tt, b, f) -> map1 f (fun f -> MExists (s, tt, b, f))
         | MForall (s, tt, b, f) -> map1 f (fun f -> MForall (s, tt, b, f))
         | MPrev (i, f, b, inf) -> map1 f (fun f -> MPrev (i, f, b, inf))
         | MNext (i, f, b, inf) -> map1 f (fun f -> MNext (i, f, b, inf))
         | MENext (i, t_opt, f, v) -> add_hash (map1 f (fun f -> MENext (i, t_opt, f, v)))
         | MOnce (i, f, inf1, inf2) -> map1 f (fun f -> MOnce (i, f, inf1, inf2))
         | MEventually (i, f, inf1, inf2) -> map1 f (fun f -> MEventually (i, f, inf1, inf2))
         | MEEventually (i, t_opt, f, v) -> add_hash (map1 f (fun f -> MEEventually (i, t_opt, f, v)))
         | MHistorically (i, f, inf1, inf2) -> map1 f (fun f -> MHistorically (i, f, inf1, inf2))
         | MAlways (i, f, inf1, inf2) -> map1 f (fun f -> MAlways (i, f, inf1, inf2))
         | MEAlways (i, t_opt, f, inf) -> add_hash (map1 f (fun f -> MEAlways (i, t_opt, f, inf)))
         | MSince (s, i, f, g, inf1, inf2) -> map2 f g (fun f g -> MSince (s, i, f, g, inf1, inf2))
         | MUntil (i, f, g, inf1, inf2) -> map2 f g (fun f g -> MUntil (i, f, g, inf1, inf2))
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
        | MIff (_, _, f, g, _)
        | MSince (_, _, f, g, _, _)
        | MUntil (_, f, g, _, _)
        | MEUntil (_, _, _, f, g, _) -> Set.union (fv f) (fv g)
      | MExists (_, _, _, f)
        | MForall (_, _, _, f)
        | MPrev (_, f, _, _)
        | MNext (_, f, _, _)
        | MENext (_, _, f, _)
        | MOnce (_, f, _, _) 
        | MEventually (_, f, _, _)
        | MEEventually (_, _, f, _)
        | MHistorically (_, f, _, _)
        | MAlways (_, f, _, _)
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
      | MIff (s, t, f, g, inf) -> map2 fvs f g (fun f g -> MIff (s, t, f, g, inf)) id2
      | MPrev (i, f, b, inf) -> map1 fvs f (fun f -> MPrev (i, f, b, inf)) id
      | MNext (i, f, b, inf) -> map1 fvs f (fun f -> MNext (i, f, b, inf)) id
      | MENext (i, t_opt, f, v) -> map1 fvs f (fun f -> MENext (i, t_opt, f, v)) id
      | MOnce (i, f, inf1, inf2) -> map1 fvs f (fun f -> MOnce (i, f, inf1, inf2)) id
      | MEventually (i, f, inf1, inf2) -> map1 fvs f (fun f -> MEventually (i, f, inf1, inf2)) id
      | MEEventually (i, t_opt, f, v) -> map1 fvs f (fun f -> MEEventually (i, t_opt, f, v)) id
      | MHistorically (i, f, inf1, inf2) -> map1 fvs f (fun f -> MHistorically (i, f, inf1, inf2)) id
      | MAlways (i, f, inf1, inf2) -> map1 fvs f (fun f -> MAlways (i, f, inf1, inf2)) id
      | MEAlways (i, t_opt, f, inf) -> map1 fvs f (fun f -> MEAlways (i, t_opt, f, inf)) id
      | MSince (s, i, f, g, inf1, inf2) -> map2 fvs f g (fun f g -> MSince (s, i, f, g, inf1, inf2)) id2
      | MUntil (i, f, g, inf1, inf2) -> map2 fvs f g (fun f g -> MUntil (i, f, g, inf1, inf2)) id2
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
        | Predicate' (_, _, f) | Let' (_, _, _, f) -> aux f
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
        | Prev (i, f) -> MPrev (i, make (aux f) f.info.filter, true, ([], []))
        | Next (i, f) when Enftype.is_only_observable tf.info.enftype -> MNext (i, make (aux f) f.info.filter, true, [])
        | Next (i, f) -> MENext (i, None, make (aux f) f.info.filter, Etc.empty_valuation)
        | Once (i, f) -> MOnce (i, make (aux f) f.info.filter, [], Leaf (Once.init ()))
        | Eventually (i, f) when Enftype.is_only_observable tf.info.enftype ->
           MEventually (i, make (aux f) f.info.filter, ([], []), Leaf (Eventually.init ()))
        | Eventually (i, f) -> MEEventually (i, None, make (aux f) f.info.filter, Etc.empty_valuation)
        | Historically (i, f) -> MHistorically (i, make (aux f) f.info.filter, [], Leaf (Historically.init ()))
        | Always (i, f) when Enftype.is_only_observable tf.info.enftype ->
           MAlways (i, make (aux f) f.info.filter, ([], []), Leaf (Always.init ()))
        | Always (i, f) -> MEAlways (i, None, make (aux f) f.info.filter, Etc.empty_valuation)
        | Since (s, i, f, g) ->
           MSince (s, i, make (aux f) f.info.filter, make (aux g) g.info.filter, (([], []), []), Leaf (Since.init ()))
        | Until (_, i, f, g) when Enftype.is_only_observable tf.info.enftype ->
           MUntil (i, make (aux f) f.info.filter, make (aux g) g.info.filter, (([], []), []), Leaf (Until.init ()))
        | Until (s, i, f, g) ->
           MEUntil (s, i, None, make (aux f) f.info.filter, make (aux g) g.info.filter, Etc.empty_valuation)
        | Type (f, _) -> aux f
        | Let _ -> raise (Invalid_argument "Let bindings must be unrolled to initialize MFormula")
      in set_make (aux tf) tf.info.filter


    let equal mf1 mf2 = mf1.hash = mf2.hash

    let rec rank mf = match mf.mf with
      | MTT | MFF -> 0
      | MEqConst _ -> 0
      | MPredicate (r, _) -> Sig.rank_of_pred r
      | MNeg f
        | MExists (_, _, _, f)
        | MForall (_, _, _, f)
        | MPrev (_, f, _, _)
        | MNext (_, f, _, _)
        | MENext (_, _, f, _)
        | MOnce (_, f, _, _)
        | MEventually (_, f, _, _)
        | MEEventually (_, _, f, _)
        | MHistorically (_, f, _, _)
        | MAlways (_, f, _, _)
        | MEAlways (_, _, f, _)
        | MAgg (_, _, _, _, _, f)
        | MTop (_, _, _, _, _, f) -> rank f
      | MImp (_, f, g, _)
        | MIff (_, _, f, g, _)
        | MSince (_, _, f, g, _, _)
        | MUntil (_, f, g, _, _)
        | MEUntil (_, _, _, f, g, _) -> rank f + rank g
      | MAnd (_, fs, _)
        | MOr (_, fs, _) -> List.fold ~init:0 ~f:(+) (List.map fs ~f:rank)



    let rec apply_valuation (v: Etc.valuation) mf =
      let r = apply_valuation v in
      let av_term = Sig.eval in
      let av_buf2 b = Buf2.map (Pdt.specialize_partial v) (Pdt.specialize_partial v) b in
      let av_bufn b = Bufn.map (Pdt.specialize_partial v) b in
      let av_buft b = Buft.map (Pdt.specialize_partial v) (fun t -> t) b in
      let av_buf2t b = Buf2t.map (Pdt.specialize_partial v) (Pdt.specialize_partial v) (fun t -> t) b in
      let av_pdt p = Pdt.specialize_partial v p in
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
        | MIff (s, t, f, g, bi) -> MIff (s, t, r f, r g, av_buf2 bi)
        | MExists (x, tt, b, f) -> MExists (x, tt, b, r f)
        | MForall (x, tt, b, f) -> MForall (x, tt, b, r f)
        | MPrev (i, f, b, pi) -> MPrev (i, r f, b, av_buft pi)
        | MNext (i, f, b, si) -> MNext (i, r f, b, si)
        | MENext (i, ts, f, vv) -> MENext (i, ts, r f, Etc.extend_valuation v vv)
        | MOnce (i, f, ti, oi) -> MOnce (i, r f, ti, av_pdt oi)
        | MEventually (i, f, bi, oi) -> MEventually (i, r f, av_buft bi, av_pdt oi)
        | MEEventually (i, ts, f, vv) -> MEEventually (i, ts, r f, Etc.extend_valuation v vv)
        | MHistorically (i, f, ti, oi) -> MHistorically (i, r f, ti, av_pdt oi)
        | MAlways (i, f, bi, ai) -> MAlways (i, r f, av_buft bi, av_pdt ai)
        | MEAlways (i, ts, f, vv) -> MEAlways (i, ts, r f, Etc.extend_valuation v vv)
        | MSince (s, i, f, g, bi, si) -> MSince (s, i, r f, r g, av_buf2t bi, av_pdt si)
        | MUntil (i, f, g, bi, ui) -> MUntil (i, r f, r g, av_buf2t bi, av_pdt ui)
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
        | FInterval of Time.t * Interval.t * MFormula.t * int * Etc.valuation
        | FUntil of Time.t * Side.t * Interval.t * MFormula.t * MFormula.t * int * Etc.valuation
        | FAlways of Time.t * Interval.t * MFormula.t * int * Etc.valuation
        | FEventually of Time.t * Interval.t * MFormula.t * int * Etc.valuation

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
        | FFormula _ -> Proof.S (Proof.make_snextassm tp)
        | FInterval _ when equal_polarity pol POS -> Proof.S (Proof.make_snextassm tp)
        | FInterval (_, i, _, _, _) -> Proof.V (Proof.make_vnextassm tp i)
        | FUntil _ when equal_polarity pol POS -> Proof.S (Proof.make_stt tp)
        | FUntil _ -> Proof.V (Proof.make_vff tp)
        | FEventually _ when equal_polarity pol POS -> Proof.S (Proof.make_stt tp)
        | FEventually _ -> Proof.V (Proof.make_vff tp)
        | FAlways _ when equal_polarity pol POS -> Proof.S (Proof.make_stt tp)
        | FAlways _ -> Proof.V (Proof.make_vff tp)
      

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

  let do_neg = function
    | Proof.S sp -> Proof.V (Proof.make_vneg sp)
    | V vp -> S (Proof.make_sneg vp)

  let do_and (p1: Proof.t) (p2: Proof.t) : Proof.t list = match p1, p2 with
    | S sp1, S sp2 -> [S (Proof.make_sand sp1 sp2)]
    | S _ , V vp2 -> [V (Proof.make_vandr vp2)]
    | V vp1, S _ -> [V (Proof.make_vandl vp1)]
    | V vp1, V vp2 -> [(V (Proof.make_vandl vp1)); (V (Proof.make_vandr vp2))]

  let do_ands (ps: Proof.t list) : Proof.t list =
    let sps = List.map ~f:(function S sp1 -> Some sp1 | _ -> None) ps in
    match Option.all sps with
    | Some sps -> [Proof.S (List.fold_left (List.tl_exn sps) ~init:(List.hd_exn sps)
                              ~f:(fun l r -> Proof.make_sand l r))]
    | None -> let vps = List.filter_map ~f:(function V vp -> Some vp | _ -> None) ps in
              List.map ~f:(fun vp -> Proof.V (Proof.make_vandl vp)) vps

  let do_or (p1: Proof.t) (p2: Proof.t) : Proof.t list = match p1, p2 with
    | S sp1, S sp2 -> [(S (Proof.make_sorl sp1)); (S (Proof.make_sorr sp2))]
    | S sp1, V _ -> [S (Proof.make_sorl sp1)]
    | V _ , S sp2 -> [S (Proof.make_sorr sp2)]
    | V vp1, V vp2 -> [V (Proof.make_vor vp1 vp2)]

  let do_ors (ps: Proof.t list) : Proof.t list =
    let vps = List.map ~f:(function V vp1 -> Some vp1 | _ -> None) ps in
    match Option.all vps with
    | Some vps -> [Proof.V (List.fold_left (List.tl_exn vps) ~init:(List.hd_exn vps)
                              ~f:(fun l r -> Proof.make_vor l r))]
    | None -> let sps = List.filter_map ~f:(function S sp -> Some sp | _ -> None) ps in
              List.map ~f:(fun sp -> Proof.S (Proof.make_sorl sp)) sps


  let do_imp (p1: Proof.t) (p2: Proof.t) : Proof.t list = match p1, p2 with
    | S _, S sp2 -> [S (Proof.make_simpr sp2)]
    | S sp1, V vp2 -> [V (Proof.make_vimp sp1 vp2)]
    | V vp1, S sp2 -> [S (Proof.make_simpl vp1); S (Proof.make_simpr sp2)]
    | V vp1, V _ -> [S (Proof.make_simpl vp1)]

  let do_iff (p1: Proof.t) (p2: Proof.t) : Proof.t = match p1, p2 with
    | S sp1, S sp2 -> S (Proof.make_siffss sp1 sp2)
    | S sp1, V vp2 -> V (Proof.make_viffsv sp1 vp2)
    | V vp1, S sp2 -> V (Proof.make_viffvs vp1 sp2)
    | V vp1, V vp2 -> S (Proof.make_siffvv vp1 vp2)

  (*let do_exists_leaf x tc = function
    | Proof.S sp -> [Proof.S (Proof.make_sexists x (Dom.tt_default tc) sp)]
    | V vp -> [Proof.V (Proof.make_vexists x (Part.trivial vp))]*)

  (*let do_exists_node x tc part =
    if Part.exists part Proof.isS then
      (let sats = Part.filter part (fun p -> Proof.isS p) in
       (Part.values (Part.map2_dedup Proof.equal sats (fun (s, p) ->
                         match p with
                         | S sp -> (let witness = Setc.some_elt tc s in
                                    (Setc.Finite (Set.of_list (module Dom) [witness]),
                                     Proof.S (Proof.make_sexists x (Setc.some_elt tc s) sp)))
                         | V vp -> raise (Invalid_argument "found V proof in S list")))))
    else [V (Proof.make_vexists x (Part.map_dedup Proof.v_equal part Proof.unV))]*)

  (*let do_forall_leaf x tc = function
    | Proof.S sp -> [Proof.S (Proof.make_sforall x (Part.trivial sp))]
    | V vp -> [Proof.V (Proof.make_vforall x (Dom.tt_default tc) vp)]*)

  (*let do_forall_node x tc part =
    if Part.for_all part Proof.isS then
      [Proof.S (Proof.make_sforall x (Part.map part Proof.unS))]
    else
      (let vios = Part.filter part (fun p -> Proof.isV p) in
       (Part.values (Part.map2_dedup Proof.equal vios (fun (s, p) ->
                         match p with
                         | S _ -> raise (Invalid_argument "found S proof in V list")
                         | V vp -> (let witness = Setc.some_elt tc s in
                                    (Setc.Finite (Set.of_list (module Dom) [witness]),
                                     Proof.V (Proof.make_vforall x (Setc.some_elt tc s) vp)))))))*)

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
    | _, _ -> raise (Invalid_argument
                       (Printf.sprintf "Cannot match terms %s with domain elements %s"
                          (Term.list_to_string_core trms) (Dom.list_to_string ds)))
                        

  (*let print_maps maps =
    Stdio.print_endline "> Map:";
    List.iter maps ~f:(fun map -> Map.iteri map ~f:(fun ~key:k ~data:v ->
                                      Stdio.printf "%s -> %s\n" (Term.to_string k) (Dom.to_string v)))*)

  let proof_false tp = function
    | FObligation.POS -> Proof.V (Proof.make_vff tp)
    | NEG -> S (Proof.make_stt tp)

  let approx_false tp pol = Pdt.Leaf (proof_false tp pol)

  let approx_default expls tp pol =
    match List.last expls with
    | Some expl when E.at expl = tp -> expl
    | _ -> approx_false tp pol


  let approx_expl1 aexpl vars mf = match mf with
    | MNeg _ -> Pdt.apply1_reduce Proof.equal vars (fun p -> do_neg p) (Pdt.exquant aexpl)
    | _ -> raise (Invalid_argument ("function is not defined for " ^ MFormula.core_op_to_string mf))

  let approx_expl2 aexpl1 aexpl2 vars mf =
    match mf with
    | MAnd _ -> Pdt.apply2_reduce Proof.equal vars (fun p1 p2 -> minp_list (do_and p1 p2)) aexpl1 aexpl2
    | MOr _ -> Pdt.apply2_reduce Proof.equal vars (fun p1 p2 -> minp_list (do_or p1 p2)) aexpl1 aexpl2
    | MImp _ -> Pdt.apply2_reduce Proof.equal vars (fun p1 p2 -> minp_list (do_imp p1 p2)) (Pdt.exquant aexpl1) aexpl2
    | MIff _ -> Pdt.apply2_reduce Proof.equal vars (fun p1 p2 -> do_iff p1 p2) aexpl1 aexpl2
    | _ -> raise (Invalid_argument ("function is not defined for " ^ MFormula.core_op_to_string mf))

  
  let rec approx_ors vars tp pol = function
    | [] when FObligation.equal_polarity pol FObligation.POS -> Pdt.Leaf (Proof.V (Proof.make_vff tp))
    | [] -> Pdt.Leaf (Proof.S (Proof.make_stt tp))
    | [pdt] -> pdt
    | pdts -> Pdt.applyN_reduce Proof.equal vars (fun ps -> minp_list (do_ors ps)) pdts

  (*let rec approx_ands vars tp pol = function
    | [] when FObligation.equal_polarity pol FObligation.NEG -> Pdt.Leaf (Proof.V (Proof.make_vff tp))
    | [] -> Pdt.Leaf (Proof.S (Proof.make_stt tp))
    | [pdt] -> pdt
    | pdts -> Pdt.applyN_reduce Proof.equal vars (fun ps -> minp_list (do_ands ps)) pdts*)

  let approx_quant aexpl x mf =
    match mf with
    | MExists _ -> Pdt.quantify ~forall:false x aexpl
    | MForall _ -> Pdt.quantify ~forall:true x aexpl
    | _ -> raise (Invalid_argument ("function is not defined for " ^ MFormula.core_op_to_string mf))

  let relevant_fobligs fobligs test h vv pol =
    let f (k, _, pol') =
      let (h', v') = FObligation.hv k in
      h = h' && Etc.equal_valuation v' vv && FObligation.equal_polarity pol pol' && test k
    in Set.elements (Set.filter fobligs ~f)

  let expls_approx test tp pol vars fobligs h vv =
    let f (k, v, _) =  
      let p = FObligation.corresp_proof tp pol None k in
      let p' = proof_false tp pol in
      Pdt.from_valuation vars v p p' in
    List.map (relevant_fobligs fobligs test h vv pol) ~f

  let approx_next vars (fobligs: FObligations.t) _ (h, vv) _ tp pol = (*TODO*)
    let expls = expls_approx FObligation.is_finterval tp pol vars fobligs h vv in
    (*let relevant_fobligs =
      Set.elements (Set.filter fobligs ~f:(fun (k, _, pol') ->
      match k with
      | FInterval (_, _, _, h', v') ->
      h = h' && Etc.equal_valuation v' vv && FObligation.polarity_equal pol pol'
      | _ -> false)) in*)
    approx_ors vars tp pol expls

  let approx_once vars expls aexpl i tp pol =
    match List.last expls, pol with
    | Some expl, _ when E.at expl = tp -> expl
    | _, FObligation.POS ->
       Pdt.apply1_reduce Proof.equal vars (Once.do_once_base tp (Interval.left i)) aexpl
    | _, _ -> approx_false tp pol

  let approx_historically vars expls aexpl i tp pol =
    match List.last expls, pol with
    | Some expl, _ when E.at expl = tp -> expl
    | _, FObligation.NEG ->
       Pdt.apply1_reduce Proof.equal vars (Historically.do_historically_base tp (Interval.left i)) aexpl
    | _, _ -> approx_false tp pol

  let approx_eventually vars aexpl (fobligs: FObligations.t) i h_opt tp pol = (*TODO*)
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
          expls_approx FObligation.is_feventually tp pol vars fobligs h vv
        end in
    let aexpl_next = approx_ors vars tp pol expls in
    (*print_endline ("approx_eventually aexpl_new=" ^ Expl.to_string aexpl_new);
    print_endline ("approx_eventually aexpl_next=" ^ Expl.to_string aexpl_next);
    print_endline ("approx_eventually pol=" ^ FObligation.polarity_to_string pol);
    print_endline ("approx_eventually i=" ^ Interval.to_string i);*)
    Pdt.apply2_reduce Proof.equal vars
      (fun p1 p2 -> Eventually.do_eventually_base tp i (FObligation.equal_polarity pol POS) p1 p2)
      aexpl_next aexpl_new

  let approx_always vars aexpl (fobligs: FObligations.t) i h_opt tp pol = (*TODO*)
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
          expls_approx FObligation.is_falways tp pol vars fobligs h vv
        end in
    let aexpl_next = approx_ors vars tp pol expls in
    Pdt.apply2_reduce Proof.equal vars
      (fun p1 p2 -> Always.do_always_base tp i (FObligation.equal_polarity pol POS) p1 p2)
      aexpl_next aexpl_new 

  let approx_since vars expls aexpl1 aexpl2 i tp pol =
    match List.last expls, pol with
    | Some expl, _ when E.at expl = tp -> expl
    | _ -> Pdt.apply2_reduce Proof.equal vars
             (Since.do_since_base tp (Interval.left i) (FObligation.equal_polarity pol FObligation.POS)) aexpl1 aexpl2

  let approx_until vars aexpl1 aexpl2 (fobligs: FObligations.t) i h_opt tp pol = (*TODO*)
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
          expls_approx FObligation.is_funtil tp pol vars fobligs h vv
        end in
    let aexpl_next = approx_ors vars tp pol expls in
    (*print_endline ("approx_until aexpl_new1=" ^ Expl.to_string aexpl_new1);
    print_endline ("approx_until aexpl_new2=" ^ Expl.to_string aexpl_new2);
    print_endline ("approx_until aexpl_next=" ^ Expl.to_string aexpl_next);
    print_endline ("approx_until pol=" ^ FObligation.polarity_to_string pol);
    print_endline ("approx_until i=" ^ Interval.to_string i);
    print_endline ( CI.Expl.to_string (   Pdt.apply3_reduce Proof.equal vars
      (fun p1 p2 p3 -> Until.do_until_base tp i (pol == POS) p1 p2 p3)
      aexpl_new1 aexpl_new2 aexpl_next));*)
    Pdt.apply3_reduce Proof.equal vars
      (fun p1 p2 p3 -> Until.do_until_base tp i (FObligation.equal_polarity pol POS) p1 p2 p3)
      aexpl_new1 aexpl_new2 aexpl_next

  let else_any f tp = function
    | Some pol -> f tp pol
    | None -> Pdt.Leaf (Proof.S (Proof.make_stt tp))

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

  let meval (ts: timestamp) tp (db: Db.t) ~pol (fobligs: FObligations.t) mformula memo =
    let outer_tp = tp in
    let rec meval_rec (ts: timestamp) tp (db: Db.t) ~pol (fobligs: FObligations.t) memo mformula =
      (*print_endline "--meval_rec";*)
      (*print_endline ("mf=" ^ MFormula.to_string mformula);*)
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
           | MTT -> let expl = Pdt.Leaf (Proof.S (Proof.make_stt tp)) in
                    memo, ([expl], expl, MTT)
           | MFF -> let expl = Pdt.Leaf (Proof.V (Proof.make_vff tp)) in
                    memo, ([expl], expl, MFF)
           | MEqConst (trm, d) ->
              let l1 = Pdt.Leaf (Proof.S (Proof.make_seqconst tp trm d)) in
              let l2 = Pdt.Leaf (Proof.V (Proof.make_veqconst tp trm d)) in
              let expl = Pdt.Node (Lbl.of_term trm,
                                   [(Setc.Complement (Set.of_list (module Dom) [d]), l2);
                                    (Setc.Finite (Set.of_list (module Dom) [d]), l1)]) in
              memo, ([expl], expl, MEqConst (trm, d))
           | MPredicate (r, trms) when not (Enftype.is_observable (Sig.enftype_of_pred r)) ->
              (*print_endline ("not observable: " ^ r);*)
              let expl = Pdt.Leaf (if FObligation.equal_polarity FObligation.POS
                                        (Option.value pol ~default:FObligation.POS) then
                                     (Proof.V (Proof.make_vff tp))
                                   else
                                     (Proof.S (Proof.make_stt tp))) in
              memo, ([expl], expl, MPredicate (r, trms))
           | MPredicate (r, trms) ->
              let db' = match Sig.kind_of_pred r with
                | Trace -> Db.filter db ~f:(fun evt -> String.equal r (fst(evt)))
                | External -> Db.retrieve_external r
                | Builtin -> Db.retrieve_builtin ts tp r
                | Predicate -> raise (Invalid_argument "cannot evaluate Predicate")
                | Let -> raise (Invalid_argument "cannot evaluate Let")in
              if List.is_empty trms then
                (let expl = if Db.is_empty db'
                            then Pdt.Leaf (Proof.V (Proof.make_vpred tp r trms))
                            else Leaf (S (Proof.make_spred tp r trms)) in
                 memo, ([expl], expl, MPredicate (r, trms)))
              else
                let maps = List.filter_opt (
                               Set.fold (Db.events db') ~init:[]
                                 ~f:(fun acc evt -> match_terms (List.map ~f:(fun x -> x.trm) trms) (snd evt)
                                                      (Map.empty (module Lbl)) :: acc)) in
                let expl = if List.is_empty maps
                           then Pdt.Leaf (Proof.V (Proof.make_vpred tp r trms))
                           else E.pdt_of tp r trms mformula.lbls maps in
                (*print_endline "--MPredicate";
                print_endline r;*)
                (*  print_endline ("maps=" ^ (String.concat ~sep:"; " (List.map maps ~f:(fun map -> String.concat ~sep:", " (List.map (Map.to_alist map) ~f:(fun (lbl, d) -> Lbl.to_string lbl ^ " -> " ^ Dom.to_string d))))));
                  print_endline ("lbls=" ^ (String.concat ~sep:", " (List.map lbls ~f:Lbl.to_string)));*)
                (*print_endline ("expl=" ^ E.to_string expl);*)
                memo, ([expl], expl, MPredicate (r, trms))
           | MAgg (s, op, op_fun, x, y, mf) ->
              let memo, (expls, aexpl, mf') = meval_rec ts tp db fobligs ~pol memo mf in
              (*print_endline ("--MAgg.aexpl=" ^ E.to_string aexpl);
              print_endline ("mf=" ^ MFormula.to_string mformula);
              print_endline ("aexpl=" ^ Expl.to_string aexpl);*)
              (*print_endline ("lbls="  ^ String.concat ~sep:", " (List.map ~f:Lbl.to_string mformula.lbls));
              print_endline ("lbls'=" ^ String.concat ~sep:", " (List.map ~f:Lbl.to_string mf.lbls));*)
              let aggregate = E.aggregate op_fun s tp x y mformula.lbls mf.lbls in
              (*print_endline ("MAgg.aexpl=" ^ E.to_string aexpl);*)
              (*print_endline ("MAgg.mformula=" ^ MFormula.to_string mformula);*)
              let f_expls = List.map expls ~f:aggregate in
              let f_aexpl = aggregate aexpl in
              (*print_endline ("--MAgg.f_aexpl=" ^ E.to_string f_aexpl);*)
              memo, (f_expls, f_aexpl, MAgg (s, op, op_fun, x, y, mf'))
           | MTop (s, op, op_fun, x, y, mf) ->
              let memo, (expls, aexpl, mf') = meval_rec ts tp db fobligs ~pol memo mf in
              (*print_endline ("--MAgg.aexpl=" ^ E.to_string aexpl);
              print_endline ("mf=" ^ MFormula.to_string mformula);
              print_endline ("aexpl=" ^ Expl.to_string aexpl);*)
              (*print_endline ("lbls="  ^ String.concat ~sep:", " (List.map ~f:Lbl.to_string mformula.lbls));
              print_endline ("lbls'=" ^ String.concat ~sep:", " (List.map ~f:Lbl.to_string mf.lbls));*)
              let aggregate = E.table_operator op_fun s tp x y mformula.lbls mf.lbls in
              (*print_endline ("MAgg.aexpl=" ^ E.to_string aexpl);*)
              (*print_endline ("MAgg.mformula=" ^ MFormula.to_string mformula);*)
              let f_expls = List.map expls ~f:aggregate in
              let f_aexpl = aggregate aexpl in
              (*print_endline ("--MTop.f_aexpl=" ^ E.to_string f_aexpl);*)
              memo, (f_expls, f_aexpl, MTop (s, op, op_fun, x, y, mf'))
           | MNeg (mf) ->
              let memo, (expls, aexpl, mf') = meval_rec ts tp db fobligs ~pol:(pol >>| FObligation.neg) memo mf in
              (*print_endline ("--MNeg");
              print_endline ("--mformula=" ^ MFormula.to_string mformula);
              print_endline ("--aexpl=" ^ E.to_string aexpl);*)
              let f_neg pdt = Pdt.apply1_reduce Proof.equal mformula.lbls
                                (fun p -> do_neg p) (Pdt.exquant pdt) in
              let f_expls = List.map expls ~f:f_neg in
              let f_aexpl = approx_expl1 aexpl mformula.lbls mformula.mf in
              memo, (f_expls, f_aexpl, MNeg mf')
           | MAnd (s, mfs, buf2) ->
              let memo, data =
                List.fold_map ~init:memo ~f:(meval_rec ts tp db ~pol fobligs) mfs in
              let expls_list, aexpl_list, mfs' = List.unzip3 data in
              let apply_ands = Pdt.applyN_reduce Proof.equal mformula.lbls (fun ps -> minp_list (do_ands ps)) in
              let (f_expls, buf2') = Bufn.take apply_ands (Bufn.add expls_list buf2) in
              let aexpl = apply_ands aexpl_list in
              memo, (f_expls, aexpl, MAnd (s, mfs', buf2'))
           | MOr (s, mfs, buf2) ->
              let memo, data =
                List.fold_map ~init:memo ~f:(meval_rec ts tp db ~pol fobligs) mfs in
              let expls_list, aexpl_list, mfs' = List.unzip3 data in
              let apply_ors = Pdt.applyN_reduce Proof.equal mformula.lbls (fun ps -> minp_list (do_ors ps)) in
              let (f_expls, buf2') = Bufn.take apply_ors (Bufn.add expls_list buf2) in
              let aexpl = apply_ors aexpl_list in
              memo, (f_expls, aexpl, MOr (s, mfs', buf2'))
           | MImp (s, mf1, mf2, buf2) ->
              let memo, (expls1, aexpl1, mf1') = meval_rec ts tp db ~pol:(pol >>| FObligation.neg) fobligs memo mf1 in
              let memo, (expls2, aexpl2, mf2') = meval_rec ts tp db ~pol fobligs memo mf2 in
              let f_imp pdt1 pdt2 =
                Pdt.apply2_reduce Proof.equal mformula.lbls
                  (fun p1 p2 -> minp_list (do_imp p1 p2)) (Pdt.exquant pdt1) pdt2 in
              (*print_endline "--MImp";*)
              (*print_endline ("mformula=" ^ MFormula.to_string mformula);*)
              (*print_endline ("aexpl1=" ^ E.to_string aexpl1);
              print_endline ("aexpl2=" ^ E.to_string aexpl2);*)
              (*print_endline ("lbls=" ^ Lbl.to_string_list mformula.lbls);*)
              let (f_expls, buf2') = Buf2.take f_imp (Buf2.add expls1 expls2 buf2) in
              let aexpl = approx_expl2 aexpl1 aexpl2 mformula.lbls mformula.mf in
              (*print_endline ("aexpl=" ^ E.to_string aexpl);*)
              memo, (f_expls, aexpl, MImp (s, mf1', mf2', buf2'))
           | MIff (s, t, mf1, mf2, buf2) ->
              let memo, (expls1, _, mf1') = meval_rec ts tp db ~pol fobligs memo mf1 in
              let memo, (expls2, _, mf2') = meval_rec ts tp db ~pol fobligs memo mf2 in
              let f = Pdt.apply2_reduce Proof.equal mformula.lbls (fun p1 p2 -> do_iff p1 p2) in
              let (f_expls, buf2') = Buf2.take f (Buf2.add expls1 expls2 buf2) in
              let aexpl = else_any (approx_default f_expls) tp pol in
              memo, (f_expls, aexpl, MIff (s, t, mf1', mf2', buf2'))
           | MExists (x, tc, b, mf) ->
              (*print_endline "--MExists";
                print_endline ("x =" ^ x);
                print_endline ("lbls =" ^ (Lbl.to_string_list lbls));
                print_endline ("lbls'=" ^ (Lbl.to_string_list lbls'));*)
              let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
              let quant expl = approx_quant expl x mformula.mf in
              let expls = List.map expls ~f:quant in
              (*print_endline ("aexpl (before) = " ^ Expl.to_string aexpl);*)
              let aexpl = quant aexpl in
              (*print_endline ("aexpl (after) = " ^ E.to_string aexpl);*)
              memo, (expls, aexpl, MExists(x, tc, b, mf'))
           | MForall (x, tc, b, mf) ->
              (*print_endline "--MForall";
                print_endline ("x =" ^ x);*)
                (*print_endline ("lbls =" ^ (Lbl.to_string_list lbls));
                print_endline ("lbls'=" ^ (Lbl.to_string_list lbls'));*)
              let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
              let quant expl = approx_quant expl x mformula.mf in
              let expls = List.map expls ~f:quant in
              (*print_endline ("aexpl (before) = " ^ Expl.to_string aexpl);*)
              let aexpl = quant aexpl in
              (*print_endline ("aexpl (after) = " ^ Expl.to_string aexpl);*)
              memo, (expls, aexpl, MForall(x, tc, b, mf'))
           | MPrev (i, mf, first, (buf, tss)) ->
              let memo, (expls, _, mf') = meval_rec ts tp db ~pol fobligs memo mf in
              let (f_expls, (buf', tss')) =
                Buft.another_take
                  (fun expl ts ts' -> Pdt.apply1_reduce Proof.equal mformula.lbls
                                        (fun p -> Prev_Next.update_eval Prev i p ts ts') expl)
                  (buf @ expls, tss @ [ts]) in
              let aexpl = else_any (approx_default f_expls) tp pol in
              memo, ((if first then (Leaf (V Proof.make_vprev0) :: f_expls) else f_expls), aexpl, MPrev (i, mf', false, (buf', tss')))
           | MNext (i, mf, first, tss) ->
              let memo, (expls, _, mf') = meval_rec ts tp db ~pol fobligs memo mf in
              let (expls', first) = if first && (List.length expls) > 0 then (List.tl_exn expls, false)
                                    else (expls, first) in
              let (f_expls, (_, tss')) =
                Buft.another_take
                  (fun expl ts ts' -> Pdt.apply1_reduce Proof.equal mformula.lbls
                                        (fun p -> Prev_Next.update_eval Next i p ts ts') expl)
                  (expls', tss @ [ts]) in
              memo, (f_expls, else_any approx_false tp pol, MNext (i, mf', first, tss'))
           | MENext (i, f_ts, mf, v) ->
              let memo, (_, _, mf') = meval_rec ts tp db ~pol fobligs memo mf in
              let aexpl = else_any (approx_next mformula.lbls fobligs i (mformula.hash, v) mformula) tp pol in
              memo, ([aexpl], aexpl, MENext (i, f_ts, mf', v))
           | MOnce (i, mf, tstps, moaux_pdt) ->
              let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
              let ((moaux_pdt', expls'), _, tstps') =
                Buft.take
                  (fun expl ts tp (aux_pdt, es) ->
                    let (aux_pdt', es') =
                      Pdt.split_prod (Pdt.apply2 mformula.lbls (fun p aux -> (* Stdio.printf "%s\n" (Once.to_string aux); *)
                                          Once.update i ts tp p aux) expl aux_pdt) in
                    (aux_pdt', es @ (Pdt.split_list es')))
                  (moaux_pdt, []) (expls, (tstps @ [(ts,tp)])) in
              let expls'' = List.map expls' ~f:(Pdt.reduce Proof.equal) in
              let aexpl = else_any (approx_once mformula.lbls expls'' aexpl i) tp pol in
              memo, (expls'', aexpl, MOnce (i, mf', tstps', moaux_pdt'))
           | MEventually (i, mf, (buf, ntstps), meaux_pdt) ->
              let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
              let (meaux_pdt', buf', ntstps') =
                Buft.take
                  (fun expl ts tp aux_pdt -> Pdt.apply2 mformula.lbls (fun p aux -> Eventually.update i ts tp p aux) expl aux_pdt)
                  meaux_pdt (buf @ expls, (ntstps @ [(ts,tp)])) in
              let (nts, ntp) = match ntstps' with
                | [] -> (ts, tp)
                | (nts', ntp') :: _ -> (nts', ntp') in
              let (meaux_pdt', es') =
                Pdt.split_prod (Pdt.apply1 mformula.lbls (fun aux -> Eventually.eval i nts ntp (aux, [])) meaux_pdt') in
              let expls' = Pdt.split_list es' in
              let expls'' = List.map expls' ~f:(Pdt.reduce Proof.equal) in
              (*print_endline ("MEventually aexpl(before)=" ^ Expl.to_string aexpl);*)
              let aexpl = else_any (approx_eventually mformula.lbls aexpl fobligs i None) tp pol in
              (*print_endline ("MEventually aexpl(after)=" ^ Expl.to_string aexpl);*)
              memo, (expls'', aexpl, MEventually (i, mf', (buf', ntstps'), meaux_pdt'))
           | MEEventually (i, f_ts, mf, v) ->
              let memo, (_, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
              let aexpl = else_any (approx_eventually mformula.lbls aexpl fobligs i (Some (mformula.hash, v))) tp pol in
              memo, ([aexpl], aexpl, MEEventually (i, f_ts, mf', v))
           | MHistorically (i, mf, tstps, mhaux_pdt) ->
              let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
              let ((mhaux_pdt', expls'), _, tstps') =
                Buft.take
                  (fun expl ts tp (aux_pdt, es) ->
                    let (aux_pdt', es') =
                      Pdt.split_prod (Pdt.apply2 mformula.lbls
                                        (fun p aux -> Historically.update i ts tp p aux) expl aux_pdt) in
                    (aux_pdt', es @ (Pdt.split_list es')))
                  (mhaux_pdt, []) (expls, (tstps @ [(ts,tp)])) in
              let expls'' = List.map expls' ~f:(Pdt.reduce Proof.equal) in
              let aexpl = else_any (approx_historically mformula.lbls expls'' aexpl i) tp pol in
              memo, (expls'', aexpl, MHistorically (i, mf', tstps', mhaux_pdt'))
           | MAlways (i, mf, (buf, ntstps), maaux_pdt) ->
              let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
              let (maaux_pdt', buf', ntstps') =
                Buft.take
                  (fun expl ts tp aux_pdt -> Pdt.apply2 mformula.lbls (fun p aux -> Always.update i ts tp p aux) expl aux_pdt)
                  maaux_pdt (buf @ expls, (ntstps @ [(ts,tp)])) in
              let (nts, ntp) = match ntstps' with
                | [] -> (ts, tp)
                | (nts', ntp') :: _ -> (nts', ntp') in
              let (maaux_pdt', es') =
                Pdt.split_prod (Pdt.apply1 mformula.lbls (fun aux -> Always.eval i nts ntp (aux, [])) maaux_pdt') in
              let expls' = Pdt.split_list es' in
              let expls'' = List.map expls' ~f:(Pdt.reduce Proof.equal) in
              let aexpl = else_any (approx_always mformula.lbls aexpl fobligs i None) tp pol in
              memo, (expls'', aexpl, MAlways (i, mf', (buf', ntstps'), maaux_pdt'))
           | MEAlways (i, f_ts, mf, v) ->
              let memo, (_, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
              (*print_endline "--MEAlways";
              print_endline ("lbls = " ^ (Lbl.to_string_list mformula.lbls));
              print_endline ("aexpl = " ^ E.to_string aexpl);*)
              let aexpl = else_any (approx_always mformula.lbls aexpl fobligs i (Some (mformula.hash, v))) tp pol in
              memo, ([aexpl], aexpl, MEAlways (i, f_ts, mf', v))
           | MSince (s, i, mf1, mf2, (buf2, tstps), msaux_pdt) ->
              let memo, (expls1, aexpl1, mf1') = meval_rec ts tp db ~pol fobligs memo mf1 in
              let memo, (expls2, aexpl2, mf2') = meval_rec ts tp db ~pol fobligs memo mf2 in
              let ((msaux_pdt', expls'), (buf2', tstps')) =
                Buf2t.take
                  (fun expl1 expl2 ts tp (aux_pdt, es) ->
                    let (aux_pdt', es') =
                      Pdt.split_prod (Pdt.apply3 mformula.lbls
                                        (fun p1 p2 aux ->
                                          Since.update i ts tp p1 p2 aux) expl1 expl2 aux_pdt) in
                    (aux_pdt', es @ (Pdt.split_list es')))
                  (msaux_pdt, []) (Buf2.add expls1 expls2 buf2) (tstps @ [(ts,tp)]) in
              let expls'' = List.map expls' ~f:(Pdt.reduce Proof.equal) in
              let aexpl = else_any (approx_since mformula.lbls expls'' aexpl1 aexpl2 i) tp pol in
              (*print_endline "--MSince";
                print_endline ("aexpl1=" ^ Expl.to_string aexpl1);
                print_endline ("aexpl2=" ^ Expl.to_string aexpl2);
                print_endline ("aexpl=" ^ Expl.to_string aexpl);*)
              memo, (expls'', aexpl, MSince (s, i, mf1', mf2', (buf2', tstps'), msaux_pdt'))
           | MUntil (i, mf1, mf2, (buf2, ntstps), muaux_pdt) ->
              let memo, (expls1, aexpl1, mf1') = meval_rec ts tp db ~pol fobligs memo mf1 in
              let memo, (expls2, aexpl2, mf2') = meval_rec ts tp db ~pol fobligs memo mf2 in
              let (muaux_pdt', (buf2', ntstps')) =
                Buf2t.take
                  (fun expl1 expl2 ts tp aux_pdt ->
                    Pdt.apply3 mformula.lbls (fun p1 p2 aux -> Until.update i ts tp p1 p2 aux) expl1 expl2 aux_pdt)
                  muaux_pdt (Buf2.add expls1 expls2 buf2) (ntstps @ [(ts,tp)]) in
              let (nts, ntp) = match ntstps' with
                | [] -> (ts, tp)
                | (nts', ntp') :: _ -> (nts', ntp') in
              let (muaux_pdt', es') =
                Pdt.split_prod (Pdt.apply1 mformula.lbls (fun aux -> Until.eval i nts ntp (aux, [])) muaux_pdt') in
              let expls' = Pdt.split_list es' in
              let expls'' = List.map expls' ~f:(Pdt.reduce Proof.equal) in
              let aexpl = else_any (approx_until mformula.lbls aexpl1 aexpl2 fobligs i None) tp pol in
              memo, (expls'', aexpl, MUntil (i, mf1', mf2', (buf2', ntstps'), muaux_pdt'))
           | MEUntil (s, i, f_ts, mf1, mf2, v) ->
              let memo, (_, aexpl1, mf1') = meval_rec ts tp db ~pol fobligs memo mf1 in
              let memo, (_, aexpl2, mf2') = meval_rec ts tp db ~pol fobligs memo mf2 in
              let aexpl = else_any (approx_until mformula.lbls aexpl1 aexpl2 fobligs i (Some (mformula.hash, v))) tp pol in
              memo, ([aexpl], aexpl, MEUntil (s, i, f_ts, mf1', mf2', v))
         in let mf = { mformula with mf } in
            (*print_endline ("add memo: " ^ " (" ^ MFormula.to_string mf ^ ", " ^ Int.to_string tp ^ ", " ^ Int.to_string mformula.hash ^ ") -> " ^ E.to_string aexpl);*)
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

  type res = E.t list * E.t * MFormula.t
  
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

end
