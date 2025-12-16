open Base
open Expl
open Option

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm

open Etc
open Mformula

let debug s =
  if !Global.debug then Stdio.printf "[debug:monitor] %s\n%!" s

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

let rec match_terms trms ds map =
  (*print_endline ("trms=" ^ Term.list_to_string trms);
    print_endline ("ds=" ^ String.concat ~sep:", " (List.map ~f:Dom.to_string ds));*)
  match trms, ds with
  | [], [] -> Some(map)
  | ITerm.Const c :: trms, d :: ds ->
    if Dom.equal c d then match_terms trms ds map else None
  | ITerm.Var x :: trms, d :: ds ->
     (match match_terms trms ds map with
      | None -> None
      | Some map' ->
         (match Map.find map' x with
          | None -> let map'' = Map.add_exn map' ~key:x ~data:d in Some map''
          | Some z -> (if Dom.equal d z then Some map' else None)))
  | _, _ -> raise (Errors.MonitoringError
                     (Printf.sprintf "Cannot match terms %s with domain elements %s"
                        (ITerm.list_to_string_core trms) (Dom.list_to_string ds)))

(*let print_maps maps =
  Stdio.print_endline "> Map:";
  List.iter maps ~f:(fun map -> Map.iteri map ~f:(fun ~key:k ~data:v ->
  Stdio.printf "%s -> %s\n" (Term.to_string k) (Dom.to_string v)))*)


(*let memo = Hashtbl.create (module Formula)*)

module Memo = struct

  type 'a t = { map: (int, 'a, Int.comparator_witness) Map.t;
                ex_events: (string, String.comparator_witness) Set.t;
                ex_obligations: (int, Int.comparator_witness) Set.t }

  let find memo (mf: IFormula.t) pol =
    if !Global.memo then
      begin
        let hash = mf.hash * 65599 + (Polarity.to_int pol) in
        match Map.find memo.map hash, mf.events, mf.obligations with
        | None, _, _
        | _, None, _
        | _, _, None -> None
        | Some _, Some mf_events, _ when Set.exists ~f:(Map.mem mf_events) memo.ex_events ->
          None
        | Some _, _, Some mf_obligations when not (Set.are_disjoint mf_obligations memo.ex_obligations) ->
          None
        | Some res, _, _ ->
          debug (Printf.sprintf "Memo.find: %d" hash);
          Some res
      end
    else None

  let add_event memo e = { memo with ex_events = Set.add memo.ex_events e }
  let add_obligation memo h = { memo with ex_obligations = Set.add memo.ex_obligations h }
  let empty = { map = Map.empty (module Int);
                ex_events = Set.empty (module String);
                ex_obligations = Set.empty (module Int) }
  
  let memoize memo (mf: IFormula.t) pol res =
    if !Global.memo then
      let hash = mf.hash * 65599 + (Polarity.to_int pol) in
      debug (Printf.sprintf "Memo.memoize: %d" hash);
      { memo with map = Map.update memo.map hash ~f:(fun _ -> res) }
    else memo

  let to_string (memo : 'a t) =
    Printf.sprintf "memo(map.keys = {%s};\n     ex_events = {%s};\n     ex_obligations = {%s})"
      (String.concat ~sep:", " (List.map (Map.keys memo.map) ~f:Int.to_string))
      (String.concat ~sep:", " (Set.elements memo.ex_events))
      (String.concat ~sep:", " (List.map ~f:Int.to_string (Set.elements memo.ex_obligations)))
  
end

let monitor_steps = ref 0
    
let meval (ts: timestamp) tp (db: Db.t) ~pol (fobligs: FObligations.t) (m: (string * IFormula.t) list) (mformula: IFormula.t) memo =
  let outer_tp = tp in
  let map_expl f (tp, (ts, x)) = (tp, x) in
  let one_ts tp ts expl = [TS.make tp ts expl] in
  let p (mf: IFormula.t) = Array.get mf.projs in
  let rec meval_rec (ts: timestamp) tp (db: Db.t) ~pol (fobligs: FObligations.t) memo (mformula: IFormula.t) :
    'a *  (Expl.t TS.t list * Expl.t * IFormula.t) =
    debug (Printf.sprintf "meval_rec (%s, %d, %s, %s)..." (Time.to_string ts) tp (IFormula.value_to_string mformula) (Polarity.to_string (Polarity.value pol)));
    incr monitor_steps;
    (*debug (Printf.sprintf "memo = %s" (Memo.to_string memo));*)
    match Memo.find memo mformula (Polarity.value pol) with
    | Some (expls, aexpl, mf) ->
      (memo, (expls, aexpl, { mf with lbls = mformula.lbls; projs = mformula.projs }))
    | None -> 
       let memo, (expls, aexpl, mf) =
         match mformula.mf with
         | MTT -> let expl = Pdt.Leaf true in
                  memo, (one_ts tp ts expl, expl, IFormula.MTT)
         | MFF -> let expl = Pdt.Leaf false in
                  memo, (one_ts tp ts expl, expl, MFF)
         | MEqConst (trm, d) ->
           let expl = Pdt.Node
               (ITerm.unvar trm,
                [(Setc.Complement (Set.of_list (module Dom) [d]), Pdt.Leaf false);
                 (Setc.Finite (Set.of_list (module Dom) [d]), Pdt.Leaf true)]) in
           memo, (one_ts tp ts expl, expl, MEqConst (trm, d))
         | MPredicate (r, trms) when Sig.mem r && not (Enftype.is_observable (Sig.enftype_of_pred r)) ->
            let expl = Pdt.Leaf (not (Polarity.equal Polarity.POS
                                      (Polarity.value pol))) in
            memo, (one_ts tp ts expl, expl, MPredicate (r, trms))
         | MPredicate (r, trms) ->
           begin
             match List.find m (fun (e, _) -> String.equal r e) with
             | None ->
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
                              (Map.empty (module Int)) :: acc)) in
                 let expl = if List.is_empty maps
                   then Pdt.Leaf false
                   else Expl.pdt_of tp r (Array.to_list mformula.lbls) maps in
                 memo, (one_ts tp ts expl, expl, MPredicate (r, trms))
             | Some (_, mf) ->
               let memo, (expls, aexpl, mf') = meval_rec ts tp db fobligs ~pol memo mf in
               memo, (expls, aexpl, MPredicate (r, trms))
           end
         | MAgg (s, op, op_fun, x, y, mf) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db fobligs ~pol memo mf in
            let aggregate = Expl.aggregate op_fun s (p mf) tp x (ITerm.to_vars mf.lbls y) mformula.lbls mf.lbls in
            let f_expls = List.map expls ~f:(TS.map aggregate) in
            let f_aexpl = aggregate aexpl in
            memo, (f_expls, f_aexpl, MAgg (s, op, op_fun, x, y, mf'))
         | MTop (s, op, op_fun, x, y, mf) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db fobligs ~pol memo mf in
            let aggregate = Expl.table_operator op_fun s (p mf) tp x (ITerm.to_vars mf.lbls y) mformula.lbls mf.lbls in
            let f_expls = List.map expls ~f:(TS.map aggregate) in
            let f_aexpl = aggregate aexpl in
            memo, (f_expls, f_aexpl, MTop (s, op, op_fun, x, y, mf'))
         | MNeg (mf) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db fobligs ~pol:(pol >>| Polarity.neg) memo mf in
            let expls = update_neg expls in
            let aexpl = approximate_neg aexpl in
            memo, (expls, aexpl, MNeg mf')
         | MAnd (s, b, mfs, bufn) -> 
            let memo, data = List.fold_map ~init:memo ~f:(meval_rec ts tp db ~pol fobligs) mfs in
            let expls_list, aexpl_list, mfs' = List.unzip3 data in
            let (f_expls, bufn) = update_and (List.map mfs ~f:p) expls_list bufn in
            let aexpl = approximate_and (List.map mfs ~f:p) aexpl_list in
            memo, (f_expls, aexpl, MAnd (s, b, mfs', bufn))
         | MOr (s, b, mfs, bufn) ->
            let memo, data = List.fold_map ~init:memo ~f:(meval_rec ts tp db ~pol fobligs) mfs in
            let expls_list, aexpl_list, mfs' = List.unzip3 data in
            let (f_expls, bufn) = update_or (List.map mfs ~f:p) expls_list bufn in
            let aexpl = approximate_or (List.map mfs ~f:p) aexpl_list in
            memo, (f_expls, aexpl, MOr (s, b, mfs', bufn))
         | MImp (s, b, mf1, mf2, buf2) ->
            let memo, (expls1, aexpl1, mf1') = meval_rec ts tp db ~pol:(pol >>| Polarity.neg) fobligs memo mf1 in
            let memo, (expls2, aexpl2, mf2') = meval_rec ts tp db ~pol fobligs memo mf2 in
            let (f_expls, buf2) = update_imp (p mf1) (p mf2) expls1 expls2 buf2 in
            let aexpl = approximate_imp (p mf1) (p mf2) aexpl1 aexpl2 in
            memo, (f_expls, aexpl, MImp (s, b, mf1', mf2', buf2))
         | MExists (x, tc, b, b', mf) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            memo, (expls, aexpl, MExists (x, tc, b, b', mf'))
         | MForall (x, tc, b, b', mf) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            memo, (expls, aexpl, MForall (x, tc, b, b', mf'))
         | MPrev (i, mf, aux) -> 
            let memo, (expls, _, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = Prev.add expls aux in 
            let aux, f_expls = Prev.update aux in
            let aexpl = Prev.approximate tp f_expls pol in
            memo, (f_expls, aexpl, MPrev (i, mf', aux))
         | MNext (i, mf, aux) ->
            let memo, (expls, _, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = Next.add expls aux in
            let aux, f_expls = Next.update aux in
            let aexpl = Next.approximate pol in
            memo, (f_expls, aexpl, MNext (i, mf', aux))
         | MENext (i, f_ts, mf, v) ->
            let memo, (_, _, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aexpl = approximate_enext mformula.lbls fobligs (mformula.hash, v) tp pol in
            memo, (one_ts tp ts aexpl, aexpl, MENext (i, f_ts, mf', v))
         | MOnce (i, mf, aux) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = Once.add expls aux in
            let aux, f_expls = Once.update aux in
            let aexpl = Once.approximate f_expls aexpl i tp pol in
            memo, (f_expls, aexpl, MOnce (i, mf', aux))
         | MSimpleOnce (mf, aux) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = SimpleOnce.add expls aux in
            let aux, f_expls = SimpleOnce.update aux in
            let aexpl = SimpleOnce.approximate f_expls aexpl tp pol in
            memo, (f_expls, aexpl, MSimpleOnce (mf', aux))
         | MEventually (i, mf, aux) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = Eventually.add expls aux in
            let aux, f_expls = Eventually.update aux in
            let aexpl = approximate_eventually mformula.lbls aexpl fobligs i None tp pol in
            memo, (f_expls, aexpl, MEventually (i, mf', aux))
         | MEEventually (i, f_ts, mf, v) ->
            let memo, (_, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aexpl = approximate_eventually mformula.lbls aexpl fobligs i (Some (mformula.hash, v)) tp pol in
            memo, (one_ts tp ts aexpl, aexpl, MEEventually (i, f_ts, mf', v))
         | MHistorically (i, mf, aux) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = Once.add expls aux in
            let aux, f_expls = Once.update aux in
            let aexpl = Once.approximate_historically f_expls aexpl i tp pol in
            memo, (f_expls, aexpl, MHistorically (i, mf', aux))
         | MAlways (i, mf, aux) ->
            let memo, (expls, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aux = Eventually.add expls aux in
            let aux, f_expls = Eventually.update aux in
            let aexpl = approximate_always mformula.lbls aexpl fobligs i None tp pol in
            memo, (f_expls, aexpl, MAlways (i, mf', aux))
         | MEAlways (i, f_ts, mf, v) ->
            let memo, (_, aexpl, mf') = meval_rec ts tp db ~pol fobligs memo mf in
            let aexpl = approximate_always mformula.lbls aexpl fobligs i (Some (mformula.hash, v)) tp pol in
            memo, (one_ts tp ts aexpl, aexpl, MEAlways (i, f_ts, mf', v))
         | MSince (s, i, mf1, mf2, aux) ->
            let memo, (expls1, aexpl1, mf1') = meval_rec ts tp db ~pol fobligs memo mf1 in
            let memo, (expls2, aexpl2, mf2') = meval_rec ts tp db ~pol fobligs memo mf2 in
            let aux = Since.add expls1 expls2 aux in
            let aux, f_expls = Since.update (p mf1) (p mf2) aux in
            let aexpl = Since.approximate (p mf1) (p mf2) f_expls aexpl1 aexpl2 i tp pol in
            memo, (f_expls, aexpl, MSince (s, i, mf1', mf2', aux))
         | MSimpleSince (s, mf1, mf2, aux) ->
            let memo, (expls1, aexpl1, mf1') = meval_rec ts tp db ~pol fobligs memo mf1 in
            let memo, (expls2, aexpl2, mf2') = meval_rec ts tp db ~pol fobligs memo mf2 in
            let aux = SimpleSince.add expls1 expls2 aux in
            let aux, f_expls = SimpleSince.update (p mf1) (p mf2) aux in
            let aexpl = SimpleSince.approximate (p mf1) (p mf2) f_expls aexpl1 aexpl2 tp pol in
            memo, (f_expls, aexpl, MSimpleSince (s, mf1', mf2', aux))
         | MUntil (i, mf1, mf2, aux) ->
            let memo, (expls1, aexpl1, mf1') = meval_rec ts tp db ~pol fobligs memo mf1 in
            let memo, (expls2, aexpl2, mf2') = meval_rec ts tp db ~pol fobligs memo mf2 in
            let aux = Until.add expls1 expls2 aux in
            let aux, f_expls = Until.update (p mf1) (p mf2) aux in
            let aexpl = approximate_until mformula.lbls id id aexpl1 aexpl2 fobligs i None tp pol in
            memo, (f_expls, aexpl, MUntil (i, mf1', mf2', aux))
         | MEUntil (s, i, f_ts, mf1, mf2, v) ->
            let memo, (_, aexpl1, mf1') = meval_rec ts tp db ~pol fobligs memo mf1 in
            let memo, (_, aexpl2, mf2') = meval_rec ts tp db ~pol fobligs memo mf2 in
            let aexpl = approximate_until mformula.lbls id id aexpl1 aexpl2 fobligs i (Some (mformula.hash, v)) tp pol in
            memo, (one_ts tp ts aexpl, aexpl, MEUntil (s, i, f_ts, mf1', mf2', v))
         | MLabel (s, mf) ->
            let memo, (expls, aexpl, mf) = meval_rec ts tp db ~pol fobligs memo mf in
            memo, (expls, aexpl, MLabel (s, mf))
       in
       let mf = { mformula with mf } in
       let memo = if tp = outer_tp then Memo.memoize memo mformula (Polarity.value pol) (expls, aexpl, mf) else memo in
       debug (Printf.sprintf "meval_rec (%s, %d, %s) = %s"
                (Time.to_string ts) tp (IFormula.value_to_string mformula) (Expl.to_string aexpl));
       memo, (expls, aexpl, mf)
  in meval_rec ts tp db ~pol fobligs memo mformula


module MState = struct

  type t = { mf: IFormula.t
           ; tp_cur: timepoint                        (* current time-point evaluated    *)
           ; tp_out: timepoint                        (* last time-point that was output *)
           ; ts_waiting: timestamp Queue.t
           ; tsdbs: (timestamp * Db.t) Queue.t
           ; tpts: (timepoint, timestamp) Hashtbl.t
           ; lets: (string * IFormula.t) list }

  let init mf =
    let mf, lets = IFormula.init mf in
    { mf
    ; tp_cur = 0
    ; tp_out = -1
    ; ts_waiting = Queue.create ()
    ; tsdbs = Queue.create ()
    ; tpts = Hashtbl.create (module Int)
    ; lets }

  let tp_cur ms = ms.tp_cur

  let tsdbs ms = ms.tsdbs

  let to_string indent { mf
                       ; tp_cur
                       ; tp_out
                       ; ts_waiting
                       ; tsdbs
                       ; tpts } =
    "\nMState: \n\n" ^
      Printf.sprintf "%smf = %s\n" indent (IFormula.to_string mf) ^
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

type res = Expl.t TS.t list * Expl.t * IFormula.t

let mstep ?(force_evaluate_lets=false) ts db approx (ms: MState.t) (fobligs: FObligations.t) (memo : res Memo.t) =
  let pol_opt = if approx then Some Polarity.POS else None in
  (*let memo, ms = List.fold_left ms.lets ~init:(memo, ms)
      ~f:(fun (memo, ms) (e, mf) -> 
          let memo, (_, _, mf) = meval ts ms.tp_cur db ~pol:None fobligs ms.lets mf memo in
          memo, { ms with lets = ms.lets @ [e, mf] }) in*)
  let memo, (_, aexpl, mf') = meval ts ms.tp_cur db ~pol:pol_opt fobligs ms.lets ms.mf memo in
  let memo, ms =
    if force_evaluate_lets then
      List.fold_left ms.lets ~init:(memo, { ms with lets = [] })
        ~f:(fun (memo, ms) (e, mf) -> 
            let memo, (_, _, mf) = meval ts ms.tp_cur db ~pol:None fobligs ms.lets mf memo in
            memo, { ms with lets = ms.lets @ [e, mf] })
    else memo, ms in
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
