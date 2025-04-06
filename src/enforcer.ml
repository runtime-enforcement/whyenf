open Base
open Stdio

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm
open Etc
open Global

open Monitor
open MFormula

let print_debug s =
  if !Global.debug then
    Stdio.printf "\027[32m[enforcer] %s\027[0m\n" s
  else ()

module Triple = struct

  type t = Db.t * Db.t * FObligations.t

  let join (sup1, cau1, fobligs1) (sup2, cau2, fobligs2) =
    (Db.union sup1 sup2, Db.union cau1 cau2, Set.union fobligs1 fobligs2)

  (*let equal (sup1, cau1, fobligs1) (sup2, cau2, fobligs2) =
    Db.equal sup1 sup2 && Db.equal cau1 cau2 && Set.equal fobligs1 fobligs2*)

  let db_equal (sup1, cau1, _) (sup2, cau2, _) =
    Db.equal sup1 sup2 && Db.equal cau1 cau2

  let sup (sup, _, _) = sup
  let cau (_, cau, _) = cau
  (*let fobligs (_, _, fobligs) = fobligs*)

  let empty = (Db.empty, Db.empty, Set.empty (module FObligation))
  (*let empty2 fobligs = (Db.empty, Db.empty, fobligs)*)

  (*let is_empty (sup, cau, fobligs) = Db.is_empty sup && Db.is_empty cau && Set.is_empty fobligs*)

  let update_db db (sup, cau, _) = Db.union (Db.diff db sup) cau

  let update_fobligs fobligs (_, _, fobligs') = Set.union fobligs fobligs'

  let update_memo (sup, cau, fobligs) memo =
    let memo = Set.fold (Set.map (module String) ~f:Db.Event.name (Db.events (Db.union sup cau)))
                 ~init:memo ~f:Memo.add_event in
    let memo = Set.fold (Set.map (module Int) ~f:FObligation.h fobligs)
                 ~init:memo ~f:Memo.add_obligation in
    memo

(*let to_lists (sup, cau, fobligs) =
  (Set.to_list sup, Set.to_list cau, fobligs)*)

let to_string indent (sup, cau, fobligs) =
  "\nTriple:\n" ^
  Printf.sprintf "\n%ssup = %s" indent (Db.to_string sup) ^
  Printf.sprintf "\n%scau = %s" indent (Db.to_string cau) ^
  Printf.sprintf "\n%sfobligs = [%s]\n" indent (FObligations.to_string fobligs)

end

let inc_ts ts = Time.(ts + !s_ref)

module EState = struct

  type t = { ms: MState.t
           ; tp: timepoint
           ; ts: timestamp
           ; db: Db.t
           ; r : Triple.t
           ; fobligs: FObligations.t
           ; memo: Monitor.res Monitor.Memo.t
           ; nick: bool
           }

  let to_string { ms
    ; tp
    ; ts
    ; db
    ; r
    ; fobligs } =
    "\n<> EState <> \n" ^
    Printf.sprintf "ts = %s\n" (Time.to_string ts) ^
    Printf.sprintf "tp = %d\n" tp ^
    Printf.sprintf "db = %s\n" (Db.to_string db) ^
    Printf.sprintf "fobligs = %s\n" (FObligations.to_string fobligs) ^
    Printf.sprintf "%s" (MState.to_string "  " ms) ^
    (Triple.to_string "  " r)

  let init ms mf = { ms;
                     tp = 0;
                     ts = Time.zero;
                     db = Db.create [];
                     r = Triple.empty;
                     fobligs = Set.singleton (module FObligation)
                                 (FFormula (mf, -1, empty_valuation), POS);
                     memo = Memo.empty;
                     nick = false }

  let update r es =
    let memo = Triple.update_memo r es.memo in
    { es with db      = Triple.update_db es.db r;
              fobligs = Triple.update_fobligs es.fobligs r;
              r       = Triple.join es.r r;
              memo }

  let add_sup sup es =
    update (Db.singleton sup, Db.empty, Set.empty (module FObligation)) es

  let add_cau cau es =
    update (Db.empty, Db.singleton cau, Set.empty (module FObligation)) es

  let add_foblig foblig es =
    update (Db.empty, Db.empty, Set.singleton (module FObligation) foblig) es

  let fixpoint fn es =
    let rec loop r es =
      let es' = fn (update r es) in
      if not (Triple.db_equal es.r es'.r) then
        loop es.r es'
      else
        es'
    in loop Triple.empty es

  let mstep_state es =
    mstep es.tp es.ts es.db true es.ms es.fobligs

  let exec_monitor mf es =
    let memo, (aexpl, _) = mstep_state { es with ms = { es.ms with mf } } es.nick es.memo in
    { es with memo }, aexpl

  (*let rec filter_eval (db : Db.t) = function
    | Filter.An e -> Db.mem_trace db e
    | AllOf fis   -> List.for_all fis ~f:(filter_eval db)
    | OneOf fis   -> List.exists  fis ~f:(filter_eval db)
  
  let can_skip es mformula =
    not (filter_eval es.db mformula.filter)*)

  let default_ts ts es =
    Option.value ts ~default:es.ts
      
  let eval_fix ts tp v = function
    | FEvent (r, trms, pol, h) -> FEvent (r, List.map ~f:(Sig.eval v) trms, pol, h)
    | FOblig (fo, pol)         -> FOblig (FObligation.set_valuation v fo, pol) (* this set_valuation does not set the right valuation in the failing example *)

  let apply_fix es = function
    | FEvent (r, trms, POS, _) -> add_cau (r, List.map ~f:Term.unconst trms) es
    | FEvent (r, trms, NEG, _) -> add_sup (r, List.map ~f:Term.unconst trms) es
    | FOblig (fo, pol)         -> add_foblig (fo, pol) es

  let apply_fixes es = List.fold_left ~f:apply_fix ~init:es

  let f_leaf ts tp v = function
    | FFalse fixes -> assert (not (List.is_empty fixes));
                      List.map ~f:(eval_fix ts tp v) fixes
    | FTrue _ -> []
  
  let f_var ls     = List.dedup_and_sort (List.concat ls) ~compare:Monitor.compare_fix
  let f_ex ls      = if List.exists ~f:List.is_empty ls then
                       []
                     else
                       List.dedup_and_sort (List.concat ls) ~compare:Monitor.compare_fix
  let f_all ls     = List.dedup_and_sort (List.concat ls) ~compare:Monitor.compare_fix
  let f_impossible = []
    
  let enf mf es =
    print_debug ("goal: " ^ value_to_string mf);
    let es = { es with r = Triple.empty; fobligs = FObligations.empty } in
    let v = Map.empty (module String) in
    let rec loop es =
      let es, p = exec_monitor mf es (*{ es with memo = Memo.empty } *) in
      print_debug ("verdict: " ^ Expl.to_string ~to_string:Monitor.fbool_to_string p);
      let fixes = Expl.Pdt.fold (f_leaf es.ts es.tp) f_var f_ex f_all f_impossible p in
      match List.exists ~f:Monitor.fix_is_oblig fixes,
            List.exists ~f:Monitor.fix_is_event fixes with
      | _, true ->
         let fixes = List.filter ~f:Monitor.fix_is_event fixes in
         print_debug ("fixes:\n" ^ String.concat ~sep:"\n" (List.map ~f:Monitor.fix_to_string fixes));
         let es = apply_fixes es fixes in
         loop es
      | true, false ->
         let es = apply_fixes es fixes in
         print_debug ("fixes:\n" ^ String.concat ~sep:"\n" (List.map ~f:Monitor.fix_to_string fixes));
         loop es
      | false, false -> es
    in
    loop es

end

module Order = struct

  type t = ReOrd of Db.t * Db.t | PrOrd of Db.t | NoOrd

  let print_json ts = function
    | PrOrd c ->
       Stdio.printf "{ \"ts\": %s, \"cause\": %s, \"proactive\": true }\n"
         (Time.to_epoch_string ts) (Db.to_json c)
    | ReOrd (c, s) when not (Db.is_empty c) && not (Db.is_empty s) ->
       Stdio.printf "{ \"ts\": %s, \"cause\": %s, \"suppress\": %s }\n"
         (Time.to_epoch_string ts) (Db.to_json c) (Db.to_json s)
    | ReOrd (c, s) when not (Db.is_empty c) && Db.is_empty s ->
       Stdio.printf "{ \"ts\": %s, \"cause\": %s }\n"
         (Time.to_epoch_string ts) (Db.to_json c)
    | ReOrd (c, s) when Db.is_empty c && not (Db.is_empty s) ->
       Stdio.printf "{ \"ts\": %s, \"suppress\": %s }\n"
         (Time.to_epoch_string ts) (Db.to_json s)
    | ReOrd (_, _) -> Stdio.printf "{ \"ts\": %s }\n" (Time.to_epoch_string ts)
    | NoOrd -> Stdio.printf "{ \"ts\": %s, \"proactive\": true }\n" (Time.to_epoch_string ts)

  let print_textual ts = function
    | PrOrd c -> Stdio.printf "[Enforcer] @%s proactively commands:\nCause: \n%s\nOK.\n"
                   (Time.to_epoch_string ts) (Db.to_string c)
    | ReOrd (c, s) when not (Db.is_empty c) && not (Db.is_empty s) ->
       Stdio.printf "[Enforcer] @%s reactively commands:\nCause:\n%s\nSuppress:\n%s\nOK.\n"
         (Time.to_epoch_string ts) (Db.to_string c) (Db.to_string s)
    | ReOrd (c, s) when not (Db.is_empty c) && Db.is_empty s ->
       Stdio.printf "[Enforcer] @%s reactively commands:\nCause:\n%s\nOK.\n"
         (Time.to_epoch_string ts) (Db.to_string c)
    | ReOrd (c, s) when Db.is_empty c && not (Db.is_empty s) ->
       Stdio.printf "[Enforcer] @%s reactively commands:\nSuppress:\n%s\nOK.\n"
         (Time.to_epoch_string ts) (Db.to_string s)
    | ReOrd (_, _) -> Stdio.printf "[Enforcer] @%s OK.\n" (Time.to_epoch_string ts)
    | NoOrd -> Stdio.printf "[Enforcer] @%s nothing to do proactively.\n" (Time.to_epoch_string ts)
  
  let print ts ord =
    if !json then print_json ts ord else print_textual ts ord
  
end

let goal (es: EState.t) =
  (*print_endline ("state_goal=" ^ EState.to_string es);*)
  let obligs = List.map (Set.elements es.fobligs) ~f:(FObligation.eval es.ts es.tp) in
  match obligs with
    | [] -> MFormula._tt
    | [mf] -> mf
    | mfs -> MFormula.mapn_mf mfs Filter.tt (fun mfs -> MAnd (L, mfs, empty_nop_info (List.length mfs)))

let update_fobligs (es: EState.t) =
  let aux (es: EState.t) mf  = 
    let memo, (_, ms) = EState.mstep_state { es with ms = { es.ms with mf } } es.nick es.memo in
    { es with memo }, ms.mf in
  let es, fobligs_list =
    List.fold_map (Set.elements es.fobligs) ~init:es ~f:(FObligation.fold_map aux) in
  { es with fobligs = Set.of_list (module FObligation) fobligs_list }

let exec' (tf: Tformula.t) inc (b: Time.Span.s) =
  let reactive_step new_db (es: EState.t) =
    (*print_endline ("-- reactive_step tp=" ^ string_of_int es.tp);*)
    (*let time_before = Unix.gettimeofday() in*)
    let mf = goal es in
    (*let time_after = Unix.gettimeofday() in
      print_endline ("Goal time: " ^ string_of_float (time_after -. time_before));*)
    (*print_endline ("goal="^  MFormula.to_string mf);*)
    (*let time_before = Unix.gettimeofday() in*)
    let es = { es with ms      = { es.ms with tp_cur = es.tp };
                       r       = (Db.singleton Db.Event._tp,
                                  Db.empty,
                                  FObligations.empty);
                       db      = Db.add_event new_db Db.Event._tp;
                       fobligs = FObligations.empty;
                       nick    = false;
                       memo    = Monitor.Memo.empty } in
    (*let time_after = Unix.gettimeofday() in*)
    (*print_endline ("Update es time: " ^ string_of_float (time_after -. time_before));*)
    (*let time_before = Unix.gettimeofday() in*)
    (*Hashtbl.clear es.memo;*)
    (*let time_after = Unix.gettimeofday() in
      print_endline ("Clear memo time: " ^ string_of_float (time_after -. time_before));*)
    (*print_endline ("before: " ^ EState.to_string es);*)
    (*let time_before = Unix.gettimeofday() in*)
    let es = EState.enf mf es in
    (*print_endline ("BEFORE UPDATE: " ^ EState.to_string es);*)
    let es = update_fobligs es in
    (*print_endline ("AFTER UPDATE: " ^ EState.to_string es);*)
    (*let time_after = Unix.gettimeofday() in
      print_endline ("Enf time: " ^ string_of_float (time_after -. time_before));*)
    (*print_endline ("after: " ^ EState.to_string es);*)
    Order.ReOrd (Triple.cau es.r, Triple.sup es.r), es
  in
  let proactive_step (es: EState.t) =
    (*Hashtbl.clear es.memo;*)
    (*print_endline ("-- proactive_step ts=" ^ string_of_int es.ts);*)

    (*print_endline "-- proactive_step";
      print_endline (EState.to_string es);*)
    let mf = goal es in
    (*print_endline ("goal="^  MFormula.to_string mf);*)
    let es' = { es with ms      = { es.ms with tp_cur = es.tp };
                        r       = Triple.empty;
                        db      = Db.create [];
                        fobligs = FObligations.empty;
                        nick    = true;
                        memo    = Monitor.Memo.empty } in
    (*Hashtbl.clear es.memo;*)
    (*print_endline ("before: " ^ EState.to_string es);*)
    let es' = EState.enf mf es' in
    let es' = update_fobligs es' in
    (*print_endline ("after: " ^ EState.to_string es');*)
    if Db.mem (Triple.cau es'.r) Db.Event._tp then
      Order.PrOrd (Db.remove (Triple.cau es'.r) Db.Event._tp), es'
    else
      Order.NoOrd, es
  in
  let rec process_db (pb: Other_parser.Parsebuf.t) (es: EState.t) =
    (*let time_before = Unix.gettimeofday() in*)
    (*print_endline ("--process_db " ^ string_of_int !Monitor.meval_c);*)
    Monitor.meval_c := 0;
    if Int.equal pb.ts (-1) && FObligations.accepts_empty es.fobligs then
      es
    else if not (Time.equal (Time.of_int pb.ts) es.ts) then
      match proactive_step es with
      | PrOrd c as o, es' -> Other_parser.Stats.add_cau ~ins:true (Db.size c) pb.stats;
                             Order.print es.ts o;
                             process_db pb { es' with tp = es.tp + 1;
                                                      ts = inc_ts es.ts;
                                                      db = es.db }
      | NoOrd as o, es'   -> Order.print es.ts o;
                             process_db pb { es' with ts = inc_ts es.ts;
                                                      db = es.db }
      | _ -> raise (Invalid_argument "Reactive step did not return a proactive command")
    else if not (Db.is_tick pb.db) then
      match reactive_step pb.db es with
      | ReOrd (c, s) as o, es' -> Other_parser.Stats.add_cau (Db.size c) pb.stats;
                                  Other_parser.Stats.add_sup (Db.size s) pb.stats;
                                  Order.print es.ts o;
                                  if pb.check then
                                    es
                                  else
                                    { es' with tp = es'.tp + 1 }
      | _ -> raise (Invalid_argument "Reactive step did not return a reactive command")
    else
      es
  in
  let rec step first pb_opt (es: EState.t) =
    let conclude (pb: Other_parser.Parsebuf.t) es =
      let _ = process_db { pb with ts = -1; db = Db.create [] } es
      in ()
    in
    match Other_parser.Trace.parse_from_channel inc pb_opt with
    | None -> ()
    | Some (more, pb) ->
       let es = if first then { es with ts = Time.of_int pb.ts } else es in
       let es = process_db pb es in
       Stdlib.flush_all();
       if more then step false (Some(pb)) es else conclude pb es in
  let mf = Monitor.MFormula.init tf in
  (*print_endline (Monitor.MFormula.to_string mf);*)
  let ms = Monitor.MState.init mf in
  let es = EState.init ms mf in
  step true None es

let make_monitoring (tyf : Tyformula.t) : Tyformula.t =
  let open Tyformula in
  let xs = Set.elements (fv tyf) in
  Sig.add_pred "violation" xs Enftype.cau 0 Trace;
  let vars = List.map ~f:(fun x -> Tterm.make_dummy (Tterm.var x)) xs in
  let violation = make_dummy (Predicate ("violation", vars)) in
  let tyf = make_dummy (Imp (Side.R, tyf, violation)) in
  let tyf = List.fold_right xs ~init:tyf ~f:(fun x f -> make_dummy (forall x f)) in
  make_dummy (Always (Interval.full, tyf))

let compile (f: Formula.t) (b: Time.Span.s) : Tformula.t =
  let open Tyformula.MFOTL_Enforceability(Sig) in
  (* Applying alpha conversion to obtain unique variable names *)
  let f = Formula.convert_vars f in
  (* Typing terms: Formula.t -> Tyformula.t *)
  let tyf = Tyformula.of_formula' f in
  (* If monitoring, do f -> FORALL x_1, ..., x_k. f IMPLIES violation(x_1, ..., x_k) *)
  let tyf = if !monitoring then make_monitoring tyf else tyf in
  (* Typing formulae: Tyformula.t -> Tyformula.typed_t *)
  let typed_tyf = do_type tyf b in
  (* Checking monitorability: Tyformula.typed_t -> Tformula.t *)
  let tf = Tformula.of_formula' typed_tyf in
  (* Checking transparency *)
  let transparent = is_transparent typed_tyf in
  if (not transparent) then
    print_endline "This formula cannot be transparently enforced.";
  tf

let exec (f: Formula.t) =
  let tf = compile f !b_ref in
  exec' tf !inc_ref !b_ref

