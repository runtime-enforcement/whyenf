open Base
open Expl
open Option

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm
module Valuation = ITerm.Valuation

open Etc

let debug s =
  if !Global.debug then Stdio.printf "[debug:mformula] %s\n%!" s

(* Polarity *)

module Polarity = struct

  type t  = POS | NEG [@@deriving compare, sexp_of, hash, equal]
            
  let neg = function POS -> NEG | NEG -> POS
    
  let to_string = function
      | POS -> "+"
      | NEG -> "-"

  let to_int = function
    | POS -> 1
    | NEG -> 0

  let value = Option.value ~default:POS

end

(* Timestamped data *)

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

(* Buffers *)

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

(* Temporal operators *)

let proof_false = function
  | Polarity.POS -> false
  | NEG -> true
    
let approximate_false pol = Pdt.Leaf (proof_false pol)

let approximate_false_opt pol_opt =
  Pdt.Leaf (proof_false (Polarity.value pol_opt))
    
let els pol_opt = function
  | Some p -> p
  | None -> approximate_false (Option.value ~default:Polarity.POS pol_opt)

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

  let add (expls: Expl.t TS.t list) (aux : t) : t =
     { aux with
       tstps = aux.tstps @ (List.map expls ~f:(fun te -> (te.ts, te.tp)));
       buf = aux.buf @ (List.map expls ~f:TS.data) } 

  let rec update (aux : t) : t * Expl.t TS.t list =
    match aux.tstps, aux.buf with
    | [(ts, tp)], _ when aux.first ->
       { aux with first = false }, [TS.make tp ts (Pdt.Leaf false)]
    | (ts, tp) :: (ts', tp') :: tstps, buf_expl :: buf when Interval.diff_is_in ts ts' aux.itv ->
       let aux, bs = update { aux with tstps = (ts', tp') :: tstps; buf } in
       aux, (TS.make tp ts buf_expl)::bs
    | (ts, tp) :: (ts', tp') :: tstps, buf_expl :: buf ->
       let aux, bs = update { aux with tstps = (ts', tp') :: tstps; buf }  in
       aux, (TS.make tp ts (Pdt.Leaf false))::bs
    | _,  _ -> aux, []

  let approximate_ tp expls =
    match List.last expls with
    | Some te when TS.tp te = tp -> Some te.data
    | _ -> None

  let approximate tp expls pol = els pol (approximate_ tp expls)

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

  let add (expls: Expl.t TS.t list) (aux : t) : t =
     { aux with
       tstps = aux.tstps @ (List.map expls ~f:(fun te -> (te.ts, te.tp)));
       tstps_todo = aux.tstps_todo @ (List.map expls ~f:(fun te -> (te.ts, te.tp)));
       buf = aux.buf @ (List.map expls ~f:TS.data) }

  let rec update (aux : t) : t * Expl.t TS.t list = 
    match aux.tstps, aux.tstps_todo, aux.buf with
    | (ts', tp') :: tstps, (ts, tp) :: tstps_todo, buf_expl :: buf when tp' = tp + 1 ->
       let aux, bs = update { aux with tstps = (ts', tp') :: tstps;
                                       tstps_todo = tstps_todo } in
       let b = TS.make tp ts (if Interval.diff_is_in ts ts' aux.itv
                              then buf_expl
                              else Pdt.Leaf false) in
       aux, b::bs
    | _ -> aux, []

  let approximate pol = approximate_false_opt pol

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

  let add (expls : Expl.t TS.t list) (aux : t) : t =
    { aux with buf = Buft.add aux.buf expls }
  
  let rec update (aux : t) : t * Expl.t TS.t list =
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
       let oaux, b = Pdt.split_prod (Pdt.apply2_reduce equal_alpha_t_bool (process ts tp) id id expl_pdt aux.oaux) in
       let aux = { aux with oaux; buf } in
       let aux, bs = update aux in
       aux, (TS.make tp ts b)::bs
    | _ -> aux, []

  let approximate_ i b neg =
    Bool.equal neg (b && Interval.has_zero i)

  let approximate (expls: Expl.t TS.t list) (aexpl: Expl.t) (moaux: Interval.t) (tp: timepoint) (pol: Polarity.t option) : Expl.t =
    match List.last expls, Polarity.value pol with
    | Some expl, _ when expl.tp = tp -> expl.data
    | _, Polarity.POS ->
      Pdt.apply1_reduce Bool.equal (approximate_ moaux true) id aexpl
    | _, pol -> approximate_false pol

 let approximate_historically (expls: Expl.t TS.t list) (aexpl: Expl.t) (i: Interval.t) (tp: timepoint) (pol: Polarity.t option) : Expl.t =
   match List.last expls, Polarity.value pol with
   | Some expl, _ when expl.tp = tp -> expl.data
   | _, Polarity.NEG ->
     Pdt.apply1_reduce Bool.equal (approximate_ i false) id aexpl
   | _, pol -> approximate_false pol

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

  let add (expls: Expl.t TS.t list) (aux : t) : t =
    { aux with
      tstps_todo = aux.tstps_todo @ (List.map expls ~f:(fun te -> (te.ts, te.tp)));
      buf = Buft.add aux.buf expls } 
  
  let rec update (aux : t) : t * Expl.t TS.t list =
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
         let eaux = Pdt.apply2_reduce equal_alpha_t (load1 ts tp) id id expl_pdt aux.eaux in
         let aux = { aux with eaux; buf } in
         load ~ts_opt:(Some ts) aux
      | _ -> ts_opt, aux
    in
    let ts_opt, aux = load aux in
    match aux.tstps_todo, ts_opt with
    | (ts, tp)::tstps_todo, Some ts' when Interval.diff_right_of ts ts' aux.itv_in -> 
       let eaux, b = Pdt.split_prod (Pdt.apply1_reduce equal_alpha_t_bool (process ts tp) id aux.eaux) in
       let aux = { aux with eaux; tstps_todo } in
       let aux, bs = update aux in
       aux, (TS.make tp ts b)::bs
    | _ -> aux, []

  let approximate tp i is_pos b_next b_now =
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

  let add (expls1: Expl.t TS.t list) (expls2: Expl.t TS.t list) (aux: t) : t =
    { aux with buf = Buf2t.add aux.buf expls1 expls2 } 
  
  let rec update proj1 proj2 (aux : t) : t * Expl.t TS.t list =
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
      (*print_endline (Expl.to_string expl_alpha_pdt); 
       print_endline (Expl.to_string expl_beta_pdt);
        print_endline (beta_alphas_to_string aux.saux); *)
       let saux, b = Pdt.split_prod (Pdt.apply3_reduce equal_beta_alphas_t_bool (process ts tp) proj1 proj2 id expl_alpha_pdt expl_beta_pdt aux.saux) in
       let aux = { aux with saux; buf } in
       let aux, bs = update proj1 proj2 aux in
       aux, (TS.make tp ts b)::bs
    | _ -> aux, []

  let approximate_ tp a pol b_alpha b_beta =
    match b_alpha, b_beta, pol with
      | _    , true, true when Time.Span.is_zero a        -> true
      | _    , _   , true                                 -> false
      | false, _   , false when not (Time.Span.is_zero a) -> false
      | _    , _   , false                                -> true

  let approximate proj1 proj2 (expls: Expl.t TS.t list) (aexpl1: Expl.t) (aexpl2: Expl.t) (i: Interval.t) (tp: timepoint) (pol: Polarity.t option) =
    match List.last expls, pol with
    | Some expl, _ when expl.tp = tp -> expl.data
    | _ -> Pdt.apply2_reduce Bool.equal 
             (approximate_ tp (Interval.left i) (Polarity.equal (Polarity.value pol) Polarity.POS)) proj1 proj2 aexpl1 aexpl2

  
  let map f g (aux: t) =
    { aux with saux = f aux.saux; buf = Buf2t.map g g (fun t -> t) aux.buf }
  
end

module Until = struct

  type alphas_beta_t = { not_alpha_in : Tdeque.t;
                         not_alpha_out: Tdeque.t;
                         beta_in  : Tdeque.t;
                         beta_out : Tdeque.t } [@@deriving compare, sexp_of, hash, equal]

  let equal_alphas_beta_t_bool (uaux, b) (uaux', b') =
    equal_alphas_beta_t uaux uaux' && Bool.equal b b'

  type t = { uaux        : alphas_beta_t Pdt.t;
             itv_beta_in : Interval.t;
             itv_alpha_in: Interval.t;
             itv_out     : Interval.t;
             tstps_todo  : (timestamp * timepoint) list;
             buf         : (Expl.t, Expl.t, timestamp * timepoint) Buf2t.t }

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
      (Buf2t.to_string Expl.to_string Expl.to_string (fun (ts, tp) -> Printf.sprintf "(%s, %d)" (Time.to_string ts) tp) aux.buf)


  let init itv_beta_in = { uaux         = Pdt.Leaf { not_alpha_in  = Tdeque.empty
                                                   ; not_alpha_out = Tdeque.empty
                                                   ; beta_in   = Tdeque.empty
                                                   ; beta_out  = Tdeque.empty };
                           itv_beta_in;
                           itv_alpha_in = Interval.to_zero itv_beta_in;
                           itv_out      = Option.value_exn (Interval.out_right itv_beta_in);
                           tstps_todo   = [];
                           buf          = (([], []), []) }

  let rec update_tstps tstps (expls: 'a TS.t list) : (timestamp * timepoint) list =
    let last_tp = Option.value (Option.map (List.last tstps) ~f:snd) ~default:(-1) in
    tstps @ List.filter_map expls ~f:(fun te -> if te.tp > last_tp then Some (te.ts, te.tp) else None) 

  let rec update_tstps2 tstps expls1 expls2 =
    let tstps = update_tstps tstps expls1 in
    update_tstps tstps expls2

  let add (expls1: Expl.t TS.t list) (expls2: Expl.t TS.t list) (aux: t) : t =
    let tstps_todo = update_tstps2 aux.tstps_todo expls1 expls2 in
    { aux with tstps_todo;
               buf = Buf2t.add aux.buf expls1 expls2 } 
    
  let rec update proj1 proj2 (aux : t) : t * Expl.t TS.t list =
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
    let rec load ?(ts_opt=None) uaux =
      match Buf2t.get uaux.buf with
      | Some ((expl_alpha_pdt, expl_beta_pdt), (ts, tp)), buf ->
         let uaux = Pdt.apply3_reduce equal_alphas_beta_t (load1 ts tp) proj1 proj2 id expl_alpha_pdt expl_beta_pdt aux.uaux in
         let aux = { aux with uaux; buf } in
         load ~ts_opt:(Some ts) aux
      | _ -> ts_opt, aux
    in
    let ts_opt, aux = load aux in
    let rec loop aux = 
      match aux.tstps_todo, ts_opt with
      | (ts, tp)::tstps_todo, Some ts' when Interval.diff_right_of ts ts' aux.itv_beta_in ->
         let uaux, b = Pdt.split_prod (Pdt.apply1_reduce equal_alphas_beta_t_bool (process ts tp) id aux.uaux) in
         let aux = { aux with uaux; tstps_todo } in
         let aux, bs = loop aux in
         aux, (TS.make tp ts b)::bs
      | _ -> aux, []
    in loop aux

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

(* Monitorable formulae (MFormulae) *)

module MFormulaMake (Var : Modules.V) (Term : MFOTL_lib.Term.T with type v = Var.t) = struct

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
    | MAgg          of Var.t * Aggregation.op * Aggregation.op_fun * MyTerm.t * Var.t list * t
    | MTop          of Var.t list * string * Aggregation.op_tfun * MyTerm.t list * Var.t list * t
    | MNeg          of t
    | MAnd          of Side.t * t list * nop_info
    | MOr           of Side.t * t list * nop_info
    | MImp          of Side.t * t * t * binop_info
    | MExists       of Var.t * Dom.tt * bool * t
    | MForall       of Var.t * Dom.tt * bool * t
    | MPrev         of Interval.t * t * prev_info
    | MNext         of Interval.t * t * next_info
    | MENext        of Interval.t * timestamp option * t * Valuation.t
    | MOnce         of Interval.t * t * once_info
    | MEventually   of Interval.t * t * eventually_info
    | MEEventually  of Interval.t * timestamp option * t * Valuation.t
    | MHistorically of Interval.t * t * historically_info
    | MAlways       of Interval.t * t * always_info
    | MEAlways      of Interval.t * timestamp option * t * Valuation.t
    | MSince        of Side.t * Interval.t * t * t * since_info
    | MUntil        of Interval.t * t * t * until_info
    | MEUntil       of Side.t * Interval.t * timestamp option *  t * t * Valuation.t
    | MLabel        of string * t
    | MLet          of string * Var.t list * t * t

  and t = { mf: core_t;       (* Formula *)
            filter: Filter.t; (* Filter (for skipping) *)
            events: (string, String.comparator_witness) Set.t option;
                              (* Relevant events *)
            obligations: (int, Int.comparator_witness) Set.t option;
                              (* Relevant obligations *)
            hash: int;        (* Hash *)
            lbls: Lbl.t list; (* Labels *)
            projs: int list;  (* Map current indices -> parent indices *)
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
    | MTop (_, _, _, _, _, f)
    | MLabel (_, f) -> [f]
    | MImp (_, f1, f2, _)
    | MSince (_, _, f1, f2, _)
    | MUntil (_, f1, f2, _)
    | MEUntil (_, _, _, f1, f2, _)
    | MLet (_, _, f1, f2) -> [f1; f2]
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
    | MAgg (s, op, _, x, y, f) ->
      Printf.sprintf (Etc.paren l (-1) "%s <- %s(%s; %s; %s)") (Var.to_string s)
        (Aggregation.op_to_string op) (MyTerm.value_to_string x)
        (Etc.string_list_to_string (List.map ~f:Var.to_string y)) (value_to_string_rec (-1) f)
    | MTop (s, op, _, x, y, f) ->
      Printf.sprintf (Etc.paren l (-1) "[%s] <- %s(%s; %s; %s)")
        (Etc.string_list_to_string (List.map ~f:Var.to_string s)) op (MyTerm.list_to_string x)
        (Etc.string_list_to_string (List.map ~f:Var.to_string y)) (value_to_string_rec (-1) f)
    | MNeg f -> Printf.sprintf "¬%a" (fun _ -> value_to_string_rec 5) f
    | MAnd (_, fs, _) -> Printf.sprintf (Etc.paren l 4 "%s") (String.concat ~sep:"∧" (List.map fs ~f:(value_to_string_rec 4)))
    | MOr (_, fs, _) -> Printf.sprintf (Etc.paren l 3 "%s") (String.concat ~sep:"∨" (List.map fs ~f:(value_to_string_rec 4)))
    | MImp (_, f, g, _) -> Printf.sprintf (Etc.paren l 4 "%a → %a") (fun _ -> value_to_string_rec 4) f (fun _ -> value_to_string_rec 4) g
    | MExists (x, _, _, f) -> Printf.sprintf (Etc.paren l 5 "∃%s. %a") (Var.to_string x) (fun _ -> value_to_string_rec 5) f
    | MForall (x, _, _, f) -> Printf.sprintf (Etc.paren l 5 "∀%s. %a") (Var.to_string x) (fun _ -> value_to_string_rec 5) f
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
    | MLabel (s, f) -> Printf.sprintf (Etc.paren l 0 "{%s}{%a}") s (fun _ -> value_to_string_rec 0) f
    | MLet (e, vars, f, g) ->
      Printf.sprintf (Etc.paren l (-1) "LET %s(%s) = %s IN %s")
        e (Etc.string_list_to_string (List.map ~f:Var.to_string vars))
        (value_to_string_rec (-1) f) (value_to_string_rec (-1) g)
  let value_to_string = value_to_string_rec 0

  let rec with_aux_to_string_rec l mf =
    match mf.mf with
    | MTT -> Printf.sprintf "⊤"
    | MFF -> Printf.sprintf "⊥"
    | MEqConst (trm, c) -> Printf.sprintf "%s = %s" (Term.value_to_string trm) (Dom.to_string c)
    | MPredicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
    | MAgg (s, op, _, x, y, f) ->
      Printf.sprintf (Etc.paren l (-1) "%s <- %s(%s; %s; %s)") (Var.to_string s)
        (Aggregation.op_to_string op) (MyTerm.value_to_string x)
        (Etc.string_list_to_string (List.map ~f:Var.to_string y)) (value_to_string_rec (-1) f)
    | MTop (s, op, _, x, y, f) ->
      Printf.sprintf (Etc.paren l (-1) "[%s] <- %s(%s; %s; %s)")
        (Etc.string_list_to_string (List.map ~f:Var.to_string s)) op
        (MyTerm.list_to_string x) (Etc.string_list_to_string (List.map ~f:Var.to_string y))
        (value_to_string_rec (-1) f)
    | MNeg f -> Printf.sprintf "¬%a" (fun _ -> value_to_string_rec 5) f
    | MAnd (_, fs, _) -> Printf.sprintf (Etc.paren l 4 "%s") (String.concat ~sep:"∧" (List.map fs ~f:(value_to_string_rec 4)))
    | MOr (_, fs, _) -> Printf.sprintf (Etc.paren l 3 "%s") (String.concat ~sep:"∨" (List.map fs ~f:(value_to_string_rec 4)))
    | MImp (_, f, g, _) -> Printf.sprintf (Etc.paren l 4 "%a → %a") (fun _ -> value_to_string_rec 4) f (fun _ -> value_to_string_rec 4) g
    | MExists (x, _, _, f) -> Printf.sprintf (Etc.paren l 5 "∃%s. %a") (Var.to_string x) (fun _ -> value_to_string_rec 5) f
    | MForall (x, _, _, f) -> Printf.sprintf (Etc.paren l 5 "∀%s. %a") (Var.to_string x) (fun _ -> value_to_string_rec 5) f
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
    | MLabel (s, f) -> Printf.sprintf (Etc.paren l 0 "{%s}{%a}") s (fun _ -> value_to_string_rec 0) f
    | MLet (e, vars, f, g) -> Printf.sprintf (Etc.paren l (-1) "LET %s(%s) = %s IN %s")
                                e (Etc.string_list_to_string (List.map ~f:Var.to_string vars))
                                (value_to_string_rec (-1) f) (value_to_string_rec (-1) g)
  
  let with_aux_to_string = with_aux_to_string_rec 0

  let rec to_string ?(l=0) mf =
    let n = "\n" ^ Etc.spaces (l*4) in
    Printf.sprintf  "%s{ mf = %s;%s  filter = %s;%s  events = %s;%s  obligations = %s;%s  hash = %d;%s  lbls = %s;%s  projs = [%s];%s  subformulae = [%s] }"
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
      (String.concat ~sep:", " (List.map ~f:string_of_int mf.projs)) n
      (String.concat ~sep:";"
         (List.map ~f:(fun f -> Printf.sprintf "\n%s" (to_string ~l:(l+1) f)) (subs mf)))
  

  let rec core_op_to_string = function
    | MTT -> Printf.sprintf "⊤"
    | MFF -> Printf.sprintf "⊥"
    | MEqConst (_, _) -> Printf.sprintf "="
    | MPredicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
    | MAgg (s, op, _, x, y, _) -> Printf.sprintf "%s <- %s(%s; %s)" (Var.to_string s)
                                    (Aggregation.op_to_string op) (MyTerm.to_string x)
                                    (Etc.string_list_to_string (List.map ~f:Var.to_string y))
    | MTop (s, op, _, x, y, _) -> Printf.sprintf "[%s] <- %s(%s; %s)"
                                    (Etc.string_list_to_string (List.map ~f:Var.to_string s)) op
                                    (MyTerm.list_to_string x) (Etc.string_list_to_string (List.map ~f:Var.to_string y))
    | MNeg _ -> Printf.sprintf "¬"
    | MAnd (_, _, _) -> Printf.sprintf "∧"
    | MOr (_, _, _) -> Printf.sprintf "∨"
    | MImp (_, _, _, _) -> Printf.sprintf "→"
    | MExists (x, _, _, _) -> Printf.sprintf "∃ %s." (Var.to_string x)
    | MForall (x, _, _, _) -> Printf.sprintf "∀ %s." (Var.to_string x)
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
    | MLabel (s, _) -> Printf.sprintf "{%s}" s
    | MLet (e, vars, _, _) -> Printf.sprintf "LET %s(%s)" e (Etc.string_list_to_string (List.map ~f:Var.to_string vars))

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
    | MLabel (s, _) -> Printf.sprintf "N"
    | MLet _ -> Printf.sprintf "N"
 
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
       String.hash "MPredicate" +++ String.hash e +++ list_hash Term.hash t
    | MAgg (s, op, _, x, y, f) ->
       String.hash "MAgg"
       +++ Var.hash s +++ Aggregation.hash_op op +++ MyTerm.hash x
       +++ list_hash Var.hash y +++ f.hash
    | MTop (s, op, _, x, y, f) ->
       String.hash "MTop"
       +++ list_hash Var.hash s +++ String.hash op
       +++ list_hash MyTerm.hash x +++ list_hash Var.hash y +++ f.hash
    | MNeg f ->
       String.hash "MNeg" +++ f.hash
    | MAnd (s, fs, _) ->
       String.hash "MAnd" +++ Side.hash s +++ ppp fs
    | MOr (s, fs, _) ->
       String.hash "MOr" +++ Side.hash s +++ ppp fs
    | MImp (s, f, g, _) ->
       String.hash "MImp" +++ Side.hash s +++ f.hash +++ g.hash
    | MExists (x, _, _, f) ->
       String.hash "MExists" +++ Var.hash x +++ f.hash
    | MForall (x, _, _, f) ->
       String.hash "MForall" +++ Var.hash x +++ f.hash
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
       String.hash "MEEventually" +++ Interval.hash i +++ f.hash +++ Valuation.hash v
    | MHistorically (i, f, _) ->
       String.hash "MHistorically" +++ Interval.hash i +++ f.hash
    | MAlways (i, f, _) ->
       String.hash "MAlways" +++ Interval.hash i +++ f.hash
    | MEAlways (i, _, f, v) ->
       String.hash "MEAlways" +++ Interval.hash i +++ f.hash +++ Valuation.hash v
    | MSince (s, i, f, g, _) ->
       String.hash "MSince" +++ Side.hash s +++ Interval.hash i +++ f.hash +++ g.hash
    | MUntil (i, f, g, _) ->
       String.hash "MUntil" +++ Interval.hash i +++ f.hash +++ g.hash
    | MEUntil (s, i, _, f, g, v) ->
       String.hash "MEUntil" +++ Side.hash s +++ Interval.hash i +++ f.hash
       +++ g.hash +++ Valuation.hash v
    | MLabel (s, f) -> f.hash
    | MLet (e, vars, f, g) ->
      String.hash "MLet" +++ String.hash e +++ list_hash Var.hash vars +++ f.hash +++ g.hash

  (*and hash mf = core_hash mf.mf*)

  let set_events mf =
    let with_events mf events =
      { mf with events = Some events;
                obligations = Some (Set.empty (module Int)) } in
    let add_hash mf =
      { mf with obligations = Some (Set.add (Option.value_exn mf.obligations) mf.hash) } in
    let rec map1 m f comb =
      let f = aux m f in
      { mf with mf          = comb f;
                events      = f.events;
                obligations = f.obligations }
    and map2 m f1 f2 comb =
      let f1 = aux m f1 in
      let f2 = aux m f2 in
      { mf with mf          = comb f1 f2;
                events      = Some (Set.union (Option.value_exn f1.events) (Option.value_exn f2.events));
                obligations = Some (Set.union (Option.value_exn f1.obligations) (Option.value_exn f2.obligations)) }
    and mapn m fs comb =
      let fs = List.map ~f:(aux m) fs in
      { mf with mf          = comb fs;
                events      = Some (Set.union_list (module String) (List.map ~f:(fun f -> Option.value_exn f.events) fs));
                obligations = Some (Set.union_list (module Int) (List.map ~f:(fun f -> Option.value_exn f.obligations) fs)) }
    and aux m mf = 
      match mf.events with
      | Some _ -> mf
      | None ->
        match mf.mf with
        | MTT
        | MFF
        | MEqConst _ -> with_events mf (Set.empty (module String))
        | MPredicate (r, _) ->
          (match Map.find m r with
           | Some evs -> with_events mf evs
           | None ->  with_events mf (Set.singleton (module String) r))
        | MPredicate (r, _) -> with_events mf (Set.singleton (module String) r)
        | MAgg (s, op, op_fun, x, y, f) -> map1 m f (fun f -> MAgg (s, op, op_fun, x, y, f))
        | MTop (s, op, op_fun, x, y, f) -> map1 m f (fun f -> MTop (s, op, op_fun, x, y, f))
        | MNeg f -> map1 m f (fun f -> MNeg f)
        | MAnd (s, fs, inf) -> mapn m fs (fun fs -> MAnd (s, fs, inf))
        | MOr (s, fs, inf) -> mapn m fs (fun fs -> MOr (s, fs, inf))
        | MImp (s, f, g, inf) -> map2 m f g (fun f g -> MImp (s, f, g, inf))
        | MExists (s, tt, b, f) -> map1 m f (fun f -> MExists (s, tt, b, f))
        | MForall (s, tt, b, f) -> map1 m f (fun f -> MForall (s, tt, b, f))
        | MPrev (i, f, inf) -> map1 m f (fun f -> MPrev (i, f, inf))
        | MNext (i, f, inf) -> map1 m f (fun f -> MNext (i, f, inf))
        | MENext (i, t_opt, f, v) -> add_hash (map1 m f (fun f -> MENext (i, t_opt, f, v)))
        | MOnce (i, f, inf) -> map1 m f (fun f -> MOnce (i, f, inf))
        | MEventually (i, f, inf) -> map1 m f (fun f -> MEventually (i, f, inf))
        | MEEventually (i, t_opt, f, v) -> add_hash (map1 m f (fun f -> MEEventually (i, t_opt, f, v)))
        | MHistorically (i, f, inf) -> map1 m f (fun f -> MHistorically (i, f, inf))
        | MAlways (i, f, inf) -> map1 m f (fun f -> MAlways (i, f, inf))
        | MEAlways (i, t_opt, f, inf) -> add_hash (map1 m f (fun f -> MEAlways (i, t_opt, f, inf)))
        | MSince (s, i, f, g, inf) -> map2 m f g (fun f g -> MSince (s, i, f, g, inf))
        | MUntil (i, f, g, inf) -> map2 m f g (fun f g -> MUntil (i, f, g, inf))
        | MEUntil (s, i, t_opt, f, g, v) -> add_hash (map2 m f g (fun f g -> MEUntil (s, i, t_opt, f, g, v)))
        | MLabel (s, f) -> map1 m f (fun f -> MLabel (s, f))
        | MLet (s, vars, f, g) ->
          let f = aux m f in
          map1 (Map.update m s (fun _ -> Option.value_exn f.events)) g (fun g -> MLet (s, vars, f, g))
    in aux (Map.empty (module String)) mf

  let rec fv mf = match mf.mf with
    | MTT | MFF -> Set.empty (module Var)
    | MEqConst (trm, _) -> Set.of_list (module Var) (Term.fv_list [trm])
    | MPredicate (_, trms) -> Set.of_list (module Var) (Term.fv_list trms)
    | MAgg (s, _, _, _, y, _) -> Set.of_list (module Var) (s::y)
    | MTop (s, _, _, _, y, _) -> Set.of_list (module Var) (s@y)
    | MNeg f -> fv f
    | MAnd (_, fs, _)
      | MOr (_, fs, _) -> Set.union_list (module Var) (List.map fs ~f:fv)
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
      | MEAlways (_, _, f, _)
    | MLabel (_, f) -> fv f
    | MLet (_, vars, f, g) -> Set.union (Set.diff (fv f) (Set.of_list (module Var) vars)) (fv g)

  let equal mf1 mf2 = mf1.hash = mf2.hash

  let make mf filter =
    { mf; filter; events = None; obligations = None; hash = core_hash mf; lbls = []; projs = [] }

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
      | MTop (_, _, _, _, _, f)
      | MLabel (_, f) -> rank f
    | MImp (_, f, g, _)
      | MSince (_, _, f, g, _)
      | MUntil (_, f, g, _)
      | MEUntil (_, _, _, f, g, _) -> rank f + rank g
    | MAnd (_, fs, _)
    | MOr (_, fs, _) -> List.fold ~init:0 ~f:(+) (List.map fs ~f:rank)
    | MLet (_, _, _, f) -> rank f
  
  let rec size mf = match mf.mf with
    | MTT | MFF
    | MEqConst _ 
    | MPredicate _ -> 1
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
      | MTop (_, _, _, _, _, f)
      | MLabel (_, f) -> 1 + size f
    | MImp (_, f, g, _)
      | MSince (_, _, f, g, _)
      | MUntil (_, f, g, _)
      | MEUntil (_, _, _, f, g, _)
      | MLet (_, _, f, g) -> 1 + size f + size g
    | MAnd (_, fs, _)
    | MOr (_, fs, _) -> List.fold ~init:1 ~f:(+) (List.map fs ~f:size)

  let set_projs lbls mf =
    (* Computes the projection for the child with lbls' onto the parent with lbls *)
    let projs = List.mapi mf.lbls ~f:(fun i lbl' ->
        match List.findi lbls ~f:(fun _ lbl -> match lbl, lbl' with
            | Lbl.LAll x, LVar x'
            | LEx x, LVar x'
            | LEx x, LAll x'
            | LAll x, LEx x' -> String.equal x x'
            | _, _ -> Lbl.equal lbl lbl') with
        | Some (i, _) -> i
        | None -> -1) in
    { mf with projs }

end

module MFormula = struct

  include MFormulaMake(Term.StringVar)(Term)

  let rec set_lbls ?(fvs=[]) ?(m=Map.empty (module String)) mf =
    let with_lbls mf lbls = { mf with lbls } in
    let order_lbls lbls fvs =
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
      var_terms @ quants @ nonvars in
    let lbls_of_term term =
      order_lbls (Lbl.of_term term :: List.map ~f:Lbl.var (Term.fv_list [term])) fvs in
    let lbls_of_terms terms =
      order_lbls (List.map ~f:Lbl.of_term terms @ List.map ~f:Lbl.var (Term.fv_list terms)) fvs in
    let map1 fvs m f comb flbls =
      let f = set_lbls ~fvs ~m f in
      let lbls = flbls f.lbls in
      { mf with mf = comb f (set_projs lbls); lbls } in
    let map2 fvs m f1 f2 comb flbls =
      let f1 = set_lbls ~fvs ~m f1 in
      let f2 = set_lbls ~fvs ~m f2 in
      let lbls = flbls f1.lbls f2.lbls in
      { mf with mf = comb f1 f2 (set_projs lbls); lbls } in
    let mapn fvs m fs comb flbls =
      let fs = List.map ~f:(set_lbls ~fvs ~m) fs in
      let lbls = flbls (order_lbls
                          (List.concat (List.map ~f:(fun f -> f.lbls) fs)) fvs) in
      { mf with mf = comb fs (set_projs lbls); lbls } in
    let id lbls = lbls in
    let id2 lbls1 lbls2 = order_lbls (lbls1 @ lbls2) fvs in
    let imp lbls1 lbls2 = order_lbls ((List.map ~f:Lbl.exquant lbls1) @ lbls2) fvs in
    let mf' = match mf.mf with
      | MTT | MFF -> with_lbls mf []
      | MAgg (s, op, op_fun, x, y, f) ->
        let y    = Etc.reorder_subset ~equal:String.equal y fvs in
        let sy   = Etc.reorder_subset ~equal:String.equal (s::y) fvs in
        let fvs' = Etc.reorder_subset ~equal:String.equal (Set.elements (fv f)) y in
        map1 fvs' m f (fun f p -> MAgg (s, op, op_fun, x, y, p f)) (fun _ -> List.map ~f:Lbl.var sy)
      | MTop (s, op, op_fun, x, y, f) ->
        let y    = Etc.reorder_subset ~equal:String.equal y fvs in
        let sy   = Etc.reorder_subset ~equal:String.equal (s@y) fvs in
        let fvs' = Etc.reorder_subset ~equal:String.equal (Set.elements (fv f)) y in
        map1 fvs' m f (fun f p -> MTop (s, op, op_fun, x, y, p f)) (fun _ -> List.map ~f:Lbl.var sy)
      | MEqConst (t, _) ->
        (match t.trm with
         | Term.Const _ -> with_lbls mf []
         | _ -> with_lbls mf (lbls_of_term t))
      | MPredicate (e, ts) ->
        (match Map.find m e with
         | Some (vars, lbls) ->
           (*print_endline "case 1";*)
           let lbls = Lbl.substs
               (Map.of_alist_exn (module String) (List.zip_exn vars ts)) lbls in
           let extra_fvs = List.filter fvs
               ~f:(fun v -> not (List.mem lbls (LVar v) ~equal:Lbl.equal)) in
           with_lbls mf ((List.map ~f:Lbl.var extra_fvs) @ lbls)
         | None ->
           (*print_endline "case 2";
           print_endline (Int.to_string (List.length ts));
             print_endline (Int.to_string (List.length (List.filter ~f:(fun t -> not (Term.is_const t)) ts)));*)
           with_lbls mf (lbls_of_terms (List.filter ~f:(fun t -> not (Term.is_const t)) ts)))
      | MExists (x, tt, b, f) ->
        map1 (fvs @ [x]) m f (fun f p -> MExists (x, tt, b, p f)) (Lbl.quantify_list ~forall:false x)
      | MForall (x, tt, b, f) ->
        map1 (fvs @ [x]) m f (fun f p -> MForall (x, tt, b, p f)) (Lbl.quantify_list ~forall:true x)
      | MNeg f ->
        map1 fvs m f (fun f p -> MNeg (p f)) (List.map ~f:Lbl.exquant)
      | MAnd (s, fs, inf) ->
        mapn fvs m fs (fun fs p -> MAnd (s, List.map ~f:p fs, inf)) id
      | MOr (s, fs, inf) ->
        mapn fvs m fs (fun fs p -> MOr (s, List.map ~f:p fs, inf)) id
      | MImp (s, f, g, inf) ->
        map2 fvs m f g (fun f g p -> MImp (s, p f, p g, inf)) imp
      | MPrev (i, f, inf) ->
        map1 fvs m f (fun f p -> MPrev (i, p f, inf)) id
      | MNext (i, f, inf) ->
        map1 fvs m f (fun f p -> MNext (i, p f, inf)) id
      | MENext (i, t_opt, f, v) ->
        map1 fvs m f (fun f p -> MENext (i, t_opt, p f, v)) id
      | MOnce (i, f, inf) ->
        map1 fvs m f (fun f p -> MOnce (i, p f, inf)) id
      | MEventually (i, f, inf) ->
        map1 fvs m f (fun f p -> MEventually (i, p f, inf)) id
      | MEEventually (i, t_opt, f, v) ->
        map1 fvs m f (fun f p -> MEEventually (i, t_opt, p f, v)) id
      | MHistorically (i, f, inf) ->
        map1 fvs m f (fun f p -> MHistorically (i, p f, inf)) id
      | MAlways (i, f, inf) ->
        map1 fvs m f (fun f p -> MAlways (i, p f, inf)) id
      | MEAlways (i, t_opt, f, inf) ->
        map1 fvs m f (fun f p -> MEAlways (i, t_opt, p f, inf)) id
      | MSince (s, i, f, g, inf) ->
        map2 fvs m f g (fun f g p -> MSince (s, i, p f, p g, inf)) id2
      | MUntil (i, f, g, inf) ->
        map2 fvs m f g (fun f g p -> MUntil (i, p f, p g, inf)) id2
      | MEUntil (s, i, t_opt, f, g, v) ->
        map2 fvs m f g (fun f g p -> MEUntil (s, i, t_opt, p f, p g, v)) id2 
      | MLabel (s, f) ->
        map1 fvs m f (fun f p -> MLabel (s, p f)) id
      | MLet (e, vars, f, g) ->
        let f = set_lbls ~fvs:vars ~m f in
        let m = Map.update m e (fun _ -> (vars, f.lbls)) in
        map1 fvs m g (fun g p -> MLet (e, vars, f, p g)) id
    in
    (*debug (Printf.sprintf "set_lbls(%s)=%s" (to_string mf) (to_string mf'));*)
    mf'

  let set_make mf filter =
    set_lbls (set_events (make mf filter))

  let init (tf: Tformula.t) =
    let rec aux (tf: Tformula.t) =
      let r = match tf.form with
      | Tformula.TT -> MTT
      | FF -> MFF
      | EqConst (x, c) -> MEqConst (Sig.normalize (Tterm.to_term x), c)
      | Predicate (r, trms) -> MPredicate (r, Sig.normalize_list (Tterm.to_terms trms))
      | Predicate' (_, _, f) | Let' (_, _, _, _, f) -> aux f
      | Agg ((s, tt), op, x, y, f) ->
         let op_fun = Aggregation.eval op tt in
         MAgg (s, op, op_fun, Sig.normalize (Tterm.to_term x), List.map ~f:fst y, make (aux f) Filter.tt)
      | Top (s, op, x, y, f) ->
         let op_fun = Sig.tfunc op in
         MTop (List.map ~f:fst s, op, op_fun, Sig.normalize_list (Tterm.to_terms x),
               List.map ~f:fst y, make (aux f) Filter.tt)
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
      | Next (i, f) -> MENext (i, None, make (aux f) f.info.filter, Valuation.empty)
      | Once (i, f) -> MOnce (i, make (aux f) f.info.filter, Once.init i true)
      | Eventually (i, f) when Enftype.is_only_observable tf.info.enftype ->
         MEventually (i, make (aux f) f.info.filter, Eventually.init i true)
      | Eventually (i, f) -> MEEventually (i, None, make (aux f) f.info.filter, Valuation.empty)
      | Historically (i, f) -> MHistorically (i, make (aux f) f.info.filter, Once.init i false)
      | Always (i, f) when Enftype.is_only_observable tf.info.enftype ->
         MAlways (i, make (aux f) f.info.filter, Eventually.init i false)
      | Always (i, f) -> MEAlways (i, None, make (aux f) f.info.filter, Valuation.empty)
      | Since (s, i, f, g) ->
         MSince (s, i, make (aux f) f.info.filter, make (aux g) g.info.filter, Since.init i)
      | Until (_, i, f, g) when Enftype.is_only_observable tf.info.enftype ->
         MUntil (i, make (aux f) f.info.filter, make (aux g) g.info.filter, Until.init i)
      | Until (s, i, f, g) ->
         MEUntil (s, i, None, make (aux f) f.info.filter, make (aux g) g.info.filter, Valuation.empty)
      | Type (f, _) -> aux f
      | Label (s, f) -> MLabel (s, make (aux f) f.info.filter)
      | Let (e, _, vars, f, g) ->
        let vars = vars |> List.map ~f:fst |> List.map ~f:fst in
        MLet (e, vars, make (aux f) f.info.filter, make (aux g) f.info.filter)
      in
      r
    in
    set_make (aux tf) tf.info.filter

end

module IFormula = struct

  include MFormulaMake(ITerm.IntVar)(ITerm)

  let set_make mf filter lbls =
    let mf = make mf filter in
    set_events { mf with lbls }

  let _tp     = set_make (MPredicate (Sig.tilde_tp_event_name, [])) Filter.tt []
  let _neg_tp = set_make (MNeg _tp) Filter.tt []
  let _tt     = set_make MTT Filter.tt []
  let _ff     = set_make MFF Filter.tt []
  let singleton_tp = Set.singleton (module String) Sig.tilde_tp_event_name

  let rec init (mf: MFormula.t) : t * (string * t) list =
    let rec pull_lets (mf: MFormula.t) =
      match mf.mf with
      | MFormula.MLet (e, vars, f, g) -> let g, glets = pull_lets g in g, (e, f) :: glets
      | _ -> mf, [] in
    let mf, lets = pull_lets mf in
    let rec aux (mf: MFormula.t)  = 
      let mf_core = match mf.mf with
        | MFormula.MTT -> MTT
        | MFF -> MFF
        | MEqConst (t, d) -> MEqConst (ITerm.init mf.lbls t, d)
        | MPredicate (r, ts) -> MPredicate (r, ITerm.init_multiple mf.lbls ts)
        | MAgg (s, op, f_op, x, y, f) ->
          MAgg (ITerm.of_var mf.lbls s, op, f_op, x, ITerm.of_vars f.lbls y, aux f)
        | MTop (s, op, f_op, x, y, f) ->
          MTop (ITerm.of_vars mf.lbls s, op, f_op, x, ITerm.of_vars f.lbls y, aux f)
        | MNeg f -> MNeg (aux f)
        | MAnd (s, fs, inf) -> MAnd (s, List.map ~f:aux fs, inf)
        | MOr (s, fs, inf) -> MOr (s, List.map ~f:aux fs, inf)
        | MImp (s, f, g, inf) -> MImp (s, aux f, aux g, inf)
        | MExists (x, tt, b, f) -> MExists (ITerm.of_var mf.lbls x, tt, b, aux f)
        | MForall (x, tt, b, f) -> MForall (ITerm.of_var mf.lbls x, tt, b, aux f)
        | MPrev (i, f, inf) -> MPrev (i, aux f, inf)
        | MNext (i, f, inf) -> MNext (i, aux f, inf)
        | MENext (i, ts, f, vv) -> MENext (i, ts, aux f, vv)
        | MOnce (i, f, inf) -> MOnce (i, aux f, inf)
        | MEventually (i, f, inf) -> MEventually (i, aux f, inf)
        | MEEventually (i, ts, f, vv) -> MEEventually (i, ts, aux f, vv)
        | MHistorically (i, f, inf) -> MHistorically (i, aux f, inf)
        | MAlways (i, f, inf) -> MAlways (i, aux f, inf)
        | MEAlways (i, ts, f, vv) -> MEAlways (i, ts, aux f, vv)
        | MSince (s, i, f, g, inf) -> MSince (s, i, aux f, aux g, inf)
        | MUntil (i, f, g, inf) -> MUntil (i, aux f, aux g, inf)
        | MEUntil (s, i, ts, f, g, vv) -> MEUntil (s, i, ts, aux f, aux g, vv)
        | MLabel (s, f) -> MLabel (s, aux f)
        | MLet (e, vars, f, g) -> MLet (e, ITerm.of_vars mf.lbls vars, aux f, aux g) in
      { mf = mf_core;
        filter = mf.filter;
        events = mf.events;
        obligations = mf.obligations;
        hash = core_hash mf_core;
        lbls = mf.lbls;
        projs = mf.projs }
    in aux mf, List.map ~f:(fun (e, mf) -> (e, aux mf)) lets

    let map_mf mf filter ?(exquant=false) ?(new_events=None) f =
      let lbls = if exquant then List.map ~f:Lbl.exquant mf.lbls else mf.lbls in
      let mf_mf = f mf (set_projs lbls) in
      { mf          = mf_mf;
        filter;
        events      = Option.map2 mf.events new_events Set.union;
        obligations = mf.obligations;
        hash        = core_hash mf_mf;
        lbls;
        projs       = [] }
    
  let map2_mf mf1 mf2 filter ?(new_events=None) f =
    let lbls = Etc.dedup ~equal:Lbl.equal (mf1.lbls @ mf2.lbls) in
    let mf_mf = f mf1 mf2 (set_projs lbls) in
    { mf          = mf_mf;
      filter;
      events      = Option.map2 (Option.map2 mf1.events mf2.events ~f:Set.union) new_events ~f:Set.union;
      obligations = Option.map2 mf1.obligations mf2.obligations ~f:Set.union;
      hash        = core_hash mf_mf;
      lbls;
      projs       = [] }

  let mapn_mf mfs filter ?(new_events=None) f =
    let lbls = Etc.dedup ~equal:Lbl.equal (List.concat_map mfs ~f:(fun mf -> mf.lbls)) in
    let mf_mf = f mfs (set_projs lbls) in
    { mf          = mf_mf;
      filter;
      events      = Option.map2 (
          Option.map (Option.all (List.map ~f:(fun mf -> mf.events) mfs))
            ~f:(Set.union_list (module String)))
          new_events ~f:Set.union;
      obligations = Option.map (Option.all (List.map ~f:(fun mf -> mf.obligations) mfs))
                      ~f:(Set.union_list (module Int));
      hash        = core_hash mf_mf;
      lbls;
      projs       = [] }

  let unproj (mf: t) (v: Valuation.t) : Valuation.t =
    let f v = Option.map ~f:fst (List.findi mf.projs ~f:(fun _ -> Int.equal v)) in
    Valuation.map_keys v ~f

  let rec apply_valuation ?(parent_lbls=[]) (v: Valuation.t) (mf: t) : t =
    if Valuation.is_empty v then mf else
      let lbls = List.filter_map ~f:(Sig.eval_lbl_to_lbl mf.lbls v) mf.lbls in
      let r = apply_valuation ~parent_lbls:lbls v in
      let mr mf = apply_valuation ~parent_lbls:lbls (unproj mf v) mf in
      let av_term = Sig.eval mf.lbls in
      let spec t = Pdt.specialize_partial mf.lbls v t in
      let av_buf2 b = Buf2.map (TS.map spec) (TS.map spec) b in
      let av_bufn b = Bufn.map (TS.map spec) b in
      let av_buft b = Buft.map (spec) (fun t -> t) b in
      let av_buf2t b = Buf2t.map (spec) (spec) (fun t -> t) b in
      let av_pdt p = spec p in
      debug (Printf.sprintf "apply_valuation (%s, %s)..."
               (Valuation.to_string v) (to_string mf));
      let mf_ = match mf.mf with
        | MTT -> MTT
        | MFF -> MFF
        | MEqConst (trm, d) ->
          (match (Sig.eval mf.lbls v trm).trm with
           | Const d' when Dom.equal d d' -> MTT
           | Const _ -> MFF
           | _ -> MEqConst (trm, d))
        | MPredicate (e, t) -> MPredicate (e, List.map t ~f:(av_term v))
        | MAgg (s, op, op_fun, x, y, f) -> MAgg (s, op, op_fun, x, y, mr f)
        | MTop (s, op, op_fun, x, y, f) -> MTop (s, op, op_fun, x, y, mr f)
        | MNeg f -> MNeg (r f)
        | MAnd (s, fs, bi) -> MAnd (s, List.map ~f:mr fs, av_bufn bi)
        | MOr (s, fs, bi) -> MOr (s, List.map ~f:mr fs, av_bufn bi)
        | MImp (s, f, g, bi) -> MImp (s, mr f, mr g, av_buf2 bi)
        | MExists (x, tt, b, f) -> MExists (x, tt, b, r f)
        | MForall (x, tt, b, f) -> MForall (x, tt, b, r f)
        | MPrev (i, f, pi) -> MPrev (i, r f, Prev.map spec pi)
        | MNext (i, f, si) -> MNext (i, r f, si)
        | MENext (i, ts, f, vv) -> MENext (i, ts, r f, Valuation.extend v vv)
        | MOnce (i, f, oi) -> MOnce (i, r f, Once.map spec spec oi)
        | MEventually (i, f, oi) -> MEventually (i, r f, Eventually.map spec spec oi)
        | MEEventually (i, ts, f, vv) -> MEEventually (i, ts, r f, Valuation.extend v vv)
        | MHistorically (i, f, oi) -> MHistorically (i, r f, Once.map spec spec oi)
        | MAlways (i, f, ai) -> MAlways (i, r f, Eventually.map spec spec ai)
        | MEAlways (i, ts, f, vv) -> MEAlways (i, ts, r f, Valuation.extend v vv)
        | MSince (s, i, f, g, si) -> MSince (s, i, mr f, mr g, Since.map spec spec si)
        | MUntil (i, f, g, ui) -> MUntil (i, mr f, mr g, Until.map spec spec ui)
        | MEUntil (s, i, ts, f, g, vv) -> MEUntil (s, i, ts, mr f, mr g, Valuation.extend v vv)
        | MLabel (s, f) -> MLabel (s, r f)
        | MLet (e, vars, f, g) -> MLet (e, vars, f, mr g)
      in
      let r = set_projs parent_lbls (set_make mf_ mf.filter lbls) in
      debug (Printf.sprintf "apply_valuation (%s, %s) = %s"
               (Valuation.to_string v) (to_string mf) (to_string r));
      r

end

(* Future obligations *)

module FObligation = struct

  include IFormula

  module T = struct

    type kind =
      | FFormula of IFormula.t * int * Valuation.t
      | FInterval of timestamp * Interval.t * IFormula.t * int * Valuation.t
      | FUntil of timestamp * Side.t * Interval.t * IFormula.t * IFormula.t * int * Valuation.t
      | FAlways of timestamp * Interval.t * IFormula.t * int * Valuation.t
      | FEventually of timestamp * Interval.t * IFormula.t * int * Valuation.t

    type t = kind * Valuation.t * Polarity.t

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

    let compare_kind k1 k2 = match k1, k2 with
      | FFormula (_, h, v), FFormula (_, h', v') ->
         Etc.lexicographic2 Int.compare Valuation.compare (h, v) (h', v')
      | FFormula _, _ -> 1
      | FInterval _, FFormula _ -> -1
      | FInterval (ts, i, _, h, v), FInterval (ts', i', _, h', v') ->
         Etc.lexicographic4
           Time.compare Interval.compare Int.compare Valuation.compare
           (ts, i, h, v) (ts', i', h', v')
      | FInterval _, _ -> 1
      | FAlways _, FFormula _ | FAlways _, FInterval _ -> -1
      | FAlways (ts, i, _, h, v), FAlways (ts', i', _, h', v') ->
         Etc.lexicographic4 Time.compare Interval.compare Int.compare Valuation.compare
           (ts, i, h, v) (ts', i', h', v')
      | FAlways _, _ -> 1
      | FEventually _, FFormula _ | FEventually _, FInterval _ | FEventually _, FAlways _ -> -1
      | FEventually (ts, i, _, h, v), FEventually (ts', i', _, h', v') ->
         Etc.lexicographic4 Time.compare Interval.compare Int.compare Valuation.compare
           (ts, i, h, v) (ts', i', h', v')
      | FEventually _, FUntil _ -> 1
      | FUntil (ts, s, i, _, _, h, v), FUntil (ts', s', i', _, _, h', v') ->
         Etc.lexicographic5 Time.compare Side.compare Interval.compare Int.compare Valuation.compare
           (ts, s, i, h, v) (ts', s', i', h', v')
      | FUntil _, _ -> -1

    let compare =
      Etc.lexicographic3 compare_kind Valuation.compare Polarity.compare

    let sexp_of_t _ = Sexp.Atom "FObligation"
        
    let corresp_proof tp pol _ = function
      | FFormula _ -> true
      | FInterval _ when Polarity.equal pol POS -> true
      | FInterval (_, i, _, _, _) -> false
      | FUntil _ when Polarity.equal pol POS -> true
      | FUntil _ -> false
      | FEventually _ when Polarity.equal pol POS -> true
      | FEventually _ -> false
      | FAlways _ when Polarity.equal pol POS -> true
      | FAlways _ -> false

    let kind_to_string = function
      | FFormula (f, h, v) ->
         Printf.sprintf "FFormula(%s, %d, %s)" (to_string f) h (Valuation.to_string v)
      | FInterval (ts, i, mf, h, v) ->
         Printf.sprintf "FInterval(%s, %s, %s, %d, %s)"
           (Time.to_string ts) (Interval.to_string i) (to_string mf)
           h (Valuation.to_string v)
      | FUntil (ts, s, i, mf, mg, h, v) ->
         Printf.sprintf "FUntil(%s, %s, %s, %s, %s, %d, %s)"
           (Time.to_string ts) (Side.to_string s)
           (Interval.to_string i) (to_string mf) (to_string mg) h (Valuation.to_string v)
      | FAlways (ts, i, mf, h, v) ->
         Printf.sprintf "FAlways(%s, %s, %s, %d, %s)"
           (Time.to_string ts) (Interval.to_string i) (to_string mf)
           h (Valuation.to_string v)
      | FEventually (ts, i, mf, h, v) ->
         Printf.sprintf "FEventually(%s, %s, %s, %d, %s)"
           (Time.to_string ts) (Interval.to_string i) (to_string mf)
           h (Valuation.to_string v)

    let to_string ((kind, valuation, pol) : t) =
      Printf.sprintf "Kind: %s; " (kind_to_string kind) ^
        Printf.sprintf "Valuation: %s; " (Valuation.to_string valuation) ^
          Printf.sprintf "Polarity: %s" (Polarity.to_string pol)

    let eval_kind ts' _ k =
      let tp_filter mf = 
        Filter.conj mf.filter (Filter.An Sig.tilde_tp_event_name) in
      match k with
      | FFormula (mf, _, _) -> mf
      | FInterval (ts, i, mf, _, v) ->
         if Interval.diff_is_in ts ts' i then
           map_mf
             (map_mf mf Filter.tt ~new_events:(Some singleton_tp)
                (fun mf p -> (MAnd (L, [_tp; p mf], empty_nop_info 2))))
             Filter.tt
             (fun mf p -> MEUntil (R, i, Some ts, _neg_tp, p mf, v))
         else
           _tt
      | FUntil (ts, side, i, mf1, mf2, _, v) ->
         if not (Interval.diff_right_of ts ts' i) then
           let mf1' = match mf1.mf with
             | MImp (_, mf11, mf12, _) when IFormula.equal _tp mf11 -> mf12
             | _ -> mf1 in
           let mf2' = match mf2.mf with
             | MAnd (_, [mf21; mf22], _) when IFormula.equal _tp mf21 -> mf22
             | _ -> mf2 in
           map2_mf
             (if IFormula.equal mf1' _neg_tp then
                _neg_tp
              else
                map_mf mf1' (tp_filter mf1') ~new_events:(Some singleton_tp)
                  (fun mf p -> MImp (R, _tp, p mf, empty_binop_info)))
             (map_mf mf2' Filter.tt ~new_events:(Some singleton_tp)
                (fun mf p -> MAnd (R, [_tp; p mf], empty_nop_info 2)))
             Filter.tt
             (fun mf1 mf2 p -> MEUntil (side, i, Some ts, p mf1, p mf2, v))
         else
           _ff
      | FAlways (ts, i, mf, _, v) ->
         if not (Interval.diff_right_of ts ts' i) then
           let mf' = match mf.mf with
             | MImp (_, mf1, mf2, _) when IFormula.equal _tp mf1 -> mf2
             | _ -> mf in
           map_mf
             (map_mf mf' (tp_filter mf') ~new_events:(Some singleton_tp)
                (fun mf p -> MImp (R, _tp, p mf, empty_binop_info)))
             Filter.tt
             (fun mf p -> MEAlways (i, Some ts, p mf, v))
         else
           _tt
      | FEventually (ts, i, mf, _, v) ->
         if not (Interval.diff_right_of ts ts' i) then
           let mf' = match mf.mf with
             | MAnd (_, [mf1; mf2], _) when IFormula.equal _tp mf1 -> mf2
             | _ -> mf in
           map_mf
             (map_mf mf' Filter.tt ~new_events:(Some singleton_tp)
                (fun mf p -> MAnd (L, [_tp; p mf], empty_nop_info 2)))
             Filter.tt
             (fun mf p -> MEEventually (i, Some ts, p mf, v))
         else
           _ff

    let eval ts tp (k, v, pol) =
      let mf = apply_valuation v (eval_kind ts tp k) in
      let mf = match pol with
        | Polarity.POS -> mf
        | NEG -> match mf.mf with
          | MNeg mf -> mf
          | _       -> map_mf mf Filter.tt (fun mf p -> MNeg (p mf)) ~exquant:true in
      debug (Printf.sprintf "FObligation.eval (ts=%s, tp=%d, k=%s, v=%s, pol=%s) = %s"
               (Time.to_string ts) tp (kind_to_string k) (Valuation.to_string v) (Polarity.to_string pol)
               (IFormula.to_string mf));
      mf


    let accepts_empty = function
      | (FFormula _, _, pol) -> Polarity.equal pol NEG
      | (FInterval _, _, pol) -> Polarity.equal pol NEG
      | (FUntil _, _, pol) -> Polarity.equal pol NEG
      | (FAlways _, _, pol) -> Polarity.equal pol POS
      | (FEventually _, _, pol) -> Polarity.equal pol NEG

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

(* Helper functions *)

let relevant_fobligs fobligs test h vv pol =
  let f (k, _, pol') =
    let (h', v') = FObligation.hv k in
    h = h' && Valuation.equal v' vv && Polarity.equal pol pol' && test k
  in Set.elements (Set.filter fobligs ~f)

let expls_approx test tp pol (lbls: Lbl.t list) fobligs h vv =
  let f (k, v, _) =  
    let p = FObligation.corresp_proof tp pol None k in
    let p' = proof_false pol in
    Pdt.from_valuation lbls v p p' in
  List.map (relevant_fobligs fobligs test h vv pol) ~f

let apply_ands projs (pdts: Expl.t list) =
  Pdt.applyN_reduce Bool.equal (List.fold_left ~init:true ~f:(&&)) (List.zip_exn projs pdts)

let apply_ors projs (pdts: Expl.t list) =
  Pdt.applyN_reduce Bool.equal (List.fold_left ~init:false ~f:(||)) (List.zip_exn projs pdts)

let apply_imp proj1 proj2 pdt1 pdt2 =
  Pdt.apply2_reduce Bool.equal (fun p1 p2 -> (not p1) || p2) proj1 proj2 pdt1 pdt2

(* Approximation functions (except past operators) *)

let approximate_neg pdt =
  Pdt.apply1_reduce Bool.equal (fun b -> not b) id pdt
  
let approximate_and projs aexpl_list = 
  apply_ands projs aexpl_list

let approximate_or projs aexpl_list = 
  apply_ors projs aexpl_list

let approximate_imp proj1 proj2 (aexpl1: Expl.t) (aexpl2: Expl.t) =
  apply_imp proj1 proj2 aexpl1 aexpl2

let approximate_enext (lbls: Lbl.t list) (fobligs: FObligations.t) (h, vv) tp pol_opt =
  let expls = expls_approx FObligation.is_finterval tp (Polarity.value pol_opt) lbls fobligs h vv in
  Pdt.applyN_reduce Bool.equal (List.fold ~init:false ~f:(||)) (List.map expls ~f:(fun expl -> (id, expl)))

let approximate_eventually (lbls: Lbl.t list) (aexpl: Expl.t) (fobligs: FObligations.t) (i: Interval.t) (h_opt: (int * Valuation.t) option) (tp: timepoint) (pol: Polarity.t option) =
  let aexpl_new = aexpl in
  let pol = Polarity.value pol in
  let expls = match h_opt with
    | None -> []
    | Some (h, vv) -> expls_approx FObligation.is_feventually tp pol lbls fobligs h vv in
  let aexpl_next = Pdt.applyN_reduce Bool.equal (List.fold ~init:false ~f:(||)) (List.map expls ~f:(fun expl -> (id, expl))) in
  Pdt.apply2_reduce Bool.equal 
    (fun p1 p2 -> Eventually.approximate tp i (Polarity.equal pol POS) p1 p2)
    id id aexpl_next aexpl_new

let approximate_always (lbls: Lbl.t list) aexpl (fobligs: FObligations.t) i h_opt tp (pol: Polarity.t option) =
  let aexpl_new = aexpl in
  let pol = Polarity.value pol in
  let expls = match h_opt with
    | None -> []
    | Some (h, vv) -> expls_approx FObligation.is_falways tp pol lbls fobligs h vv in
  let aexpl_next = Pdt.applyN_reduce Bool.equal (List.fold ~init:false ~f:(||)) (List.map expls ~f:(fun expl -> (id, expl))) in
  Pdt.apply2_reduce Bool.equal 
    (fun p1 p2 -> Eventually.approximate_always tp i (Polarity.equal pol POS) p1 p2)
    id id aexpl_next aexpl_new

let approximate_until (lbls: Lbl.t list) proj1 proj2 aexpl1 aexpl2 (fobligs: FObligations.t) i h_opt tp (pol: Polarity.t option) =
  let aexpl_new1 = aexpl1 in
  let aexpl_new2 = aexpl2 in
  let pol = Polarity.value pol in
  let expls = match h_opt with
    | None -> []
    | Some (h, vv) -> expls_approx FObligation.is_funtil tp pol lbls fobligs h vv in
  let aexpl_next = Pdt.applyN_reduce Bool.equal (List.fold ~init:false ~f:(||)) (List.map expls ~f:(fun expl -> (id, expl))) in
  Pdt.apply3_reduce Bool.equal 
    (fun p1 p2 p3 -> Until.approximate tp i (Polarity.equal pol POS) p1 p2 p3)
    proj1 proj2 id aexpl_new1 aexpl_new2 aexpl_next

(* Update functions (non-temporal operators) *)

let update_neg (expls: Expl.t TS.t list) : Expl.t TS.t list =
  List.map expls ~f:(TS.map approximate_neg)

let update_and projs (expls_list: Expl.t TS.t list list) (bufn: MFormula.nop_info) : Expl.t TS.t list * MFormula.nop_info =
  Bufn.take (TS.map_list (apply_ands projs)) (Bufn.add expls_list bufn)

let update_or projs (expls_list: Expl.t TS.t list list) (bufn: MFormula.nop_info) : Expl.t TS.t list * MFormula.nop_info =
  Bufn.take (TS.map_list (apply_ors projs)) (Bufn.add expls_list bufn) 

let update_imp proj1 proj2 (expls1: Expl.t TS.t list) (expls2: Expl.t TS.t list) (buf2: MFormula.binop_info) : Expl.t TS.t list * MFormula.binop_info =
  Buf2.take (TS.map2 (apply_imp proj1 proj2)) (Buf2.add expls1 expls2 buf2)

