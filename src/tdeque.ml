open MFOTL_lib

open MFOTL_lib.Etc

type t = Time.t Fdeque.t [@@deriving compare, sexp_of, hash, equal]

let empty : t = Fdeque.empty

let to_string (q: t) = list_to_string "" (fun _ -> Time.to_string) (Fdeque.to_list q)

let is_empty (q: t) : bool = Fdeque.is_empty q

let enqueue_back (q: t) (ts: timestamp) : t =
  Fdeque.enqueue_back q ts

let rec split (f: timestamp -> timestamp -> bool) (q: t) (q': t) (ts: timestamp) : t * t =
  match Fdeque.dequeue_front q with
  | None -> q, q'
  | Some (ts', t) when f ts' ts -> split f t (enqueue_back q' ts') ts 
  | Some _ -> q, q'

(* Clean the queue q from all elements with timestamps outside (= to the left) of ts - i *)
let clean (f: timestamp -> timestamp -> bool) (q: t) (ts: timestamp) : t =
  let rec aux q1 =
    match Fdeque.dequeue_front q1 with
    | None -> q1
    | Some (ts', t) when f ts' ts -> aux t
    | Some _  -> q1
  in aux q

(* Given two queues q and q', returns updated states for q and q' such that for each element a in q:
   * if a has a timestamp in ts - i, a stays in q
   * if a has a timestamp outside (= to the left) of ts - i, a is enqueued into q' *)
let rec split_left (q: t) (q': t) (ts: timestamp) (i: Interval.t) : t * t =
  split (fun ts' ts -> Interval.diff_right_of ts' ts i) q q' ts 

(* Clean the queue q from all elements with timestamps outside (= to the left) of ts - i *)
let clean_left (q: t) (ts: timestamp) (i: Interval.t) : t =
  clean (fun ts' ts -> Interval.diff_right_of ts' ts i) q ts

(* Given two queues q and q', returns updated states for q and q' such that for each element a in q:
   * if a has a timestamp in ts + i, a stays in q
   * if a has a timestamp outside (= to the left) of ts + i, a is enqueued into q' *)
let rec split_right (q: t) (q': t) (ts: timestamp) (i: Interval.t) : t * t =
  split (fun ts' ts -> Interval.diff_left_of ts ts' i) q q' ts   

(* Clean the queue q from all elements with timestamps outside (= to the left) of ts - i *)
let clean_right (q: t) (ts: timestamp) (i: Interval.t) : t =
  clean (fun ts' ts -> Interval.diff_left_of ts ts' i) q ts 

let rec compute_until (q: t) (q': t) : bool =
  match Fdeque.dequeue_front q, Fdeque.dequeue_front q' with
  | Some (ts, _), Some (ts', _) when ts < ts' -> false
  | _           , Some _                      -> true
  | _           , _                           -> false
  
