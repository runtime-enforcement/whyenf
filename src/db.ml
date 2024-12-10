open Base

module Dom = MFOTL_lib.Dom
module Etc = MFOTL_lib.Etc
module Time = MFOTL_lib.Time

module Event = struct

  module T = struct

    type t = string * Dom.t list [@@deriving compare, sexp_of]

    (*let equal (name1, ds1) (name2, ds2) =
      String.equal name1 name2 &&
        (match (List.for_all2 ds1 ds2 ~f:(fun d1 d2 -> Dom.equal d1 d2)) with
         | Ok b -> b
         | Unequal_lengths -> false)*)

    let to_string (name, ds) = Printf.sprintf "%s(%s)" name (Dom.list_to_string ds)

    let to_json (name, ds) =
      Printf.sprintf "{ \"name\": \"%s\", \"args\": [ %s ] }"
        name
        (String.concat ~sep:", "
           (List.map2_exn (Sig.vars_of_pred name) ds ~f:(fun x d ->
                Printf.sprintf "{ \"var\": \"%s\", \"value\": \"%s\" }" x (Dom.to_string d))))

    let name = fst

  end

  include T
  include Comparable.Make(T)

  let _tp = (Sig.tilde_tp_event_name, [])
  let _tick = (Sig.tick_event_name, [])

end

type ev_set = (Event.t, Event.comparator_witness) Set.t

type t = {
    events : ev_set;
    trace  : (String.t, String.comparator_witness) Set.t
  }

let events db = db.events

let mem_trace db e = Set.mem db.trace e

let equal db1 db2 = Set.equal db1.events db2.events && Set.equal db1.trace db2.trace

let set_trace db =
  { db with trace = Set.map (module String) db.events ~f:Event.name }

let create evtl = {
    events = Set.of_list (module Event) evtl;
    trace  = Set.of_list (module String) (List.map evtl ~f:Event.name)
  }

let diff db1 db2 =
  set_trace { db1 with events = Set.diff db1.events db2.events } 
  
let union db1 db2 = {
    events = Set.union db1.events db2.events;
    trace  = Set.union db1.trace db2.trace
  }

let empty = { events = Set.empty (module Event);
              trace = Set.empty (module String) }

let singleton ev = create [ev]

let mem db = Set.mem db.events
let is_empty db = Set.is_empty db.events
let remove db x = set_trace { db with events = Set.remove db.events x }
let size db = Set.length db.events
let filter db ~f = set_trace { db with events = Set.filter db.events ~f }

let event name consts =
  let pred_sig = Hashtbl.find_exn Sig.table name in
  if Sig.arity pred_sig = List.length consts then
    (name, List.map2_exn (Sig.arg_ttts pred_sig) consts
             ~f:(fun tc c -> match snd tc with
                             | TConst TInt -> Dom.Int (Int.of_string c)
                             | TConst TStr -> Str c
                             | TConst TFloat -> Float (Float.of_string c)
                             | ttt -> raise (Invalid_argument
                                               (Printf.sprintf "cannot create event with arg type %s"
                                                  (Ctxt.ttt_to_string ttt)))))
  else raise (Invalid_argument
                (Printf.sprintf "predicate %s has arity %d" name (Sig.arity pred_sig)))

let add_event db evt = set_trace { db with events = Set.add db.events evt }

let is_tick db =
  mem db Event._tick && size db = 1

let ev_set_to_string events =
  Etc.string_list_to_string (List.map ~f:Event.to_string (Set.elements events))

let to_string db = ev_set_to_string db.events

let to_json db =
  "[ " ^ (String.concat ~sep:", "
            (List.rev(Set.fold db.events ~init:[] ~f:(fun acc evt ->
                          Event.to_json evt :: acc)))) ^ " ]"

let retrieve_external name =
  let tts = List.map ~f:Ctxt.unconst (Sig.arg_ttts_of_pred name) in
  let dom_list_list = Funcs.Python.retrieve_db name tts in
  let events: Event.t list = List.map dom_list_list ~f:(fun dom_list -> (name, dom_list)) in
  create events

let retrieve_builtin ts tp = function
  | name when String.equal name Sig.tp_event_name -> create [("TP", [Int tp])]
  | name when String.equal name Sig.ts_event_name -> create [("TS", [Int (Time.to_int ts)])]
  | name -> raise (Invalid_argument (Printf.sprintf "builtin %s does not exist" name)) 

