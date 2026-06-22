open Base

module Sup = struct

  type t = Abs | Itl | TSup | Sup | Obs | NonObs [@@deriving compare, sexp_of, hash, equal]

  let value = function
    | NonObs -> 0
    | Obs    -> 1
    | Sup    -> 2
    | TSup   -> 3
    | Itl    -> 4
    | Abs    -> 5

  let to_string = function
    | NonObs -> "NonObs"
    | Obs    -> "Obs"
    | Sup    -> "Sup"
    | TSup   -> "TSup"
    | Itl    -> "Itl"
    | Abs    -> "Abs"

end

module Cau = struct

  type t = Itl | TCau | Cau | NonCau [@@deriving compare, sexp_of, hash, equal]

  let value = function
    | NonCau -> 0
    | Cau    -> 1
    | TCau   -> 2
    | Itl    -> 3

  let to_string = function
    | NonCau -> "NonCau"
    | Cau    -> "Cau"
    | TCau   -> "TCau"
    | Itl    -> "Itl"

end

module Suppressability  = Lattice.Linear(Sup)
module Causability      = Lattice.Linear(Cau)
module SuppressabilityL = Lattice.Make(Suppressability)
module CausabilityL     = Lattice.Make(Causability)

include Lattice.Make2(Suppressability)(Causability)

let bot           = (Sup.NonObs, Cau.NonCau)
let cau           = (Sup.Obs,    Cau.Cau)
let sup           = (Sup.Sup,    Cau.NonCau)
let causup        = (Sup.Sup,    Cau.Cau)
let caubot        = (Sup.NonObs, Cau.Cau)
let obs           = (Sup.Obs,    Cau.NonCau)
let abs           = (Sup.Abs,    Cau.NonCau)
let itl           = (Sup.Itl,    Cau.Itl)

let causable      = (Sup.NonObs, Cau.Cau)
let suppressable  = (Sup.Sup,    Cau.NonCau)
let tcausable     = (Sup.NonObs, Cau.TCau)
let tsuppressable = (Sup.TSup,   Cau.NonCau)

let get_sup (a, _) = a
let get_cau (_, b) = b

let neg_sup = function
  | Sup.Sup -> Cau.Cau
  | _       -> NonCau

let neg_cau a b = match a, b with
  | Cau.Cau, _          -> Sup.Sup
  | NonCau , Sup.NonObs -> NonObs
  | _      , _          -> Obs

let neg (a, b) : t = (neg_cau b a, neg_sup a)

let is_causable        a = CausabilityL.(geq (get_cau a) Cau)
let is_suppressable    a = SuppressabilityL.(geq (get_sup a) Sup)
let is_observable      a = SuppressabilityL.(geq (get_sup a) Obs)
let is_only_observable a = not (is_causable a) && not (is_suppressable a) && is_observable a
let is_absent          a = SuppressabilityL.(geq (get_sup a) Abs)
let is_internal        a = Cau.(equal (get_cau a) Itl) && Sup.(equal (get_sup a) Itl)
let is_transparent     a =
  (if is_causable a then CausabilityL.(geq (get_cau a) TCau) else true)
  && (if is_suppressable a then SuppressabilityL.(geq (get_sup a) TSup) else true)
  && (is_causable a || is_suppressable a)

let to_string ((a, b) as d) =
  match a, b with
  | Sup.NonObs, Cau.NonCau -> "Bot"
  | Sup.Obs   , Cau.NonCau -> "Obs"
  | Sup.Sup   , Cau.NonCau -> "Sup"
  | Sup.Obs   , Cau.Cau    -> "Cau"
  | Sup.Abs   , Cau.NonCau -> "Abs"
  | Sup.Itl   , Cau.Itl    -> "Itl"
  | Sup.Sup   , Cau.Cau    -> "CauSup"
  | Sup.Sup   , Cau.NonCau -> "suppressable"
  | Sup.NonObs, Cau.Cau    -> "causable"
  | _         ,    _       -> to_string d

let to_string_alias = to_string


let to_string_let d =
  if is_causable d then (
    if is_suppressable d then "+-" else "+"
  )
  else if is_suppressable d then "-"
  else if is_observable d then ""
  else "?"

module Constraint = struct

  type enftype_t = t [@@deriving equal]
  
  type t = { lower: enftype_t option; upper: enftype_t option } [@@deriving equal]

  let empty = { lower = None; upper = None }

  let lower      enftype = { empty with lower = Some enftype }
  let upper      enftype = { empty with upper = Some enftype }

  let to_string c =
    let g s enftype = enftype |> to_string |> Printf.sprintf s |> (fun x -> [x]) in
    String.concat ~sep:" ∧ "
      (Option.value_map c.lower ~default:[] ~f:(g "t ≽ %s")
       @ Option.value_map c.upper ~default:[] ~f:(g "%s ≽ t"))

  exception CannotMerge of string

  let merge_join = Option.merge ~f:join
  let merge_meet = Option.merge ~f:meet
  let geq_opt x y = Option.value ~default:true (Option.map2 ~f:geq x y)
  (*let equal_opt x y = Option.value ~default:false (Option.map2 ~f:equal x y)*)
  let is_causable_opt = Option.value_map ~default:false ~f:is_causable
  let is_suppressable_opt = Option.value_map ~default:false ~f:is_suppressable

  let merge ~key = function
    | `Left t | `Right t -> Some t
    | `Both ((c:t), (c':t)) when equal c c' -> Some c
    | `Both ((c:t), (c':t)) ->
       (*print_endline (Printf.sprintf "Merging c=%s with c'=%s..." (to_string c) (to_string c'));*)
       let lower           = merge_join c.lower c'.lower in
       let upper           = merge_meet c.upper c'.upper in
       let c'' =
         if (
           not (geq_opt upper lower) (* if there is nothing between lower and upper *)
           (* NOTE: a CauSup lower bound (event both caused and suppressed) is no
              longer rejected here.  Such candidates are now allowed through and
              validated downstream by the per-SCC SMT incompatibility check
              (Smt_check), which proves the cause/suppress conditions exclusive. *)
         ) then (
           (*Stdio.printf "%s %s %b %b %b\n"
             (match upper with None -> "None" | Some b -> to_string_alias b)
             (match lower with None -> "None" | Some b -> to_string_alias b)
             (not (geq_opt upper lower))
             (is_error_opt upper)
             (is_causable_opt lower && is_suppressable_opt lower);*)
           raise (CannotMerge key)
         )
         else
           Some { lower; upper }
       in
       (*print_endline (Printf.sprintf "... got c''=%s..." (to_string (Option.value_exn c'')));*)
       c''

  let solve c =
    match c.upper, c.lower with
    (* lower demands both cause and suppress: resolve to CauSup and let the
       SMT incompatibility check decide whether it is actually enforceable. *)
    | Some enftype, Some lo when is_causable lo && is_suppressable lo ->
       meet enftype causup
    | Some enftype, _ when not (is_causable enftype && is_suppressable enftype) -> enftype
    | Some enftype, Some enftype' when is_causable enftype' ->
       meet enftype (Sup.Obs, Cau.Cau)
    | Some enftype, Some enftype' when is_suppressable enftype' ->
       meet enftype (Sup.Sup, Cau.NonCau)
    | Some enftype, _ ->
       meet enftype (Sup.Obs, Cau.NonCau)
    | _ -> raise (Etc.EnforceabilityError "cannot solve constraint without an upper bound")
    (*match c.upper with
    | Some enftype -> enftype
    | _ -> raise (Etc.EnforceabilityError "cannot solve constraint without an upper bound")*)

end
      
