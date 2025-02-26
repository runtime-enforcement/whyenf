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

module Sct = struct

  type t = Sct | NonSct | AnySct | ErrSct [@@deriving compare, sexp_of, hash, equal]

  let to_string = function
    | NonSct -> "NonSct"
    | Sct    -> "Sct"
    | AnySct -> "AnySct"
    | ErrSct -> "ErrSct"

end

module Suppressability  = Lattice.Linear(Sup)
module Causability      = Lattice.Linear(Cau)
module SuppressabilityL = Lattice.Make(Suppressability)
module CausabilityL     = Lattice.Make(Causability)

module Strictness = struct

  type t = Sct.t [@@deriving compare, sexp_of, hash, equal]

  let join a b = match a, b with
    | Sct.AnySct, _ | _, Sct.AnySct
      | NonSct, Sct | Sct, NonSct -> Sct.AnySct
    | _, ErrSct -> a
    | ErrSct, _ -> b
    | _, _ -> a

  let meet a b = match a, b with
    | Sct.ErrSct, _ | _, Sct.ErrSct
      | NonSct, Sct | Sct, NonSct -> Sct.ErrSct
    | _, AnySct -> a
    | AnySct, _ -> b
    | _, _ -> a

  let to_string = Sct.to_string

end

include Lattice.Make3(Suppressability)(Causability)(Strictness)

let bot           = (Sup.NonObs, Cau.NonCau, Sct.AnySct)
let cau           = (Sup.Obs,    Cau.Cau,    Sct.AnySct)
let ncau          = (Sup.Obs,    Cau.Cau,    Sct.NonSct)
let sup           = (Sup.Sup,    Cau.NonCau, Sct.AnySct)
let causup        = (Sup.Sup,    Cau.Cau,    Sct.AnySct)
let caubot        = (Sup.NonObs, Cau.Cau,    Sct.AnySct)
let obs           = (Sup.Obs,    Cau.NonCau, Sct.AnySct)
let sct           = (Sup.Sup,    Cau.Cau,    Sct.Sct)
let ncaubot       = (Sup.NonObs, Cau.Cau,    Sct.NonSct)
let abs           = (Sup.Abs,    Cau.NonCau, Sct.AnySct)
let itl           = (Sup.Itl,    Cau.Itl,    Sct.AnySct)

let causable      = (Sup.NonObs, Cau.Cau,    Sct.ErrSct)
let suppressable  = (Sup.Sup,    Cau.NonCau, Sct.ErrSct)
let tcausable     = (Sup.NonObs, Cau.TCau,   Sct.ErrSct)
let tsuppressable = (Sup.TSup,   Cau.NonCau, Sct.ErrSct)

let get_sup (a, _, _) = a
let get_cau (_, b, _) = b
let get_sct (_, _, c) = c

let neg_sup = function
  | Sup.Sup -> Cau.Cau
  | _       -> NonCau

let neg_cau a b = match a, b with
  | Cau.Cau, _          -> Sup.Sup
  | NonCau , Sup.NonObs -> NonObs
  | _      , _          -> Obs

let neg (a, b, c) : t = (neg_cau b a, neg_sup a, c)

let is_causable        a = CausabilityL.(geq (get_cau a) Cau)
let is_suppressable    a = SuppressabilityL.(geq (get_sup a) Sup)
let is_observable      a = SuppressabilityL.(geq (get_sup a) Obs)
let is_only_observable a = not (is_causable a) && not (is_suppressable a) && is_observable a
let is_absent          a = SuppressabilityL.(geq (get_sup a) Abs)
let is_internal        a = Cau.(equal (get_cau a) Itl) && Sup.(equal (get_sup a) Itl)
let is_error           a = Sct.(equal (get_sct a) ErrSct)
let is_strict          a = Sct.(equal (get_sct a) Sct)
let is_non_strict      a = Sct.(equal (get_sct a) NonSct)
let is_transparent     a =
  (if is_causable a then CausabilityL.(geq (get_cau a) TCau) else true)
  && (if is_suppressable a then SuppressabilityL.(geq (get_sup a) TSup) else true)
  && (is_causable a || is_suppressable a)

let to_string ((a, b, c) as d) =
  match a, b, c with
  | Sup.NonObs, Cau.NonCau, _          -> "Bot"
  | Sup.Obs   , Cau.NonCau, _          -> "Obs"
  | Sup.Sup   , Cau.NonCau, Sct.AnySct -> "Sup"
  | Sup.Obs   , Cau.Cau   , Sct.AnySct -> "Cau"
  | Sup.Obs   , Cau.Cau   , Sct.NonSct -> "NCau"
  | Sup.Obs   , Cau.Cau   , Sct.Sct    -> "SCau"
  | Sup.Sup   , Cau.NonCau, Sct.NonSct -> "NSup"
  | Sup.Sup   , Cau.NonCau, Sct.Sct    -> "SSup"
  | Sup.Abs   , Cau.NonCau, Sct.AnySct -> "Abs"
  | Sup.Itl   , Cau.Itl   , Sct.AnySct -> "Itl"
  | Sup.Sup   , Cau.Cau   , Sct.AnySct -> "CauSup"
  | Sup.Sup   , Cau.NonCau, Sct.ErrSct -> "suppressable"
  | Sup.NonObs, Cau.Cau   , Sct.ErrSct -> "causable"
  | Sup.NonObs, Cau.Cau   , Sct.NonSct -> "non-strictly causable"
  | Sup.NonObs, Cau.Cau   , Sct.Sct    -> "strictly causable"
  | _         ,    _      , _          -> to_string d

let to_string_let d =
  if equal d bot then "?"
  else if equal d obs then "!"
  else if equal d sup then "-"
  else if equal d cau then "+"
  else if equal d causup then "+-"
  else if equal d caubot then "+?"
  else ""

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

  exception CannotMerge

  let merge_join = Option.merge ~f:join
  let merge_meet = Option.merge ~f:meet
  let geq_opt x y = Option.value ~default:false (Option.map2 ~f:geq x y)
  (*let equal_opt x y = Option.value ~default:false (Option.map2 ~f:equal x y)*)
  let is_error_opt = Option.value_map ~default:false ~f:is_error
  let is_causable_opt = Option.value_map ~default:false ~f:is_causable
  let is_suppressable_opt = Option.value_map ~default:false ~f:is_suppressable

  let merge ~key:_ = function
    | `Left t | `Right t -> Some t
    | `Both ((c:t), (c':t)) when equal c c' -> Some c
    | `Both ((c:t), (c':t)) ->
       (*print_endline (Printf.sprintf "Merging c=%s with c'=%s..." (to_string c) (to_string c'));*)
       let lower           = merge_join c.lower c'.lower in
       let upper           = merge_meet c.upper c'.upper in
       let c'' = 
         if (
           not (geq_opt upper lower) (* if there is nothing between lower and upper *)
           || is_error_opt upper     (* if upper contains an error *)
           || is_causable_opt lower && is_suppressable_opt lower (* if lower is CauSup *)
         ) then
           raise CannotMerge
         else
           Some { lower; upper }
       in
       (*print_endline (Printf.sprintf "... got c''=%s..." (to_string (Option.value_exn c'')));*)
       c''

  let solve c =
    match c.lower with
    | Some enftype -> enftype
    | _ -> raise (Etc.EnforceabilityError "cannot solve constraint without a lower bound")
    (*match c.upper with
    | Some enftype -> enftype
    | _ -> raise (Etc.EnforceabilityError "cannot solve constraint without an upper bound")*)

end
      
