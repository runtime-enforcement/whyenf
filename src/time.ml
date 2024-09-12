open Core

open CalendarLib

type t = Fcalendar.t

let equal = Fcalendar.equal
let compare = Fcalendar.compare

let hash_fold_t state t =
  let open Fcalendar in
  let state = Hash.fold_int state (year t) in
  let state = Hash.fold_int state (Date.int_of_month (month t)) in
  let state = Hash.fold_int state (day_of_month t) in
  let state = Hash.fold_int state (hour t) in
  let state = Hash.fold_int state (minute t) in
  Hash.fold_float state (Time.Second.to_float (second t))

let sexp_of_t calendar =
  let open Fcalendar in
  let year = year calendar in
  let month = month calendar |> Date.int_of_month in
  let day = day_of_month calendar in
  let hour = hour calendar in
  let minute = minute calendar in
  let second = second calendar in
  Sexp.List [
    Sexp.Atom (string_of_int year);
    Sexp.Atom (string_of_int month);
    Sexp.Atom (string_of_int day);
    Sexp.Atom (string_of_int hour);
    Sexp.Atom (string_of_int minute);
    Sexp.Atom (string_of_float (Time.Second.to_float second))
  ]

module type U = sig
  
  type u [@@deriving equal, compare, sexp_of, hash]

  val min_seconds : u -> float
  val max_seconds : u -> float
  val (+) : t -> u -> t
  val neg : u -> u
  val inc : u -> u
  val dec : u -> u
  val is_zero : u -> bool
  val of_string : string -> u
  val to_string : u -> string
  
end

module type S = sig
  
  type v

  val equal_v : v -> v -> bool
  val compare_v : v -> v -> int
  val sexp_of_v : v -> Sexp.t
  val hash_fold_v : Base_internalhash_types.state -> v -> Base_internalhash_types.state

  val min_seconds : v -> float
  val max_seconds : v -> float
  val leq : v -> v -> bool
  val (+) : t -> v -> t
  val inc : v -> v
  val dec : v -> v
  val is_zero : v -> bool
  val zero : v
  val to_string : v -> string
  
end

module Span  = struct

  module Second : U = struct
 
    type u = int [@@deriving equal, compare, sexp_of, hash]

    let min_seconds u = float_of_int u
    let max_seconds u = float_of_int u
    let (+) t u = Fcalendar.add t (Fcalendar.Period.second (float_of_int u))
    let neg u = - u
    let inc u = Int.(+) u 1
    let dec u = Int.(-) u 1
    let is_zero u = 0 = u
    let of_string s = int_of_string s
    let to_string u = Int.to_string u ^ "s"
    
  end

  module Second_ : U = Second 

  module Minute : U = struct
 
    type u = int [@@deriving equal, compare, sexp_of, hash]

    let min_seconds u = float_of_int u *. 60.
    let max_seconds u = float_of_int u *. 60. (* Ignores leap seconds! *)
    let (+) t u = Fcalendar.add t (Fcalendar.Period.minute u)
    let neg u = - u
    let inc u = Int.(+) u 1
    let dec u = Int.(-) u 1
    let is_zero u = 0 = u
    let of_string s = int_of_string s 
    let to_string u = Int.to_string u ^ "m"
    
  end
  
  module Hour : U = struct
 
    type u = int [@@deriving equal, compare, sexp_of, hash]

    let min_seconds u = float_of_int u *. 3600.
    let max_seconds u = float_of_int u *. 3600.
    let (+) t u = Fcalendar.add t (Fcalendar.Period.hour u)
    let neg u = - u
    let inc u = Int.(+) u 1
    let dec u = Int.(-) u 1
    let is_zero u = 0 = u
    let of_string s = int_of_string s
    let to_string u = Int.to_string u ^ "h"
    
  end
  
  module Day : U = struct
 
    type u = int [@@deriving equal, compare, sexp_of, hash]

    let min_seconds u = float_of_int u *. 86400.
    let max_seconds u = float_of_int u *. 86400.
    let (+) t u = Fcalendar.add t (Fcalendar.Period.day u)
    let neg u = - u
    let inc u = Int.(+) u 1
    let dec u = Int.(-) u 1
    let is_zero u = 0 = u
    let of_string s = int_of_string s
    let to_string u = Int.to_string u ^ "d"
    
  end

  module Month : U = struct
 
    type u = int [@@deriving equal, compare, sexp_of, hash]

    let min_seconds u = float_of_int u *. 86400. *. 28.
    let max_seconds u = float_of_int u *. 86400. *. 31. (* Ignores leap seconds! *)
    let (+) t u = Fcalendar.add t (Fcalendar.Period.month u)
    let neg u = - u
    let inc u = Int.(+) u 1
    let dec u = Int.(-) u 1
    let is_zero u = 0 = u
    let of_string s = int_of_string s
    let to_string u = Int.to_string u ^ "M"
    
  end

  module Year : U = struct
 
    type u = int [@@deriving equal, compare, sexp_of, hash]

    let min_seconds u = float_of_int u *. 86400. *. 365.
    let max_seconds u = float_of_int u *. 86400. *. 366. (* Ignores leap seconds! *)
    let (+) t u = Fcalendar.add t (Fcalendar.Period.year u)
    let neg u = - u
    let inc u = Int.(+) u 1
    let dec u = Int.(-) u 1
    let is_zero u = 0 = u
    let of_string s = int_of_string s
    let to_string u = Int.to_string u ^ "y"
    
  end

  type s =
    | Second of Second.u
    | Minute of Minute.u
    | Hour   of Hour.u
    | Day    of Day.u
    | Month  of Month.u
    | Year   of Year.u
  [@@deriving equal, compare, sexp_of, hash]

  let (+) t = function
    | Second u -> Second.(+) t u
    | Minute u -> Minute.(+) t u
    | Hour   u -> Hour.(+) t u
    | Day    u -> Day.(+) t u
    | Month  u -> Month.(+) t u
    | Year   u -> Year.(+) t u

  let neg = function
    | Second u -> Second (Second.neg u)
    | Minute u -> Minute (Minute.neg u)
    | Hour   u -> Hour (Hour.neg u)
    | Day    u -> Day (Day.neg u)
    | Month  u -> Month (Month.neg u)
    | Year   u -> Year (Year.neg u)

  let inc = function
    | Second u -> Second (Second.inc u)
    | Minute u -> Minute (Minute.inc u)
    | Hour   u -> Hour (Hour.inc u)
    | Day    u -> Day (Day.inc u)
    | Month  u -> Month (Month.inc u)
    | Year   u -> Year (Year.inc u)

  let dec = function
    | Second u -> Second (Second.dec u)
    | Minute u -> Minute (Minute.dec u)
    | Hour   u -> Hour (Hour.dec u)
    | Day    u -> Day (Day.dec u)
    | Month  u -> Month (Month.dec u)
    | Year   u -> Year (Year.dec u)


  let is_zero = function
    | Second u -> Second.is_zero u
    | Minute u -> Minute.is_zero u
    | Hour   u -> Hour.is_zero u
    | Day    u -> Day.is_zero u
    | Month  u -> Month.is_zero u
    | Year   u -> Year.is_zero u
  
  let make s = function
    | "" | "s" -> Second (Second.of_string s)
    | "m" -> Minute (Minute.of_string s)
    | "h" -> Hour (Hour.of_string s)
    | "d" -> Day (Day.of_string s)
    | "M" -> Month (Month.of_string s)
    | "Y" -> Year (Year.of_string s)
    | u -> failwith ("Invalid time unit: " ^ u)

  let of_string s =
    let pattern = Str.regexp "^[ \t]*\\([0-9]+\\)[ \t]*\\(.*\\)[ \t]*$" in
    if Str.string_match pattern s 0 then
      let i = Str.matched_group 1 s in
      let s = Str.matched_group 2 s in
      make s i
    else
      raise (Invalid_argument ("Invalid string for bound: " ^ s))

  let to_string = function
    | Second u -> Second.to_string u
    | Minute u -> Minute.to_string u
    | Hour   u -> Hour.to_string u
    | Day    u -> Day.to_string u
    | Month  u -> Month.to_string u
    | Year   u -> Year.to_string u

  let (-) t u = (+) t (neg u)

  let zero = Second (Second.of_string "0")
  let infty = Year (Year.of_string (string_of_int (Int.max_value)))

  let min_seconds = function
    | Second u -> Second.min_seconds u
    | Minute u -> Minute.min_seconds u
    | Hour   u -> Hour.min_seconds u
    | Day    u -> Day.min_seconds u
    | Month  u -> Month.min_seconds u
    | Year   u -> Year.min_seconds u

  let max_seconds = function
    | Second u -> Second.max_seconds u
    | Minute u -> Minute.max_seconds u
    | Hour   u -> Hour.max_seconds u
    | Day    u -> Day.max_seconds u
    | Month  u -> Month.max_seconds u
    | Year   u -> Year.max_seconds u

  let leq a b = Float.(<=) (max_seconds a) (min_seconds b)


  module S = struct
    
    type v = s
    let equal_v = equal_s
    let compare_v = compare_s
    let sexp_of_v = sexp_of_s
    let hash_fold_v = hash_fold_s

    let min_seconds = min_seconds
    let max_seconds = max_seconds
    let leq = leq
    let (+) = (+)
    let inc = inc
    let dec = dec
    let is_zero = is_zero
    let zero = zero
    let to_string = to_string

  end

end

let of_float ts = Fcalendar.from_unixfloat ts
let of_int ts = of_float (float_of_int ts)

let (+) = Span.(+)
let (-) = Span.(-)

let (<=) t u = (Fcalendar.compare t u) <= 0
let (<) t u = (Fcalendar.compare t u) < 0
let (==) t u = (Fcalendar.compare t u) = 0

let min t u = if t <= u then t else u
let max t u = if u <= t then t else u

let zero = Fcalendar.make 0 0 0 0 0 0.

let to_string = Printer.Fcalendar.to_string


