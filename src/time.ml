open Core

open CalendarLib

(*type t = Second of int | Minute of int | Hour of int *)
type t = Calendar.t

let equal = Calendar.equal
let compare = Calendar.compare

let hash_fold_t state t =
  let open Calendar in
  let state = Hash.fold_int state (year t) in
  let state = Hash.fold_int state (Date.int_of_month (month t)) in
  let state = Hash.fold_int state (day_of_month t) in
  let state = Hash.fold_int state (hour t) in
  let state = Hash.fold_int state (minute t) in
  Hash.fold_float state (Time.Second.to_float (second t))

let sexp_of_t calendar =
  let open Calendar in
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

module Span = struct

  open Calendar.Period
  
  type t = Calendar.Period.t
    
  let to_period t = t

  let equal = equal
  let compare = compare
  
  let hash_fold_t state t =
    let y, m, d, s = ymds t in
    let state = Hash.fold_int state y in
    let state = Hash.fold_int state m in
    let state = Hash.fold_int state d in
    Hash.fold_int state s

  let sexp_of_t t =
    let y, m, d, s = ymds t in
    Sexp.List [
        Sexp.Atom (string_of_int y);
        Sexp.Atom (string_of_int m);
        Sexp.Atom (string_of_int d);
        Sexp.Atom (string_of_int s)
      ]

  let inc t =
    match ymds t with
    | 0, 0, 0, s -> second (s+1)
    | 0, 0, d, _ -> day    (d+1)
    | 0, m, _, _ -> month  (m+1)
    | y, _, _, _ -> year   (y+1)

  let dec t =
    match ymds t with
    | 0, 0, 0, s -> second (s-1)
    | 0, 0, d, _ -> day    (d-1)
    | 0, m, _, _ -> month  (m-1)
    | y, _, _, _ -> year   (y-1)

  let inv = opp

  let (+) = add
  let (-) = sub

  let (<=) t u = compare t u <= 0
  let (<)  t u = compare t u < 0

  let min t u = if t <= u then t else u
  let max t u = if u <= t then t else u

  let max_span = year Int.max_value

  let is_zero = equal empty
  let zero = empty
  
  let make i = function
    | "" | "s" -> second i
    | "m" -> minute i
    | "h" -> hour i
    | "d" -> day i
    | "M" -> month i
    | "Y" -> year i
    | u -> failwith ("Invalid time unit: " ^ u)

  let to_int t =
    let y, m, d, s = ymds t in
    Int.(((y*365+m)*30+d)*24*3600+s)

  let of_string s =
    let (_, v, u) = String.fold s ~init:(false, "", "")
                      ~f:(fun (b, v, u) c ->
                        if b then (b, v, u ^ String.of_char c)
                        else if Char.is_digit c then (b, v ^ String.of_char c, u)
                        else (true, v, String.of_char c)) in
    make (int_of_string v) u

  let to_string t =
    let y, m, d, s = ymds t in
    Printf.sprintf "%dy %dm %dd %ds" y m d s
  
end

let of_float ts = Calendar.from_unixfloat ts

let of_int ts = of_float (float_of_int ts)

let (+) t u = Calendar.add t (Span.to_period u)

let (-) t u = Calendar.sub t u
let (--) t u = Calendar.add t (Calendar.Period.opp (Span.to_period u))

let (<=) t u = (Calendar.compare t u) <= 0
let (<) t u = (Calendar.compare t u) < 0

let min t u = if t <= u then t else u
let max t u = if u <= t then t else u

let zero = Calendar.make 0 0 0 0 0 0

let to_string = Printer.Calendar.to_string


