open Core

type t = Second of int | Minute of int | Hour of int [@@deriving compare, sexp_of, hash, equal]

let (+) t u = match t, u with
  | Second i, Second j -> Second (i+j)
  | Second i, Minute j -> Second (j*60 + i)
  | Second i, Hour   j -> Second (j*3600 + i)
  | Minute i, Minute j -> Minute (i+j)
  | Minute i, Second j -> Second (i*60 + j)
  | Minute i, Hour   j -> Minute (j*60 + i)
  | Hour   i, Hour   j -> Hour   (i+j)
  | Hour   i, Second j -> Second (i*3600 + j)
  | Hour   i, Minute j -> Second (i*60 + j)

let inc t = match t with
  | Second i -> Second Int.(i+1)
  | Minute i -> Minute Int.(i+1)
  | Hour   i -> Hour   Int.(i+1)

let dec t = match t with
  | Second i -> Second Int.(i-1)
  | Minute i -> Minute Int.(i-1)
  | Hour   i -> Hour   Int.(i-1)

let inv = function
  | Second i -> Second (-i)
  | Minute i -> Minute (-i)
  | Hour   i -> Hour   (-i)

let (|+) t u = match t, u with
  | Second i, Second j -> Second (Int.max Int.(i+j) 0)
  | Second i, Minute j -> Second (Int.max Int.(j*60 + i) 0)
  | Second i, Hour   j -> Second (Int.max Int.(j*3600 + i) 0)
  | Minute i, Minute j -> Minute (Int.max Int.(i+j) 0)
  | Minute i, Second j -> Second (Int.max Int.(i*60 + j) 0)
  | Minute i, Hour   j -> Minute (Int.max Int.(j*60 + i) 0)
  | Hour   i, Hour   j -> Hour   (Int.max Int.(i+j) 0)
  | Hour   i, Second j -> Second (Int.max Int.(i*3600 + j) 0)
  | Hour   i, Minute j -> Second (Int.max Int.(i*60 + j) 0)

let (-) t u = (+) t (inv u)

let (|-) t u = (|+) t (inv u)

let (<=) t u = match t, u with
  | Second i, Second j -> i <= j
  | Second i, Minute j -> i <= j*60
  | Second i, Hour   j -> i <= j*3600
  | Minute i, Minute j -> i <= j
  | Minute i, Second j -> i*60 <= j
  | Minute i, Hour   j -> i <= j*60
  | Hour   i, Hour   j -> i <= j
  | Hour   i, Second j -> i*3600 <= j
  | Hour   i, Minute j -> i*60 <= j

let (<) t u = match t, u with
  | Second i, Second j -> i < j
  | Second i, Minute j -> i < j*60
  | Second i, Hour   j -> i < j*3600
  | Minute i, Minute j -> i < j
  | Minute i, Second j -> i*60 < j
  | Minute i, Hour   j -> i < j*60
  | Hour   i, Hour   j -> i < j
  | Hour   i, Second j -> i*3600 < j
  | Hour   i, Minute j -> i*60 < j

let min t u = match t, u with
  | Second i, Second j -> Second (Int.min i j)
  | Second i, Minute j -> Second (Int.min i (j*60))
  | Second i, Hour   j -> Second (Int.min i (j*3600))
  | Minute i, Minute j -> Minute (Int.min i j)
  | Minute i, Second j -> Second (Int.min (i*60) j)
  | Minute i, Hour   j -> Minute (Int.min i (j*60))
  | Hour   i, Hour   j -> Hour   (Int.min i j)
  | Hour   i, Second j -> Hour   (Int.min (i*3600) j)
  | Hour   i, Minute j -> Hour   (Int.min (i*60) j)

let max t u = match t, u with
  | Second i, Second j -> Second (Int.max i j)
  | Second i, Minute j -> Second (Int.max i (j*60))
  | Second i, Hour   j -> Second (Int.max i (j*3600))
  | Minute i, Minute j -> Minute (Int.max i j)
  | Minute i, Second j -> Second (Int.max (i*60) j)
  | Minute i, Hour   j -> Minute (Int.max i (j*60))
  | Hour   i, Hour   j -> Hour   (Int.max i j)
  | Hour   i, Second j -> Hour   (Int.max (i*3600) j)
  | Hour   i, Minute j -> Hour   (Int.max (i*60) j)

let is_zero = function
  | Second 0 -> true
  | Minute 0 -> true
  | Hour   0 -> true
  | _ -> false

let zero = Second 0
let max_time = Second max_int

let to_zero = function
  | Second i -> Second 0
  | Minute i -> Minute 0
  | Hour   i -> Hour   0

let to_string = function
  | Second i -> string_of_int i
  | Minute i -> string_of_int i ^ " m"
  | Hour   i -> string_of_int i ^ " h"

(* Only for backwards-compatibility -- do not use for arithmetics *)
let to_int = function
  | Second i -> i
  | Minute i -> i*60
  | Hour   i -> i*3600

let make i = function
  | "" | "s" -> Second i
  | "m" -> Minute i
  | "h" -> Hour i

let of_timestamp i = Second i
