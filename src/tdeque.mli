open MFOTL_lib

open MFOTL_lib.Etc

type t

val empty : t
val to_string : t -> string
val is_empty : t -> bool
val enqueue_back : t -> timestamp -> t
val split_left : t -> t -> timestamp -> Interval.t -> t * t
val clean_left : t -> timestamp -> Interval.t -> t 
val split_right : t -> t -> timestamp -> Interval.t -> t * t
val clean_right : t -> timestamp -> Interval.t -> t 
val compute_until : t -> t -> bool
