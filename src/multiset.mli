open Base

type ('a, 'b) t

val is_empty: ('a, 'b) t -> bool

val empty: ('a, 'b) Comparator.Module.t -> ('a, 'b) t

val equal: ('a, 'b) t -> ('a, 'b) t -> bool

val fold: ('a, 'b) t -> init:'c -> f:(value:'a -> card:int -> 'c -> 'c) -> 'c

val card: ('a, 'b) t -> int

val median: compare:('a -> 'a -> int) -> ('a, 'b) t -> 'a

val min: ('a, 'b) t -> 'a
val max: ('a, 'b) t -> 'a

val map: ('c, 'd) Comparator.Module.t -> f:('a -> 'c) -> ('a, 'b) t -> ('c, 'd) t

val append: ('a, 'b) t -> 'a -> ('a, 'b) t
val add: ('a, 'b) Comparator.Module.t ->  ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
val union: ('a, 'b) Comparator.Module.t ->  ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
val inter: ('a, 'b) Comparator.Module.t ->  ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
