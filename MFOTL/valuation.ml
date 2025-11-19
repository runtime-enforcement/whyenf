open Core

open Modules

module type T = sig

  type v
  type c
  type t = (v, Dom.t, c) Map.t

  val compare: t -> t -> int
  val equal: t -> t -> bool
  val empty: t
  val sexp_of: t -> Sexp.t
  val extend: t -> t -> t
  val hash: t -> int

  val to_string: t -> string

  val of_alist_exn : v list -> Dom.t list -> t
  val map_keys: t -> f:(v -> v option) -> t

  val is_empty: t -> bool

end

module Make (Var : V) = struct

  type v = Var.t
  type c = Var.comparator_witness
  type t = (Var.t, Dom.t, Var.comparator_witness) Map.t

  let compare (v: t) (v': t) = Map.compare_direct Dom.compare v v'

  let equal (v: t) (v': t) = Map.equal Dom.equal v v'

  let empty: t = Map.empty (module Var)

  let sexp_of (v: t) =
    let f (k, d) = Sexp.List [Atom (Var.to_string k); Atom (Dom.to_string d)] in
    Sexp.List (List.map (Map.to_alist v) ~f)

  let extend v v' =
    let f ~key:_ d = match d with
      | `Left d -> Some d
      | `Right d -> Some d
      | `Both (d, _) -> Some d in
    Map.merge v v' ~f

  let hash (v: t) =
    let f acc (x, d) = Var.hash x lxor Dom.hash d lxor acc in
    List.fold_left ~init:0 ~f (Map.to_alist v)

  let to_string (v: t) =
    let f (x, d) = Printf.sprintf "%s -> %s" (Var.to_string x) (Dom.to_string d) in
    Etc.string_list_to_string (List.map (Map.to_alist v) ~f)

  let of_alist_exn s v : t =
    Map.of_alist_exn (module Var) (List.zip_exn s v)

  let map_keys (v: t) ~f:(f: Var.t -> Var.t option) : t =
    Map.map_keys_exn (module Var)
      (Map.filter_keys v ~f:(fun v -> Option.is_some (f v)))
      ~f:(fun v -> Option.value_exn (f v))

  let is_empty = Map.is_empty 
      
end

