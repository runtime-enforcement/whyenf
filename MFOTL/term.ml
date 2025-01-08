open Base

open Modules

exception TermError of string

module type T = sig

  type t [@@deriving compare, sexp_of, hash, equal]
  type v [@@deriving compare, sexp_of, hash, equal]
  type d [@@deriving compare, sexp_of, hash, equal]

  type comparator_witness
  val comparator : (t, comparator_witness) Comparator.t

  (*val var : v -> t
  val const : d -> t
  val app : string -> t list -> t*)
  val dummy_var : v -> t

  val unvar_opt : t -> v option

  val fv_list : t list -> v list
  val fn_list : t list -> string list
  val size : t -> int
  val exists_subterm : f:(t -> bool) -> t -> bool
  val equal : t -> t -> bool

  val to_string : t -> string
  val value_to_string : ?l:int -> t -> string
  val list_to_string : t list -> string

  val subst : (v, t, 'a) Map.t -> t -> t
  val substs : (v, t, 'a) Map.t -> t list -> t list

end

module Make (Var : V) (Dom : D) (Uop : O) (Bop : O) (Info : I) = struct

  module Ctxt = Ctxt.Make(Dom)

  module T = struct

    type core_t =
      | Var of Var.t
      | Const of Dom.t
      | App of string * t list
      | Unop of Uop.t * t
      | Binop of t * Bop.t * t
      | Proj of t * string
      | Record of (string * t) list
                    [@@deriving compare, sexp_of, hash, equal]
    and t = { trm : core_t; info : Info.t }
    
    type v = Var.t [@@deriving compare, sexp_of, hash, equal]
    type d = Dom.t [@@deriving compare, sexp_of, hash, equal]

    let make trm info = { trm; info }
    let make_dummy trm = make trm Info.dummy

    let var x = Var x
    let const d = Const d
    let app f trms = App (f, trms)
    let unop o trm = Unop (o, trm)
    let binop trm o trm' = Binop (trm, o, trm')
    let proj trm p = Proj (trm, p)
    let record kvs = Record kvs

    let dummy_var v = make_dummy (var v)

    let unvar_opt t = match t.trm with
      | Var x -> Some x
      | _ -> None

    let is_var t = match t.trm with
      | Var _ -> true
      | _ -> false

    let is_const t = match t.trm with
      | Const _ -> true
      | _ -> false

    let rec to_string_core = function
      | Var x -> Printf.sprintf "Var %s" (Var.to_string x)
      | Const d -> Printf.sprintf "Const %s" (Dom.to_string d)
      | App (f, ts) -> Printf.sprintf "App %s(%s)" f
                         (String.concat ~sep:", " (List.map ts ~f:to_string))
      | Unop (o, t) -> Printf.sprintf "Unop %s (%s)" (Uop.to_string o) (to_string t)
      | Binop (t, o, t') -> Printf.sprintf "Binop (%s) %s (%s)"
                              (to_string t) (Bop.to_string o) (to_string t')
      | Proj (t, p) -> Printf.sprintf "Proj (%s).%s" (to_string t) p
      | Record kvs ->
         Printf.sprintf "Record { %s }"
           (String.concat ~sep:", " (List.map kvs ~f:(fun (k, v) -> k ^ " : " ^ to_string v)))
    and to_string t =
      Info.to_string 0 (to_string_core t.trm) t.info

    let rec value_to_string_core ?(l=0) t =  match t with
      | Var x -> Printf.sprintf "%s" (Var.to_string x)
      | Const d -> Printf.sprintf "%s" (Dom.to_string d)
      | App (f, ts) -> Printf.sprintf "%s(%s)" f
                         (String.concat ~sep:", " (List.map ts ~f:(value_to_string ~l)))
      | Unop (o, t) -> let l' = Uop.prio o in
                       Printf.sprintf (Etc.paren l l' "%s %s")
                         (Uop.to_string o)
                         (value_to_string ~l:10 t)
      | Binop (t, o, t') -> let l' = Bop.prio o in
                            Printf.sprintf (Etc.paren l l' "%s %s %s")
                              (value_to_string ~l:l' t)
                              (Bop.to_string o)
                              (value_to_string ~l:l' t')
      | Proj (t, p) -> Printf.sprintf "%s.%s" (value_to_string ~l:10 t) p
      | Record kvs ->
         let f (k, v) = k ^ " : " ^ value_to_string v in
         Printf.sprintf "{ %s }" (String.concat ~sep:", " (List.map kvs ~f))
    and value_to_string ?(l=0) t =
      Info.to_string l (value_to_string_core ~l t.trm) t.info

    let unvar t = match t.trm with
      | Var x -> x
      | _ -> raise (TermError (Printf.sprintf "unvar is undefined for %s" (to_string t)))

    let unconst t = match t.trm with
      | Const c -> c
      | _ -> raise (TermError (Printf.sprintf "unconst is undefined for %s" (to_string t)))

    let rec fv_list = function
      | [] -> []
      | t :: ts -> (match t.trm with
                    | Const _ -> []
                    | Var x -> [x]
                    | App (_, trms) -> fv_list trms
                    | Unop (_, trm) -> fv_list [trm]
                    | Binop (trm, _, trm') -> fv_list [trm; trm']
                    | Proj (trm, _) -> fv_list [trm]
                    | Record kvs -> fv_list (List.map ~f:snd kvs)) @ fv_list ts

    let rec fn_list = function
      | [] -> []
      | t :: ts -> (match t.trm with
                    | Const _ | Var _ -> []
                    | App (f, _) -> [f]
                    | Unop (_, trm) -> fn_list [trm]
                    | Binop (trm, _, trm') -> fn_list [trm; trm']
                    | Proj (trm, _) -> fn_list [trm]
                    | Record kvs -> fn_list (List.map ~f:snd kvs)) @ fn_list ts

    let rec size t = match t.trm with
      | Var _ -> 1
      | Const _ -> 1
      | App (f, ts) -> 1 + List.fold_left ~f:(+) ~init:0 (List.map ~f:size ts)
      | Unop (o, t) -> 1 + size t
      | Binop (t, o, t') -> 1 + size t + size t'
      | Proj (t, p) -> 1 + size t
      | Record kvs -> 1 + List.fold_left ~f:(+) ~init:0 (List.map ~f:(fun (_, v) -> size v) kvs)

    let rec exists_subterm ~f t =
      f t || begin match t.trm with
             | Var _ | Const _ -> false
             | App (_, ts) -> List.exists ~f:(exists_subterm ~f) ts
             | Unop (_, t) -> exists_subterm ~f t
             | Binop (t, _, t') -> exists_subterm ~f t || exists_subterm ~f t'
             | Proj (t, _) -> exists_subterm ~f t
             | Record kvs -> List.exists ~f:(fun (_, v) -> exists_subterm ~f v) kvs
             end

    let list_to_string trms = String.concat ~sep:", " (List.map trms ~f:value_to_string)
    let list_to_string_core trms = String.concat ~sep:", " (List.map trms ~f:value_to_string_core)

    let filter_vars = List.filter_map ~f:(fun t -> match t.trm with Var x -> Some x | _ -> None)

    let rec reorder l = function
      | [] -> l
      | h::t when not (List.mem l h ~equal) -> reorder l t
      | h::t -> h :: (reorder (List.filter l ~f:(fun x -> not (equal x h))) t)

    let rec subst v t =
      let trm = match t.trm with
      | Var x -> (match Map.find v x with
                  | None -> Var x
                  | Some t -> t.trm)
      | Const d -> Const d
      | App (f, ts) -> App (f, List.map ~f:(subst v) ts)
      | Unop (o, t) -> Unop (o, subst v t)
      | Binop (t, o, t') -> Binop (subst v t, o, subst v t')
      | Proj (t, p) -> Proj (subst v t, p)
      | Record kvs -> Record (List.map ~f:(fun (k, w) -> (k, subst v w)) kvs)
      in { t with trm }

    let substs v = List.map ~f:(subst v)

  end

  include T
  include Comparator.Make(T)

end
