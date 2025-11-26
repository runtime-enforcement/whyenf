open Base

open Modules

exception TermError of string

module type T = sig

  type t [@@deriving compare, sexp_of, hash, equal]
  type v [@@deriving compare, sexp_of, hash, equal]
  type d [@@deriving compare, sexp_of, hash, equal]

  type comparator_witness
  val core_equal : t -> t -> bool
  val comparator : (t, comparator_witness) Comparator.t

  val dummy_var : v -> t
  val dummy_app : string -> t list -> t

  val dummy_int : int -> t
  val unvar_opt : t -> v option
  val unconst_opt : t -> d option

  val is_var : t -> bool
  val is_const : t -> bool
      
  val fv_list : t list -> v list
  val fn_list : t list -> string list
  val size : t -> int
  val exists_subterm : f:(t -> bool) -> t -> bool
  val equal : t -> t -> bool

  val to_string : t -> string
  val value_to_string : ?l:int -> t -> string
  val value_to_latex : ?l:int -> t -> string
  val list_to_string : t list -> string
  val list_to_latex : t list -> string
  val to_json : t -> string

  val subst : (v, t, 'a) Map.t -> t -> t
  val substs : (v, t, 'a) Map.t -> t list -> t list

  val map_consts: f:(d -> d) -> t -> t

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

    let rec core_equal t u =
      match t.trm, u.trm with
      | Var v, Var v' -> Var.equal_ident v v'
      | Const d, Const d' -> Dom.equal d d'
      | App (f, trms), App (f', trms') ->
         String.equal f f'
         && (match List.for_all2 trms trms' ~f:core_equal with
             | Ok b -> b
             | _ -> false)
      | Unop (u, trm), Unop (u', trm') -> Uop.equal u u' && core_equal trm trm'
      | Binop (l, b, r), Binop (l', b', r') -> core_equal l l' && Bop.equal b b' && core_equal r r'
      | Proj (trm, a), Proj (trm', a') -> core_equal trm trm' && String.equal a a'
      | Record kvs, Record kvs' ->
        (match List.for_all2 kvs kvs' ~f:(fun (k, v) (k', v') -> String.equal k k' && core_equal v v') with
         | Ok b -> b
         | _ -> false)
      | _ -> false

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
    let dummy_app f trms = make_dummy (app f trms)
    let dummy_int i = make_dummy (Const (Dom.of_int i))

    let unvar_opt t = match t.trm with
      | Var x -> Some x
      | _ -> None

    let unconst_opt t = match t.trm with
      | Const d -> Some d
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

    let rec value_to_latex_core ?(l=0) t =  match t with
      | Var x -> Printf.sprintf "%s" (Var.to_latex x)
      | Const d -> Printf.sprintf "%s" (Dom.to_latex d)
      | App (f, ts) -> Printf.sprintf "\\mathsf{%s}(%s)"
                         (Etc.latex_string f)
                         (String.concat ~sep:", " (List.map ts ~f:(value_to_latex ~l)))
      | Unop (o, t) -> let l' = Uop.prio o in
                       Printf.sprintf (Etc.paren l l' "%s %s")
                         (Uop.to_latex o)
                         (value_to_latex ~l:10 t)
      | Binop (t, o, t') -> let l' = Bop.prio o in
                            Printf.sprintf (Etc.paren l l' "%s %s %s")
                              (value_to_latex ~l:l' t)
                              (Bop.to_latex o)
                              (value_to_latex ~l:l' t')
      | Proj (t, p) -> Printf.sprintf "%s.%s" (value_to_latex ~l:10 t) p
      | Record kvs ->
         let f (k, v) = k ^ " : " ^ value_to_latex v in
         Printf.sprintf "{ %s }" (String.concat ~sep:", " (List.map kvs ~f))
    and value_to_latex ?(l=0) t =
      Info.to_string l (value_to_latex_core ~l t.trm) t.info

    let rec to_json t = match t.trm with
      | Var x -> Printf.sprintf "{ \"constructor\": \"Var\", \"name\": \"%s\" }" (Var.to_string x)
      | Const d -> Printf.sprintf "{ \"constructor\": \"Const\", \"value\": %s }" (Dom.to_json d)
      | App (f, ts) -> Printf.sprintf "{ \"constructor\": \"App\", \"fun\": \"%s\", \"args\": [%s] }"
                         f (String.concat ~sep:", " (List.map ts ~f:to_json))
      | Unop (o, t) -> Printf.sprintf "{ \"constructor\": \"Unop\", \"op\": \"%s\", \"arg\": %s }"
                         (Uop.to_string o) (to_json t)
      | Binop (t, o, t') -> Printf.sprintf "{ \"constructor\": \"Binop\", \"op\": \"%s\", \"args\": [%s, %s] }"
                              (Bop.to_string o) (to_json t) (to_json t')
      | Proj (t, p) -> Printf.sprintf "{ \"constructor\": \"Proj\", \"arg\": %s, \"field\": \"%s\" }"
                         (to_json t) p
      | Record kvs -> Printf.sprintf "{ \"constructor\": \"Record\", \"fields\": {%s} }"
                        (String.concat ~sep:", "
                           (List.map kvs ~f:(fun (k, v) -> Printf.sprintf "\"%s\" : %s" k (to_json v))))

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
      | App (_, ts) -> 1 + List.fold_left ~f:(+) ~init:0 (List.map ~f:size ts)
      | Unop (_, t) -> 1 + size t
      | Binop (t, _, t') -> 1 + size t + size t'
      | Proj (t, _) -> 1 + size t
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
    let list_to_latex trms = String.concat ~sep:", " (List.map trms ~f:value_to_latex)

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

    let rec map_consts ~f t =
      let trm = match t.trm with
      | Var x -> Var x
      | Const d -> Const (f d)
      | App (f', ts) -> App (f', List.map ~f:(map_consts ~f) ts)
      | Unop (o, t) -> Unop (o, map_consts ~f t)
      | Binop (t, o, t') -> Binop (map_consts ~f t, o, map_consts ~f t')
      | Proj (t, p) -> Proj (map_consts ~f t, p)
      | Record kvs -> Record (List.map ~f:(fun (k, w) -> (k, map_consts ~f w)) kvs)
      in { t with trm }

  end

  include T
  include Comparator.Make(T)

end
