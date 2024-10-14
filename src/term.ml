open Base
open Sformula

module T = struct

  type t = Var of string | Const of Dom.t | App of string * t list [@@deriving sexp_of, hash]

  let rec compare t t' =
    match t, t' with
    | Var s, Var s' -> String.compare s s'
    | Var _, _ -> -1
    | Const d, Const d' -> Dom.compare d d'
    | Const _, Var _ -> 1
    | Const _, App _ -> -1
    | App (s, ts), App (s', ts') ->
       Etc.lexicographic2 String.compare (Etc.lexicographics compare) (s, ts) (s', ts')
    | App _, _ -> 1

  let var x = Var x
  let const d = Const d
  let app f trms = App (f, trms)

  let is_var = function
    | Var x -> true
    | _ -> false

  let is_const = function
    | Const d -> true
    | _ -> false

  let unvar = function
    | Var x -> x
    | Const _ -> raise (Invalid_argument "unvar is undefined for Consts")
    | App _ -> raise (Invalid_argument "unvar is undefined for Apps")

  let unconst = function
    | Var _ -> raise (Invalid_argument "unconst is undefined for Vars")
    | App _ -> raise (Invalid_argument "unconst is undefined for Apps")
    | Const c -> c

  let rec fv_list = function
    | [] -> []
    | Const c :: trms -> fv_list trms
    | Var x :: trms -> x :: fv_list trms
    | App (_, trms) :: trms' -> fv_list trms @ fv_list trms'

  let rec fn_list = function
    | [] -> []
    | Const c :: trms -> fn_list trms
    | Var x :: trms -> fn_list trms
    | App (f, trms) :: trms' -> f :: fn_list (trms @ trms')

  let rec equal t t' = match t, t' with
    | Var x, Var x' -> String.equal x x'
    | Const d, Const d' -> Dom.equal d d'
    | App (f, ts), App (f', ts') ->
       String.equal f f' &&
         (match List.map2 ts ts' ~f:equal with
          | Ok b -> List.for_all b (fun x -> x)
          | Unequal_lengths -> false)
    | _ -> false

  let rec to_string = function
    | Var x -> Printf.sprintf "Var %s" x
    | Const d -> Printf.sprintf "Const %s" (Dom.to_string d)
    | App (f, ts) -> Printf.sprintf "App %s(%s)" f (String.concat ~sep:", " (List.map ts ~f:to_string))

  let rec value_to_string = function
    | Var x -> Printf.sprintf "%s" x
    | Const d -> Printf.sprintf "%s" (Dom.to_string d)
    | App (f, ts) -> Printf.sprintf "%s(%s)" f (String.concat ~sep:", " (List.map ts ~f:value_to_string))

  let rec list_to_string trms = String.concat ~sep:", " (List.map trms ~f:value_to_string)

  let filter_vars = List.filter_map ~f:(function Var x -> Some x | _ -> None)

  let rec reorder l = function
    | [] -> l
    | h::t when not (List.mem l (Var h) ~equal) -> reorder l t
    | h::t -> (Var h) :: (reorder (List.filter l (fun x -> not (equal x (Var h)))) t)

  let rec subst v = function
    | Var x -> (match Map.find v x with
                | None -> Var x
                | Some trm -> trm)
    | Const d -> Const d
    | App (f, ts) -> App (f, List.map ~f:(subst v) ts)

  let rec substs v = List.map ~f:(subst v)

  let rec init = function
    | SConst (Const.CInt i)    -> Const (Int i)
    | SConst (Const.CFloat f)  -> Const (Float f)
    | SConst (Const.CStr s)    -> Const (Str s)
    | SApp   (f, ts)           -> App (f, List.map ~f:init ts)
    | SVar   s                 -> Var s
    | SBop   (None, t, bop, u) ->
       (let f = match bop with
          | Bop.BAdd -> "add"
          | BSub     -> "sub"
          | BMul     -> "mul"
          | BDiv     -> "div"
          | BPow     -> "pow"
          | BFAdd    -> "fadd"
          | BFSub    -> "fsub"
          | BFMul    -> "fmul"
          | BFDiv    -> "fdiv"
          | BFPow    -> "fpow"
          | BEq      -> "eq"
          | BNeq     -> "neq"
          | BLt      -> "lt"
          | BLeq     -> "leq"
          | BGt      -> "gt"
          | BGeq     -> "geq"
          | BConc    -> "conc" in
        App (f, [init t; init u]))
    | SUop   (uop, t)           ->
       (let f = match uop with
          | Uop.USub -> "usub"
          | Uop.UNot -> "not" in
        App (f, [init t]))

end

include T
include Comparator.Make(T)
