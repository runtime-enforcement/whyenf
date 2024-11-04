open Base

module Const = struct

  type t =
    | CBool  of bool
    | CInt   of int
    | CFloat of float
    | CStr   of string
    [@@deriving compare, sexp_of, hash]

  let to_string = function
    | CBool  true  -> Printf.sprintf "⊤"
    | CBool  false -> Printf.sprintf "⊥"
    | CInt   i     -> Printf.sprintf "%d" i
    | CFloat f     -> Printf.sprintf "%f" f
    | CStr   s     -> s

  let to_dom = function
    | CInt i -> Dom.Int i
    | CFloat f -> Float f
    | CStr s -> Str s

end

module Aop = struct

  type t = ASum | AAvg | AMed | ACnt | AMin | AMax | AStd
           [@@deriving compare, sexp_of, hash, equal]

  let to_string = function
    | ASum    -> "SUM"
    | AAvg    -> "AVG"
    | AMed    -> "MED"
    | ACnt    -> "CNT"
    | AMin    -> "MIN"
    | AMax    -> "MAX"
    | AStd    -> "STD"
  
end

module Bop2 = struct

  type t = BIff [@@deriving compare, sexp_of, hash]

  let to_string = function
    | BIff   -> "↔"

  let prio = function
    | BIff   -> 80

end

module Bop = struct

  type t =
    | BAnd | BOr | BImp
    | BAdd | BSub | BMul | BDiv | BPow
    | BFAdd | BFSub | BFMul | BFDiv | BFPow
    | BEq | BNeq | BLt | BLeq | BGt | BGeq
    | BConc
    [@@deriving compare, sexp_of, hash]

  let is_relational = function
    | BEq | BNeq | BLt | BLeq | BGt | BGeq -> true
    | _ -> false

  let to_string = function
    | BAnd   -> "∧"
    | BOr    -> "∨"
    | BImp   -> "→"
    | BAdd   -> "+"
    | BSub   -> "-"
    | BMul   -> "*"
    | BDiv   -> "/"
    | BPow   -> "**"
    | BFAdd  -> "+."
    | BFSub  -> "-."
    | BFMul  -> "*."
    | BFDiv  -> "/."
    | BFPow  -> "**."
    | BEq    -> "="
    | BNeq   -> "≠"
    | BLt    -> "<"
    | BLeq   -> "≤"
    | BGt    -> ">"
    | BGeq   -> "≥"
    | BConc  -> "^"

  let prio = function
    | BPow   -> 10
    | BFPow  -> 10
    | BFMul  -> 20
    | BFDiv  -> 20
    | BMul   -> 20
    | BDiv   -> 20
    | BAdd   -> 30
    | BSub   -> 30
    | BFAdd  -> 30
    | BFSub  -> 30
    | BConc  -> 30
    | BEq    -> 40
    | BNeq   -> 40
    | BLt    -> 40
    | BLeq   -> 40
    | BGt    -> 40
    | BGeq   -> 40
    | BAnd   -> 50
    | BOr    -> 60
    | BImp   -> 70

end

module Uop = struct

  type t = USub | UFSub | UNot
           [@@deriving compare, sexp_of, hash]

  let to_string = function
    | USub  -> "-"
    | UFSub -> "-."
    | UNot  -> "¬"

  let prio = function
    | USub  -> 8
    | UFSub -> 8
    | UNot  -> 45

end

module Btop = struct

  type t = BSince | BUntil | BRelease | BTrigger
           [@@deriving compare, sexp_of, hash]

  let to_string = function
    | BSince   -> "S"
    | BUntil   -> "U"
    | BRelease -> "R"
    | BTrigger -> "T"

  let prio _ = 49

end

module Utop = struct

  type t = UNext | UPrev | UAlways | UHistorically | UEventually | UOnce
           [@@deriving compare, sexp_of, hash]

  let to_string = function
    | UNext         -> "○"
    | UPrev         -> "●"
    | UAlways       -> "□"
    | UHistorically -> "■"
    | UEventually   -> "◊"
    | UOnce         -> "⧫"

  let prio _ = 47

end


type t =
  | SConst of Const.t
  | SVar of string
  | SApp of string * t list
  | SLet of string * Enftype.t option * string list * t * t
  | SAgg of string * Aop.t * t * string list * t
  | SAssign of t * string * t
  | SBop of Side.t option * t * Bop.t * t
  | SBop2 of (Side.t * Side.t) option * t * Bop2.t * t
  | SUop of Uop.t * t
  | SExists of string list * t
  | SForall of string list * t
  | SBtop of Side.t option * Interval.t * t * Btop.t * t
  | SUtop of Interval.t * Utop.t * t
  [@@deriving compare, sexp_of, hash]

let rec to_string_rec l = function
  | SConst c -> Const.to_string c
  | SVar s -> s
  | SApp (f, ts) -> Printf.sprintf "%s(%s)" f (list_to_string ts)
  | SLet (r, enftype_opt, vars, f, g) ->
     Printf.sprintf "LET %s(%s)%s = %s IN %s" r
       (Etc.string_list_to_string vars)
       (Option.fold enftype_opt ~init:""
          ~f:(fun _ enftype -> " : " ^ Enftype.to_string enftype))
       (to_string_rec 4 f)
       (to_string_rec 4 g)
  | SAgg (s, op, x, y, f) -> Printf.sprintf "%s <- %s(%s; %s; %s)"
                               s
                               (Aop.to_string op)
                               (to_string x)
                               (String.concat ~sep:", " y)
                               (to_string_rec 5 f)
  | SAssign (f, s, t) -> Printf.sprintf "%s; %s <- %s"
                           (to_string_rec 5 f)
                           s
                           (to_string t)
  | SBop (s_opt, f, bop, g) -> Printf.sprintf "%s %s%s %s"
                                 (to_string_rec (Bop.prio bop) f)
                                 (Bop.to_string bop)
                                 (Option.fold s_opt ~init:"" ~f:(fun _ -> Side.to_string))
                                 (to_string_rec (Bop.prio bop) g)
  | SBop2 (s2_opt, f, bop, g) -> Printf.sprintf "%s %s%s %s"
                                   (to_string_rec (Bop2.prio bop) f)
                                   (Bop2.to_string bop)
                                   (Option.fold s2_opt ~init:"" ~f:(fun _ -> Side.to_string2))
                                   (to_string_rec (Bop2.prio bop) g)
  | SUop (uop, f) -> Printf.sprintf "%s %s"
                       (Uop.to_string uop)
                       (to_string_rec (Uop.prio uop) f)
  | SExists (xs, f) -> Printf.sprintf (Etc.paren l 5 "∃%s. %s")
                         (String.concat ~sep:", " xs)
                         (to_string_rec 5 f)
  | SForall (xs, f) -> Printf.sprintf (Etc.paren l 5 "∀%s. %s")
                         (String.concat ~sep:", " xs)
                         (to_string_rec 5 f)
  | SBtop (s_opt, i, f, btop, g) -> Printf.sprintf "%s %s%s%s %s"
                                      (to_string_rec (Btop.prio btop) f)
                                      (Btop.to_string btop)
                                      (Interval.to_string i)
                                      (Option.fold s_opt ~init:"" ~f:(fun _ -> Side.to_string))
                                      (to_string_rec (Btop.prio btop) g)
  | SUtop (i, utop, f) -> Printf.sprintf "%s%s %s"
                            (Utop.to_string utop)
                            (Interval.to_string i)
                            (to_string_rec (Utop.prio utop) f)

and list_to_string ts = String.concat ~sep:", " (List.map ~f:to_string ts)

and to_string t = to_string_rec 0 t
