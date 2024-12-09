open Base
open Sformula

module TrivialInfo : MFOTL_Base.I with type t = unit = struct

  type t = unit [@@deriving compare, sexp_of, hash, equal]

  let to_string _ s () = s
  let dummy = () 

end

module StringVar : MFOTL_Base.V with type t = string = struct

  module T = struct

    type t = string [@@deriving compare, sexp_of, hash, equal]
    
    let to_string s = s
    let ident s = s
    let of_ident s = s

    let replace _ z = z
    
  end

  include T
  include Comparator.Make(T)
  
end

module NoOp = struct

  type t = unit [@@deriving compare, sexp_of, hash, equal]

  let to_string _ = assert false
  let prio _ = 0

end

include MFOTL_Term.Make(StringVar)(Dom)(NoOp)(NoOp)(TrivialInfo)

let rec init sf =
  let trm = match sf with
  | SConst (Const.CBool true)  -> Const (Int 1)
  | SConst (Const.CBool false) -> Const (Int 0)
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
        | BConc    -> "conc"
        | _        -> raise (Errors.FormulaError
                               (Printf.sprintf "Operator %s is not valid in term"
                                  (Sformula.Bop.to_string bop))) in
      App (f, [init t; init u]))
  | SUop   (uop, t)           ->
     (let f = match uop with
        | Uop.USub -> "usub"
        | Uop.UFSub -> "ufsub"
        | Uop.UNot -> "not" in
      App (f, [init t]))
  | sf -> raise (Errors.FormulaError
                   (Printf.sprintf "Expression %s is not a valid term"
                      (Sformula.to_string sf)))
  in make_dummy trm
