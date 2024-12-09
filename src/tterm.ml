open Base

module TypedVar : MFOTL_lib.Modules.V with type t = (string * MFOTL_lib.Dom.tt) = struct

  module T = struct
    
    type t = string * MFOTL_lib.Dom.tt [@@deriving compare, sexp_of, hash, equal]

    let to_string (x, tt) = Printf.sprintf "%s:%s" x (MFOTL_lib.Dom.tt_to_string tt)
    let ident = fst
    let of_ident _ = raise (Invalid_argument "Cannot create a typed variable without a type")

    let replace (_, tt) (z, _) = (z, tt)

  end
  
  include T
  include Comparator.Make(T)

end

include MFOTL_lib.Term.Make(TypedVar)(MFOTL_lib.Dom)(Term.NoOp)(Term.NoOp)(Term.TrivialInfo)

let convert_var (types : Ctxt.t) x = (x, Ctxt.get_tt_exn x types)

let convert_vars types = List.map ~f:(convert_var types)

let rec convert (types : Ctxt.t) (t : Term.t) =
  let trm = match t.trm with
  | Term.Var v -> Var (convert_var types v)
  | Const c -> Const c
  | App (f, ts) -> App (f, convert_multiple types ts)
  | _ -> raise (Invalid_argument (Printf.sprintf "cannot convert %s" (Term.to_string t)))
  in make_dummy trm

and convert_multiple types ts = List.map ~f:(convert types) ts

let rec to_term t =
  let trm = match t.trm with
  | Var (v, _) -> Term.Var v
  | Const c -> Const c
  | App (f, ts) -> App (f, to_terms ts)
  | _ -> raise (Invalid_argument (Printf.sprintf "cannot convert %s" (to_string t)))
  in Term.make_dummy trm

and to_terms = List.map ~f:to_term
