open Base

module Etc = MFOTL_lib.Etc

module S = struct
  type t = (string, String.comparator_witness) Set.t
  let equal = Set.equal 
  let compare = Set.compare_direct 
  let sexp_of_t s = Sexp.List (List.map (Set.elements s) ~f:(fun x -> Sexp.Atom x))
  let empty = Set.empty (module String)
  (*let is_empty = Set.is_empty*)
  let mem = Set.mem
  let filter = Set.filter
  let singleton = Set.singleton (module String)
  let of_list = Set.of_list (module String)
  (*let length = Set.length*)
  let elements = Set.elements
  let to_string s =
    Printf.sprintf "{%s}" (String.concat ~sep:", " (elements s))
end

module T = struct
  
  type t =
    | LVar  of string
    | LEx   of string
    | LAll  of string
    | LClos of string * Term.t list [@@deriving equal, compare, sexp_of]

  let var s = LVar s
  let ex s = LEx s
  let all s = LAll s
  let clos s terms vars = LClos (s, terms)

  let exquant = function
    | LVar x -> LVar x
    | LEx x -> LAll x
    | LAll x -> LEx x
    | LClos (f, ts) -> LClos (f, ts)

  let is_var = function
    | LVar _ -> true
    | _ -> false

  let unvar = function
    | LVar s -> s
    | _ -> raise (Errors.TermError "unvar is undefined for non-variable labels")

  let term = function
    | LVar s -> Term.make_dummy (Term.Var s)
    | LClos (f, ts) -> Term.make_dummy (App (f, ts))
    | _ -> raise (Errors.TermError "term is undefined for quantified labels")

  let of_term t = match Term.(t.trm) with
    | Term.Var s -> LVar s
    | App (f, ts) -> LClos (f, ts)
    | _ -> raise (Errors.TermError "of_term is undefined for quantified labels")

  let to_string = function
    | LVar x -> Printf.sprintf "LVar %s" x
    | LEx x -> Printf.sprintf "LEx %s" x
    | LAll x -> Printf.sprintf "LAll %s" x
    | LClos (f, ts) ->
       Printf.sprintf "LClos %s(%s)"
         f (String.concat ~sep:", " (List.map ts ~f:Term.to_string))

  let to_string_list lbls =
    "[" ^ String.concat ~sep:", " (List.map ~f:to_string lbls) ^ "]"

  let quantify ~forall x = function
    | LVar x' when String.equal x x' ->
       if forall then LAll x' else LEx x'
    | lbl -> lbl

  let quantify_array ~forall x lbls =
    Array.map lbls ~f:(quantify ~forall x)

  let rec unquantify_list x =
    let rec unquantify_list2 = function
      | [] -> []
      | (LAll x' as lbl) :: terms | (LEx x' as lbl) :: terms when String.equal x x'
        -> lbl :: terms
      | lbl :: terms
        -> lbl :: unquantify_list2 terms in
    function
    | [] -> []
    | LAll x' :: terms | LEx x' :: terms when String.equal x x' ->
       LVar x' :: (unquantify_list2 terms)
    | lbl :: terms -> lbl :: (unquantify_list x terms)

  (* Order terms in lbls' to fulfill the following invariants:
   * all variables in y, ordered as in lbls, come first
   * then comes x
   * then come all other variables not in x or y
   * any term using a variable z comes after z
   *)
  let order lbls lbls' x y =
    let vars  = List.filter lbls ~f:is_var in
    let lbls1 = (Etc.reorder ~equal:equal (List.map y ~f:var) vars) @ [x] in
    let lbls2 = List.filter lbls' ~f:(fun lbl -> not (List.mem lbls1 lbl ~equal:equal)) in
    lbls1 @ lbls2

  let rec subst m = function
    | LVar x ->
      (match Map.find m x with
       | Some term -> of_term term
       | None -> LVar x)
    | LEx x -> LEx x
    | LAll x -> LAll x
    | LClos (e, ts) -> LClos (e, Term.substs m ts)

  let substs m = List.map ~f:(subst m)

end

include T
include Comparator.Make(T)
