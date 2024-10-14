open Base

module S = struct
  type t = (string, String.comparator_witness) Set.t
  let equal = Set.equal 
  let compare = Set.compare_direct 
  let sexp_of_t s = Sexp.List (List.map (Set.elements s) ~f:(fun x -> Sexp.Atom x))
  let empty = Set.empty (module String)
  let is_empty = Set.is_empty
  let mem = Set.mem
  let filter = Set.filter
  let singleton = Set.singleton (module String)
  let of_list = Set.of_list (module String)
  let length = Set.length
  let elements = Set.elements
  let to_string s =
    Printf.sprintf "{%s}" (String.concat ~sep:", " (elements s))
end

module T = struct
  
  type t =
    | LVar  of string
    | LEx   of string
    | LAll  of string
    | LClos of string * Term.t list * S.t [@@deriving equal, compare, sexp_of]

  let var s = LVar s
  let ex s = LEx s
  let all s = LAll s
  let clos s terms vars = LClos (s, terms, vars)

  let is_var = function
    | LVar _ -> true
    | _ -> false

  let term = function
    | LVar s -> Term.Var s
    | LClos (f, ts, v) -> App (f, ts)

  let of_term = function
    | Term.Var s -> LVar s
    | App (f, ts) -> LClos (f, ts, S.empty)

  let to_string = function
    | LVar x -> Printf.sprintf "LVar %s" x
    | LEx x -> Printf.sprintf "LEx %s" x
    | LAll x -> Printf.sprintf "LAll %s" x
    | LClos (f, ts, v) ->
       Printf.sprintf "LClos %s(%s; [%s])"
         f (String.concat ~sep:", " (List.map ts ~f:Term.to_string)) (S.to_string v)

  let to_string_list lbls =
    String.concat ~sep:", " (List.map ~f:to_string lbls)

  let rec fv = function
    | LVar s -> S.singleton s
    | LClos (f, ts, vars) ->
       S.filter (S.of_list (Term.fv_list ts)) ~f:(fun x -> not (S.mem vars x))

  let quantify ~forall x = function
    | LVar x' when String.equal x x' ->
       if forall then LAll x' else LEx x'
    | LClos (f, ts, vars) as lbl ->
       let fvs = fv lbl in
       (if S.mem fvs x then
          LClos (f, ts, Set.add vars x)
        else
          LClos (f, ts, vars))
    | lbl -> lbl

  let quantify_list ~forall x lbls =
    List.map lbls ~f:(quantify ~forall x)

  let rec unquantify_list x =
    let rec unquantify_list2 = function
      | [] -> []
      | (LAll x' as lbl) :: terms | (LEx x' as lbl) :: terms when String.equal x x'
        -> lbl :: terms
      | LClos (f, ts, vars) :: terms
        -> LClos (f, ts, Set.remove vars x) :: unquantify_list2 terms
      | lbl :: terms
        -> lbl :: unquantify_list2 terms in
    function
    | [] -> []
    | LAll x' :: terms | LEx x' :: terms when String.equal x x' ->
       LVar x' :: (unquantify_list2 terms)
    | lbl :: terms -> lbl :: (unquantify_list x terms)


  let rec eval (v: Etc.valuation) = function
    | LVar s when Map.mem v s -> Term.Const (Map.find_exn v s)
    | LVar s -> Var s
    | LClos (f, ts, _) ->
       let aux = function | `Left y | `Right y | `Both (y, _) -> Some y in
       Sig.eval v (App (f, ts))
    | _ -> assert false

end

include T
include Comparator.Make(T)
