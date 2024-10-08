open Base

open Dom

type ttt = TConst of tt | TVar of string [@@deriving compare, sexp_of, hash]

let unconst = function
  | TConst tt -> tt
  | TVar _ -> raise (Invalid_argument "unconst is undefined for TVars")

let ttt_equal ttt ttt' = match ttt, ttt' with
  | TConst tt, TConst tt' -> tt_equal tt tt'
  | TVar tv, TVar tv' -> String.equal tv tv'
  | _, _ -> false

let ttt_to_string = function
  | TConst tt -> tt_to_string tt
  | TVar   tv -> "'" ^ tv

let tvs = function
  | TConst _ -> []
  | TVar tv -> [tv]

module UnionFind : sig

  type t
  val empty : t
  val add : t -> string -> tt option -> t
  val union : t -> string -> string -> t
  val find : t -> string -> t * tt option
  val set : t -> string -> tt option -> t

end = struct

  type u = Root of tt option | Child of string
  type t = (string, u, String.comparator_witness) Map.t

  let empty = Map.empty (module String)

  let rec find_root uf key =
    match Map.find_exn uf key with
    | Root _ -> uf, key
    | Child key' -> let uf, root = find_root uf key' in
                    (Map.update uf key ~f:(fun _ -> Child root)), root

  let add uf key tt_opt =
    (*Stdio.printf "add('%s)\n" key;*)
    if Map.mem uf key then
      uf
    else
      Map.add_exn uf ~key ~data:(Root tt_opt)

  let union uf key1 key2 =
    (*Stdio.printf "union('%s,'%s)\n" key1 key2;*)
    let uf, root1 = find_root uf key1 in
    let uf, root2 = find_root uf key2 in
    if root1 != root2 then
      Map.update uf root2 ~f:(fun _ -> Child root1)
    else
      uf

  let find uf key =
    (*Stdio.printf "find('%s)\n" key;*)
    let uf, root = find_root uf key in
    match Map.find_exn uf root with
    | Root tt_opt -> uf, tt_opt

  let set uf key tt_opt =
    (*Stdio.printf "set('%s,%s)\n" key (match tt_opt with Some  tt -> Dom.tt_to_string tt | _ -> "None");*)
    let uf, root = find_root uf key in
    Map.update uf root (fun _ -> Root tt_opt)

end 

type t = { types: (string, ttt, String.comparator_witness) Map.t;
           tvs: UnionFind.t;
           next_var: int;
           next_tv: int }

let empty = { types = Map.empty (module String);
              tvs = UnionFind.empty;
              next_var = 0;
              next_tv = 0 }

let fresh_var ctxt =
  { ctxt with next_var = ctxt.next_var + 1 }, "~v" ^ string_of_int ctxt.next_var

let fresh_ttt ctxt =
  let fresh_tv = "t" ^ string_of_int (ctxt.next_tv) in
  { ctxt with next_tv = ctxt.next_tv + 1;
              tvs = UnionFind.add ctxt.tvs fresh_tv None },
  TVar fresh_tv

let merge v tv ttt_new ctxt =
  match ttt_new with
  | TConst tt -> (match UnionFind.find ctxt.tvs tv with
                  | tvs, Some tt' when Dom.tt_equal tt tt' -> { ctxt with tvs }
                  | _  , Some tt' ->
                     raise (Invalid_argument (
                                Printf.sprintf "type clash for %s: found %s, expected %s"
                                  v (tt_to_string tt) (tt_to_string tt')))
                  | tvs, None -> { ctxt with tvs = UnionFind.set ctxt.tvs tv (Some tt) })
  | TVar tv' -> { ctxt with tvs = UnionFind.union ctxt.tvs tv tv' }

let unify v ttt ttt' ctxt =
  match ttt, ttt' with
  | TConst tt, TConst tt' when tt_equal tt tt' -> ctxt, ttt'
  | TConst tt, TConst tt' ->
     raise (Invalid_argument (
                Printf.sprintf "type clash for %s: found %s, expected %s"
                  v (tt_to_string tt) (tt_to_string tt')))
  | TVar tv, _  -> merge v tv  ttt' ctxt, ttt'
  | _, TVar tv' -> merge v tv' ttt  ctxt, ttt

let get_tt_exn v ctxt =
  match Map.find ctxt.types v with
  | Some (TConst tt) -> tt
  | Some (TVar tv) -> (match snd (UnionFind.find ctxt.tvs tv) with
                       | Some tt -> tt
                       | None -> raise (Invalid_argument (
                                            Printf.sprintf "cannot find concrete type for variable %s" v)))
  | _ -> raise (Invalid_argument (
                    Printf.sprintf "cannot find concrete type for variable %s" v))

let type_const d ttt ctxt =
  let tt = tt_of_domain d in
  unify ("constant " ^ to_string d) ttt (TConst tt) ctxt

let type_var v ttt ctxt =
  match Map.find ctxt.types v with
  | None -> let tvs = match ttt with
              | TConst _  -> ctxt.tvs
              | TVar tv -> UnionFind.add ctxt.tvs tv None in
            { ctxt with types = Map.add_exn ctxt.types ~key:v ~data:ttt; tvs }, ttt
  | Some ttt' -> unify ("variable " ^ v) ttt ttt' ctxt

let replace_ttt tv ttt_new ttt = if ttt_equal ttt (TVar tv) then ttt_new else ttt

let convert_with_fresh_ttts ctxt ttts =
  let old_tvs = Etc.dedup ~equal:String.equal (List.concat (List.map ~f:tvs ttts)) in
  let ctxt, new_ttts = List.fold_map old_tvs ~init:ctxt ~f:(fun ctxt old_tv -> fresh_ttt ctxt) in
  ctxt, List.fold2_exn old_tvs new_ttts ~init:ttts
          ~f:(fun tts old_tv new_ttt -> List.map ~f:(replace_ttt old_tv new_ttt) tts)

