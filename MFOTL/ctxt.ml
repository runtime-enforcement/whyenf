open Base
open Modules

module type C = sig

  type d
  
  type tt 
  
  type ttt =
    | TConst of tt
    | TNamed of string
    | TVar of string
    | TSum of (string * ttt) list [@@deriving compare, sexp_of, hash, equal]

  type t

  type meet = ttt -> ttt -> ttt option

  exception CtxtError of string

  val unconst : ttt -> tt

  val empty : t
  val empty_meet : meet
  val of_meet : meet -> t
  val of_alist : ?meet:meet -> (string * ttt) list -> t
  val mem : t -> string -> bool
  val remove : t -> string -> t
  val fresh_var : t -> t * string
  val fresh_ttt : t -> t * ttt
  val add_tv : string -> t -> t
  val convert_with_fresh_ttts : t -> ttt list -> t * ttt list
  val merge : t -> t -> t
  val get_ttt : string -> t -> default:ttt -> ttt
  val get_ttt_exn : string -> t -> ttt
  val get_tt : string -> t -> default:tt -> tt
  val get_tt_exn : string -> t -> tt
  val get_concrete_exn : string -> t -> ttt
  val eval : ttt -> t -> ttt
  val type_const : d -> ttt -> t -> t * ttt
  val type_var : string -> ttt -> t -> t * ttt
  val unify : ttt -> ttt -> t -> t * ttt
  val vars : t -> string list
  val tvs : t -> string list

  val ttt_to_string : ttt -> string
  val to_string : t -> string

end

module Make (Dom : D) = struct

  type d = Dom.t

  type tt = Dom.tt [@@deriving compare, sexp_of, hash, equal]
  
  type ttt =
    | TConst of tt
    | TNamed of string
    | TVar   of string
    | TSum   of (string * ttt) list [@@deriving compare, sexp_of, hash, equal]

  type meet = ttt -> ttt -> ttt option
  
  exception CtxtError of string

  let unconst = function
    | TConst tt -> tt
    | TNamed _ -> raise (CtxtError "unconst is undefined for TNamed")
    | TVar _ -> raise (CtxtError "unconst is undefined for TVar")
    | TSum _ -> raise (CtxtError "unconst is undefined for TSum")

  let rec ttt_to_string = function
    | TConst tt  -> Dom.tt_to_string tt
    | TNamed tn  -> tn
    | TVar   tv  -> "'" ^ tv
    | TSum   kvs -> let f (k, v) = k ^ " : " ^ ttt_to_string v in
                    "{" ^ String.concat ~sep:", " (List.map kvs ~f) ^ "}"

  let rec tvs = function
    | TConst _
      | TNamed _  -> []
    | TVar   tv  -> [tv]
    | TSum   kvs -> List.dedup_and_sort (List.concat_map ~f:(fun (_, v) -> tvs v) kvs)
                      ~compare:String.compare

  module UnionFind : sig
    
    type t
    val empty : t
    val keys : t -> string list
    (*val mem : t -> string -> bool *)
    val add : t -> string -> ttt -> t
    val find : t -> string -> t * ttt
    val union : unify:(ttt -> ttt -> t -> t * ttt) -> t -> string -> string -> t
    val merge : unify:(ttt -> ttt -> t -> t * ttt) -> t -> t -> t
    val set : t -> string -> ttt -> t
    val to_string : t -> string

  end = struct

    type root =
      | Nil
      | Named of string
      | Const of tt
      | Sum of (string * ttt) list
 
    let ttt_of_root ~rkey = function
      | Nil -> TVar rkey
      | Named s -> TNamed s
      | Const tt -> TConst tt
      | Sum ttt -> TSum ttt

    let root_of_ttt = function
      | TNamed s -> Named s
      | TConst tt -> Const tt
      | TSum ttt -> Sum ttt
      | TVar _ -> Nil

    let root_to_string = function
      | Nil -> "Nil"
      | Named s -> s
      | Const tt -> Dom.tt_to_string tt
      | Sum kvs -> ttt_to_string (TSum kvs)
      
    type u =
      | Child of string            
      | Root of root

    type t = (string, u, String.comparator_witness) Map.t

    let empty : t = Map.empty (module String)
    let keys : t -> string list = Map.keys 
    (*let mem : t -> string -> bool = Map.mem*)

    let add (uf: t) (key: string) (ttt: ttt) : t =
      if Map.mem uf key
      then uf
      else Map.add_exn uf ~key ~data:(Root (root_of_ttt ttt))

    let rec repr uf key =
      match Map.find uf key with
      | Some (Child key') ->
         let uf, root = repr uf key' in
         (Map.update uf key ~f:(fun _ -> Child root)), root
      | _ -> uf, key

    let find (uf: t) (key: string) : t * ttt =
      let uf, rkey = repr uf key in
      match Map.find uf rkey with
      | Some (Root ttt) -> uf, ttt_of_root ~rkey ttt
      | _ -> uf, TVar key
 
    let union ~(unify:(ttt -> ttt -> t -> t * ttt)) (uf: t) (key1: string) (key2: string) : t =
      let uf, rkey1 = repr uf key1 in
      let uf, rkey2 = repr uf key2 in
      if not (String.equal rkey1 rkey2) then
        (match snd (find uf rkey1), snd (find uf rkey2) with
        | TVar _,  _     -> Map.update uf rkey1 ~f:(fun _ -> Child rkey2)
        | _     , TVar _ -> Map.update uf rkey2 ~f:(fun _ -> Child rkey1)
        | ttt   , ttt'   ->
           let uf = Map.update uf rkey2 ~f:(fun _ -> Child rkey1) in
           let uf, ttt = unify ttt ttt' uf in
           Map.update uf rkey1 ~f:(fun _ -> Root (root_of_ttt ttt)))
      else
        uf

    let merge ~(unify:(ttt -> ttt -> t -> t * ttt)) (uf1: t) (uf2: t) : t =
      let f ~key:key2 ~data:(u2: u) uf1 =
        match u2 with
        | Child key2' -> Map.update uf1 key2 ~f:(fun _ -> Child key2')
        | Root root2 ->
           let ttt2 = ttt_of_root ~rkey:key2 root2 in
           if Map.mem uf1 key2
           then fst (unify (snd (find uf1 key2)) ttt2 uf1)
           else add uf1 key2 ttt2 in
      Map.fold uf2 ~init:uf1 ~f
      
    let set (uf: t) (key: string) (ttt: ttt) : t =
      (*Stdio.printf "set('%s,%s)\n" key (match tt_opt with Some  tt -> Dom.tt_to_string tt | _ -> "None");*)
      let uf, rkey = repr uf key in
      Map.update uf rkey ~f:(fun _ -> Root (root_of_ttt ttt))

    let u_to_string = function
      | Root root -> root_to_string root
      | Child s -> Printf.sprintf "child(%s)" s
    
    let to_string t =
      Printf.sprintf "[%s]"
        (String.concat ~sep:", "
           (List.map ~f:(fun (k, v) -> Printf.sprintf "%s → %s" k (u_to_string v))
              (Map.to_alist t)))

  end 

  type t = { types: (string, ttt, String.comparator_witness) Map.t;
             (* mapping from variable names to variable types *)
             tvs: UnionFind.t;
             (* representatives of equivalence classes of variable types (from unification) *)
             next_var: int;
             next_tv: int;
             meet: meet }

  let of_meet meet =
    { types = Map.empty (module String);
      tvs = UnionFind.empty;
      next_var = 0;
      next_tv = 0;
      meet }

  let empty_meet _ _ = None

  let empty = of_meet empty_meet

  let types_to_string types =
    Printf.sprintf "[%s]"
        (String.concat ~sep:", "
           (List.map ~f:(fun (k, v) -> Printf.sprintf "%s → %s" k (ttt_to_string v))
              (Map.to_alist types)))

  let to_string t =
    Printf.sprintf "{ types = %s;\n   tvs = %s;\n   next_var = %d;\n   next_tv = %d }"
      (types_to_string t.types) (UnionFind.to_string t.tvs) t.next_var t.next_tv

  let of_alist ?(meet=empty_meet) types = { (of_meet meet) with types = Map.of_alist_exn (module String) types }

  let mem ctxt s = Map.mem ctxt.types s

  let remove ctxt s = { ctxt with types = Map.remove ctxt.types s }

  let fresh_var ctxt =
    { ctxt with next_var = ctxt.next_var + 1 }, "~v" ^ Int.to_string ctxt.next_var

  let add_tv tv ctxt =
    { ctxt with tvs = UnionFind.add ctxt.tvs tv (TVar tv) }

  let fresh_ttt ctxt =
    let fresh_tv = "t" ^ Int.to_string (ctxt.next_tv) in
    add_tv fresh_tv { ctxt with next_tv = ctxt.next_tv + 1 },
    TVar fresh_tv

  (*let rec merge_one tv ttt' ctxt =
    let tvs = merge_one_tvs tv ttt' ctxt.tvs in
    { ctxt with tvs }*)

  let rec merge_one_tvs tv ttt' meet (tvs: UnionFind.t) : UnionFind.t = 
    let tvs, ttt = UnionFind.find tvs tv in
    match ttt, ttt' with
    | _, TVar tv' -> UnionFind.union ~unify:(unify_tvs meet) tvs tv tv' 
    | TVar _, _ -> UnionFind.set tvs tv ttt'
    | _, _ -> fst (unify_tvs meet ttt ttt' tvs)

  and unify ttt ttt' (ctxt: t) : t * ttt =
    (*let ttt_old = ttt in*)
    let tvs, ttt = unify_tvs ctxt.meet ttt ttt' ctxt.tvs in
    (*Stdio.print_endline (Printf.sprintf "unify(%s, %s, %s) = %s"
                   (ttt_to_string ttt_old) (ttt_to_string ttt') (to_string ctxt) (to_string { ctxt with tvs }));*)
    { ctxt with tvs }, ttt

  and unify_tvs meet ttt ttt' (tvs: UnionFind.t) : UnionFind.t * ttt =
    let ctxt_err () =
      raise (CtxtError (
                 Printf.sprintf "type clash: found %s, expected %s"
                   (ttt_to_string ttt') (ttt_to_string ttt))) in
    match ttt, ttt' with
    | TConst tt, TConst tt' when Dom.equal_tt tt tt' -> tvs, ttt'
    | TNamed tn, TNamed tn' when String.equal tn tn' -> tvs, ttt'
    | TSum kvs, TSum kvs' ->
       let tvs, kvs'' = 
         try 
           List.fold2_exn kvs kvs' ~init:(tvs, [])
             ~f:(fun (tvs, kvs'') (f, ttt) (f', ttt') ->
               assert (String.equal f f');
               let tvs, ttt'' = unify_tvs meet ttt ttt' tvs in
               tvs, (f, ttt'') :: kvs'')
         with _ -> ctxt_err () in
       tvs, TSum (List.rev kvs'')
    | TVar tv, _  -> merge_one_tvs tv  ttt' meet tvs, ttt'
    | _, TVar tv' -> merge_one_tvs tv' ttt  meet tvs, ttt
    | ttt, ttt'   -> match meet ttt ttt' with
                     | Some ttt'' -> tvs, ttt''
                     | None -> ctxt_err ()

  let get_ttt v ctxt ~default = Option.value ~default (Map.find ctxt.types v)

  let get_ttt_exn v ctxt = Map.find_exn ctxt.types v

  let get_tt v ctxt ~default =
    match Map.find ctxt.types v with
    | Some (TConst tt) -> tt
    | Some (TVar tv) ->
       (match snd (UnionFind.find ctxt.tvs tv) with
        | TConst tt -> tt
        | _ -> default)
    | _ -> default

  let get_tt_exn v ctxt =
    let ctxt_err () =
      raise (CtxtError (
                 Printf.sprintf "cannot find concrete type for variable %s" v)) in
    match Map.find ctxt.types v with
    | Some (TConst tt) -> tt
    | Some (TVar tv) ->
       (match snd (UnionFind.find ctxt.tvs tv) with
        | TConst tt -> tt
        | _ -> ctxt_err ())
    | _ -> ctxt_err ()

  let get_concrete_exn v ctxt =
    let ctxt_err () =
      raise (CtxtError (
                 Printf.sprintf "cannot find concrete type for variable %s" v)) in
    match Map.find ctxt.types v with
    | Some (TConst tt) -> TConst tt
    | Some (TNamed tn) -> TNamed tn
    | Some (TVar tv) ->
       (match snd (UnionFind.find ctxt.tvs tv) with
        | TConst tt -> TConst tt
        | TNamed tn -> TNamed tn
        | _ -> ctxt_err ())
    | _ -> ctxt_err ()

  let rec eval ttt ctxt = match ttt with
    | TConst tt  -> TConst tt
    | TNamed tn  -> TNamed tn
    | TVar   tv  -> snd (UnionFind.find ctxt.tvs tv)
    | TSum   kvs -> TSum (List.map ~f:(fun (k, v) -> (k, eval v ctxt)) kvs)

  let type_const d ttt ctxt =
    let tt = Dom.tt_of_domain d in
    unify ttt (TConst tt) ctxt

  let type_var v ttt ctxt = 
    match Map.find ctxt.types v with
    | None -> let tvs = match ttt with
                | TVar tv -> UnionFind.add ctxt.tvs tv (TVar tv)
                | _ -> ctxt.tvs in
              { ctxt with types = Map.add_exn ctxt.types ~key:v ~data:ttt; tvs }, ttt
    | Some ttt' -> unify ttt ttt' ctxt

  let replace_ttt tv ttt_new ttt = if equal_ttt ttt (TVar tv) then ttt_new else ttt

  let convert_with_fresh_ttts ctxt ttts =
    let old_tvs = Etc.dedup ~equal:String.equal (List.concat (List.map ~f:tvs ttts)) in
    let ctxt, new_ttts = List.fold_map old_tvs ~init:ctxt ~f:(fun ctxt _ -> fresh_ttt ctxt) in
    ctxt, List.fold2_exn old_tvs new_ttts ~init:ttts
            ~f:(fun tts old_tv new_ttt -> List.map ~f:(replace_ttt old_tv new_ttt) tts)

  let vars ctxt = Map.keys ctxt.types
  let tvs ctxt = UnionFind.keys ctxt.tvs

  let merge ctxt ctxt' =
    let tvs = UnionFind.merge ~unify:(unify_tvs ctxt.meet) ctxt.tvs ctxt'.tvs in
    let ctxt = { ctxt with tvs } in
    let ctxt = Map.fold ctxt'.types ~init:ctxt
                 ~f:(fun ~key:v ~data:_ ctxt -> fst (type_var v (get_ttt_exn v ctxt') ctxt)) in
    (*Stdio.print_endline (Printf.sprintf "merge(%s, %s) = %s" (to_string ctxt) (to_string ctxt') (to_string ctxt));*)
    ctxt

end
