open Base
open Sformula

module MyTerm = Term

open MFOTL_lib

module IntVar : Modules.V with type t = int = struct

  module T = struct

    type t = int [@@deriving compare, sexp_of, hash, equal]
    
    let to_string s = Printf.sprintf "#%d" s
    let to_latex s = Printf.sprintf "\\mathit{%d}" s
    let ident s = Int.to_string s
    let of_ident s = 0

    let replace z _ = z
    
    let equal_ident = equal
    
  end

  include T
  include Comparator.Make(T)
  
end

module Valuation = Valuation.Make(IntVar)
    
include Term.Make(IntVar)(Dom)(MyTerm.NoOp)(MyTerm.NoOp)(MyTerm.TrivialInfo)

let init (lbls: Lbl.t array) (trm: MyTerm.t) =
  let trm = 
    match trm.trm with
    | MyTerm.Const d -> Const d
    | App (f, ts) ->
      let f _ = function
        | Lbl.LClos (f', ts') ->
          String.equal f f'
          && (match List.for_all2 ts ts' ~f:MyTerm.equal with
              | Base.List.Or_unequal_lengths.Ok b -> b
              | _ -> false)
        | _ -> false in
      Var (fst (Array.findi_exn lbls ~f))
    | Var s ->
      let f _ = function
        | Lbl.LVar s' | LAll s' | LEx s' -> String.equal s s'
        | _ -> false in
      Var (fst (Array.findi_exn lbls ~f))
    | _ -> assert false in
  make_dummy trm

let init_multiple (lbls: Lbl.t array) (trms: MyTerm.t list) =
  List.map ~f:(init lbls) trms

let to_term (lbls: Lbl.t array) (trm: t) =
  let trm =
    match trm.trm with
    | Const d -> MyTerm.Const d
    | Var i ->
      (match Array.get lbls i with
       | LVar x -> Var x
       | LClos (f, trms) -> App (f, trms)
       | _ -> assert false)
    | _ -> assert false in
  MyTerm.make_dummy trm

let to_terms (lbls: Lbl.t array) (trms: t list) =
  List.map ~f:(to_term lbls) trms

let of_var (lbls: Lbl.t array) (s: string) =
  let f _ = function
    | Lbl.LVar s' | LAll s' | LEx s' -> String.equal s s'
    | _ -> false in
  fst (Array.findi_exn lbls ~f)

let of_vars (lbls: Lbl.t array) (s: string list) =
  List.map ~f:(of_var lbls) s

let to_var (lbls: Lbl.t array) (y: int) =
  match Array.get lbls y with
  | LVar x | LEx x | LAll x -> x
  | _ -> assert false
  
let to_vars (lbls: Lbl.t array) (y: int list) =
  List.map ~f:(to_var lbls) y

