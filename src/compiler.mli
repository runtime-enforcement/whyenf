open Base

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm

module Enforcement : module type of Tyformula.MFOTL_Enforceability(Sig)

type compiled_let =
  string
  * Enftype.t option
  * (Tterm.TypedVar.t * Dom.tt option) list
  * Tyformula.typed_t
  * Tyformula.typed_t option
  * Enforcement.clause list option

val compile_and_write :
  filename:string ->
  py_source:string option ->
  let_map:Enforcement.let_map ->
  lets:compiled_let list ->
  clauses:Enforcement.clause list ->
  Enfflash.program
