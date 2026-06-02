open Base

module MyTerm = Term
open MFOTL_lib
module Term = MyTerm

type compiled_let =
  string
  * Enftype.t option
  * (Tterm.TypedVar.t * Dom.tt option) list
  * Tyformula.typed_t
  * Tyformula.typed_t option
  * Normalize.clause list option
  * Normalize.trigger option

val compile_and_write :
  filename:string ->
  py_source:string option ->
  let_map:Enforceability.let_map ->
  lets:compiled_let list ->
  clauses:Normalize.clause list ->
  Enfflash.program
