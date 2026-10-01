open MFOTL_lib

let debug = ref false
let forall = ref false
let monitoring = ref false
let inc_ref = ref Stdio.In_channel.stdin
let outc_ref = ref Stdio.Out_channel.stdout
let json = ref false
let b_ref = ref Time.Span.zero
let s_ref = ref (Time.Span.Second (Time.Span.Second.of_string "1"))
let label = ref false
let simplify = ref false
let filter = ref true
let memo = ref true
let unroll_all = ref false
let print_normal_form = ref false
(* -fix-since: rewrite  f S g  whose right operand has variables that f does
   not have into the equivalent  (f ∨ ¬⧫g) S g  (see Lformula.pull_lets). *)
let fix_since = ref false
