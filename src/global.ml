open MFOTL_lib

let debug = ref false
let inc_ref = ref Stdio.In_channel.stdin
let outc_ref = ref Stdio.Out_channel.stdout
let json = ref false
let b_ref = ref Time.Span.zero
let s_ref = ref (Time.Span.Second (Time.Span.Second.of_string "1"))
