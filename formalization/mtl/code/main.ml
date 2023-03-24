open Explanator.Explanator

let s_of_sum s_of_left s_of_right = function
  | Inl x -> "Inl (" ^ s_of_left x ^ ")"
  | Inr y -> "Inr (" ^ s_of_right y ^ ")"

let s_of_nat n = Z.to_string (integer_of_nat n)

let s_of_list s_of xs = "[" ^ String.concat ", " (List.map s_of xs) ^ "]"

let rec s_of_sproof = function
  | STT n -> "STT " ^ s_of_nat n
  | SAtm (s, n) -> "SAtm (" ^ s ^ ", " ^ s_of_nat n ^ ")"
  | SNeg p -> "SNeg (" ^ s_of_vproof p ^ ")"
  | SDisjL p -> "SDisjL (" ^ s_of_sproof p ^ ")"
  | SDisjR p -> "SDisjR (" ^ s_of_sproof p ^ ")"
  | SConj (p, q) -> "SConj (" ^ s_of_sproof p ^ ", " ^ s_of_sproof q ^ ")"
  | SSince (p, qs) -> "SSince (" ^ s_of_sproof p ^ ", " ^ s_of_list s_of_sproof qs ^ ")"
  | SUntil (qs, p) -> "SUntil (" ^ s_of_list s_of_sproof qs ^ ", " ^ s_of_sproof p ^ ")"
  | SNext p -> "SNext (" ^ s_of_sproof p ^ ")"
  | SPrev p -> "SPrev (" ^ s_of_sproof p ^ ")"
  and s_of_vproof = function
  | VFF n -> "VFF " ^ s_of_nat n
  | VAtm (s, n) -> "VAtm (" ^ s ^ ", " ^ s_of_nat n ^ ")"
  | VNeg p -> "VNeg (" ^ s_of_sproof p ^ ")"
  | VDisj (p, q) -> "VDisj (" ^ s_of_vproof p ^ ", " ^ s_of_vproof q ^ ")"
  | VConjL p -> "VConjL (" ^ s_of_vproof p ^ ")"
  | VConjR p -> "VConjR (" ^ s_of_vproof p ^ ")"
  | VSince (n, p, qs) -> "VSince (" ^ s_of_nat n ^ ", " ^ s_of_vproof p ^ ", " ^ s_of_list s_of_vproof qs ^ ")"
  | VUntil (n, qs, p) -> "VUntil (" ^ s_of_nat n ^ ", " ^ s_of_list s_of_vproof qs ^ ", " ^ s_of_vproof p ^ ")"
  | VSince_never (n, qs) -> "VSince_never (" ^ s_of_nat n ^ ", " ^ s_of_list s_of_vproof qs ^ ")"
  | VUntil_never (n, qs) -> "VUntil_never (" ^ s_of_nat n ^ ", " ^ s_of_list s_of_vproof qs ^ ")"
  | VSince_le n -> "VSince_le " ^ s_of_nat n
  | VNext p -> "VNext (" ^ s_of_vproof p ^ ")"
  | VNext_ge n -> "VNext_ge " ^ s_of_nat n
  | VNext_le n -> "VNext_le " ^ s_of_nat n
  | VPrev p -> "VPrev (" ^ s_of_vproof p ^ ")"
  | VPrev_ge n -> "VPrev_ge " ^ s_of_nat n
  | VPrev_le n -> "VPrev_le " ^ s_of_nat n
  | VPrev_zero -> "VPrev_zero"

let of_int n = nat_of_integer (Z.of_int n)

let trace = to_trace [(Set ["MyAtom2"], of_int 0)]

let expl_size = opt_size trace (of_int 0) (Disj (Atom "MyAtom", Neg (Atom "MyAtom2")))
let expl_depth = opt_depth trace (of_int 0) (Disj (Atom "MyAtom", Neg (Atom "MyAtom2")))

let _ = Printf.printf "%s\n" (s_of_sum s_of_sproof s_of_vproof expl_size)
let _ = Printf.printf "%s\n" (s_of_nat (msize expl_size))
let _ = Printf.printf "%s\n" (s_of_sum s_of_sproof s_of_vproof expl_depth)
let _ = Printf.printf "%s\n" (s_of_nat (mdepth expl_depth))
