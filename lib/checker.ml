module Explanator2 : sig
  type nat
  val integer_of_nat : nat -> Z.t
  type 'a vproof = VFF of nat | VAtm of 'a * nat | VNeg of 'a sproof |
    VDisj of 'a vproof * 'a vproof | VConjL of 'a vproof | VConjR of 'a vproof |
    VSince of nat * 'a vproof * 'a vproof list |
    VUntil of nat * 'a vproof list * 'a vproof |
    VSince_never of nat * nat * 'a vproof list |
    VUntil_never of nat * nat * 'a vproof list | VSince_le of nat |
    VNext of 'a vproof | VNext_ge of nat | VNext_le of nat | VPrev of 'a vproof
    | VPrev_ge of nat | VPrev_le of nat | VPrev_zero
  and 'a sproof = STT of nat | SAtm of 'a * nat | SNeg of 'a vproof |
    SDisjL of 'a sproof | SDisjR of 'a sproof | SConj of 'a sproof * 'a sproof |
    SSince of 'a sproof * 'a sproof list | SUntil of 'a sproof list * 'a sproof
    | SNext of 'a sproof | SPrev of 'a sproof
  type enat = Enat of nat | Infinity_enat
  type i
  type 'a mtl = TT | FF | Atom of 'a | Neg of 'a mtl | Disj of 'a mtl * 'a mtl |
    Conj of 'a mtl * 'a mtl | Next of i * 'a mtl | Prev of i * 'a mtl |
    Since of 'a mtl * i * 'a mtl | Until of 'a mtl * i * 'a mtl
  type 'a set
  type 'a trace_rbt
  type 'a trace
  type ('a, 'b) sum = Inl of 'a | Inr of 'b
  val strmatm : (string -> nat) -> (string sproof, string vproof) sum -> nat
  val ratm :
    (string -> nat) ->
      (string sproof, string vproof) sum ->
        (string sproof, string vproof) sum -> bool
  val strmdepth : (string sproof, string vproof) sum -> nat
  val rdepth :
    (string sproof, string vproof) sum ->
      (string sproof, string vproof) sum -> bool
  val strset : string list -> string set
  val opt_atm :
    (string -> nat) ->
      string trace -> nat -> string mtl -> (string sproof, string vproof) sum
  val strs_at : string sproof -> nat
  val strv_at : string vproof -> nat
  val interval : nat -> enat -> i
  val opt_depth :
    string trace -> nat -> string mtl -> (string sproof, string vproof) sum
  val is_opt_atm :
    (string -> nat) ->
      string trace ->
        nat -> string mtl -> (string sproof, string vproof) sum -> bool
  val strs_check : string trace -> string mtl -> string sproof -> bool
  val strv_check : string trace -> string mtl -> string vproof -> bool
  val strmaxreach : (string sproof, string vproof) sum -> nat
  val strminreach : (string sproof, string vproof) sum -> enat
  val is_opt_depth :
    string trace ->
      nat -> string mtl -> (string sproof, string vproof) sum -> bool
  val rmaxmaxreach :
    (string sproof, string vproof) sum ->
      (string sproof, string vproof) sum -> bool
  val rmaxminreach :
    (string sproof, string vproof) sum ->
      (string sproof, string vproof) sum -> bool
  val rminmaxreach :
    (string sproof, string vproof) sum ->
      (string sproof, string vproof) sum -> bool
  val rminminreach :
    (string sproof, string vproof) sum ->
      (string sproof, string vproof) sum -> bool
  val trace_of_list : ('a set * nat) list -> 'a trace
  val opt_maxmaxreach :
    string trace -> nat -> string mtl -> (string sproof, string vproof) sum
  val opt_maxminreach :
    string trace -> nat -> string mtl -> (string sproof, string vproof) sum
  val opt_minmaxreach :
    string trace -> nat -> string mtl -> (string sproof, string vproof) sum
  val opt_minminreach :
    string trace -> nat -> string mtl -> (string sproof, string vproof) sum
  val nat_of_integer : Z.t -> nat
  val is_opt_maxmaxreach :
    string trace ->
      nat -> string mtl -> (string sproof, string vproof) sum -> bool
  val is_opt_maxminreach :
    string trace ->
      nat -> string mtl -> (string sproof, string vproof) sum -> bool
  val is_opt_minmaxreach :
    string trace ->
      nat -> string mtl -> (string sproof, string vproof) sum -> bool
  val is_opt_minminreach :
    string trace ->
      nat -> string mtl -> (string sproof, string vproof) sum -> bool
end = struct

type nat = Nat of Z.t;;

let rec integer_of_nat (Nat x) = x;;

let rec equal_nata m n = Z.equal (integer_of_nat m) (integer_of_nat n);;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_nat = ({equal = equal_nata} : nat equal);;

let rec plus_nata m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

let plus_nat = ({plus = plus_nata} : nat plus);;

let zero_nata : nat = Nat Z.zero;;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

let zero_nat = ({zero = zero_nata} : nat zero);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec less_eq_nat m n = Z.leq (integer_of_nat m) (integer_of_nat n);;

let rec less_nat m n = Z.lt (integer_of_nat m) (integer_of_nat n);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

let rec inf_nata x = min ord_nat x;;

type 'a inf = {inf : 'a -> 'a -> 'a};;
let inf _A = _A.inf;;

let inf_nat = ({inf = inf_nata} : nat inf);;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec sup_nata x = max ord_nat x;;

type 'a sup = {sup : 'a -> 'a -> 'a};;
let sup _A = _A.sup;;

let sup_nat = ({sup = sup_nata} : nat sup);;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

let preorder_nat = ({ord_preorder = ord_nat} : nat preorder);;

let order_nat = ({preorder_order = preorder_nat} : nat order);;

type 'a semilattice_sup =
  {sup_semilattice_sup : 'a sup; order_semilattice_sup : 'a order};;

type 'a semilattice_inf =
  {inf_semilattice_inf : 'a inf; order_semilattice_inf : 'a order};;

type 'a lattice =
  {semilattice_inf_lattice : 'a semilattice_inf;
    semilattice_sup_lattice : 'a semilattice_sup};;

let semilattice_sup_nat =
  ({sup_semilattice_sup = sup_nat; order_semilattice_sup = order_nat} :
    nat semilattice_sup);;

let semilattice_inf_nat =
  ({inf_semilattice_inf = inf_nat; order_semilattice_inf = order_nat} :
    nat semilattice_inf);;

let lattice_nat =
  ({semilattice_inf_lattice = semilattice_inf_nat;
     semilattice_sup_lattice = semilattice_sup_nat}
    : nat lattice);;

let ceq_nata : (nat -> nat -> bool) option = Some equal_nata;;

type 'a ceq = {ceq : ('a -> 'a -> bool) option};;
let ceq _A = _A.ceq;;

let ceq_nat = ({ceq = ceq_nata} : nat ceq);;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

let semigroup_add_nat = ({plus_semigroup_add = plus_nat} : nat semigroup_add);;

let monoid_add_nat =
  ({semigroup_add_monoid_add = semigroup_add_nat; zero_monoid_add = zero_nat} :
    nat monoid_add);;

type ('a, 'b) phantom = Phantom of 'b;;

type set_impla = Set_Choose | Set_Collect | Set_DList | Set_RBT | Set_Monada;;

let set_impl_nata : (nat, set_impla) phantom = Phantom Set_RBT;;

type 'a set_impl = {set_impl : ('a, set_impla) phantom};;
let set_impl _A = _A.set_impl;;

let set_impl_nat = ({set_impl = set_impl_nata} : nat set_impl);;

type 'a linorder = {order_linorder : 'a order};;

let linorder_nat = ({order_linorder = order_nat} : nat linorder);;

type ordera = Eq | Lt | Gt;;

let rec eq _A a b = equal _A a b;;

let rec comparator_of (_A1, _A2)
  x y = (if less _A2.order_linorder.preorder_order.ord_preorder x y then Lt
          else (if eq _A1 x y then Eq else Gt));;

let rec compare_nat x = comparator_of (equal_nat, linorder_nat) x;;

let ccompare_nata : (nat -> nat -> ordera) option = Some compare_nat;;

type 'a ccompare = {ccompare : ('a -> 'a -> ordera) option};;
let ccompare _A = _A.ccompare;;

let ccompare_nat = ({ccompare = ccompare_nata} : nat ccompare);;

let rec equal_list _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_list _A x22 y22
    | [], [] -> true;;

type 'a vproof = VFF of nat | VAtm of 'a * nat | VNeg of 'a sproof |
  VDisj of 'a vproof * 'a vproof | VConjL of 'a vproof | VConjR of 'a vproof |
  VSince of nat * 'a vproof * 'a vproof list |
  VUntil of nat * 'a vproof list * 'a vproof |
  VSince_never of nat * nat * 'a vproof list |
  VUntil_never of nat * nat * 'a vproof list | VSince_le of nat |
  VNext of 'a vproof | VNext_ge of nat | VNext_le of nat | VPrev of 'a vproof |
  VPrev_ge of nat | VPrev_le of nat | VPrev_zero
and 'a sproof = STT of nat | SAtm of 'a * nat | SNeg of 'a vproof |
  SDisjL of 'a sproof | SDisjR of 'a sproof | SConj of 'a sproof * 'a sproof |
  SSince of 'a sproof * 'a sproof list | SUntil of 'a sproof list * 'a sproof |
  SNext of 'a sproof | SPrev of 'a sproof;;

let rec equal_sproof _A = ({equal = equal_sproofa _A} : 'a sproof equal)
and equal_sproofa _A
  x0 x1 = match x0, x1 with SNext x9, SPrev x10 -> false
    | SPrev x10, SNext x9 -> false
    | SUntil (x81, x82), SPrev x10 -> false
    | SPrev x10, SUntil (x81, x82) -> false
    | SUntil (x81, x82), SNext x9 -> false
    | SNext x9, SUntil (x81, x82) -> false
    | SSince (x71, x72), SPrev x10 -> false
    | SPrev x10, SSince (x71, x72) -> false
    | SSince (x71, x72), SNext x9 -> false
    | SNext x9, SSince (x71, x72) -> false
    | SSince (x71, x72), SUntil (x81, x82) -> false
    | SUntil (x81, x82), SSince (x71, x72) -> false
    | SConj (x61, x62), SPrev x10 -> false
    | SPrev x10, SConj (x61, x62) -> false
    | SConj (x61, x62), SNext x9 -> false
    | SNext x9, SConj (x61, x62) -> false
    | SConj (x61, x62), SUntil (x81, x82) -> false
    | SUntil (x81, x82), SConj (x61, x62) -> false
    | SConj (x61, x62), SSince (x71, x72) -> false
    | SSince (x71, x72), SConj (x61, x62) -> false
    | SDisjR x5, SPrev x10 -> false
    | SPrev x10, SDisjR x5 -> false
    | SDisjR x5, SNext x9 -> false
    | SNext x9, SDisjR x5 -> false
    | SDisjR x5, SUntil (x81, x82) -> false
    | SUntil (x81, x82), SDisjR x5 -> false
    | SDisjR x5, SSince (x71, x72) -> false
    | SSince (x71, x72), SDisjR x5 -> false
    | SDisjR x5, SConj (x61, x62) -> false
    | SConj (x61, x62), SDisjR x5 -> false
    | SDisjL x4, SPrev x10 -> false
    | SPrev x10, SDisjL x4 -> false
    | SDisjL x4, SNext x9 -> false
    | SNext x9, SDisjL x4 -> false
    | SDisjL x4, SUntil (x81, x82) -> false
    | SUntil (x81, x82), SDisjL x4 -> false
    | SDisjL x4, SSince (x71, x72) -> false
    | SSince (x71, x72), SDisjL x4 -> false
    | SDisjL x4, SConj (x61, x62) -> false
    | SConj (x61, x62), SDisjL x4 -> false
    | SDisjL x4, SDisjR x5 -> false
    | SDisjR x5, SDisjL x4 -> false
    | SNeg x3, SPrev x10 -> false
    | SPrev x10, SNeg x3 -> false
    | SNeg x3, SNext x9 -> false
    | SNext x9, SNeg x3 -> false
    | SNeg x3, SUntil (x81, x82) -> false
    | SUntil (x81, x82), SNeg x3 -> false
    | SNeg x3, SSince (x71, x72) -> false
    | SSince (x71, x72), SNeg x3 -> false
    | SNeg x3, SConj (x61, x62) -> false
    | SConj (x61, x62), SNeg x3 -> false
    | SNeg x3, SDisjR x5 -> false
    | SDisjR x5, SNeg x3 -> false
    | SNeg x3, SDisjL x4 -> false
    | SDisjL x4, SNeg x3 -> false
    | SAtm (x21, x22), SPrev x10 -> false
    | SPrev x10, SAtm (x21, x22) -> false
    | SAtm (x21, x22), SNext x9 -> false
    | SNext x9, SAtm (x21, x22) -> false
    | SAtm (x21, x22), SUntil (x81, x82) -> false
    | SUntil (x81, x82), SAtm (x21, x22) -> false
    | SAtm (x21, x22), SSince (x71, x72) -> false
    | SSince (x71, x72), SAtm (x21, x22) -> false
    | SAtm (x21, x22), SConj (x61, x62) -> false
    | SConj (x61, x62), SAtm (x21, x22) -> false
    | SAtm (x21, x22), SDisjR x5 -> false
    | SDisjR x5, SAtm (x21, x22) -> false
    | SAtm (x21, x22), SDisjL x4 -> false
    | SDisjL x4, SAtm (x21, x22) -> false
    | SAtm (x21, x22), SNeg x3 -> false
    | SNeg x3, SAtm (x21, x22) -> false
    | STT x1, SPrev x10 -> false
    | SPrev x10, STT x1 -> false
    | STT x1, SNext x9 -> false
    | SNext x9, STT x1 -> false
    | STT x1, SUntil (x81, x82) -> false
    | SUntil (x81, x82), STT x1 -> false
    | STT x1, SSince (x71, x72) -> false
    | SSince (x71, x72), STT x1 -> false
    | STT x1, SConj (x61, x62) -> false
    | SConj (x61, x62), STT x1 -> false
    | STT x1, SDisjR x5 -> false
    | SDisjR x5, STT x1 -> false
    | STT x1, SDisjL x4 -> false
    | SDisjL x4, STT x1 -> false
    | STT x1, SNeg x3 -> false
    | SNeg x3, STT x1 -> false
    | STT x1, SAtm (x21, x22) -> false
    | SAtm (x21, x22), STT x1 -> false
    | SPrev x10, SPrev y10 -> equal_sproofa _A x10 y10
    | SNext x9, SNext y9 -> equal_sproofa _A x9 y9
    | SUntil (x81, x82), SUntil (y81, y82) ->
        equal_list (equal_sproof _A) x81 y81 && equal_sproofa _A x82 y82
    | SSince (x71, x72), SSince (y71, y72) ->
        equal_sproofa _A x71 y71 && equal_list (equal_sproof _A) x72 y72
    | SConj (x61, x62), SConj (y61, y62) ->
        equal_sproofa _A x61 y61 && equal_sproofa _A x62 y62
    | SDisjR x5, SDisjR y5 -> equal_sproofa _A x5 y5
    | SDisjL x4, SDisjL y4 -> equal_sproofa _A x4 y4
    | SNeg x3, SNeg y3 -> equal_vproofa _A x3 y3
    | SAtm (x21, x22), SAtm (y21, y22) -> eq _A x21 y21 && equal_nata x22 y22
    | STT x1, STT y1 -> equal_nata x1 y1
and equal_vproofa _A
  x0 x1 = match x0, x1 with VPrev_le x17, VPrev_zero -> false
    | VPrev_zero, VPrev_le x17 -> false
    | VPrev_ge x16, VPrev_zero -> false
    | VPrev_zero, VPrev_ge x16 -> false
    | VPrev_ge x16, VPrev_le x17 -> false
    | VPrev_le x17, VPrev_ge x16 -> false
    | VPrev x15, VPrev_zero -> false
    | VPrev_zero, VPrev x15 -> false
    | VPrev x15, VPrev_le x17 -> false
    | VPrev_le x17, VPrev x15 -> false
    | VPrev x15, VPrev_ge x16 -> false
    | VPrev_ge x16, VPrev x15 -> false
    | VNext_le x14, VPrev_zero -> false
    | VPrev_zero, VNext_le x14 -> false
    | VNext_le x14, VPrev_le x17 -> false
    | VPrev_le x17, VNext_le x14 -> false
    | VNext_le x14, VPrev_ge x16 -> false
    | VPrev_ge x16, VNext_le x14 -> false
    | VNext_le x14, VPrev x15 -> false
    | VPrev x15, VNext_le x14 -> false
    | VNext_ge x13, VPrev_zero -> false
    | VPrev_zero, VNext_ge x13 -> false
    | VNext_ge x13, VPrev_le x17 -> false
    | VPrev_le x17, VNext_ge x13 -> false
    | VNext_ge x13, VPrev_ge x16 -> false
    | VPrev_ge x16, VNext_ge x13 -> false
    | VNext_ge x13, VPrev x15 -> false
    | VPrev x15, VNext_ge x13 -> false
    | VNext_ge x13, VNext_le x14 -> false
    | VNext_le x14, VNext_ge x13 -> false
    | VNext x12, VPrev_zero -> false
    | VPrev_zero, VNext x12 -> false
    | VNext x12, VPrev_le x17 -> false
    | VPrev_le x17, VNext x12 -> false
    | VNext x12, VPrev_ge x16 -> false
    | VPrev_ge x16, VNext x12 -> false
    | VNext x12, VPrev x15 -> false
    | VPrev x15, VNext x12 -> false
    | VNext x12, VNext_le x14 -> false
    | VNext_le x14, VNext x12 -> false
    | VNext x12, VNext_ge x13 -> false
    | VNext_ge x13, VNext x12 -> false
    | VSince_le x11, VPrev_zero -> false
    | VPrev_zero, VSince_le x11 -> false
    | VSince_le x11, VPrev_le x17 -> false
    | VPrev_le x17, VSince_le x11 -> false
    | VSince_le x11, VPrev_ge x16 -> false
    | VPrev_ge x16, VSince_le x11 -> false
    | VSince_le x11, VPrev x15 -> false
    | VPrev x15, VSince_le x11 -> false
    | VSince_le x11, VNext_le x14 -> false
    | VNext_le x14, VSince_le x11 -> false
    | VSince_le x11, VNext_ge x13 -> false
    | VNext_ge x13, VSince_le x11 -> false
    | VSince_le x11, VNext x12 -> false
    | VNext x12, VSince_le x11 -> false
    | VUntil_never (x101, x102, x103), VPrev_zero -> false
    | VPrev_zero, VUntil_never (x101, x102, x103) -> false
    | VUntil_never (x101, x102, x103), VPrev_le x17 -> false
    | VPrev_le x17, VUntil_never (x101, x102, x103) -> false
    | VUntil_never (x101, x102, x103), VPrev_ge x16 -> false
    | VPrev_ge x16, VUntil_never (x101, x102, x103) -> false
    | VUntil_never (x101, x102, x103), VPrev x15 -> false
    | VPrev x15, VUntil_never (x101, x102, x103) -> false
    | VUntil_never (x101, x102, x103), VNext_le x14 -> false
    | VNext_le x14, VUntil_never (x101, x102, x103) -> false
    | VUntil_never (x101, x102, x103), VNext_ge x13 -> false
    | VNext_ge x13, VUntil_never (x101, x102, x103) -> false
    | VUntil_never (x101, x102, x103), VNext x12 -> false
    | VNext x12, VUntil_never (x101, x102, x103) -> false
    | VUntil_never (x101, x102, x103), VSince_le x11 -> false
    | VSince_le x11, VUntil_never (x101, x102, x103) -> false
    | VSince_never (x91, x92, x93), VPrev_zero -> false
    | VPrev_zero, VSince_never (x91, x92, x93) -> false
    | VSince_never (x91, x92, x93), VPrev_le x17 -> false
    | VPrev_le x17, VSince_never (x91, x92, x93) -> false
    | VSince_never (x91, x92, x93), VPrev_ge x16 -> false
    | VPrev_ge x16, VSince_never (x91, x92, x93) -> false
    | VSince_never (x91, x92, x93), VPrev x15 -> false
    | VPrev x15, VSince_never (x91, x92, x93) -> false
    | VSince_never (x91, x92, x93), VNext_le x14 -> false
    | VNext_le x14, VSince_never (x91, x92, x93) -> false
    | VSince_never (x91, x92, x93), VNext_ge x13 -> false
    | VNext_ge x13, VSince_never (x91, x92, x93) -> false
    | VSince_never (x91, x92, x93), VNext x12 -> false
    | VNext x12, VSince_never (x91, x92, x93) -> false
    | VSince_never (x91, x92, x93), VSince_le x11 -> false
    | VSince_le x11, VSince_never (x91, x92, x93) -> false
    | VSince_never (x91, x92, x93), VUntil_never (x101, x102, x103) -> false
    | VUntil_never (x101, x102, x103), VSince_never (x91, x92, x93) -> false
    | VUntil (x81, x82, x83), VPrev_zero -> false
    | VPrev_zero, VUntil (x81, x82, x83) -> false
    | VUntil (x81, x82, x83), VPrev_le x17 -> false
    | VPrev_le x17, VUntil (x81, x82, x83) -> false
    | VUntil (x81, x82, x83), VPrev_ge x16 -> false
    | VPrev_ge x16, VUntil (x81, x82, x83) -> false
    | VUntil (x81, x82, x83), VPrev x15 -> false
    | VPrev x15, VUntil (x81, x82, x83) -> false
    | VUntil (x81, x82, x83), VNext_le x14 -> false
    | VNext_le x14, VUntil (x81, x82, x83) -> false
    | VUntil (x81, x82, x83), VNext_ge x13 -> false
    | VNext_ge x13, VUntil (x81, x82, x83) -> false
    | VUntil (x81, x82, x83), VNext x12 -> false
    | VNext x12, VUntil (x81, x82, x83) -> false
    | VUntil (x81, x82, x83), VSince_le x11 -> false
    | VSince_le x11, VUntil (x81, x82, x83) -> false
    | VUntil (x81, x82, x83), VUntil_never (x101, x102, x103) -> false
    | VUntil_never (x101, x102, x103), VUntil (x81, x82, x83) -> false
    | VUntil (x81, x82, x83), VSince_never (x91, x92, x93) -> false
    | VSince_never (x91, x92, x93), VUntil (x81, x82, x83) -> false
    | VSince (x71, x72, x73), VPrev_zero -> false
    | VPrev_zero, VSince (x71, x72, x73) -> false
    | VSince (x71, x72, x73), VPrev_le x17 -> false
    | VPrev_le x17, VSince (x71, x72, x73) -> false
    | VSince (x71, x72, x73), VPrev_ge x16 -> false
    | VPrev_ge x16, VSince (x71, x72, x73) -> false
    | VSince (x71, x72, x73), VPrev x15 -> false
    | VPrev x15, VSince (x71, x72, x73) -> false
    | VSince (x71, x72, x73), VNext_le x14 -> false
    | VNext_le x14, VSince (x71, x72, x73) -> false
    | VSince (x71, x72, x73), VNext_ge x13 -> false
    | VNext_ge x13, VSince (x71, x72, x73) -> false
    | VSince (x71, x72, x73), VNext x12 -> false
    | VNext x12, VSince (x71, x72, x73) -> false
    | VSince (x71, x72, x73), VSince_le x11 -> false
    | VSince_le x11, VSince (x71, x72, x73) -> false
    | VSince (x71, x72, x73), VUntil_never (x101, x102, x103) -> false
    | VUntil_never (x101, x102, x103), VSince (x71, x72, x73) -> false
    | VSince (x71, x72, x73), VSince_never (x91, x92, x93) -> false
    | VSince_never (x91, x92, x93), VSince (x71, x72, x73) -> false
    | VSince (x71, x72, x73), VUntil (x81, x82, x83) -> false
    | VUntil (x81, x82, x83), VSince (x71, x72, x73) -> false
    | VConjR x6, VPrev_zero -> false
    | VPrev_zero, VConjR x6 -> false
    | VConjR x6, VPrev_le x17 -> false
    | VPrev_le x17, VConjR x6 -> false
    | VConjR x6, VPrev_ge x16 -> false
    | VPrev_ge x16, VConjR x6 -> false
    | VConjR x6, VPrev x15 -> false
    | VPrev x15, VConjR x6 -> false
    | VConjR x6, VNext_le x14 -> false
    | VNext_le x14, VConjR x6 -> false
    | VConjR x6, VNext_ge x13 -> false
    | VNext_ge x13, VConjR x6 -> false
    | VConjR x6, VNext x12 -> false
    | VNext x12, VConjR x6 -> false
    | VConjR x6, VSince_le x11 -> false
    | VSince_le x11, VConjR x6 -> false
    | VConjR x6, VUntil_never (x101, x102, x103) -> false
    | VUntil_never (x101, x102, x103), VConjR x6 -> false
    | VConjR x6, VSince_never (x91, x92, x93) -> false
    | VSince_never (x91, x92, x93), VConjR x6 -> false
    | VConjR x6, VUntil (x81, x82, x83) -> false
    | VUntil (x81, x82, x83), VConjR x6 -> false
    | VConjR x6, VSince (x71, x72, x73) -> false
    | VSince (x71, x72, x73), VConjR x6 -> false
    | VConjL x5, VPrev_zero -> false
    | VPrev_zero, VConjL x5 -> false
    | VConjL x5, VPrev_le x17 -> false
    | VPrev_le x17, VConjL x5 -> false
    | VConjL x5, VPrev_ge x16 -> false
    | VPrev_ge x16, VConjL x5 -> false
    | VConjL x5, VPrev x15 -> false
    | VPrev x15, VConjL x5 -> false
    | VConjL x5, VNext_le x14 -> false
    | VNext_le x14, VConjL x5 -> false
    | VConjL x5, VNext_ge x13 -> false
    | VNext_ge x13, VConjL x5 -> false
    | VConjL x5, VNext x12 -> false
    | VNext x12, VConjL x5 -> false
    | VConjL x5, VSince_le x11 -> false
    | VSince_le x11, VConjL x5 -> false
    | VConjL x5, VUntil_never (x101, x102, x103) -> false
    | VUntil_never (x101, x102, x103), VConjL x5 -> false
    | VConjL x5, VSince_never (x91, x92, x93) -> false
    | VSince_never (x91, x92, x93), VConjL x5 -> false
    | VConjL x5, VUntil (x81, x82, x83) -> false
    | VUntil (x81, x82, x83), VConjL x5 -> false
    | VConjL x5, VSince (x71, x72, x73) -> false
    | VSince (x71, x72, x73), VConjL x5 -> false
    | VConjL x5, VConjR x6 -> false
    | VConjR x6, VConjL x5 -> false
    | VDisj (x41, x42), VPrev_zero -> false
    | VPrev_zero, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VPrev_le x17 -> false
    | VPrev_le x17, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VPrev_ge x16 -> false
    | VPrev_ge x16, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VPrev x15 -> false
    | VPrev x15, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VNext_le x14 -> false
    | VNext_le x14, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VNext_ge x13 -> false
    | VNext_ge x13, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VNext x12 -> false
    | VNext x12, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VSince_le x11 -> false
    | VSince_le x11, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VUntil_never (x101, x102, x103) -> false
    | VUntil_never (x101, x102, x103), VDisj (x41, x42) -> false
    | VDisj (x41, x42), VSince_never (x91, x92, x93) -> false
    | VSince_never (x91, x92, x93), VDisj (x41, x42) -> false
    | VDisj (x41, x42), VUntil (x81, x82, x83) -> false
    | VUntil (x81, x82, x83), VDisj (x41, x42) -> false
    | VDisj (x41, x42), VSince (x71, x72, x73) -> false
    | VSince (x71, x72, x73), VDisj (x41, x42) -> false
    | VDisj (x41, x42), VConjR x6 -> false
    | VConjR x6, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VConjL x5 -> false
    | VConjL x5, VDisj (x41, x42) -> false
    | VNeg x3, VPrev_zero -> false
    | VPrev_zero, VNeg x3 -> false
    | VNeg x3, VPrev_le x17 -> false
    | VPrev_le x17, VNeg x3 -> false
    | VNeg x3, VPrev_ge x16 -> false
    | VPrev_ge x16, VNeg x3 -> false
    | VNeg x3, VPrev x15 -> false
    | VPrev x15, VNeg x3 -> false
    | VNeg x3, VNext_le x14 -> false
    | VNext_le x14, VNeg x3 -> false
    | VNeg x3, VNext_ge x13 -> false
    | VNext_ge x13, VNeg x3 -> false
    | VNeg x3, VNext x12 -> false
    | VNext x12, VNeg x3 -> false
    | VNeg x3, VSince_le x11 -> false
    | VSince_le x11, VNeg x3 -> false
    | VNeg x3, VUntil_never (x101, x102, x103) -> false
    | VUntil_never (x101, x102, x103), VNeg x3 -> false
    | VNeg x3, VSince_never (x91, x92, x93) -> false
    | VSince_never (x91, x92, x93), VNeg x3 -> false
    | VNeg x3, VUntil (x81, x82, x83) -> false
    | VUntil (x81, x82, x83), VNeg x3 -> false
    | VNeg x3, VSince (x71, x72, x73) -> false
    | VSince (x71, x72, x73), VNeg x3 -> false
    | VNeg x3, VConjR x6 -> false
    | VConjR x6, VNeg x3 -> false
    | VNeg x3, VConjL x5 -> false
    | VConjL x5, VNeg x3 -> false
    | VNeg x3, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VNeg x3 -> false
    | VAtm (x21, x22), VPrev_zero -> false
    | VPrev_zero, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VPrev_le x17 -> false
    | VPrev_le x17, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VPrev_ge x16 -> false
    | VPrev_ge x16, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VPrev x15 -> false
    | VPrev x15, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VNext_le x14 -> false
    | VNext_le x14, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VNext_ge x13 -> false
    | VNext_ge x13, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VNext x12 -> false
    | VNext x12, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VSince_le x11 -> false
    | VSince_le x11, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VUntil_never (x101, x102, x103) -> false
    | VUntil_never (x101, x102, x103), VAtm (x21, x22) -> false
    | VAtm (x21, x22), VSince_never (x91, x92, x93) -> false
    | VSince_never (x91, x92, x93), VAtm (x21, x22) -> false
    | VAtm (x21, x22), VUntil (x81, x82, x83) -> false
    | VUntil (x81, x82, x83), VAtm (x21, x22) -> false
    | VAtm (x21, x22), VSince (x71, x72, x73) -> false
    | VSince (x71, x72, x73), VAtm (x21, x22) -> false
    | VAtm (x21, x22), VConjR x6 -> false
    | VConjR x6, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VConjL x5 -> false
    | VConjL x5, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VDisj (x41, x42) -> false
    | VDisj (x41, x42), VAtm (x21, x22) -> false
    | VAtm (x21, x22), VNeg x3 -> false
    | VNeg x3, VAtm (x21, x22) -> false
    | VFF x1, VPrev_zero -> false
    | VPrev_zero, VFF x1 -> false
    | VFF x1, VPrev_le x17 -> false
    | VPrev_le x17, VFF x1 -> false
    | VFF x1, VPrev_ge x16 -> false
    | VPrev_ge x16, VFF x1 -> false
    | VFF x1, VPrev x15 -> false
    | VPrev x15, VFF x1 -> false
    | VFF x1, VNext_le x14 -> false
    | VNext_le x14, VFF x1 -> false
    | VFF x1, VNext_ge x13 -> false
    | VNext_ge x13, VFF x1 -> false
    | VFF x1, VNext x12 -> false
    | VNext x12, VFF x1 -> false
    | VFF x1, VSince_le x11 -> false
    | VSince_le x11, VFF x1 -> false
    | VFF x1, VUntil_never (x101, x102, x103) -> false
    | VUntil_never (x101, x102, x103), VFF x1 -> false
    | VFF x1, VSince_never (x91, x92, x93) -> false
    | VSince_never (x91, x92, x93), VFF x1 -> false
    | VFF x1, VUntil (x81, x82, x83) -> false
    | VUntil (x81, x82, x83), VFF x1 -> false
    | VFF x1, VSince (x71, x72, x73) -> false
    | VSince (x71, x72, x73), VFF x1 -> false
    | VFF x1, VConjR x6 -> false
    | VConjR x6, VFF x1 -> false
    | VFF x1, VConjL x5 -> false
    | VConjL x5, VFF x1 -> false
    | VFF x1, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VFF x1 -> false
    | VFF x1, VNeg x3 -> false
    | VNeg x3, VFF x1 -> false
    | VFF x1, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VFF x1 -> false
    | VPrev_le x17, VPrev_le y17 -> equal_nata x17 y17
    | VPrev_ge x16, VPrev_ge y16 -> equal_nata x16 y16
    | VPrev x15, VPrev y15 -> equal_vproofa _A x15 y15
    | VNext_le x14, VNext_le y14 -> equal_nata x14 y14
    | VNext_ge x13, VNext_ge y13 -> equal_nata x13 y13
    | VNext x12, VNext y12 -> equal_vproofa _A x12 y12
    | VSince_le x11, VSince_le y11 -> equal_nata x11 y11
    | VUntil_never (x101, x102, x103), VUntil_never (y101, y102, y103) ->
        equal_nata x101 y101 &&
          (equal_nata x102 y102 && equal_list (equal_vproof _A) x103 y103)
    | VSince_never (x91, x92, x93), VSince_never (y91, y92, y93) ->
        equal_nata x91 y91 &&
          (equal_nata x92 y92 && equal_list (equal_vproof _A) x93 y93)
    | VUntil (x81, x82, x83), VUntil (y81, y82, y83) ->
        equal_nata x81 y81 &&
          (equal_list (equal_vproof _A) x82 y82 && equal_vproofa _A x83 y83)
    | VSince (x71, x72, x73), VSince (y71, y72, y73) ->
        equal_nata x71 y71 &&
          (equal_vproofa _A x72 y72 && equal_list (equal_vproof _A) x73 y73)
    | VConjR x6, VConjR y6 -> equal_vproofa _A x6 y6
    | VConjL x5, VConjL y5 -> equal_vproofa _A x5 y5
    | VDisj (x41, x42), VDisj (y41, y42) ->
        equal_vproofa _A x41 y41 && equal_vproofa _A x42 y42
    | VNeg x3, VNeg y3 -> equal_sproofa _A x3 y3
    | VAtm (x21, x22), VAtm (y21, y22) -> eq _A x21 y21 && equal_nata x22 y22
    | VFF x1, VFF y1 -> equal_nata x1 y1
    | VPrev_zero, VPrev_zero -> true
and equal_vproof _A = ({equal = equal_vproofa _A} : 'a vproof equal);;

let rec ceq_sproofa _A = Some (equal_sproofa _A);;

let rec ceq_sproof _A = ({ceq = ceq_sproofa _A} : 'a sproof ceq);;

let set_impl_sproofa : ('a sproof, set_impla) phantom = Phantom Set_RBT;;

let set_impl_sproof = ({set_impl = set_impl_sproofa} : 'a sproof set_impl);;

let rec comparator_list
  comp_a x1 x2 = match comp_a, x1, x2 with
    comp_a, x :: xa, y :: ya ->
      (match comp_a x y with Eq -> comparator_list comp_a xa ya | Lt -> Lt
        | Gt -> Gt)
    | comp_a, x :: xa, [] -> Gt
    | comp_a, [], y :: ya -> Lt
    | comp_a, [], [] -> Eq;;

let rec comparator_sproof
  comp_a x1 x2 = match comp_a, x1, x2 with
    comp_a, SPrev x, SPrev ym -> comparator_sproof comp_a x ym
    | comp_a, SPrev x, SNext yl -> Gt
    | comp_a, SPrev x, SUntil (yj, yk) -> Gt
    | comp_a, SPrev x, SSince (yh, yi) -> Gt
    | comp_a, SPrev x, SConj (yf, yg) -> Gt
    | comp_a, SPrev x, SDisjR ye -> Gt
    | comp_a, SPrev x, SDisjL yd -> Gt
    | comp_a, SPrev x, SNeg yc -> Gt
    | comp_a, SPrev x, SAtm (ya, yb) -> Gt
    | comp_a, SPrev x, STT y -> Gt
    | comp_a, SNext x, SPrev ym -> Lt
    | comp_a, SNext x, SNext yl -> comparator_sproof comp_a x yl
    | comp_a, SNext x, SUntil (yj, yk) -> Gt
    | comp_a, SNext x, SSince (yh, yi) -> Gt
    | comp_a, SNext x, SConj (yf, yg) -> Gt
    | comp_a, SNext x, SDisjR ye -> Gt
    | comp_a, SNext x, SDisjL yd -> Gt
    | comp_a, SNext x, SNeg yc -> Gt
    | comp_a, SNext x, SAtm (ya, yb) -> Gt
    | comp_a, SNext x, STT y -> Gt
    | comp_a, SUntil (x, xa), SPrev ym -> Lt
    | comp_a, SUntil (x, xa), SNext yl -> Lt
    | comp_a, SUntil (x, xa), SUntil (yj, yk) ->
        (match comparator_list (comparator_sproof comp_a) x yj
          with Eq -> comparator_sproof comp_a xa yk | Lt -> Lt | Gt -> Gt)
    | comp_a, SUntil (x, xa), SSince (yh, yi) -> Gt
    | comp_a, SUntil (x, xa), SConj (yf, yg) -> Gt
    | comp_a, SUntil (x, xa), SDisjR ye -> Gt
    | comp_a, SUntil (x, xa), SDisjL yd -> Gt
    | comp_a, SUntil (x, xa), SNeg yc -> Gt
    | comp_a, SUntil (x, xa), SAtm (ya, yb) -> Gt
    | comp_a, SUntil (x, xa), STT y -> Gt
    | comp_a, SSince (x, xa), SPrev ym -> Lt
    | comp_a, SSince (x, xa), SNext yl -> Lt
    | comp_a, SSince (x, xa), SUntil (yj, yk) -> Lt
    | comp_a, SSince (x, xa), SSince (yh, yi) ->
        (match comparator_sproof comp_a x yh
          with Eq -> comparator_list (comparator_sproof comp_a) xa yi | Lt -> Lt
          | Gt -> Gt)
    | comp_a, SSince (x, xa), SConj (yf, yg) -> Gt
    | comp_a, SSince (x, xa), SDisjR ye -> Gt
    | comp_a, SSince (x, xa), SDisjL yd -> Gt
    | comp_a, SSince (x, xa), SNeg yc -> Gt
    | comp_a, SSince (x, xa), SAtm (ya, yb) -> Gt
    | comp_a, SSince (x, xa), STT y -> Gt
    | comp_a, SConj (x, xa), SPrev ym -> Lt
    | comp_a, SConj (x, xa), SNext yl -> Lt
    | comp_a, SConj (x, xa), SUntil (yj, yk) -> Lt
    | comp_a, SConj (x, xa), SSince (yh, yi) -> Lt
    | comp_a, SConj (x, xa), SConj (yf, yg) ->
        (match comparator_sproof comp_a x yf
          with Eq -> comparator_sproof comp_a xa yg | Lt -> Lt | Gt -> Gt)
    | comp_a, SConj (x, xa), SDisjR ye -> Gt
    | comp_a, SConj (x, xa), SDisjL yd -> Gt
    | comp_a, SConj (x, xa), SNeg yc -> Gt
    | comp_a, SConj (x, xa), SAtm (ya, yb) -> Gt
    | comp_a, SConj (x, xa), STT y -> Gt
    | comp_a, SDisjR x, SPrev ym -> Lt
    | comp_a, SDisjR x, SNext yl -> Lt
    | comp_a, SDisjR x, SUntil (yj, yk) -> Lt
    | comp_a, SDisjR x, SSince (yh, yi) -> Lt
    | comp_a, SDisjR x, SConj (yf, yg) -> Lt
    | comp_a, SDisjR x, SDisjR ye -> comparator_sproof comp_a x ye
    | comp_a, SDisjR x, SDisjL yd -> Gt
    | comp_a, SDisjR x, SNeg yc -> Gt
    | comp_a, SDisjR x, SAtm (ya, yb) -> Gt
    | comp_a, SDisjR x, STT y -> Gt
    | comp_a, SDisjL x, SPrev ym -> Lt
    | comp_a, SDisjL x, SNext yl -> Lt
    | comp_a, SDisjL x, SUntil (yj, yk) -> Lt
    | comp_a, SDisjL x, SSince (yh, yi) -> Lt
    | comp_a, SDisjL x, SConj (yf, yg) -> Lt
    | comp_a, SDisjL x, SDisjR ye -> Lt
    | comp_a, SDisjL x, SDisjL yd -> comparator_sproof comp_a x yd
    | comp_a, SDisjL x, SNeg yc -> Gt
    | comp_a, SDisjL x, SAtm (ya, yb) -> Gt
    | comp_a, SDisjL x, STT y -> Gt
    | comp_a, SNeg x, SPrev ym -> Lt
    | comp_a, SNeg x, SNext yl -> Lt
    | comp_a, SNeg x, SUntil (yj, yk) -> Lt
    | comp_a, SNeg x, SSince (yh, yi) -> Lt
    | comp_a, SNeg x, SConj (yf, yg) -> Lt
    | comp_a, SNeg x, SDisjR ye -> Lt
    | comp_a, SNeg x, SDisjL yd -> Lt
    | comp_a, SNeg x, SNeg yc -> comparator_vproof comp_a x yc
    | comp_a, SNeg x, SAtm (ya, yb) -> Gt
    | comp_a, SNeg x, STT y -> Gt
    | comp_a, SAtm (x, xa), SPrev ym -> Lt
    | comp_a, SAtm (x, xa), SNext yl -> Lt
    | comp_a, SAtm (x, xa), SUntil (yj, yk) -> Lt
    | comp_a, SAtm (x, xa), SSince (yh, yi) -> Lt
    | comp_a, SAtm (x, xa), SConj (yf, yg) -> Lt
    | comp_a, SAtm (x, xa), SDisjR ye -> Lt
    | comp_a, SAtm (x, xa), SDisjL yd -> Lt
    | comp_a, SAtm (x, xa), SNeg yc -> Lt
    | comp_a, SAtm (x, xa), SAtm (ya, yb) ->
        (match comp_a x ya
          with Eq -> comparator_of (equal_nat, linorder_nat) xa yb | Lt -> Lt
          | Gt -> Gt)
    | comp_a, SAtm (x, xa), STT y -> Gt
    | comp_a, STT x, SPrev ym -> Lt
    | comp_a, STT x, SNext yl -> Lt
    | comp_a, STT x, SUntil (yj, yk) -> Lt
    | comp_a, STT x, SSince (yh, yi) -> Lt
    | comp_a, STT x, SConj (yf, yg) -> Lt
    | comp_a, STT x, SDisjR ye -> Lt
    | comp_a, STT x, SDisjL yd -> Lt
    | comp_a, STT x, SNeg yc -> Lt
    | comp_a, STT x, SAtm (ya, yb) -> Lt
    | comp_a, STT x, STT y -> comparator_of (equal_nat, linorder_nat) x y
and comparator_vproof
  comp_a x1 x2 = match comp_a, x1, x2 with comp_a, VPrev_zero, VPrev_zero -> Eq
    | comp_a, VPrev_zero, VPrev_le yz -> Gt
    | comp_a, VPrev_zero, VPrev_ge yy -> Gt
    | comp_a, VPrev_zero, VPrev yx -> Gt
    | comp_a, VPrev_zero, VNext_le yw -> Gt
    | comp_a, VPrev_zero, VNext_ge yv -> Gt
    | comp_a, VPrev_zero, VNext yu -> Gt
    | comp_a, VPrev_zero, VSince_le yt -> Gt
    | comp_a, VPrev_zero, VUntil_never (yq, yr, ys) -> Gt
    | comp_a, VPrev_zero, VSince_never (yn, yo, yp) -> Gt
    | comp_a, VPrev_zero, VUntil (yk, yl, ym) -> Gt
    | comp_a, VPrev_zero, VSince (yh, yi, yj) -> Gt
    | comp_a, VPrev_zero, VConjR yg -> Gt
    | comp_a, VPrev_zero, VConjL yf -> Gt
    | comp_a, VPrev_zero, VDisj (yd, ye) -> Gt
    | comp_a, VPrev_zero, VNeg yc -> Gt
    | comp_a, VPrev_zero, VAtm (ya, yb) -> Gt
    | comp_a, VPrev_zero, VFF y -> Gt
    | comp_a, VPrev_le x, VPrev_zero -> Lt
    | comp_a, VPrev_le x, VPrev_le yz ->
        comparator_of (equal_nat, linorder_nat) x yz
    | comp_a, VPrev_le x, VPrev_ge yy -> Gt
    | comp_a, VPrev_le x, VPrev yx -> Gt
    | comp_a, VPrev_le x, VNext_le yw -> Gt
    | comp_a, VPrev_le x, VNext_ge yv -> Gt
    | comp_a, VPrev_le x, VNext yu -> Gt
    | comp_a, VPrev_le x, VSince_le yt -> Gt
    | comp_a, VPrev_le x, VUntil_never (yq, yr, ys) -> Gt
    | comp_a, VPrev_le x, VSince_never (yn, yo, yp) -> Gt
    | comp_a, VPrev_le x, VUntil (yk, yl, ym) -> Gt
    | comp_a, VPrev_le x, VSince (yh, yi, yj) -> Gt
    | comp_a, VPrev_le x, VConjR yg -> Gt
    | comp_a, VPrev_le x, VConjL yf -> Gt
    | comp_a, VPrev_le x, VDisj (yd, ye) -> Gt
    | comp_a, VPrev_le x, VNeg yc -> Gt
    | comp_a, VPrev_le x, VAtm (ya, yb) -> Gt
    | comp_a, VPrev_le x, VFF y -> Gt
    | comp_a, VPrev_ge x, VPrev_zero -> Lt
    | comp_a, VPrev_ge x, VPrev_le yz -> Lt
    | comp_a, VPrev_ge x, VPrev_ge yy ->
        comparator_of (equal_nat, linorder_nat) x yy
    | comp_a, VPrev_ge x, VPrev yx -> Gt
    | comp_a, VPrev_ge x, VNext_le yw -> Gt
    | comp_a, VPrev_ge x, VNext_ge yv -> Gt
    | comp_a, VPrev_ge x, VNext yu -> Gt
    | comp_a, VPrev_ge x, VSince_le yt -> Gt
    | comp_a, VPrev_ge x, VUntil_never (yq, yr, ys) -> Gt
    | comp_a, VPrev_ge x, VSince_never (yn, yo, yp) -> Gt
    | comp_a, VPrev_ge x, VUntil (yk, yl, ym) -> Gt
    | comp_a, VPrev_ge x, VSince (yh, yi, yj) -> Gt
    | comp_a, VPrev_ge x, VConjR yg -> Gt
    | comp_a, VPrev_ge x, VConjL yf -> Gt
    | comp_a, VPrev_ge x, VDisj (yd, ye) -> Gt
    | comp_a, VPrev_ge x, VNeg yc -> Gt
    | comp_a, VPrev_ge x, VAtm (ya, yb) -> Gt
    | comp_a, VPrev_ge x, VFF y -> Gt
    | comp_a, VPrev x, VPrev_zero -> Lt
    | comp_a, VPrev x, VPrev_le yz -> Lt
    | comp_a, VPrev x, VPrev_ge yy -> Lt
    | comp_a, VPrev x, VPrev yx -> comparator_vproof comp_a x yx
    | comp_a, VPrev x, VNext_le yw -> Gt
    | comp_a, VPrev x, VNext_ge yv -> Gt
    | comp_a, VPrev x, VNext yu -> Gt
    | comp_a, VPrev x, VSince_le yt -> Gt
    | comp_a, VPrev x, VUntil_never (yq, yr, ys) -> Gt
    | comp_a, VPrev x, VSince_never (yn, yo, yp) -> Gt
    | comp_a, VPrev x, VUntil (yk, yl, ym) -> Gt
    | comp_a, VPrev x, VSince (yh, yi, yj) -> Gt
    | comp_a, VPrev x, VConjR yg -> Gt
    | comp_a, VPrev x, VConjL yf -> Gt
    | comp_a, VPrev x, VDisj (yd, ye) -> Gt
    | comp_a, VPrev x, VNeg yc -> Gt
    | comp_a, VPrev x, VAtm (ya, yb) -> Gt
    | comp_a, VPrev x, VFF y -> Gt
    | comp_a, VNext_le x, VPrev_zero -> Lt
    | comp_a, VNext_le x, VPrev_le yz -> Lt
    | comp_a, VNext_le x, VPrev_ge yy -> Lt
    | comp_a, VNext_le x, VPrev yx -> Lt
    | comp_a, VNext_le x, VNext_le yw ->
        comparator_of (equal_nat, linorder_nat) x yw
    | comp_a, VNext_le x, VNext_ge yv -> Gt
    | comp_a, VNext_le x, VNext yu -> Gt
    | comp_a, VNext_le x, VSince_le yt -> Gt
    | comp_a, VNext_le x, VUntil_never (yq, yr, ys) -> Gt
    | comp_a, VNext_le x, VSince_never (yn, yo, yp) -> Gt
    | comp_a, VNext_le x, VUntil (yk, yl, ym) -> Gt
    | comp_a, VNext_le x, VSince (yh, yi, yj) -> Gt
    | comp_a, VNext_le x, VConjR yg -> Gt
    | comp_a, VNext_le x, VConjL yf -> Gt
    | comp_a, VNext_le x, VDisj (yd, ye) -> Gt
    | comp_a, VNext_le x, VNeg yc -> Gt
    | comp_a, VNext_le x, VAtm (ya, yb) -> Gt
    | comp_a, VNext_le x, VFF y -> Gt
    | comp_a, VNext_ge x, VPrev_zero -> Lt
    | comp_a, VNext_ge x, VPrev_le yz -> Lt
    | comp_a, VNext_ge x, VPrev_ge yy -> Lt
    | comp_a, VNext_ge x, VPrev yx -> Lt
    | comp_a, VNext_ge x, VNext_le yw -> Lt
    | comp_a, VNext_ge x, VNext_ge yv ->
        comparator_of (equal_nat, linorder_nat) x yv
    | comp_a, VNext_ge x, VNext yu -> Gt
    | comp_a, VNext_ge x, VSince_le yt -> Gt
    | comp_a, VNext_ge x, VUntil_never (yq, yr, ys) -> Gt
    | comp_a, VNext_ge x, VSince_never (yn, yo, yp) -> Gt
    | comp_a, VNext_ge x, VUntil (yk, yl, ym) -> Gt
    | comp_a, VNext_ge x, VSince (yh, yi, yj) -> Gt
    | comp_a, VNext_ge x, VConjR yg -> Gt
    | comp_a, VNext_ge x, VConjL yf -> Gt
    | comp_a, VNext_ge x, VDisj (yd, ye) -> Gt
    | comp_a, VNext_ge x, VNeg yc -> Gt
    | comp_a, VNext_ge x, VAtm (ya, yb) -> Gt
    | comp_a, VNext_ge x, VFF y -> Gt
    | comp_a, VNext x, VPrev_zero -> Lt
    | comp_a, VNext x, VPrev_le yz -> Lt
    | comp_a, VNext x, VPrev_ge yy -> Lt
    | comp_a, VNext x, VPrev yx -> Lt
    | comp_a, VNext x, VNext_le yw -> Lt
    | comp_a, VNext x, VNext_ge yv -> Lt
    | comp_a, VNext x, VNext yu -> comparator_vproof comp_a x yu
    | comp_a, VNext x, VSince_le yt -> Gt
    | comp_a, VNext x, VUntil_never (yq, yr, ys) -> Gt
    | comp_a, VNext x, VSince_never (yn, yo, yp) -> Gt
    | comp_a, VNext x, VUntil (yk, yl, ym) -> Gt
    | comp_a, VNext x, VSince (yh, yi, yj) -> Gt
    | comp_a, VNext x, VConjR yg -> Gt
    | comp_a, VNext x, VConjL yf -> Gt
    | comp_a, VNext x, VDisj (yd, ye) -> Gt
    | comp_a, VNext x, VNeg yc -> Gt
    | comp_a, VNext x, VAtm (ya, yb) -> Gt
    | comp_a, VNext x, VFF y -> Gt
    | comp_a, VSince_le x, VPrev_zero -> Lt
    | comp_a, VSince_le x, VPrev_le yz -> Lt
    | comp_a, VSince_le x, VPrev_ge yy -> Lt
    | comp_a, VSince_le x, VPrev yx -> Lt
    | comp_a, VSince_le x, VNext_le yw -> Lt
    | comp_a, VSince_le x, VNext_ge yv -> Lt
    | comp_a, VSince_le x, VNext yu -> Lt
    | comp_a, VSince_le x, VSince_le yt ->
        comparator_of (equal_nat, linorder_nat) x yt
    | comp_a, VSince_le x, VUntil_never (yq, yr, ys) -> Gt
    | comp_a, VSince_le x, VSince_never (yn, yo, yp) -> Gt
    | comp_a, VSince_le x, VUntil (yk, yl, ym) -> Gt
    | comp_a, VSince_le x, VSince (yh, yi, yj) -> Gt
    | comp_a, VSince_le x, VConjR yg -> Gt
    | comp_a, VSince_le x, VConjL yf -> Gt
    | comp_a, VSince_le x, VDisj (yd, ye) -> Gt
    | comp_a, VSince_le x, VNeg yc -> Gt
    | comp_a, VSince_le x, VAtm (ya, yb) -> Gt
    | comp_a, VSince_le x, VFF y -> Gt
    | comp_a, VUntil_never (x, xa, xb), VPrev_zero -> Lt
    | comp_a, VUntil_never (x, xa, xb), VPrev_le yz -> Lt
    | comp_a, VUntil_never (x, xa, xb), VPrev_ge yy -> Lt
    | comp_a, VUntil_never (x, xa, xb), VPrev yx -> Lt
    | comp_a, VUntil_never (x, xa, xb), VNext_le yw -> Lt
    | comp_a, VUntil_never (x, xa, xb), VNext_ge yv -> Lt
    | comp_a, VUntil_never (x, xa, xb), VNext yu -> Lt
    | comp_a, VUntil_never (x, xa, xb), VSince_le yt -> Lt
    | comp_a, VUntil_never (x, xa, xb), VUntil_never (yq, yr, ys) ->
        (match comparator_of (equal_nat, linorder_nat) x yq
          with Eq ->
            (match comparator_of (equal_nat, linorder_nat) xa yr
              with Eq -> comparator_list (comparator_vproof comp_a) xb ys
              | Lt -> Lt | Gt -> Gt)
          | Lt -> Lt | Gt -> Gt)
    | comp_a, VUntil_never (x, xa, xb), VSince_never (yn, yo, yp) -> Gt
    | comp_a, VUntil_never (x, xa, xb), VUntil (yk, yl, ym) -> Gt
    | comp_a, VUntil_never (x, xa, xb), VSince (yh, yi, yj) -> Gt
    | comp_a, VUntil_never (x, xa, xb), VConjR yg -> Gt
    | comp_a, VUntil_never (x, xa, xb), VConjL yf -> Gt
    | comp_a, VUntil_never (x, xa, xb), VDisj (yd, ye) -> Gt
    | comp_a, VUntil_never (x, xa, xb), VNeg yc -> Gt
    | comp_a, VUntil_never (x, xa, xb), VAtm (ya, yb) -> Gt
    | comp_a, VUntil_never (x, xa, xb), VFF y -> Gt
    | comp_a, VSince_never (x, xa, xb), VPrev_zero -> Lt
    | comp_a, VSince_never (x, xa, xb), VPrev_le yz -> Lt
    | comp_a, VSince_never (x, xa, xb), VPrev_ge yy -> Lt
    | comp_a, VSince_never (x, xa, xb), VPrev yx -> Lt
    | comp_a, VSince_never (x, xa, xb), VNext_le yw -> Lt
    | comp_a, VSince_never (x, xa, xb), VNext_ge yv -> Lt
    | comp_a, VSince_never (x, xa, xb), VNext yu -> Lt
    | comp_a, VSince_never (x, xa, xb), VSince_le yt -> Lt
    | comp_a, VSince_never (x, xa, xb), VUntil_never (yq, yr, ys) -> Lt
    | comp_a, VSince_never (x, xa, xb), VSince_never (yn, yo, yp) ->
        (match comparator_of (equal_nat, linorder_nat) x yn
          with Eq ->
            (match comparator_of (equal_nat, linorder_nat) xa yo
              with Eq -> comparator_list (comparator_vproof comp_a) xb yp
              | Lt -> Lt | Gt -> Gt)
          | Lt -> Lt | Gt -> Gt)
    | comp_a, VSince_never (x, xa, xb), VUntil (yk, yl, ym) -> Gt
    | comp_a, VSince_never (x, xa, xb), VSince (yh, yi, yj) -> Gt
    | comp_a, VSince_never (x, xa, xb), VConjR yg -> Gt
    | comp_a, VSince_never (x, xa, xb), VConjL yf -> Gt
    | comp_a, VSince_never (x, xa, xb), VDisj (yd, ye) -> Gt
    | comp_a, VSince_never (x, xa, xb), VNeg yc -> Gt
    | comp_a, VSince_never (x, xa, xb), VAtm (ya, yb) -> Gt
    | comp_a, VSince_never (x, xa, xb), VFF y -> Gt
    | comp_a, VUntil (x, xa, xb), VPrev_zero -> Lt
    | comp_a, VUntil (x, xa, xb), VPrev_le yz -> Lt
    | comp_a, VUntil (x, xa, xb), VPrev_ge yy -> Lt
    | comp_a, VUntil (x, xa, xb), VPrev yx -> Lt
    | comp_a, VUntil (x, xa, xb), VNext_le yw -> Lt
    | comp_a, VUntil (x, xa, xb), VNext_ge yv -> Lt
    | comp_a, VUntil (x, xa, xb), VNext yu -> Lt
    | comp_a, VUntil (x, xa, xb), VSince_le yt -> Lt
    | comp_a, VUntil (x, xa, xb), VUntil_never (yq, yr, ys) -> Lt
    | comp_a, VUntil (x, xa, xb), VSince_never (yn, yo, yp) -> Lt
    | comp_a, VUntil (x, xa, xb), VUntil (yk, yl, ym) ->
        (match comparator_of (equal_nat, linorder_nat) x yk
          with Eq ->
            (match comparator_list (comparator_vproof comp_a) xa yl
              with Eq -> comparator_vproof comp_a xb ym | Lt -> Lt | Gt -> Gt)
          | Lt -> Lt | Gt -> Gt)
    | comp_a, VUntil (x, xa, xb), VSince (yh, yi, yj) -> Gt
    | comp_a, VUntil (x, xa, xb), VConjR yg -> Gt
    | comp_a, VUntil (x, xa, xb), VConjL yf -> Gt
    | comp_a, VUntil (x, xa, xb), VDisj (yd, ye) -> Gt
    | comp_a, VUntil (x, xa, xb), VNeg yc -> Gt
    | comp_a, VUntil (x, xa, xb), VAtm (ya, yb) -> Gt
    | comp_a, VUntil (x, xa, xb), VFF y -> Gt
    | comp_a, VSince (x, xa, xb), VPrev_zero -> Lt
    | comp_a, VSince (x, xa, xb), VPrev_le yz -> Lt
    | comp_a, VSince (x, xa, xb), VPrev_ge yy -> Lt
    | comp_a, VSince (x, xa, xb), VPrev yx -> Lt
    | comp_a, VSince (x, xa, xb), VNext_le yw -> Lt
    | comp_a, VSince (x, xa, xb), VNext_ge yv -> Lt
    | comp_a, VSince (x, xa, xb), VNext yu -> Lt
    | comp_a, VSince (x, xa, xb), VSince_le yt -> Lt
    | comp_a, VSince (x, xa, xb), VUntil_never (yq, yr, ys) -> Lt
    | comp_a, VSince (x, xa, xb), VSince_never (yn, yo, yp) -> Lt
    | comp_a, VSince (x, xa, xb), VUntil (yk, yl, ym) -> Lt
    | comp_a, VSince (x, xa, xb), VSince (yh, yi, yj) ->
        (match comparator_of (equal_nat, linorder_nat) x yh
          with Eq ->
            (match comparator_vproof comp_a xa yi
              with Eq -> comparator_list (comparator_vproof comp_a) xb yj
              | Lt -> Lt | Gt -> Gt)
          | Lt -> Lt | Gt -> Gt)
    | comp_a, VSince (x, xa, xb), VConjR yg -> Gt
    | comp_a, VSince (x, xa, xb), VConjL yf -> Gt
    | comp_a, VSince (x, xa, xb), VDisj (yd, ye) -> Gt
    | comp_a, VSince (x, xa, xb), VNeg yc -> Gt
    | comp_a, VSince (x, xa, xb), VAtm (ya, yb) -> Gt
    | comp_a, VSince (x, xa, xb), VFF y -> Gt
    | comp_a, VConjR x, VPrev_zero -> Lt
    | comp_a, VConjR x, VPrev_le yz -> Lt
    | comp_a, VConjR x, VPrev_ge yy -> Lt
    | comp_a, VConjR x, VPrev yx -> Lt
    | comp_a, VConjR x, VNext_le yw -> Lt
    | comp_a, VConjR x, VNext_ge yv -> Lt
    | comp_a, VConjR x, VNext yu -> Lt
    | comp_a, VConjR x, VSince_le yt -> Lt
    | comp_a, VConjR x, VUntil_never (yq, yr, ys) -> Lt
    | comp_a, VConjR x, VSince_never (yn, yo, yp) -> Lt
    | comp_a, VConjR x, VUntil (yk, yl, ym) -> Lt
    | comp_a, VConjR x, VSince (yh, yi, yj) -> Lt
    | comp_a, VConjR x, VConjR yg -> comparator_vproof comp_a x yg
    | comp_a, VConjR x, VConjL yf -> Gt
    | comp_a, VConjR x, VDisj (yd, ye) -> Gt
    | comp_a, VConjR x, VNeg yc -> Gt
    | comp_a, VConjR x, VAtm (ya, yb) -> Gt
    | comp_a, VConjR x, VFF y -> Gt
    | comp_a, VConjL x, VPrev_zero -> Lt
    | comp_a, VConjL x, VPrev_le yz -> Lt
    | comp_a, VConjL x, VPrev_ge yy -> Lt
    | comp_a, VConjL x, VPrev yx -> Lt
    | comp_a, VConjL x, VNext_le yw -> Lt
    | comp_a, VConjL x, VNext_ge yv -> Lt
    | comp_a, VConjL x, VNext yu -> Lt
    | comp_a, VConjL x, VSince_le yt -> Lt
    | comp_a, VConjL x, VUntil_never (yq, yr, ys) -> Lt
    | comp_a, VConjL x, VSince_never (yn, yo, yp) -> Lt
    | comp_a, VConjL x, VUntil (yk, yl, ym) -> Lt
    | comp_a, VConjL x, VSince (yh, yi, yj) -> Lt
    | comp_a, VConjL x, VConjR yg -> Lt
    | comp_a, VConjL x, VConjL yf -> comparator_vproof comp_a x yf
    | comp_a, VConjL x, VDisj (yd, ye) -> Gt
    | comp_a, VConjL x, VNeg yc -> Gt
    | comp_a, VConjL x, VAtm (ya, yb) -> Gt
    | comp_a, VConjL x, VFF y -> Gt
    | comp_a, VDisj (x, xa), VPrev_zero -> Lt
    | comp_a, VDisj (x, xa), VPrev_le yz -> Lt
    | comp_a, VDisj (x, xa), VPrev_ge yy -> Lt
    | comp_a, VDisj (x, xa), VPrev yx -> Lt
    | comp_a, VDisj (x, xa), VNext_le yw -> Lt
    | comp_a, VDisj (x, xa), VNext_ge yv -> Lt
    | comp_a, VDisj (x, xa), VNext yu -> Lt
    | comp_a, VDisj (x, xa), VSince_le yt -> Lt
    | comp_a, VDisj (x, xa), VUntil_never (yq, yr, ys) -> Lt
    | comp_a, VDisj (x, xa), VSince_never (yn, yo, yp) -> Lt
    | comp_a, VDisj (x, xa), VUntil (yk, yl, ym) -> Lt
    | comp_a, VDisj (x, xa), VSince (yh, yi, yj) -> Lt
    | comp_a, VDisj (x, xa), VConjR yg -> Lt
    | comp_a, VDisj (x, xa), VConjL yf -> Lt
    | comp_a, VDisj (x, xa), VDisj (yd, ye) ->
        (match comparator_vproof comp_a x yd
          with Eq -> comparator_vproof comp_a xa ye | Lt -> Lt | Gt -> Gt)
    | comp_a, VDisj (x, xa), VNeg yc -> Gt
    | comp_a, VDisj (x, xa), VAtm (ya, yb) -> Gt
    | comp_a, VDisj (x, xa), VFF y -> Gt
    | comp_a, VNeg x, VPrev_zero -> Lt
    | comp_a, VNeg x, VPrev_le yz -> Lt
    | comp_a, VNeg x, VPrev_ge yy -> Lt
    | comp_a, VNeg x, VPrev yx -> Lt
    | comp_a, VNeg x, VNext_le yw -> Lt
    | comp_a, VNeg x, VNext_ge yv -> Lt
    | comp_a, VNeg x, VNext yu -> Lt
    | comp_a, VNeg x, VSince_le yt -> Lt
    | comp_a, VNeg x, VUntil_never (yq, yr, ys) -> Lt
    | comp_a, VNeg x, VSince_never (yn, yo, yp) -> Lt
    | comp_a, VNeg x, VUntil (yk, yl, ym) -> Lt
    | comp_a, VNeg x, VSince (yh, yi, yj) -> Lt
    | comp_a, VNeg x, VConjR yg -> Lt
    | comp_a, VNeg x, VConjL yf -> Lt
    | comp_a, VNeg x, VDisj (yd, ye) -> Lt
    | comp_a, VNeg x, VNeg yc -> comparator_sproof comp_a x yc
    | comp_a, VNeg x, VAtm (ya, yb) -> Gt
    | comp_a, VNeg x, VFF y -> Gt
    | comp_a, VAtm (x, xa), VPrev_zero -> Lt
    | comp_a, VAtm (x, xa), VPrev_le yz -> Lt
    | comp_a, VAtm (x, xa), VPrev_ge yy -> Lt
    | comp_a, VAtm (x, xa), VPrev yx -> Lt
    | comp_a, VAtm (x, xa), VNext_le yw -> Lt
    | comp_a, VAtm (x, xa), VNext_ge yv -> Lt
    | comp_a, VAtm (x, xa), VNext yu -> Lt
    | comp_a, VAtm (x, xa), VSince_le yt -> Lt
    | comp_a, VAtm (x, xa), VUntil_never (yq, yr, ys) -> Lt
    | comp_a, VAtm (x, xa), VSince_never (yn, yo, yp) -> Lt
    | comp_a, VAtm (x, xa), VUntil (yk, yl, ym) -> Lt
    | comp_a, VAtm (x, xa), VSince (yh, yi, yj) -> Lt
    | comp_a, VAtm (x, xa), VConjR yg -> Lt
    | comp_a, VAtm (x, xa), VConjL yf -> Lt
    | comp_a, VAtm (x, xa), VDisj (yd, ye) -> Lt
    | comp_a, VAtm (x, xa), VNeg yc -> Lt
    | comp_a, VAtm (x, xa), VAtm (ya, yb) ->
        (match comp_a x ya
          with Eq -> comparator_of (equal_nat, linorder_nat) xa yb | Lt -> Lt
          | Gt -> Gt)
    | comp_a, VAtm (x, xa), VFF y -> Gt
    | comp_a, VFF x, VPrev_zero -> Lt
    | comp_a, VFF x, VPrev_le yz -> Lt
    | comp_a, VFF x, VPrev_ge yy -> Lt
    | comp_a, VFF x, VPrev yx -> Lt
    | comp_a, VFF x, VNext_le yw -> Lt
    | comp_a, VFF x, VNext_ge yv -> Lt
    | comp_a, VFF x, VNext yu -> Lt
    | comp_a, VFF x, VSince_le yt -> Lt
    | comp_a, VFF x, VUntil_never (yq, yr, ys) -> Lt
    | comp_a, VFF x, VSince_never (yn, yo, yp) -> Lt
    | comp_a, VFF x, VUntil (yk, yl, ym) -> Lt
    | comp_a, VFF x, VSince (yh, yi, yj) -> Lt
    | comp_a, VFF x, VConjR yg -> Lt
    | comp_a, VFF x, VConjL yf -> Lt
    | comp_a, VFF x, VDisj (yd, ye) -> Lt
    | comp_a, VFF x, VNeg yc -> Lt
    | comp_a, VFF x, VAtm (ya, yb) -> Lt
    | comp_a, VFF x, VFF y -> comparator_of (equal_nat, linorder_nat) x y;;

let rec ccompare_sproofa _A
  = (match ccompare _A with None -> None
      | Some comp_a -> Some (comparator_sproof comp_a));;

let rec ccompare_sproof _A =
  ({ccompare = ccompare_sproofa _A} : 'a sproof ccompare);;

let rec ceq_vproofa _A = Some (equal_vproofa _A);;

let rec ceq_vproof _A = ({ceq = ceq_vproofa _A} : 'a vproof ceq);;

let set_impl_vproofa : ('a vproof, set_impla) phantom = Phantom Set_RBT;;

let set_impl_vproof = ({set_impl = set_impl_vproofa} : 'a vproof set_impl);;

let rec ccompare_vproofa _A
  = (match ccompare _A with None -> None
      | Some comp_a -> Some (comparator_vproof comp_a));;

let rec ccompare_vproof _A =
  ({ccompare = ccompare_vproofa _A} : 'a vproof ccompare);;

let equal_literal = ({equal = (fun a b -> ((a : string) = b))} : string equal);;

let ord_literal =
  ({less_eq = (fun a b -> ((a : string) <= b));
     less = (fun a b -> ((a : string) < b))}
    : string ord);;

let preorder_literal = ({ord_preorder = ord_literal} : string preorder);;

let order_literal = ({preorder_order = preorder_literal} : string order);;

let ceq_literala : (string -> string -> bool) option
  = Some (fun a b -> ((a : string) = b));;

let ceq_literal = ({ceq = ceq_literala} : string ceq);;

let set_impl_literala : (string, set_impla) phantom = Phantom Set_RBT;;

let set_impl_literal = ({set_impl = set_impl_literala} : string set_impl);;

let linorder_literal = ({order_linorder = order_literal} : string linorder);;

let rec compare_literal x = comparator_of (equal_literal, linorder_literal) x;;

let ccompare_literala : (string -> string -> ordera) option
  = Some compare_literal;;

let ccompare_literal = ({ccompare = ccompare_literala} : string ccompare);;

type enat = Enat of nat | Infinity_enat;;

let rec less_eq_enat q x1 = match q, x1 with Infinity_enat, Enat n -> false
                       | q, Infinity_enat -> true
                       | Enat m, Enat n -> less_eq_nat m n;;

let rec less_enat x0 q = match x0, q with Infinity_enat, q -> false
                    | Enat m, Infinity_enat -> true
                    | Enat m, Enat n -> less_nat m n;;

let ord_enat = ({less_eq = less_eq_enat; less = less_enat} : enat ord);;

let rec inf_enata x = min ord_enat x;;

let inf_enat = ({inf = inf_enata} : enat inf);;

let rec sup_enata x = max ord_enat x;;

let sup_enat = ({sup = sup_enata} : enat sup);;

let preorder_enat = ({ord_preorder = ord_enat} : enat preorder);;

let order_enat = ({preorder_order = preorder_enat} : enat order);;

let semilattice_sup_enat =
  ({sup_semilattice_sup = sup_enat; order_semilattice_sup = order_enat} :
    enat semilattice_sup);;

let semilattice_inf_enat =
  ({inf_semilattice_inf = inf_enat; order_semilattice_inf = order_enat} :
    enat semilattice_inf);;

let lattice_enat =
  ({semilattice_inf_lattice = semilattice_inf_enat;
     semilattice_sup_lattice = semilattice_sup_enat}
    : enat lattice);;

let rec equal_enat x0 x1 = match x0, x1 with Enat nat, Infinity_enat -> false
                     | Infinity_enat, Enat nat -> false
                     | Enat nata, Enat nat -> equal_nata nata nat
                     | Infinity_enat, Infinity_enat -> true;;

let ceq_enata : (enat -> enat -> bool) option = Some equal_enat;;

let ceq_enat = ({ceq = ceq_enata} : enat ceq);;

let set_impl_enata : (enat, set_impla) phantom = Phantom Set_RBT;;

let set_impl_enat = ({set_impl = set_impl_enata} : enat set_impl);;

let linorder_enat = ({order_linorder = order_enat} : enat linorder);;

type 'a infinity = {infinity : 'a};;
let infinity _A = _A.infinity;;

let infinity_enat = ({infinity = Infinity_enat} : enat infinity);;

let ccompare_enata : (enat -> enat -> ordera) option
  = Some (fun x y ->
           (if equal_enat x y then Eq
             else (if less_enat x y then Lt else Gt)));;

let ccompare_enat = ({ccompare = ccompare_enata} : enat ccompare);;

let rec equal_unita u v = true;;

let equal_unit = ({equal = equal_unita} : unit equal);;

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

type i = Abs_I of (nat * enat);;

type 'a mtl = TT | FF | Atom of 'a | Neg of 'a mtl | Disj of 'a mtl * 'a mtl |
  Conj of 'a mtl * 'a mtl | Next of i * 'a mtl | Prev of i * 'a mtl |
  Since of 'a mtl * i * 'a mtl | Until of 'a mtl * i * 'a mtl;;

type num = One | Bit0 of num | Bit1 of num;;

type color = R | B;;

type ('a, 'b) rbt = Empty |
  Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt;;

type ('b, 'a) mapping_rbt = Mapping_RBTa of ('b, 'a) rbt;;

type 'a set_dlist = Abs_dlist of 'a list;;

type 'a set = Collect_set of ('a -> bool) | DList_set of 'a set_dlist |
  RBT_set of ('a, unit) mapping_rbt | Set_Monad of 'a list |
  Complement of 'a set;;

type ('b, 'a) alist = Alist of ('b * 'a) list;;

type ('a, 'b) mapping = Assoc_List_Mapping of ('a, 'b) alist |
  RBT_Mapping of ('a, 'b) mapping_rbt | Mapping of ('a -> 'b option);;

type 'a trace_rbt =
  Abs_trace_rbt of (nat * (nat * (nat, ('a set * nat)) mapping));;

type 'a trace = Trace_RBT of 'a trace_rbt;;

type ('a, 'b) sum = Inl of 'a | Inr of 'b;;

type 'a semilattice_set = Abs_semilattice_set of ('a -> 'a -> 'a);;

type mapping_impl = Mapping_Choose | Mapping_Assoc_List | Mapping_RBT |
  Mapping_Mapping;;

let rec id x = (fun xa -> xa) x;;

let one_nat : nat = Nat (Z.of_int 1);;

let rec suc n = plus_nata n one_nat;;

let rec comp f g = (fun x -> f (g x));;

let rec upt i j = (if less_nat i j then i :: upt (suc i) j else []);;

let rec minus_nat
  m n = Nat (max ord_integer Z.zero
              (Z.sub (integer_of_nat m) (integer_of_nat n)));;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec last (x :: xs) = (if null xs then x else last xs);;

let rec v_at = function VFF n -> n
               | VAtm (uv, n) -> n
               | VNeg sphi -> s_at sphi
               | VDisj (vphi, vpsi) -> v_at vphi
               | VConjL vphi -> v_at vphi
               | VConjR vpsi -> v_at vpsi
               | VNext vphi -> minus_nat (v_at vphi) one_nat
               | VNext_ge n -> n
               | VNext_le n -> n
               | VPrev vphi -> plus_nata (v_at vphi) one_nat
               | VPrev_ge n -> n
               | VPrev_le n -> n
               | VPrev_zero -> zero_nata
               | VSince (n, vpsi, vphis) -> n
               | VSince_le n -> n
               | VUntil (n, vphis, vpsi) -> n
               | VSince_never (n, li, vpsis) -> n
               | VUntil_never (n, hi, vpsis) -> n
and s_at
  = function STT n -> n
    | SAtm (uu, n) -> n
    | SNeg vphi -> v_at vphi
    | SDisjL sphi -> s_at sphi
    | SDisjR spsi -> s_at spsi
    | SConj (sphi, spsi) -> s_at sphi
    | SNext sphi -> minus_nat (s_at sphi) one_nat
    | SPrev sphi -> plus_nata (s_at sphi) one_nat
    | SSince (spsi, sphis) ->
        (match sphis with [] -> s_at spsi | _ :: _ -> s_at (last sphis))
    | SUntil (sphis, spsi) ->
        (match sphis with [] -> s_at spsi | x :: _ -> s_at x);;

let rec p_at
  x = (fun a -> (match a with Inl aa -> s_at aa | Inr aa -> v_at aa)) x;;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (suc n) xs
                     | n, [] -> n;;

let rec size_list x = gen_length zero_nata x;;

let rec rep_I (Abs_I x) = x;;

let rec fst (x1, x2) = x1;;

let rec left x = fst (rep_I x);;

let rec rep_trace_rbt (Abs_trace_rbt x) = x;;

let rec of_phantom (Phantom x) = x;;

let rec emptyb _A = Mapping_RBTa Empty;;

let rec emptya _A = Abs_dlist [];;

let rec set_empty_choose (_A1, _A2)
  = (match ccompare _A2
      with None ->
        (match ceq _A1 with None -> Set_Monad []
          | Some _ -> DList_set (emptya _A1))
      | Some _ -> RBT_set (emptyb _A2));;

let rec set_empty (_A1, _A2)
  = function Set_Choose -> set_empty_choose (_A1, _A2)
    | Set_Monada -> Set_Monad []
    | Set_RBT -> RBT_set (emptyb _A2)
    | Set_DList -> DList_set (emptya _A1)
    | Set_Collect -> Collect_set (fun _ -> false);;

let rec bot_set (_A1, _A2, _A3)
  = set_empty (_A1, _A2) (of_phantom (set_impl _A3));;

let rec the (Some x2) = x2;;

let rec rbt_comp_lookup
  c x1 k = match c, x1, k with c, Empty, k -> None
    | c, Branch (uu, l, x, y, r), k ->
        (match c k x with Eq -> Some y | Lt -> rbt_comp_lookup c l k
          | Gt -> rbt_comp_lookup c r k);;

let rec impl_ofa _B (Mapping_RBTa x) = x;;

let rec lookupb _A xa = rbt_comp_lookup (the (ccompare _A)) (impl_ofa _A xa);;

let rec impl_of (Alist x) = x;;

let rec map_of _A
  x0 k = match x0, k with
    (l, v) :: ps, k -> (if eq _A l k then Some v else map_of _A ps k)
    | [], k -> None;;

let rec lookup _A xa = map_of _A (impl_of xa);;

let rec lookupa (_A1, _A2) = function RBT_Mapping t -> lookupb _A1 t
                             | Assoc_List_Mapping al -> lookup _A2 al;;

let rec trace_rbt_nth (_A1, _A2, _A3)
  xa = (let (n, (m, t)) = rep_trace_rbt xa in
         (fun i ->
           (if less_nat i n then the (lookupa (ccompare_nat, equal_nat) t i)
             else (bot_set (_A1, _A2, _A3), plus_nata (minus_nat i n) m))));;

let rec snd (x1, x2) = x2;;

let rec tau (_A1, _A2, _A3)
  (Trace_RBT t) i = snd (trace_rbt_nth (_A1, _A2, _A3) t i);;

let rec check_upt_lu (_A1, _A2, _A3)
  rho ia i xs hi =
    (let j = minus_nat (suc hi) (size_list xs) in
      (match xs
        with [] ->
          (if equal_nata (left ia) zero_nata then less_eq_nat (suc hi) i
            else less_nat
                   (minus_nat (tau (_A1, _A2, _A3) rho hi)
                     (tau (_A1, _A2, _A3) rho i))
                   (left ia))
        | _ :: _ ->
          equal_list equal_nat xs (upt j (suc hi)) &&
            ((if equal_nata (left ia) zero_nata then less_eq_nat j i
               else (if equal_nata j zero_nata then true
                      else less_nat
                             (minus_nat
                               (tau (_A1, _A2, _A3) rho (minus_nat j one_nat))
                               (tau (_A1, _A2, _A3) rho i))
                             (left ia))) &&
              (less_eq_nat i j &&
                less_eq_nat (left ia)
                  (minus_nat (tau (_A1, _A2, _A3) rho j)
                    (tau (_A1, _A2, _A3) rho i))))));;

let rec check_upt_l (_A1, _A2, _A3)
  rho ia li xs i =
    (match xs
      with [] ->
        (if equal_nata (left ia) zero_nata then less_nat i li
          else (if not (less_eq_nat li i) && equal_nata (left ia) zero_nata
                 then less_nat zero_nata
                        (minus_nat (tau (_A1, _A2, _A3) rho li)
                          (tau (_A1, _A2, _A3) rho i))
                 else less_nat
                        (minus_nat (tau (_A1, _A2, _A3) rho i)
                          (tau (_A1, _A2, _A3) rho li))
                        (left ia)))
      | _ :: _ ->
        equal_list equal_nat xs (upt li (plus_nata li (size_list xs))) &&
          (if equal_nata (left ia) zero_nata
            then equal_nata (minus_nat (plus_nata li (size_list xs)) one_nat) i
            else less_eq_nat (minus_nat (plus_nata li (size_list xs)) one_nat)
                   i &&
                   (less_eq_nat (left ia)
                      (minus_nat (tau (_A1, _A2, _A3) rho i)
                        (tau (_A1, _A2, _A3) rho
                          (minus_nat (plus_nata li (size_list xs)) one_nat))) &&
                     less_nat
                       (minus_nat (tau (_A1, _A2, _A3) rho i)
                         (tau (_A1, _A2, _A3) rho
                           (plus_nata li (size_list xs))))
                       (left ia))));;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec gamma (_A1, _A2, _A3)
  (Trace_RBT t) i = fst (trace_rbt_nth (_A1, _A2, _A3) t i);;

let rec right x = snd (rep_I x);;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec list_member
  equal x1 y = match equal, x1, y with
    equal, x :: xs, y -> equal x y || list_member equal xs y
    | equal, [], y -> false;;

let rec list_of_dlist _A (Abs_dlist x) = x;;

let rec memberb _A xa = list_member (the (ceq _A)) (list_of_dlist _A xa);;

let rec equal_option _A x0 x1 = match x0, x1 with None, Some x2 -> false
                          | Some x2, None -> false
                          | Some x2, Some y2 -> eq _A x2 y2
                          | None, None -> true;;

let rec membera _A t x = equal_option equal_unit (lookupb _A t x) (Some ());;

let rec member (_A1, _A2)
  x xa1 = match x, xa1 with
    x, Set_Monad xs ->
      (match ceq _A1
        with None ->
          failwith "member Set_Monad: ceq = None"
            (fun _ -> member (_A1, _A2) x (Set_Monad xs))
        | Some eq -> list_member eq xs x)
    | xa, Complement x -> not (member (_A1, _A2) xa x)
    | x, RBT_set rbt -> membera _A2 rbt x
    | x, DList_set dxs -> memberb _A1 dxs x
    | x, Collect_set a -> a x;;

let rec v_check (_A1, _A2, _A3, _A4)
  rho x1 p = match rho, x1, p with
    rho, Until (phi, i, psi), p ->
      (match p with VFF _ -> false | VAtm (_, _) -> false | VNeg _ -> false
        | VDisj (_, _) -> false | VConjL _ -> false | VConjR _ -> false
        | VSince (_, _, _) -> false
        | VUntil (ia, vpsis, vphi) ->
          (let j = v_at vphi in
            (match right i
              with Enat a ->
                less_eq_nat
                  (minus_nat (tau (_A1, _A2, _A4) rho j)
                    (tau (_A1, _A2, _A4) rho ia))
                  a
              | Infinity_enat -> true) &&
              (less_eq_nat ia j &&
                (check_upt_lu (_A1, _A2, _A4) rho i ia (map v_at vpsis) j &&
                  (v_check (_A1, _A2, _A3, _A4) rho phi vphi &&
                    list_all (v_check (_A1, _A2, _A3, _A4) rho psi) vpsis))))
        | VSince_never (_, _, _) -> false
        | VUntil_never (ia, hi, vpsis) ->
          (match right i
            with Enat n ->
              less_eq_nat
                (minus_nat (tau (_A1, _A2, _A4) rho hi)
                  (tau (_A1, _A2, _A4) rho ia))
                n &&
                less_nat n
                  (minus_nat (tau (_A1, _A2, _A4) rho (suc hi))
                    (tau (_A1, _A2, _A4) rho ia))
            | Infinity_enat -> false) &&
            (check_upt_lu (_A1, _A2, _A4) rho i ia (map v_at vpsis) hi &&
              list_all (v_check (_A1, _A2, _A3, _A4) rho psi) vpsis)
        | VSince_le _ -> false | VNext _ -> false | VNext_ge _ -> false
        | VNext_le _ -> false | VPrev _ -> false | VPrev_ge _ -> false
        | VPrev_le _ -> false | VPrev_zero -> false)
    | rho, Since (phi, i, psi), p ->
        (match p with VFF _ -> false | VAtm (_, _) -> false | VNeg _ -> false
          | VDisj (_, _) -> false | VConjL _ -> false | VConjR _ -> false
          | VSince (ia, vphi, vpsis) ->
            (let j = v_at vphi in
              (match right i
                with Enat a ->
                  less_eq_nat
                    (minus_nat (tau (_A1, _A2, _A4) rho ia)
                      (tau (_A1, _A2, _A4) rho j))
                    a
                | Infinity_enat -> true) &&
                (less_eq_nat j ia &&
                  (less_eq_nat
                     (plus_nata (tau (_A1, _A2, _A4) rho zero_nata) (left i))
                     (tau (_A1, _A2, _A4) rho ia) &&
                    (check_upt_l (_A1, _A2, _A4) rho i j (map v_at vpsis) ia &&
                      (v_check (_A1, _A2, _A3, _A4) rho phi vphi &&
                        list_all (v_check (_A1, _A2, _A3, _A4) rho psi)
                          vpsis)))))
          | VUntil (_, _, _) -> false
          | VSince_never (ia, li, vpsis) ->
            (match right i
              with Enat n ->
                (equal_nata li zero_nata ||
                  less_nat n
                    (minus_nat (tau (_A1, _A2, _A4) rho ia)
                      (tau (_A1, _A2, _A4) rho (minus_nat li one_nat)))) &&
                  less_eq_nat
                    (minus_nat (tau (_A1, _A2, _A4) rho ia)
                      (tau (_A1, _A2, _A4) rho li))
                    n
              | Infinity_enat -> equal_nata li zero_nata) &&
              (less_eq_nat
                 (plus_nata (tau (_A1, _A2, _A4) rho zero_nata) (left i))
                 (tau (_A1, _A2, _A4) rho ia) &&
                (check_upt_l (_A1, _A2, _A4) rho i li (map v_at vpsis) ia &&
                  list_all (v_check (_A1, _A2, _A3, _A4) rho psi) vpsis))
          | VUntil_never (_, _, _) -> false
          | VSince_le ia ->
            less_nat (tau (_A1, _A2, _A4) rho ia)
              (plus_nata (tau (_A1, _A2, _A4) rho zero_nata) (left i))
          | VNext _ -> false | VNext_ge _ -> false | VNext_le _ -> false
          | VPrev _ -> false | VPrev_ge _ -> false | VPrev_le _ -> false
          | VPrev_zero -> false)
    | rho, Prev (xa, x), p ->
        (match p with VFF _ -> false | VAtm (_, _) -> false | VNeg _ -> false
          | VDisj (_, _) -> false | VConjL _ -> false | VConjR _ -> false
          | VSince (_, _, _) -> false | VUntil (_, _, _) -> false
          | VSince_never (_, _, _) -> false | VUntil_never (_, _, _) -> false
          | VSince_le _ -> false | VNext _ -> false | VNext_ge _ -> false
          | VNext_le _ -> false
          | VPrev vphi ->
            (let j = v_at vphi in
             let i = v_at (VPrev vphi) in
              equal_nata i (suc j) && v_check (_A1, _A2, _A3, _A4) rho x vphi)
          | VPrev_ge i ->
            less_nat zero_nata i &&
              less_enat (right xa)
                (Enat (minus_nat (tau (_A1, _A2, _A4) rho i)
                        (tau (_A1, _A2, _A4) rho (minus_nat i one_nat))))
          | VPrev_le i ->
            less_nat zero_nata i &&
              less_nat
                (minus_nat (tau (_A1, _A2, _A4) rho i)
                  (tau (_A1, _A2, _A4) rho (minus_nat i one_nat)))
                (left xa)
          | VPrev_zero -> equal_nata (v_at VPrev_zero) zero_nata)
    | rho, Next (xa, x), p ->
        (match p with VFF _ -> false | VAtm (_, _) -> false | VNeg _ -> false
          | VDisj (_, _) -> false | VConjL _ -> false | VConjR _ -> false
          | VSince (_, _, _) -> false | VUntil (_, _, _) -> false
          | VSince_never (_, _, _) -> false | VUntil_never (_, _, _) -> false
          | VSince_le _ -> false
          | VNext vphi ->
            (let j = v_at vphi in
             let i = v_at (VNext vphi) in
              equal_nata j (suc i) && v_check (_A1, _A2, _A3, _A4) rho x vphi)
          | VNext_ge i ->
            less_enat (right xa)
              (Enat (minus_nat (tau (_A1, _A2, _A4) rho (suc i))
                      (tau (_A1, _A2, _A4) rho (minus_nat (suc i) one_nat))))
          | VNext_le i ->
            less_nat
              (minus_nat (tau (_A1, _A2, _A4) rho (suc i))
                (tau (_A1, _A2, _A4) rho (minus_nat (suc i) one_nat)))
              (left xa)
          | VPrev _ -> false | VPrev_ge _ -> false | VPrev_le _ -> false
          | VPrev_zero -> false)
    | rho, Conj (xa, x), p ->
        (match p with VFF _ -> false | VAtm (_, _) -> false | VNeg _ -> false
          | VDisj (_, _) -> false
          | VConjL a -> v_check (_A1, _A2, _A3, _A4) rho xa a
          | VConjR a -> v_check (_A1, _A2, _A3, _A4) rho x a
          | VSince (_, _, _) -> false | VUntil (_, _, _) -> false
          | VSince_never (_, _, _) -> false | VUntil_never (_, _, _) -> false
          | VSince_le _ -> false | VNext _ -> false | VNext_ge _ -> false
          | VNext_le _ -> false | VPrev _ -> false | VPrev_ge _ -> false
          | VPrev_le _ -> false | VPrev_zero -> false)
    | rho, Disj (xa, x), p ->
        (match p with VFF _ -> false | VAtm (_, _) -> false | VNeg _ -> false
          | VDisj (vphi, vpsi) ->
            v_check (_A1, _A2, _A3, _A4) rho xa vphi &&
              (v_check (_A1, _A2, _A3, _A4) rho x vpsi &&
                equal_nata (v_at vphi) (v_at vpsi))
          | VConjL _ -> false | VConjR _ -> false | VSince (_, _, _) -> false
          | VUntil (_, _, _) -> false | VSince_never (_, _, _) -> false
          | VUntil_never (_, _, _) -> false | VSince_le _ -> false
          | VNext _ -> false | VNext_ge _ -> false | VNext_le _ -> false
          | VPrev _ -> false | VPrev_ge _ -> false | VPrev_le _ -> false
          | VPrev_zero -> false)
    | rho, Neg x, p ->
        (match p with VFF _ -> false | VAtm (_, _) -> false
          | VNeg a -> s_check (_A1, _A2, _A3, _A4) rho x a
          | VDisj (_, _) -> false | VConjL _ -> false | VConjR _ -> false
          | VSince (_, _, _) -> false | VUntil (_, _, _) -> false
          | VSince_never (_, _, _) -> false | VUntil_never (_, _, _) -> false
          | VSince_le _ -> false | VNext _ -> false | VNext_ge _ -> false
          | VNext_le _ -> false | VPrev _ -> false | VPrev_ge _ -> false
          | VPrev_le _ -> false | VPrev_zero -> false)
    | rho, Atom x, p ->
        (match p with VFF _ -> false
          | VAtm (b, i) ->
            eq _A3 x b &&
              not (member (_A1, _A2) x (gamma (_A1, _A2, _A4) rho i))
          | VNeg _ -> false | VDisj (_, _) -> false | VConjL _ -> false
          | VConjR _ -> false | VSince (_, _, _) -> false
          | VUntil (_, _, _) -> false | VSince_never (_, _, _) -> false
          | VUntil_never (_, _, _) -> false | VSince_le _ -> false
          | VNext _ -> false | VNext_ge _ -> false | VNext_le _ -> false
          | VPrev _ -> false | VPrev_ge _ -> false | VPrev_le _ -> false
          | VPrev_zero -> false)
    | rho, FF, p ->
        (match p with VFF _ -> true | VAtm (_, _) -> false | VNeg _ -> false
          | VDisj (_, _) -> false | VConjL _ -> false | VConjR _ -> false
          | VSince (_, _, _) -> false | VUntil (_, _, _) -> false
          | VSince_never (_, _, _) -> false | VUntil_never (_, _, _) -> false
          | VSince_le _ -> false | VNext _ -> false | VNext_ge _ -> false
          | VNext_le _ -> false | VPrev _ -> false | VPrev_ge _ -> false
          | VPrev_le _ -> false | VPrev_zero -> false)
    | rho, TT, p -> false
and s_check (_A1, _A2, _A3, _A4)
  rho x1 p = match rho, x1, p with rho, Until (xa, xaa, xb), SPrev x -> false
    | rho, Until (xa, xaa, xb), SNext x -> false
    | rho, Until (xb, xaa, xba), SUntil (xa, x) ->
        (let i = s_at (SUntil (xa, x)) in
         let j = s_at x in
          less_eq_nat i j &&
            (less_eq_nat (left xaa)
               (minus_nat (tau (_A1, _A2, _A4) rho j)
                 (tau (_A1, _A2, _A4) rho i)) &&
               less_eq_enat
                 (Enat (minus_nat (tau (_A1, _A2, _A4) rho j)
                         (tau (_A1, _A2, _A4) rho i)))
                 (right xaa) &&
              (equal_list equal_nat (map s_at xa) (upt i j) &&
                (s_check (_A1, _A2, _A3, _A4) rho xba x &&
                  list_all (s_check (_A1, _A2, _A3, _A4) rho xb) xa))))
    | rho, Until (xb, xaa, xba), SSince (xa, x) -> false
    | rho, Until (xb, xaa, xba), SConj (xa, x) -> false
    | rho, Until (xa, xaa, xb), SDisjR x -> false
    | rho, Until (xa, xaa, xb), SDisjL x -> false
    | rho, Until (xa, xaa, xb), SNeg x -> false
    | rho, Until (xb, xaa, xba), SAtm (xa, x) -> false
    | rho, Until (xa, xaa, xb), STT x -> false
    | rho, Since (xa, xaa, xb), SPrev x -> false
    | rho, Since (xa, xaa, xb), SNext x -> false
    | rho, Since (xb, xaa, xba), SUntil (xa, x) -> false
    | rho, Since (xb, xaa, xba), SSince (xa, x) ->
        (let i = s_at (SSince (xa, x)) in
         let j = s_at xa in
          less_eq_nat j i &&
            (less_eq_nat (left xaa)
               (minus_nat (tau (_A1, _A2, _A4) rho i)
                 (tau (_A1, _A2, _A4) rho j)) &&
               less_eq_enat
                 (Enat (minus_nat (tau (_A1, _A2, _A4) rho i)
                         (tau (_A1, _A2, _A4) rho j)))
                 (right xaa) &&
              (equal_list equal_nat (map s_at x) (upt (suc j) (suc i)) &&
                (s_check (_A1, _A2, _A3, _A4) rho xba xa &&
                  list_all (s_check (_A1, _A2, _A3, _A4) rho xb) x))))
    | rho, Since (xb, xaa, xba), SConj (xa, x) -> false
    | rho, Since (xa, xaa, xb), SDisjR x -> false
    | rho, Since (xa, xaa, xb), SDisjL x -> false
    | rho, Since (xa, xaa, xb), SNeg x -> false
    | rho, Since (xb, xaa, xba), SAtm (xa, x) -> false
    | rho, Since (xa, xaa, xb), STT x -> false
    | rho, Prev (xa, xaa), SPrev x ->
        (let j = s_at x in
         let i = s_at (SPrev x) in
          equal_nata i (suc j) &&
            (less_eq_nat (left xa)
               (minus_nat (tau (_A1, _A2, _A4) rho i)
                 (tau (_A1, _A2, _A4) rho (minus_nat i one_nat))) &&
               less_eq_enat
                 (Enat (minus_nat (tau (_A1, _A2, _A4) rho i)
                         (tau (_A1, _A2, _A4) rho (minus_nat i one_nat))))
                 (right xa) &&
              s_check (_A1, _A2, _A3, _A4) rho xaa x))
    | rho, Prev (xa, xaa), SNext x -> false
    | rho, Prev (xb, xaa), SUntil (xa, x) -> false
    | rho, Prev (xb, xaa), SSince (xa, x) -> false
    | rho, Prev (xb, xaa), SConj (xa, x) -> false
    | rho, Prev (xa, xaa), SDisjR x -> false
    | rho, Prev (xa, xaa), SDisjL x -> false
    | rho, Prev (xa, xaa), SNeg x -> false
    | rho, Prev (xb, xaa), SAtm (xa, x) -> false
    | rho, Prev (xa, xaa), STT x -> false
    | rho, Next (xa, xaa), SPrev x -> false
    | rho, Next (xa, xaa), SNext x ->
        (let j = s_at x in
         let i = s_at (SNext x) in
          equal_nata j (suc i) &&
            (less_eq_nat (left xa)
               (minus_nat (tau (_A1, _A2, _A4) rho j)
                 (tau (_A1, _A2, _A4) rho (minus_nat j one_nat))) &&
               less_eq_enat
                 (Enat (minus_nat (tau (_A1, _A2, _A4) rho j)
                         (tau (_A1, _A2, _A4) rho (minus_nat j one_nat))))
                 (right xa) &&
              s_check (_A1, _A2, _A3, _A4) rho xaa x))
    | rho, Next (xb, xaa), SUntil (xa, x) -> false
    | rho, Next (xb, xaa), SSince (xa, x) -> false
    | rho, Next (xb, xaa), SConj (xa, x) -> false
    | rho, Next (xa, xaa), SDisjR x -> false
    | rho, Next (xa, xaa), SDisjL x -> false
    | rho, Next (xa, xaa), SNeg x -> false
    | rho, Next (xb, xaa), SAtm (xa, x) -> false
    | rho, Next (xa, xaa), STT x -> false
    | rho, Conj (xa, xaa), SPrev x -> false
    | rho, Conj (xa, xaa), SNext x -> false
    | rho, Conj (xb, xaa), SUntil (xa, x) -> false
    | rho, Conj (xb, xaa), SSince (xa, x) -> false
    | rho, Conj (xb, xaa), SConj (xa, x) ->
        s_check (_A1, _A2, _A3, _A4) rho xb xa &&
          (s_check (_A1, _A2, _A3, _A4) rho xaa x &&
            equal_nata (s_at xa) (s_at x))
    | rho, Conj (xa, xaa), SDisjR x -> false
    | rho, Conj (xa, xaa), SDisjL x -> false
    | rho, Conj (xa, xaa), SNeg x -> false
    | rho, Conj (xb, xaa), SAtm (xa, x) -> false
    | rho, Conj (xa, xaa), STT x -> false
    | rho, Disj (xa, xaa), SPrev x -> false
    | rho, Disj (xa, xaa), SNext x -> false
    | rho, Disj (xb, xaa), SUntil (xa, x) -> false
    | rho, Disj (xb, xaa), SSince (xa, x) -> false
    | rho, Disj (xb, xaa), SConj (xa, x) -> false
    | rho, Disj (xa, xaa), SDisjR x -> s_check (_A1, _A2, _A3, _A4) rho xaa x
    | rho, Disj (xa, xaa), SDisjL x -> s_check (_A1, _A2, _A3, _A4) rho xa x
    | rho, Disj (xa, xaa), SNeg x -> false
    | rho, Disj (xb, xaa), SAtm (xa, x) -> false
    | rho, Disj (xa, xaa), STT x -> false
    | rho, Neg xa, SPrev x -> false
    | rho, Neg xa, SNext x -> false
    | rho, Neg xb, SUntil (xa, x) -> false
    | rho, Neg xb, SSince (xa, x) -> false
    | rho, Neg xb, SConj (xa, x) -> false
    | rho, Neg xa, SDisjR x -> false
    | rho, Neg xa, SDisjL x -> false
    | rho, Neg xa, SNeg x -> v_check (_A1, _A2, _A3, _A4) rho xa x
    | rho, Neg xb, SAtm (xa, x) -> false
    | rho, Neg xa, STT x -> false
    | rho, Atom xa, SPrev x -> false
    | rho, Atom xa, SNext x -> false
    | rho, Atom xb, SUntil (xa, x) -> false
    | rho, Atom xb, SSince (xa, x) -> false
    | rho, Atom xb, SConj (xa, x) -> false
    | rho, Atom xa, SDisjR x -> false
    | rho, Atom xa, SDisjL x -> false
    | rho, Atom xa, SNeg x -> false
    | rho, Atom xb, SAtm (xa, x) ->
        eq _A3 xb xa && member (_A1, _A2) xb (gamma (_A1, _A2, _A4) rho x)
    | rho, Atom xa, STT x -> false
    | rho, FF, p -> false
    | rho, TT, SPrev x -> false
    | rho, TT, SNext x -> false
    | rho, TT, SUntil (xa, x) -> false
    | rho, TT, SSince (xa, x) -> false
    | rho, TT, SConj (xa, x) -> false
    | rho, TT, SDisjR x -> false
    | rho, TT, SDisjL x -> false
    | rho, TT, SNeg x -> false
    | rho, TT, SAtm (xa, x) -> false
    | rho, TT, STT x -> true;;

let rec valid (_A1, _A2, _A3, _A4)
  rho i phi p =
    (match p
      with Inl pa ->
        s_check (_A1, _A2, _A3, _A4) rho phi pa && equal_nata (s_at pa) i
      | Inr pa ->
        v_check (_A1, _A2, _A3, _A4) rho phi pa && equal_nata (v_at pa) i);;

let rec foldc _A x xc = fold x (list_of_dlist _A xc);;

let rec folda
  f xa1 x = match f, xa1, x with
    f, Branch (c, lt, k, v, rt), x -> folda f rt (f k v (folda f lt x))
    | f, Empty, x -> x;;

let rec foldb _A x xc = folda (fun a _ -> x a) (impl_ofa _A xc);;

let rec fun_upd equal f aa b a = (if equal aa a then b else f a);;

let rec balance
  x0 s t x3 = match x0, s, t, x3 with
    Branch (R, a, w, x, b), s, t, Branch (R, c, y, z, d) ->
      Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z, Empty ->
        Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, a, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z, Empty ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c)), y,
        z, Empty
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c)), y,
        z, Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Empty, w, x, Branch (R, b, s, t, Branch (R, c, y, z, d)) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, b, s, t, Branch (R, c, y, z, d))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, d))
    | Empty, w, x, Branch (R, Branch (R, b, s, t, c), y, z, Empty) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Empty, w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Empty)
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
    | Empty, s, t, Empty -> Branch (B, Empty, s, t, Empty)
    | Empty, s, t, Branch (B, va, vb, vc, vd) ->
        Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
    | Empty, s, t, Branch (v, Empty, vb, vc, Empty) ->
        Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
    | Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
    | Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
    | Empty, s, t,
        Branch
          (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi))
        -> Branch
             (B, Empty, s, t,
               Branch
                 (v, Branch (B, ve, vj, vk, vl), vb, vc,
                   Branch (B, vf, vg, vh, vi)))
    | Branch (B, va, vb, vc, vd), s, t, Empty ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
    | Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh) ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
    | Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty) ->
        Branch
          (B, Branch (B, va, vb, vc, vd), s, t,
            Branch (v, Empty, vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch
          (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch
                 (v, Branch (B, vi, vn, vo, vp), vf, vg,
                   Branch (B, vj, vk, vl, vm)))
    | Branch (v, Empty, vb, vc, Empty), s, t, Empty ->
        Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
    | Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty ->
        Branch
          (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t,
            Empty)
    | Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty ->
        Branch
          (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t,
            Empty)
    | Branch
        (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty
        -> Branch
             (B, Branch
                   (v, Branch (B, vf, vg, vh, vi), vb, vc,
                     Branch (B, ve, vj, vk, vl)),
               s, t, Empty)
    | Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd) ->
        Branch
          (B, Branch (v, Empty, vf, vg, Empty), s, t,
            Branch (B, va, vb, vc, vd))
    | Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch
        (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch
                   (v, Branch (B, vj, vk, vl, vm), vf, vg,
                     Branch (B, vi, vn, vo, vp)),
               s, t, Branch (B, va, vb, vc, vd));;

let rec rbt_comp_ins
  c f k v x4 = match c, f, k, v, x4 with
    c, f, k, v, Empty -> Branch (R, Empty, k, v, Empty)
    | c, f, k, v, Branch (B, l, x, y, r) ->
        (match c k x with Eq -> Branch (B, l, x, f k y v, r)
          | Lt -> balance (rbt_comp_ins c f k v l) x y r
          | Gt -> balance l x y (rbt_comp_ins c f k v r))
    | c, f, k, v, Branch (R, l, x, y, r) ->
        (match c k x with Eq -> Branch (R, l, x, f k y v, r)
          | Lt -> Branch (R, rbt_comp_ins c f k v l, x, y, r)
          | Gt -> Branch (R, l, x, y, rbt_comp_ins c f k v r));;

let rec paint c x1 = match c, x1 with c, Empty -> Empty
                | c, Branch (uu, l, k, v, r) -> Branch (c, l, k, v, r);;

let rec rbt_comp_insert_with_key c f k v t = paint B (rbt_comp_ins c f k v t);;

let rec rbt_comp_insert c = rbt_comp_insert_with_key c (fun _ _ nv -> nv);;

let rec insertb _A
  xc xd xe =
    Mapping_RBTa (rbt_comp_insert (the (ccompare _A)) xc xd (impl_ofa _A xe));;

let rec list_insert
  equal x xs = (if list_member equal xs x then xs else x :: xs);;

let rec inserta _A
  xb xc = Abs_dlist (list_insert (the (ceq _A)) xb (list_of_dlist _A xc));;

let rec balance_right
  a k x xa3 = match a, k, x, xa3 with
    a, k, x, Branch (R, b, s, y, c) ->
      Branch (R, a, k, x, Branch (B, b, s, y, c))
    | Branch (B, a, k, x, b), s, y, Empty ->
        balance (Branch (R, a, k, x, b)) s y Empty
    | Branch (B, a, k, x, b), s, y, Branch (B, va, vb, vc, vd) ->
        balance (Branch (R, a, k, x, b)) s y (Branch (B, va, vb, vc, vd))
    | Branch (R, a, k, x, Branch (B, b, s, y, c)), t, z, Empty ->
        Branch (R, balance (paint R a) k x b, s, y, Branch (B, c, t, z, Empty))
    | Branch (R, a, k, x, Branch (B, b, s, y, c)), t, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, balance (paint R a) k x b, s, y,
               Branch (B, c, t, z, Branch (B, va, vb, vc, vd)))
    | Empty, k, x, Empty -> Empty
    | Branch (R, va, vb, vc, Empty), k, x, Empty -> Empty
    | Branch (R, va, vb, vc, Branch (R, ve, vf, vg, vh)), k, x, Empty -> Empty
    | Empty, k, x, Branch (B, va, vb, vc, vd) -> Empty
    | Branch (R, ve, vf, vg, Empty), k, x, Branch (B, va, vb, vc, vd) -> Empty
    | Branch (R, ve, vf, vg, Branch (R, vi, vj, vk, vl)), k, x,
        Branch (B, va, vb, vc, vd)
        -> Empty;;

let rec balance_left
  x0 s y c = match x0, s, y, c with
    Branch (R, a, k, x, b), s, y, c ->
      Branch (R, Branch (B, a, k, x, b), s, y, c)
    | Empty, k, x, Branch (B, a, s, y, b) ->
        balance Empty k x (Branch (R, a, s, y, b))
    | Branch (B, va, vb, vc, vd), k, x, Branch (B, a, s, y, b) ->
        balance (Branch (B, va, vb, vc, vd)) k x (Branch (R, a, s, y, b))
    | Empty, k, x, Branch (R, Branch (B, a, s, y, b), t, z, c) ->
        Branch (R, Branch (B, Empty, k, x, a), s, y, balance b t z (paint R c))
    | Branch (B, va, vb, vc, vd), k, x,
        Branch (R, Branch (B, a, s, y, b), t, z, c)
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), k, x, a), s, y,
               balance b t z (paint R c))
    | Empty, k, x, Empty -> Empty
    | Empty, k, x, Branch (R, Empty, vb, vc, vd) -> Empty
    | Empty, k, x, Branch (R, Branch (R, ve, vf, vg, vh), vb, vc, vd) -> Empty
    | Branch (B, va, vb, vc, vd), k, x, Empty -> Empty
    | Branch (B, va, vb, vc, vd), k, x, Branch (R, Empty, vf, vg, vh) -> Empty
    | Branch (B, va, vb, vc, vd), k, x,
        Branch (R, Branch (R, vi, vj, vk, vl), vf, vg, vh)
        -> Empty;;

let rec combine
  xa0 x = match xa0, x with Empty, x -> x
    | Branch (v, va, vb, vc, vd), Empty -> Branch (v, va, vb, vc, vd)
    | Branch (R, a, k, x, b), Branch (R, c, s, y, d) ->
        (match combine b c
          with Empty -> Branch (R, a, k, x, Branch (R, Empty, s, y, d))
          | Branch (R, b2, t, z, c2) ->
            Branch (R, Branch (R, a, k, x, b2), t, z, Branch (R, c2, s, y, d))
          | Branch (B, b2, t, z, c2) ->
            Branch (R, a, k, x, Branch (R, Branch (B, b2, t, z, c2), s, y, d)))
    | Branch (B, a, k, x, b), Branch (B, c, s, y, d) ->
        (match combine b c
          with Empty -> balance_left a k x (Branch (B, Empty, s, y, d))
          | Branch (R, b2, t, z, c2) ->
            Branch (R, Branch (B, a, k, x, b2), t, z, Branch (B, c2, s, y, d))
          | Branch (B, b2, t, z, c2) ->
            balance_left a k x (Branch (B, Branch (B, b2, t, z, c2), s, y, d)))
    | Branch (B, va, vb, vc, vd), Branch (R, b, k, x, c) ->
        Branch (R, combine (Branch (B, va, vb, vc, vd)) b, k, x, c)
    | Branch (R, a, k, x, b), Branch (B, va, vb, vc, vd) ->
        Branch (R, a, k, x, combine b (Branch (B, va, vb, vc, vd)));;

let rec rbt_comp_del
  c x xa2 = match c, x, xa2 with c, x, Empty -> Empty
    | c, x, Branch (uu, a, y, s, b) ->
        (match c x y with Eq -> combine a b
          | Lt -> rbt_comp_del_from_left c x a y s b
          | Gt -> rbt_comp_del_from_right c x a y s b)
and rbt_comp_del_from_left
  c x xa2 y s b = match c, x, xa2, y, s, b with
    c, x, Branch (B, lt, z, v, rt), y, s, b ->
      balance_left (rbt_comp_del c x (Branch (B, lt, z, v, rt))) y s b
    | c, x, Empty, y, s, b -> Branch (R, rbt_comp_del c x Empty, y, s, b)
    | c, x, Branch (R, va, vb, vc, vd), y, s, b ->
        Branch (R, rbt_comp_del c x (Branch (R, va, vb, vc, vd)), y, s, b)
and rbt_comp_del_from_right
  c x a y s xa5 = match c, x, a, y, s, xa5 with
    c, x, a, y, s, Branch (B, lt, z, v, rt) ->
      balance_right a y s (rbt_comp_del c x (Branch (B, lt, z, v, rt)))
    | c, x, a, y, s, Empty -> Branch (R, a, y, s, rbt_comp_del c x Empty)
    | c, x, a, y, s, Branch (R, va, vb, vc, vd) ->
        Branch (R, a, y, s, rbt_comp_del c x (Branch (R, va, vb, vc, vd)));;

let rec rbt_comp_delete c k t = paint B (rbt_comp_del c k t);;

let rec delete _A
  xb xc =
    Mapping_RBTa (rbt_comp_delete (the (ccompare _A)) xb (impl_ofa _A xc));;

let rec list_remove1
  equal x xa2 = match equal, x, xa2 with
    equal, x, y :: xs ->
      (if equal x y then xs else y :: list_remove1 equal x xs)
    | equal, x, [] -> [];;

let rec removea _A
  xb xc = Abs_dlist (list_remove1 (the (ceq _A)) xb (list_of_dlist _A xc));;

let rec insert (_A1, _A2)
  xa x1 = match xa, x1 with
    xa, Complement x -> Complement (remove (_A1, _A2) xa x)
    | x, RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "insert RBT_set: ccompare = None"
              (fun _ -> insert (_A1, _A2) x (RBT_set rbt))
          | Some _ -> RBT_set (insertb _A2 x () rbt))
    | x, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "insert DList_set: ceq = None"
              (fun _ -> insert (_A1, _A2) x (DList_set dxs))
          | Some _ -> DList_set (inserta _A1 x dxs))
    | x, Set_Monad xs -> Set_Monad (x :: xs)
    | x, Collect_set a ->
        (match ceq _A1
          with None ->
            failwith "insert Collect_set: ceq = None"
              (fun _ -> insert (_A1, _A2) x (Collect_set a))
          | Some eq -> Collect_set (fun_upd eq a x true))
and remove (_A1, _A2)
  x xa1 = match x, xa1 with
    x, Complement a -> Complement (insert (_A1, _A2) x a)
    | x, RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "remove RBT_set: ccompare = None"
              (fun _ -> remove (_A1, _A2) x (RBT_set rbt))
          | Some _ -> RBT_set (delete _A2 x rbt))
    | x, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "remove DList_set: ceq = None"
              (fun _ -> remove (_A1, _A2) x (DList_set dxs))
          | Some _ -> DList_set (removea _A1 x dxs))
    | x, Collect_set a ->
        (match ceq _A1
          with None ->
            failwith "remove Collect: ceq = None"
              (fun _ -> remove (_A1, _A2) x (Collect_set a))
          | Some eq -> Collect_set (fun_upd eq a x false));;

let rec image (_A1, _A2) (_B1, _B2, _B3)
  h x1 = match h, x1 with
    h, RBT_set rbt ->
      (match ccompare _A2
        with None ->
          failwith "image RBT_set: ccompare = None"
            (fun _ -> image (_A1, _A2) (_B1, _B2, _B3) h (RBT_set rbt))
        | Some _ ->
          foldb _A2 (comp (insert (_B1, _B2)) h) rbt (bot_set (_B1, _B2, _B3)))
    | g, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "image DList_set: ceq = None"
              (fun _ -> image (_A1, _A2) (_B1, _B2, _B3) g (DList_set dxs))
          | Some _ ->
            foldc _A1 (comp (insert (_B1, _B2)) g) dxs
              (bot_set (_B1, _B2, _B3)))
    | f, Complement (Complement b) -> image (_A1, _A2) (_B1, _B2, _B3) f b
    | f, Collect_set a ->
        failwith "image Collect_set"
          (fun _ -> image (_A1, _A2) (_B1, _B2, _B3) f (Collect_set a))
    | f, Set_Monad xs -> Set_Monad (map f xs);;

let rec foldl f a x2 = match f, a, x2 with f, a, [] -> a
                | f, a, x :: xs -> foldl f (f a x) xs;;

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec doConj
  p1 p2 =
    (match (p1, p2) with (Inl p1a, Inl p2a) -> [Inl (SConj (p1a, p2a))]
      | (Inl _, Inr p2a) -> [Inr (VConjR p2a)]
      | (Inr p1a, Inl _) -> [Inr (VConjL p1a)]
      | (Inr p1a, Inr p2a) -> [Inr (VConjL p1a); Inr (VConjR p2a)]);;

let rec doDisj
  p1 p2 =
    (match (p1, p2)
      with (Inl p1a, Inl p2a) -> [Inl (SDisjL p1a); Inl (SDisjR p2a)]
      | (Inl p1a, Inr _) -> [Inl (SDisjL p1a)]
      | (Inr _, Inl p2a) -> [Inl (SDisjR p2a)]
      | (Inr p1a, Inr p2a) -> [Inr (VDisj (p1a, p2a))]);;

let rec doNext
  ia i tau p =
    (match (p, less_nat tau (left i)) with (Inl _, true) -> [Inr (VNext_le ia)]
      | (Inl pa, false) ->
        (if less_eq_nat (left i) tau && less_eq_enat (Enat tau) (right i)
          then [Inl (SNext pa)] else [Inr (VNext_ge ia)])
      | (Inr pa, true) -> [Inr (VNext pa); Inr (VNext_le ia)]
      | (Inr pa, false) ->
        (if less_eq_nat (left i) tau && less_eq_enat (Enat tau) (right i)
          then [Inr (VNext pa)] else [Inr (VNext pa); Inr (VNext_ge ia)]));;

let rec doPrev
  ia i tau p =
    (match (p, less_nat tau (left i)) with (Inl _, true) -> [Inr (VPrev_le ia)]
      | (Inl pa, false) ->
        (if less_eq_nat (left i) tau && less_eq_enat (Enat tau) (right i)
          then [Inl (SPrev pa)] else [Inr (VPrev_ge ia)])
      | (Inr pa, true) -> [Inr (VPrev pa); Inr (VPrev_le ia)]
      | (Inr pa, false) ->
        (if less_eq_nat (left i) tau && less_eq_enat (Enat tau) (right i)
          then [Inr (VPrev pa)] else [Inr (VPrev pa); Inr (VPrev_ge ia)]));;

let rec filter
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filter p xs else filter p xs);;

let rec proofApp
  p r = (match (p, r)
          with (Inl (SSince (p1, p2)), Inl ra) -> Inl (SSince (p1, p2 @ [ra]))
          | (Inl (SUntil (p1, p2)), Inl ra) -> Inl (SUntil (ra :: p1, p2))
          | (Inr (VSince (i, p1, p2)), Inr ra) ->
            Inr (VSince (suc i, p1, p2 @ [ra]))
          | (Inr (VUntil (i, p1, p2)), Inr ra) ->
            Inr (VUntil (minus_nat i one_nat, ra :: p1, p2))
          | (Inr (VSince_never (i, li, p1)), Inr ra) ->
            Inr (VSince_never (suc i, li, p1 @ [ra]))
          | (Inr (VUntil_never (i, hi, p1)), Inr ra) ->
            Inr (VUntil_never (minus_nat i one_nat, hi, ra :: p1)));;

let rec doSince
  i a p1 p2 p =
    (match (p1, (p2, (equal_nata a zero_nata, p)))
      with (Inl p1a, (Inl aa, (true, Inl pa))) ->
        [proofApp (Inl pa) (Inl p1a); Inl (SSince (aa, []))]
      | (Inl _, (Inl aa, (true, Inr (VSince (_, _, _))))) ->
        [Inl (SSince (aa, []))]
      | (Inl _, (Inl aa, (true, Inr (VSince_never (_, _, _))))) ->
        [Inl (SSince (aa, []))]
      | (Inl p1a, (Inl _, (false, Inl pa))) -> [proofApp (Inl pa) (Inl p1a)]
      | (Inl _, (Inl _, (false, Inr (VSince (_, q1, q2))))) ->
        [Inr (VSince (i, q1, q2))]
      | (Inl _, (Inl _, (false, Inr (VSince_never (_, li, q))))) ->
        [Inr (VSince_never (i, li, q))]
      | (Inl p1a, (Inr _, (true, Inl pa))) -> [proofApp (Inl pa) (Inl p1a)]
      | (Inl _, (Inr p2a, (true, Inr (VSince (_, _, _))))) ->
        [proofApp p (Inr p2a)]
      | (Inl _, (Inr p2a, (true, Inr (VSince_never (_, _, _))))) ->
        [proofApp p (Inr p2a)]
      | (Inl p1a, (Inr _, (false, Inl pa))) -> [proofApp (Inl pa) (Inl p1a)]
      | (Inl _, (Inr _, (false, Inr (VSince (_, q1, q2))))) ->
        [Inr (VSince (i, q1, q2))]
      | (Inl _, (Inr _, (false, Inr (VSince_never (_, li, q))))) ->
        [Inr (VSince_never (i, li, q))]
      | (Inr _, (Inl aa, (true, Inl _))) -> [Inl (SSince (aa, []))]
      | (Inr _, (Inl aa, (true, Inr (VSince (_, _, _))))) ->
        [Inl (SSince (aa, []))]
      | (Inr _, (Inl aa, (true, Inr (VSince_never (_, _, _))))) ->
        [Inl (SSince (aa, []))]
      | (Inr p1a, (Inl _, (false, Inl _))) -> [Inr (VSince (i, p1a, []))]
      | (Inr p1a, (Inl _, (false, Inr (VSince (_, q1, q2))))) ->
        [Inr (VSince (i, p1a, [])); Inr (VSince (i, q1, q2))]
      | (Inr p1a, (Inl _, (false, Inr (VSince_never (_, li, q))))) ->
        [Inr (VSince (i, p1a, [])); Inr (VSince_never (i, li, q))]
      | (Inr p1a, (Inr p2a, (true, Inl _))) -> [Inr (VSince (i, p1a, [p2a]))]
      | (Inr p1a, (Inr p2a, (true, Inr (VSince (_, _, _))))) ->
        [Inr (VSince (i, p1a, [p2a])); proofApp p (Inr p2a)]
      | (Inr p1a, (Inr p2a, (true, Inr (VSince_never (_, _, _))))) ->
        [Inr (VSince (i, p1a, [p2a])); proofApp p (Inr p2a)]
      | (Inr p1a, (Inr _, (false, Inl _))) -> [Inr (VSince (i, p1a, []))]
      | (Inr p1a, (Inr _, (false, Inr (VSince (_, q1, q2))))) ->
        [Inr (VSince (i, p1a, [])); Inr (VSince (i, q1, q2))]
      | (Inr p1a, (Inr _, (false, Inr (VSince_never (_, li, q))))) ->
        [Inr (VSince (i, p1a, [])); Inr (VSince_never (i, li, q))]);;

let rec doUntil
  i a p1 p2 p =
    (match (p1, (p2, (equal_nata a zero_nata, p)))
      with (Inl p1a, (Inl aa, (true, Inl (SUntil (_, _))))) ->
        [proofApp p (Inl p1a); Inl (SUntil ([], aa))]
      | (Inl _, (Inl aa, (true, Inr (VUntil (_, _, _))))) ->
        [Inl (SUntil ([], aa))]
      | (Inl _, (Inl aa, (true, Inr (VUntil_never (_, _, _))))) ->
        [Inl (SUntil ([], aa))]
      | (Inl p1a, (Inl _, (false, Inl (SUntil (_, _))))) ->
        [proofApp p (Inl p1a)]
      | (Inl _, (Inl _, (false, Inr (VUntil (_, q1, q2))))) ->
        [Inr (VUntil (i, q1, q2))]
      | (Inl _, (Inl _, (false, Inr (VUntil_never (_, hi, q))))) ->
        [Inr (VUntil_never (i, hi, q))]
      | (Inl p1a, (Inr _, (true, Inl (SUntil (_, _))))) ->
        [proofApp p (Inl p1a)]
      | (Inl _, (Inr p2a, (true, Inr (VUntil (_, _, _))))) ->
        [proofApp p (Inr p2a)]
      | (Inl _, (Inr p2a, (true, Inr (VUntil_never (_, _, _))))) ->
        [proofApp p (Inr p2a)]
      | (Inl p1a, (Inr _, (false, Inl (SUntil (_, _))))) ->
        [proofApp p (Inl p1a)]
      | (Inl _, (Inr _, (false, Inr (VUntil (_, q1, q2))))) ->
        [Inr (VUntil (i, q1, q2))]
      | (Inl _, (Inr _, (false, Inr (VUntil_never (_, hi, q))))) ->
        [Inr (VUntil_never (i, hi, q))]
      | (Inr _, (Inl aa, (true, Inl (SUntil (_, _))))) ->
        [Inl (SUntil ([], aa))]
      | (Inr _, (Inl aa, (true, Inr (VUntil (_, _, _))))) ->
        [Inl (SUntil ([], aa))]
      | (Inr _, (Inl aa, (true, Inr (VUntil_never (_, _, _))))) ->
        [Inl (SUntil ([], aa))]
      | (Inr p1a, (Inl _, (false, Inl (SUntil (_, _))))) ->
        [Inr (VUntil (i, [], p1a))]
      | (Inr p1a, (Inl _, (false, Inr (VUntil (_, q1, q2))))) ->
        [Inr (VUntil (i, [], p1a)); Inr (VUntil (i, q1, q2))]
      | (Inr p1a, (Inl _, (false, Inr (VUntil_never (_, hi, q))))) ->
        [Inr (VUntil (i, [], p1a)); Inr (VUntil_never (i, hi, q))]
      | (Inr p1a, (Inr p2a, (true, Inl (SUntil (_, _))))) ->
        [Inr (VUntil (i, [p2a], p1a))]
      | (Inr p1a, (Inr p2a, (true, Inr (VUntil (_, _, _))))) ->
        [Inr (VUntil (i, [p2a], p1a)); proofApp p (Inr p2a)]
      | (Inr p1a, (Inr p2a, (true, Inr (VUntil_never (_, _, _))))) ->
        [Inr (VUntil (i, [p2a], p1a)); proofApp p (Inr p2a)]
      | (Inr p1a, (Inr _, (false, Inl (SUntil (_, _))))) ->
        [Inr (VUntil (i, [], p1a))]
      | (Inr p1a, (Inr _, (false, Inr (VUntil (_, q1, q2))))) ->
        [Inr (VUntil (i, [], p1a)); Inr (VUntil (i, q1, q2))]
      | (Inr p1a, (Inr _, (false, Inr (VUntil_never (_, hi, q))))) ->
        [Inr (VUntil (i, [], p1a)); Inr (VUntil_never (i, hi, q))]);;

let empty : ('a, 'b) alist = Alist [];;

let rec hda (x21 :: x22) = x21;;

let rec hd _A xa = hda (list_of_dlist _A xa);;

let rec tla = function [] -> []
              | x21 :: x22 -> x22;;

let rec tl _A xa = Abs_dlist (tla (list_of_dlist _A xa));;

let rec set_aux (_A1, _A2)
  = function Set_Monada -> (fun a -> Set_Monad a)
    | Set_Choose ->
        (match ccompare _A2
          with None ->
            (match ceq _A1 with None -> (fun a -> Set_Monad a)
              | Some _ ->
                foldl (fun s x -> insert (_A1, _A2) x s)
                  (DList_set (emptya _A1)))
          | Some _ ->
            foldl (fun s x -> insert (_A1, _A2) x s) (RBT_set (emptyb _A2)))
    | impl ->
        foldl (fun s x -> insert (_A1, _A2) x s) (set_empty (_A1, _A2) impl);;

let rec set (_A1, _A2, _A3)
  xs = set_aux (_A1, _A2) (of_phantom (set_impl _A3)) xs;;

let rec sum_list _A
  xs = foldr (plus _A.semigroup_add_monoid_add.plus_semigroup_add) xs
         (zero _A.zero_monoid_add);;

let rec sum_proofs _B f xs = sum_list _B (map f xs);;

let rec v_atm
  w x1 = match w, x1 with w, VFF i -> one_nat
    | w, VAtm (atm, i) -> w atm
    | w, VNeg p -> suc (s_atm w p)
    | w, VDisj (p, q) -> suc (plus_nata (v_atm w p) (v_atm w q))
    | w, VConjL p -> suc (v_atm w p)
    | w, VConjR q -> suc (v_atm w q)
    | w, VSince (i, p, qs) ->
        suc (sum_proofs monoid_add_nat (v_atm w) (p :: qs))
    | w, VUntil (i, qs, p) ->
        suc (sum_proofs monoid_add_nat (v_atm w) (qs @ [p]))
    | w, VSince_never (i, li, qs) ->
        suc (sum_proofs monoid_add_nat (v_atm w) qs)
    | w, VUntil_never (i, hi, qs) ->
        suc (sum_proofs monoid_add_nat (v_atm w) qs)
    | w, VSince_le uu -> one_nat
    | w, VNext p -> suc (v_atm w p)
    | w, VNext_le i -> one_nat
    | w, VNext_ge i -> one_nat
    | w, VPrev p -> suc (v_atm w p)
    | w, VPrev_le i -> one_nat
    | w, VPrev_ge i -> one_nat
    | w, VPrev_zero -> one_nat
and s_atm
  w x1 = match w, x1 with w, STT i -> one_nat
    | w, SAtm (atm, i) -> w atm
    | w, SNeg p -> suc (v_atm w p)
    | w, SDisjL p -> suc (s_atm w p)
    | w, SDisjR q -> suc (s_atm w q)
    | w, SConj (p, q) -> suc (plus_nata (s_atm w p) (s_atm w q))
    | w, SSince (p, qs) -> suc (sum_proofs monoid_add_nat (s_atm w) (p :: qs))
    | w, SUntil (qs, p) -> suc (sum_proofs monoid_add_nat (s_atm w) (qs @ [p]))
    | w, SNext p -> suc (s_atm w p)
    | w, SPrev p -> suc (s_atm w p);;

let rec matm
  w = (fun a -> (match a with Inl aa -> s_atm w aa | Inr aa -> v_atm w aa));;

let rec strmatm x = matm x;;

let rec ratm f p1 p2 = less_eq_nat (strmatm f p1) (strmatm f p2);;

let rec nulla _A xa = null (list_of_dlist _A xa);;

let rec semilattice_set_apply (Abs_semilattice_set x) = x;;

let rec is_empty _A
  xa = (match impl_ofa _A xa with Empty -> true
         | Branch (_, _, _, _, _) -> false);;

let rec rBT_Impl_fold1
  f x1 = match f, x1 with
    f, Branch (ca, Branch (c, l, ka, va, ra), k, v, r) ->
      folda (fun kb _ -> f kb) r
        (f k (rBT_Impl_fold1 f (Branch (c, l, ka, va, ra))))
    | f, Branch (c, Empty, k, v, r) -> folda (fun ka _ -> f ka) r k
    | f, Empty -> failwith "undefined";;

let rec fold1 _A x xc = rBT_Impl_fold1 x (impl_ofa _A xc);;

let rec set_fold1 (_A1, _A2, _A3)
  f x1 = match f, x1 with
    f, RBT_set rbt ->
      (match ccompare _A2
        with None ->
          failwith "set_fold1 RBT_set: ccompare = None"
            (fun _ -> set_fold1 (_A1, _A2, _A3) f (RBT_set rbt))
        | Some _ ->
          (if is_empty _A2 rbt
            then failwith "set_fold1 RBT_set: empty set"
                   (fun _ -> set_fold1 (_A1, _A2, _A3) f (RBT_set rbt))
            else fold1 _A2 (semilattice_set_apply f) rbt))
    | f, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "set_fold1 DList_set: ceq = None"
              (fun _ -> set_fold1 (_A1, _A2, _A3) f (DList_set dxs))
          | Some _ ->
            (if nulla _A1 dxs
              then failwith "set_fold1 DList_set: empty set"
                     (fun _ -> set_fold1 (_A1, _A2, _A3) f (DList_set dxs))
              else foldc _A1 (semilattice_set_apply f) (tl _A1 dxs)
                     (hd _A1 dxs)))
    | f, Set_Monad (x :: xs) -> fold (semilattice_set_apply f) xs x
    | f, Collect_set p ->
        failwith "set_fold1: Collect_set"
          (fun _ -> set_fold1 (_A1, _A2, _A3) f (Collect_set p))
    | f, Complement a ->
        failwith "set_fold1: Complement"
          (fun _ -> set_fold1 (_A1, _A2, _A3) f (Complement a));;

let rec max_sls _A
  = Abs_semilattice_set (max _A.order_linorder.preorder_order.ord_preorder);;

let rec maxa (_A1, _A2, _A3, _A4)
  a = set_fold1 (_A1, _A2, _A3) (max_sls _A4) a;;

let rec max_proofs (_A1, _A2, _A3) (_B1, _B2, _B3, _B4, _B5, _B6)
  f xs =
    (match xs with [] -> zero _B3
      | _ :: _ ->
        maxa (_B1, _B2, _B4, _B5)
          (image (_A1, _A2) (_B1, _B2, _B6) f (set (_A1, _A2, _A3) xs)));;

let rec s_htp (_A1, _A2)
  = function STT i -> i
    | SAtm (atm, i) -> i
    | SNeg p -> v_htp (_A1, _A2) p
    | SDisjL p -> s_htp (_A1, _A2) p
    | SDisjR q -> s_htp (_A1, _A2) q
    | SConj (p, q) -> max ord_nat (s_htp (_A1, _A2) p) (s_htp (_A1, _A2) q)
    | SSince (p, qs) ->
        max_proofs ((ceq_sproof _A2), (ccompare_sproof _A1), set_impl_sproof)
          (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
            set_impl_nat)
          (s_htp (_A1, _A2)) (p :: qs)
    | SUntil (qs, p) ->
        max_proofs ((ceq_sproof _A2), (ccompare_sproof _A1), set_impl_sproof)
          (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
            set_impl_nat)
          (s_htp (_A1, _A2)) (qs @ [p])
    | SNext p -> s_htp (_A1, _A2) p
    | SPrev p -> max ord_nat (s_at (SPrev p)) (s_htp (_A1, _A2) p)
and v_htp (_A1, _A2)
  = function VFF i -> i
    | VAtm (atm, i) -> i
    | VNeg p -> s_htp (_A1, _A2) p
    | VDisj (p, q) -> max ord_nat (v_htp (_A1, _A2) p) (v_htp (_A1, _A2) q)
    | VConjL p -> v_htp (_A1, _A2) p
    | VConjR q -> v_htp (_A1, _A2) q
    | VSince (i, p, qs) ->
        max ord_nat i
          (max_proofs ((ceq_vproof _A2), (ccompare_vproof _A1), set_impl_vproof)
            (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
              set_impl_nat)
            (v_htp (_A1, _A2)) (p :: qs))
    | VUntil (i, qs, p) ->
        max ord_nat i
          (max_proofs ((ceq_vproof _A2), (ccompare_vproof _A1), set_impl_vproof)
            (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
              set_impl_nat)
            (v_htp (_A1, _A2)) (qs @ [p]))
    | VSince_never (i, li, qs) ->
        max ord_nat (max ord_nat i li)
          (max_proofs ((ceq_vproof _A2), (ccompare_vproof _A1), set_impl_vproof)
            (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
              set_impl_nat)
            (v_htp (_A1, _A2)) qs)
    | VUntil_never (i, hi, qs) ->
        max ord_nat (max ord_nat i (suc hi))
          (max_proofs ((ceq_vproof _A2), (ccompare_vproof _A1), set_impl_vproof)
            (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
              set_impl_nat)
            (v_htp (_A1, _A2)) qs)
    | VSince_le i -> i
    | VNext p -> v_htp (_A1, _A2) p
    | VNext_le i -> suc i
    | VNext_ge i -> suc i
    | VPrev p -> max ord_nat (v_at (VPrev p)) (v_htp (_A1, _A2) p)
    | VPrev_le i -> i
    | VPrev_ge i -> i
    | VPrev_zero -> zero_nata;;

let rec min_sls _A
  = Abs_semilattice_set (min _A.order_linorder.preorder_order.ord_preorder);;

let rec mina (_A1, _A2, _A3, _A4)
  a = set_fold1 (_A1, _A2, _A3) (min_sls _A4) a;;

let rec min_proofs (_A1, _A2, _A3) (_B1, _B2, _B3, _B4, _B5, _B6)
  f xs =
    (match xs with [] -> infinity _B3
      | _ :: _ ->
        mina (_B1, _B2, _B4, _B5)
          (image (_A1, _A2) (_B1, _B2, _B6) f (set (_A1, _A2, _A3) xs)));;

let zero_enat : enat = Enat zero_nata;;

let rec minus_enat x0 n = match x0, n with Enat a, Infinity_enat -> zero_enat
                     | Infinity_enat, n -> Infinity_enat
                     | Enat a, Enat b -> Enat (minus_nat a b);;

let one_enat : enat = Enat one_nat;;

let rec s_ltp (_A1, _A2)
  = function STT i -> Enat i
    | SAtm (atm, i) -> Enat i
    | SNeg p -> v_ltp (_A1, _A2) p
    | SDisjL p -> s_ltp (_A1, _A2) p
    | SDisjR q -> s_ltp (_A1, _A2) q
    | SConj (p, q) -> min ord_enat (s_ltp (_A1, _A2) p) (s_ltp (_A1, _A2) q)
    | SSince (p, qs) ->
        min_proofs ((ceq_sproof _A2), (ccompare_sproof _A1), set_impl_sproof)
          (ceq_enat, ccompare_enat, infinity_enat, lattice_enat, linorder_enat,
            set_impl_enat)
          (s_ltp (_A1, _A2)) (p :: qs)
    | SUntil (qs, p) ->
        min_proofs ((ceq_sproof _A2), (ccompare_sproof _A1), set_impl_sproof)
          (ceq_enat, ccompare_enat, infinity_enat, lattice_enat, linorder_enat,
            set_impl_enat)
          (s_ltp (_A1, _A2)) (qs @ [p])
    | SNext p -> min ord_enat (Enat (s_at (SNext p))) (s_ltp (_A1, _A2) p)
    | SPrev p -> s_ltp (_A1, _A2) p
and v_ltp (_A1, _A2)
  = function VFF i -> Enat i
    | VAtm (atm, i) -> Enat i
    | VNeg p -> s_ltp (_A1, _A2) p
    | VDisj (p, q) -> min ord_enat (v_ltp (_A1, _A2) p) (v_ltp (_A1, _A2) q)
    | VConjL p -> v_ltp (_A1, _A2) p
    | VConjR q -> v_ltp (_A1, _A2) q
    | VSince (i, p, qs) -> zero_enat
    | VUntil (i, qs, p) ->
        min ord_enat (Enat i)
          (min_proofs ((ceq_vproof _A2), (ccompare_vproof _A1), set_impl_vproof)
            (ceq_enat, ccompare_enat, infinity_enat, lattice_enat,
              linorder_enat, set_impl_enat)
            (v_ltp (_A1, _A2)) (qs @ [p]))
    | VSince_never (i, li, qs) -> zero_enat
    | VUntil_never (i, hi, qs) ->
        min ord_enat (min ord_enat (Enat i) (Enat hi))
          (min_proofs ((ceq_vproof _A2), (ccompare_vproof _A1), set_impl_vproof)
            (ceq_enat, ccompare_enat, infinity_enat, lattice_enat,
              linorder_enat, set_impl_enat)
            (v_ltp (_A1, _A2)) qs)
    | VSince_le i -> zero_enat
    | VNext p -> min ord_enat (Enat (v_at (VNext p))) (v_ltp (_A1, _A2) p)
    | VNext_le i -> Enat i
    | VNext_ge i -> Enat i
    | VPrev p -> v_ltp (_A1, _A2) p
    | VPrev_le i -> minus_enat (Enat i) one_enat
    | VPrev_ge i -> minus_enat (Enat i) one_enat
    | VPrev_zero -> zero_enat;;

let rec doSinceBase
  i a p1 p2 =
    (match (p1, (p2, equal_nata a zero_nata))
      with (Inl _, (Inl p2a, true)) -> [Inl (SSince (p2a, []))]
      | (Inl _, (Inl _, false)) -> [Inr (VSince_never (i, i, []))]
      | (Inl _, (Inr ba, true)) -> [Inr (VSince_never (i, i, [ba]))]
      | (Inl _, (Inr _, false)) -> [Inr (VSince_never (i, i, []))]
      | (Inr _, (Inl p2a, true)) -> [Inl (SSince (p2a, []))]
      | (Inr ba, (Inl _, false)) ->
        [Inr (VSince (i, ba, [])); Inr (VSince_never (i, i, []))]
      | (Inr ba, (Inr baa, true)) ->
        [Inr (VSince (i, ba, [baa])); Inr (VSince_never (i, i, [baa]))]
      | (Inr ba, (Inr _, false)) ->
        [Inr (VSince (i, ba, [])); Inr (VSince_never (i, i, []))]);;

let rec doUntilBase
  i a p1 p2 =
    (match (p1, (p2, equal_nata a zero_nata))
      with (Inl _, (Inl p2a, true)) -> [Inl (SUntil ([], p2a))]
      | (Inl _, (Inl _, false)) -> [Inr (VUntil_never (i, i, []))]
      | (Inl _, (Inr ba, true)) -> [Inr (VUntil_never (i, i, [ba]))]
      | (Inl _, (Inr _, false)) -> [Inr (VUntil_never (i, i, []))]
      | (Inr _, (Inl p2a, true)) -> [Inl (SUntil ([], p2a))]
      | (Inr ba, (Inl _, false)) ->
        [Inr (VUntil (i, [], ba)); Inr (VUntil_never (i, i, []))]
      | (Inr ba, (Inr baa, true)) ->
        [Inr (VUntil (i, [baa], ba)); Inr (VUntil_never (i, i, [baa]))]
      | (Inr ba, (Inr _, false)) ->
        [Inr (VUntil (i, [], ba)); Inr (VUntil_never (i, i, []))]);;

let rec v_depth (_A1, _A2)
  = function VFF i -> one_nat
    | VAtm (atm, i) -> one_nat
    | VNeg p -> suc (s_depth (_A1, _A2) p)
    | VDisj (p, q) ->
        suc (max ord_nat (v_depth (_A1, _A2) p) (v_depth (_A1, _A2) q))
    | VConjL p -> suc (v_depth (_A1, _A2) p)
    | VConjR q -> suc (v_depth (_A1, _A2) q)
    | VSince (i, p, qs) ->
        suc (max_proofs
              ((ceq_vproof _A2), (ccompare_vproof _A1), set_impl_vproof)
              (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
                set_impl_nat)
              (v_depth (_A1, _A2)) (p :: qs))
    | VUntil (i, qs, p) ->
        suc (max_proofs
              ((ceq_vproof _A2), (ccompare_vproof _A1), set_impl_vproof)
              (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
                set_impl_nat)
              (v_depth (_A1, _A2)) (qs @ [p]))
    | VSince_never (i, li, qs) ->
        suc (max_proofs
              ((ceq_vproof _A2), (ccompare_vproof _A1), set_impl_vproof)
              (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
                set_impl_nat)
              (v_depth (_A1, _A2)) qs)
    | VUntil_never (i, hi, qs) ->
        suc (max_proofs
              ((ceq_vproof _A2), (ccompare_vproof _A1), set_impl_vproof)
              (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
                set_impl_nat)
              (v_depth (_A1, _A2)) qs)
    | VSince_le i -> one_nat
    | VNext p -> suc (v_depth (_A1, _A2) p)
    | VNext_le i -> one_nat
    | VNext_ge i -> one_nat
    | VPrev p -> suc (v_depth (_A1, _A2) p)
    | VPrev_le i -> one_nat
    | VPrev_ge i -> one_nat
    | VPrev_zero -> one_nat
and s_depth (_A1, _A2)
  = function STT i -> one_nat
    | SAtm (atm, i) -> one_nat
    | SNeg p -> suc (v_depth (_A1, _A2) p)
    | SDisjL p -> suc (s_depth (_A1, _A2) p)
    | SDisjR q -> suc (s_depth (_A1, _A2) q)
    | SConj (p, q) ->
        suc (max ord_nat (s_depth (_A1, _A2) p) (s_depth (_A1, _A2) q))
    | SSince (p, qs) ->
        suc (max_proofs
              ((ceq_sproof _A2), (ccompare_sproof _A1), set_impl_sproof)
              (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
                set_impl_nat)
              (s_depth (_A1, _A2)) (p :: qs))
    | SUntil (qs, p) ->
        suc (max_proofs
              ((ceq_sproof _A2), (ccompare_sproof _A1), set_impl_sproof)
              (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
                set_impl_nat)
              (s_depth (_A1, _A2)) (qs @ [p]))
    | SNext p -> suc (s_depth (_A1, _A2) p)
    | SPrev p -> suc (s_depth (_A1, _A2) p);;

let rec mdepth (_A1, _A2)
  = (fun a ->
      (match a with Inl aa -> s_depth (_A1, _A2) aa
        | Inr aa -> v_depth (_A1, _A2) aa));;

let rec strmdepth x = mdepth (ccompare_literal, equal_literal) x;;

let rec rdepth p1 p2 = less_eq_nat (strmdepth p1) (strmdepth p2);;

let rec strset x = set (ceq_literal, ccompare_literal, set_impl_literal) x;;

let rec min_list_wrt r xs = hda (filter (fun x -> list_all (r x) xs) xs);;

let rec projr (Inr x2) = x2;;

let rec projl (Inl x1) = x1;;

let rec subtract
  xb xc =
    Abs_I (let (i, j) = rep_I xc in (minus_nat i xb, minus_enat j (Enat xb)));;

let rec isl = function Inl x1 -> true
              | Inr x2 -> false;;

let rec opt_atm w rho i phi = min_list_wrt (ratm w) (cand_atm w rho i phi)
and cand_atm
  w rho i x3 = match w, rho, i, x3 with w, rho, i, TT -> [Inl (STT i)]
    | w, rho, i, FF -> [Inr (VFF i)]
    | w, rho, i, Atom n ->
        (match
          member (ceq_literal, ccompare_literal) n
            (gamma (ceq_literal, ccompare_literal, set_impl_literal) rho i)
          with true -> [Inl (SAtm (n, i))] | false -> [Inr (VAtm (n, i))])
    | w, rho, i, Disj (phi, psi) ->
        doDisj (opt_atm w rho i phi) (opt_atm w rho i psi)
    | w, rho, i, Conj (phi, psi) ->
        doConj (opt_atm w rho i phi) (opt_atm w rho i psi)
    | w, rho, i, Neg phi ->
        (let p = opt_atm w rho i phi in
          (if isl p then [Inr (VNeg (projl p))] else [Inl (SNeg (projr p))]))
    | w, rho, ia, Prev (i, phi) ->
        (if equal_nata ia zero_nata then [Inr VPrev_zero]
          else doPrev ia i
                 (minus_nat
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     ia)
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     (minus_nat ia one_nat)))
                 (opt_atm w rho (minus_nat ia one_nat) phi))
    | w, rho, ia, Next (i, phi) ->
        doNext ia i
          (minus_nat
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (plus_nata ia one_nat))
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (minus_nat (plus_nata ia one_nat) one_nat)))
          (opt_atm w rho (plus_nata ia one_nat) phi)
    | w, rho, ia, Since (phi, i, psi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VSince_le ia)]
          else (let p1 = opt_atm w rho ia phi in
                let p2 = opt_atm w rho ia psi in
                 (if equal_nata ia zero_nata
                   then doSinceBase zero_nata zero_nata p1 p2
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doSince ia (left i) p1 p2
                                 (opt_atm w rho (minus_nat ia one_nat)
                                   (Since
                                     (phi, subtract
     (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
       (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
         (minus_nat ia one_nat)))
     i,
                                       psi)))
                          else doSinceBase ia (left i) p1 p2))))
    | w, rho, ia, Until (phi, i, psi) ->
        (let p1 = opt_atm w rho ia phi in
         let p2 = opt_atm w rho ia psi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doUntil ia (left i) p1 p2
                   (opt_atm w rho (plus_nata ia one_nat)
                     (Until
                       (phi, subtract
                               (minus_nat
                                 (tau (ceq_literal, ccompare_literal,
set_impl_literal)
                                   rho (plus_nata ia one_nat))
                                 (tau (ceq_literal, ccompare_literal,
set_impl_literal)
                                   rho (minus_nat (plus_nata ia one_nat)
 one_nat)))
                               i,
                         psi)))
            else doUntilBase ia (left i) p1 p2));;

let rec strs_at x = s_at x;;

let rec strv_at x = v_at x;;

let rec zip_with_index_from
  n x1 = match n, x1 with n, x :: xs -> (n, x) :: zip_with_index_from (suc n) xs
    | n, [] -> [];;

let rec rbt_comp_bulkload
  c xs = foldr (fun (a, b) -> rbt_comp_insert c a b) xs Empty;;

let rec bulkloada _A
  xa = Mapping_RBTa (rbt_comp_bulkload (the (ccompare _A)) xa);;

let rec bulkload
  vs = RBT_Mapping (bulkloada ccompare_nat (zip_with_index_from zero_nata vs));;

let rec interval
  l r = Abs_I (if less_eq_enat (Enat l) r then (l, r)
                else rep_I (failwith "undefined"));;

let rec maxreach (_A1, _A2)
  = (fun a ->
      (match a with Inl aa -> s_htp (_A1, _A2) aa
        | Inr aa -> v_htp (_A1, _A2) aa));;

let rec minreach (_A1, _A2)
  = (fun a ->
      (match a with Inl aa -> s_ltp (_A1, _A2) aa
        | Inr aa -> v_ltp (_A1, _A2) aa));;

let rec bounded_future
  = function
    Until (phi, i, psi) ->
      bounded_future phi &&
        (bounded_future psi && not (equal_enat (right i) Infinity_enat))
    | Since (phi, i, psi) -> bounded_future phi && bounded_future psi
    | Prev (i, phi) -> bounded_future phi
    | Next (i, phi) -> bounded_future phi
    | Neg phi -> bounded_future phi
    | Conj (phi, psi) -> bounded_future phi && bounded_future psi
    | Disj (phi, psi) -> bounded_future phi && bounded_future psi
    | Atom n -> true
    | FF -> true
    | TT -> true;;

let rec opt_depth rho i phi = min_list_wrt rdepth (cand_depth rho i phi)
and cand_depth
  rho i x2 = match rho, i, x2 with rho, i, TT -> [Inl (STT i)]
    | rho, i, FF -> [Inr (VFF i)]
    | rho, i, Atom n ->
        (match
          member (ceq_literal, ccompare_literal) n
            (gamma (ceq_literal, ccompare_literal, set_impl_literal) rho i)
          with true -> [Inl (SAtm (n, i))] | false -> [Inr (VAtm (n, i))])
    | rho, i, Disj (phi, psi) ->
        doDisj (opt_depth rho i phi) (opt_depth rho i psi)
    | rho, i, Conj (phi, psi) ->
        doConj (opt_depth rho i phi) (opt_depth rho i psi)
    | rho, i, Neg phi ->
        (let p = opt_depth rho i phi in
          (if isl p then [Inr (VNeg (projl p))] else [Inl (SNeg (projr p))]))
    | rho, ia, Prev (i, phi) ->
        (if equal_nata ia zero_nata then [Inr VPrev_zero]
          else doPrev ia i
                 (minus_nat
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     ia)
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     (minus_nat ia one_nat)))
                 (opt_depth rho (minus_nat ia one_nat) phi))
    | rho, ia, Next (i, phi) ->
        doNext ia i
          (minus_nat
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (plus_nata ia one_nat))
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (minus_nat (plus_nata ia one_nat) one_nat)))
          (opt_depth rho (plus_nata ia one_nat) phi)
    | rho, ia, Since (phi, i, psi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VSince_le ia)]
          else (let p1 = opt_depth rho ia phi in
                let p2 = opt_depth rho ia psi in
                 (if equal_nata ia zero_nata
                   then doSinceBase zero_nata zero_nata p1 p2
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doSince ia (left i) p1 p2
                                 (opt_depth rho (minus_nat ia one_nat)
                                   (Since
                                     (phi, subtract
     (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
       (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
         (minus_nat ia one_nat)))
     i,
                                       psi)))
                          else doSinceBase ia (left i) p1 p2))))
    | rho, ia, Until (phi, i, psi) ->
        (let p1 = opt_depth rho ia phi in
         let p2 = opt_depth rho ia psi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doUntil ia (left i) p1 p2
                   (opt_depth rho (plus_nata ia one_nat)
                     (Until
                       (phi, subtract
                               (minus_nat
                                 (tau (ceq_literal, ccompare_literal,
set_impl_literal)
                                   rho (plus_nata ia one_nat))
                                 (tau (ceq_literal, ccompare_literal,
set_impl_literal)
                                   rho (minus_nat (plus_nata ia one_nat)
 one_nat)))
                               i,
                         psi)))
            else doUntilBase ia (left i) p1 p2));;

let rec is_opt_atm
  w rho i phi p =
    (if bounded_future phi
      then valid (ceq_literal, ccompare_literal, equal_literal,
                   set_impl_literal)
             rho i phi p &&
             ratm w p (opt_atm w rho i phi)
      else failwith "optimal: not bounded future"
             (fun _ -> is_opt_atm w rho i phi p));;

let rec strs_check
  x = s_check (ceq_literal, ccompare_literal, equal_literal, set_impl_literal)
        x;;

let rec strv_check
  x = v_check (ceq_literal, ccompare_literal, equal_literal, set_impl_literal)
        x;;

let rec strmaxreach x = maxreach (ccompare_literal, equal_literal) x;;

let rec strminreach x = minreach (ccompare_literal, equal_literal) x;;

let rec is_opt_depth
  rho i phi p =
    (if bounded_future phi
      then valid (ceq_literal, ccompare_literal, equal_literal,
                   set_impl_literal)
             rho i phi p &&
             rdepth p (opt_depth rho i phi)
      else failwith "optimal: not bounded future"
             (fun _ -> is_opt_depth rho i phi p));;

let rec rmaxmaxreach
  p1 p2 =
    equal_nata (p_at p1) (p_at p2) &&
      less_eq_nat (strmaxreach p2) (strmaxreach p1);;

let rec rmaxminreach
  p1 p2 =
    equal_nata (p_at p1) (p_at p2) &&
      less_eq_enat (strminreach p2) (strminreach p1);;

let rec rminmaxreach
  p1 p2 =
    equal_nata (p_at p1) (p_at p2) &&
      less_eq_nat (strmaxreach p1) (strmaxreach p2);;

let rec rminminreach
  p1 p2 =
    equal_nata (p_at p1) (p_at p2) &&
      less_eq_enat (strminreach p1) (strminreach p2);;

let mapping_impl_nat : (nat, mapping_impl) phantom = Phantom Mapping_RBT;;

let rec mapping_empty_choose _A
  = (match ccompare _A with None -> Assoc_List_Mapping empty
      | Some _ -> RBT_Mapping (emptyb _A));;

let rec mapping_empty _A = function Mapping_RBT -> RBT_Mapping (emptyb _A)
                           | Mapping_Assoc_List -> Assoc_List_Mapping empty
                           | Mapping_Mapping -> Mapping (fun _ -> None)
                           | Mapping_Choose -> mapping_empty_choose _A;;

let rec sorted _A
  = function
    x :: y :: zs ->
      less_eq _A.order_linorder.preorder_order.ord_preorder x y &&
        sorted _A (y :: zs)
    | [x] -> true
    | [] -> true;;

let rec trace_rbt_of_list
  xa = Abs_trace_rbt
         (if sorted linorder_nat (map snd xa)
           then (if null xa
                  then (zero_nata,
                         (zero_nata,
                           mapping_empty ccompare_nat
                             (of_phantom mapping_impl_nat)))
                  else (size_list xa, (snd (last xa), bulkload xa)))
           else (zero_nata,
                  (zero_nata,
                    mapping_empty ccompare_nat
                      (of_phantom mapping_impl_nat))));;

let rec trace_of_list xs = Trace_RBT (trace_rbt_of_list xs);;

let rec opt_maxmaxreach
  rho i phi = min_list_wrt rmaxmaxreach (cand_maxmaxreach rho i phi)
and cand_maxmaxreach
  rho i x2 = match rho, i, x2 with rho, i, TT -> [Inl (STT i)]
    | rho, i, FF -> [Inr (VFF i)]
    | rho, i, Atom n ->
        (match
          member (ceq_literal, ccompare_literal) n
            (gamma (ceq_literal, ccompare_literal, set_impl_literal) rho i)
          with true -> [Inl (SAtm (n, i))] | false -> [Inr (VAtm (n, i))])
    | rho, i, Disj (phi, psi) ->
        doDisj (opt_maxmaxreach rho i phi) (opt_maxmaxreach rho i psi)
    | rho, i, Conj (phi, psi) ->
        doConj (opt_maxmaxreach rho i phi) (opt_maxmaxreach rho i psi)
    | rho, i, Neg phi ->
        (let p = opt_maxmaxreach rho i phi in
          (if isl p then [Inr (VNeg (projl p))] else [Inl (SNeg (projr p))]))
    | rho, ia, Prev (i, phi) ->
        (if equal_nata ia zero_nata then [Inr VPrev_zero]
          else doPrev ia i
                 (minus_nat
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     ia)
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     (minus_nat ia one_nat)))
                 (opt_maxmaxreach rho (minus_nat ia one_nat) phi))
    | rho, ia, Next (i, phi) ->
        doNext ia i
          (minus_nat
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (plus_nata ia one_nat))
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (minus_nat (plus_nata ia one_nat) one_nat)))
          (opt_maxmaxreach rho (plus_nata ia one_nat) phi)
    | rho, ia, Since (phi, i, psi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VSince_le ia)]
          else (let p1 = opt_maxmaxreach rho ia phi in
                let p2 = opt_maxmaxreach rho ia psi in
                 (if equal_nata ia zero_nata
                   then doSinceBase zero_nata zero_nata p1 p2
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doSince ia (left i) p1 p2
                                 (opt_maxmaxreach rho (minus_nat ia one_nat)
                                   (Since
                                     (phi, subtract
     (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
       (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
         (minus_nat ia one_nat)))
     i,
                                       psi)))
                          else doSinceBase ia (left i) p1 p2))))
    | rho, ia, Until (phi, i, psi) ->
        (let p1 = opt_maxmaxreach rho ia phi in
         let p2 = opt_maxmaxreach rho ia psi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doUntil ia (left i) p1 p2
                   (opt_maxmaxreach rho (plus_nata ia one_nat)
                     (Until
                       (phi, subtract
                               (minus_nat
                                 (tau (ceq_literal, ccompare_literal,
set_impl_literal)
                                   rho (plus_nata ia one_nat))
                                 (tau (ceq_literal, ccompare_literal,
set_impl_literal)
                                   rho (minus_nat (plus_nata ia one_nat)
 one_nat)))
                               i,
                         psi)))
            else doUntilBase ia (left i) p1 p2));;

let rec opt_maxminreach
  rho i phi = min_list_wrt rmaxminreach (cand_maxminreach rho i phi)
and cand_maxminreach
  rho i x2 = match rho, i, x2 with rho, i, TT -> [Inl (STT i)]
    | rho, i, FF -> [Inr (VFF i)]
    | rho, i, Atom n ->
        (match
          member (ceq_literal, ccompare_literal) n
            (gamma (ceq_literal, ccompare_literal, set_impl_literal) rho i)
          with true -> [Inl (SAtm (n, i))] | false -> [Inr (VAtm (n, i))])
    | rho, i, Disj (phi, psi) ->
        doDisj (opt_maxminreach rho i phi) (opt_maxminreach rho i psi)
    | rho, i, Conj (phi, psi) ->
        doConj (opt_maxminreach rho i phi) (opt_maxminreach rho i psi)
    | rho, i, Neg phi ->
        (let p = opt_maxminreach rho i phi in
          (if isl p then [Inr (VNeg (projl p))] else [Inl (SNeg (projr p))]))
    | rho, ia, Prev (i, phi) ->
        (if equal_nata ia zero_nata then [Inr VPrev_zero]
          else doPrev ia i
                 (minus_nat
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     ia)
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     (minus_nat ia one_nat)))
                 (opt_maxminreach rho (minus_nat ia one_nat) phi))
    | rho, ia, Next (i, phi) ->
        doNext ia i
          (minus_nat
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (plus_nata ia one_nat))
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (minus_nat (plus_nata ia one_nat) one_nat)))
          (opt_maxminreach rho (plus_nata ia one_nat) phi)
    | rho, ia, Since (phi, i, psi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VSince_le ia)]
          else (let p1 = opt_maxminreach rho ia phi in
                let p2 = opt_maxminreach rho ia psi in
                 (if equal_nata ia zero_nata
                   then doSinceBase zero_nata zero_nata p1 p2
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doSince ia (left i) p1 p2
                                 (opt_maxminreach rho (minus_nat ia one_nat)
                                   (Since
                                     (phi, subtract
     (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
       (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
         (minus_nat ia one_nat)))
     i,
                                       psi)))
                          else doSinceBase ia (left i) p1 p2))))
    | rho, ia, Until (phi, i, psi) ->
        (let p1 = opt_maxminreach rho ia phi in
         let p2 = opt_maxminreach rho ia psi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doUntil ia (left i) p1 p2
                   (opt_maxminreach rho (plus_nata ia one_nat)
                     (Until
                       (phi, subtract
                               (minus_nat
                                 (tau (ceq_literal, ccompare_literal,
set_impl_literal)
                                   rho (plus_nata ia one_nat))
                                 (tau (ceq_literal, ccompare_literal,
set_impl_literal)
                                   rho (minus_nat (plus_nata ia one_nat)
 one_nat)))
                               i,
                         psi)))
            else doUntilBase ia (left i) p1 p2));;

let rec opt_minmaxreach
  rho i phi = min_list_wrt rminmaxreach (cand_minmaxreach rho i phi)
and cand_minmaxreach
  rho i x2 = match rho, i, x2 with rho, i, TT -> [Inl (STT i)]
    | rho, i, FF -> [Inr (VFF i)]
    | rho, i, Atom n ->
        (match
          member (ceq_literal, ccompare_literal) n
            (gamma (ceq_literal, ccompare_literal, set_impl_literal) rho i)
          with true -> [Inl (SAtm (n, i))] | false -> [Inr (VAtm (n, i))])
    | rho, i, Disj (phi, psi) ->
        doDisj (opt_minmaxreach rho i phi) (opt_minmaxreach rho i psi)
    | rho, i, Conj (phi, psi) ->
        doConj (opt_minmaxreach rho i phi) (opt_minmaxreach rho i psi)
    | rho, i, Neg phi ->
        (let p = opt_minmaxreach rho i phi in
          (if isl p then [Inr (VNeg (projl p))] else [Inl (SNeg (projr p))]))
    | rho, ia, Prev (i, phi) ->
        (if equal_nata ia zero_nata then [Inr VPrev_zero]
          else doPrev ia i
                 (minus_nat
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     ia)
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     (minus_nat ia one_nat)))
                 (opt_minmaxreach rho (minus_nat ia one_nat) phi))
    | rho, ia, Next (i, phi) ->
        doNext ia i
          (minus_nat
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (plus_nata ia one_nat))
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (minus_nat (plus_nata ia one_nat) one_nat)))
          (opt_minmaxreach rho (plus_nata ia one_nat) phi)
    | rho, ia, Since (phi, i, psi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VSince_le ia)]
          else (let p1 = opt_minmaxreach rho ia phi in
                let p2 = opt_minmaxreach rho ia psi in
                 (if equal_nata ia zero_nata
                   then doSinceBase zero_nata zero_nata p1 p2
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doSince ia (left i) p1 p2
                                 (opt_minmaxreach rho (minus_nat ia one_nat)
                                   (Since
                                     (phi, subtract
     (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
       (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
         (minus_nat ia one_nat)))
     i,
                                       psi)))
                          else doSinceBase ia (left i) p1 p2))))
    | rho, ia, Until (phi, i, psi) ->
        (let p1 = opt_minmaxreach rho ia phi in
         let p2 = opt_minmaxreach rho ia psi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doUntil ia (left i) p1 p2
                   (opt_minmaxreach rho (plus_nata ia one_nat)
                     (Until
                       (phi, subtract
                               (minus_nat
                                 (tau (ceq_literal, ccompare_literal,
set_impl_literal)
                                   rho (plus_nata ia one_nat))
                                 (tau (ceq_literal, ccompare_literal,
set_impl_literal)
                                   rho (minus_nat (plus_nata ia one_nat)
 one_nat)))
                               i,
                         psi)))
            else doUntilBase ia (left i) p1 p2));;

let rec opt_minminreach
  rho i phi = min_list_wrt rminminreach (cand_minminreach rho i phi)
and cand_minminreach
  rho i x2 = match rho, i, x2 with rho, i, TT -> [Inl (STT i)]
    | rho, i, FF -> [Inr (VFF i)]
    | rho, i, Atom n ->
        (match
          member (ceq_literal, ccompare_literal) n
            (gamma (ceq_literal, ccompare_literal, set_impl_literal) rho i)
          with true -> [Inl (SAtm (n, i))] | false -> [Inr (VAtm (n, i))])
    | rho, i, Disj (phi, psi) ->
        doDisj (opt_minminreach rho i phi) (opt_minminreach rho i psi)
    | rho, i, Conj (phi, psi) ->
        doConj (opt_minminreach rho i phi) (opt_minminreach rho i psi)
    | rho, i, Neg phi ->
        (let p = opt_minminreach rho i phi in
          (if isl p then [Inr (VNeg (projl p))] else [Inl (SNeg (projr p))]))
    | rho, ia, Prev (i, phi) ->
        (if equal_nata ia zero_nata then [Inr VPrev_zero]
          else doPrev ia i
                 (minus_nat
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     ia)
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     (minus_nat ia one_nat)))
                 (opt_minminreach rho (minus_nat ia one_nat) phi))
    | rho, ia, Next (i, phi) ->
        doNext ia i
          (minus_nat
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (plus_nata ia one_nat))
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (minus_nat (plus_nata ia one_nat) one_nat)))
          (opt_minminreach rho (plus_nata ia one_nat) phi)
    | rho, ia, Since (phi, i, psi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VSince_le ia)]
          else (let p1 = opt_minminreach rho ia phi in
                let p2 = opt_minminreach rho ia psi in
                 (if equal_nata ia zero_nata
                   then doSinceBase zero_nata zero_nata p1 p2
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doSince ia (left i) p1 p2
                                 (opt_minminreach rho (minus_nat ia one_nat)
                                   (Since
                                     (phi, subtract
     (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
       (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
         (minus_nat ia one_nat)))
     i,
                                       psi)))
                          else doSinceBase ia (left i) p1 p2))))
    | rho, ia, Until (phi, i, psi) ->
        (let p1 = opt_minminreach rho ia phi in
         let p2 = opt_minminreach rho ia psi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doUntil ia (left i) p1 p2
                   (opt_minminreach rho (plus_nata ia one_nat)
                     (Until
                       (phi, subtract
                               (minus_nat
                                 (tau (ceq_literal, ccompare_literal,
set_impl_literal)
                                   rho (plus_nata ia one_nat))
                                 (tau (ceq_literal, ccompare_literal,
set_impl_literal)
                                   rho (minus_nat (plus_nata ia one_nat)
 one_nat)))
                               i,
                         psi)))
            else doUntilBase ia (left i) p1 p2));;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let rec is_opt_maxmaxreach
  rho i phi p =
    (if bounded_future phi
      then valid (ceq_literal, ccompare_literal, equal_literal,
                   set_impl_literal)
             rho i phi p &&
             rmaxmaxreach p (opt_maxmaxreach rho i phi)
      else failwith "optimal: not bounded future"
             (fun _ -> is_opt_maxmaxreach rho i phi p));;

let rec is_opt_maxminreach
  rho i phi p =
    (if bounded_future phi
      then valid (ceq_literal, ccompare_literal, equal_literal,
                   set_impl_literal)
             rho i phi p &&
             rmaxminreach p (opt_maxminreach rho i phi)
      else failwith "optimal: not bounded future"
             (fun _ -> is_opt_maxminreach rho i phi p));;

let rec is_opt_minmaxreach
  rho i phi p =
    (if bounded_future phi
      then valid (ceq_literal, ccompare_literal, equal_literal,
                   set_impl_literal)
             rho i phi p &&
             rminmaxreach p (opt_minmaxreach rho i phi)
      else failwith "optimal: not bounded future"
             (fun _ -> is_opt_minmaxreach rho i phi p));;

let rec is_opt_minminreach
  rho i phi p =
    (if bounded_future phi
      then valid (ceq_literal, ccompare_literal, equal_literal,
                   set_impl_literal)
             rho i phi p &&
             rminminreach p (opt_minminreach rho i phi)
      else failwith "optimal: not bounded future"
             (fun _ -> is_opt_minminreach rho i phi p));;

end;; (*struct Explanator*)
