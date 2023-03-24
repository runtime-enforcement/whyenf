module VerifiedExplanator2 : sig
  type nat
  val integer_of_nat : nat -> Z.t
  type 'a vproof = VFF of nat | VAtm of 'a * nat | VNeg of 'a sproof |
    VDisj of 'a vproof * 'a vproof | VConjL of 'a vproof | VConjR of 'a vproof |
    VImpl of 'a sproof * 'a vproof | VIff_sv of 'a sproof * 'a vproof |
    VIff_vs of 'a vproof * 'a sproof | VOnce_le of nat |
    VOnce of nat * nat * 'a vproof list |
    VEventually of nat * nat * 'a vproof list | VHistorically of nat * 'a vproof
    | VAlways of nat * 'a vproof | VSince of nat * 'a vproof * 'a vproof list |
    VUntil of nat * 'a vproof list * 'a vproof |
    VSince_never of nat * nat * 'a vproof list |
    VUntil_never of nat * nat * 'a vproof list | VSince_le of nat |
    VNext of 'a vproof | VNext_ge of nat | VNext_le of nat | VPrev of 'a vproof
    | VPrev_ge of nat | VPrev_le of nat | VPrev_zero
  and 'a sproof = STT of nat | SAtm of 'a * nat | SNeg of 'a vproof |
    SDisjL of 'a sproof | SDisjR of 'a sproof | SConj of 'a sproof * 'a sproof |
    SImplR of 'a sproof | SImplL of 'a vproof | SIff_ss of 'a sproof * 'a sproof
    | SIff_vv of 'a vproof * 'a vproof | SOnce of nat * 'a sproof |
    SEventually of nat * 'a sproof | SHistorically of nat * nat * 'a sproof list
    | SHistorically_le of nat | SAlways of nat * nat * 'a sproof list |
    SSince of 'a sproof * 'a sproof list | SUntil of 'a sproof list * 'a sproof
    | SNext of 'a sproof | SPrev of 'a sproof
  type enat = Enat of nat | Infinity_enat
  type i
  type 'a mtl = TT | FF | Atom of 'a | Neg of 'a mtl | Disj of 'a mtl * 'a mtl |
    Conj of 'a mtl * 'a mtl | Impl of 'a mtl * 'a mtl | Iff of 'a mtl * 'a mtl |
    Next of i * 'a mtl | Prev of i * 'a mtl | Once of i * 'a mtl |
    Historically of i * 'a mtl | Eventually of i * 'a mtl | Always of i * 'a mtl
    | Since of 'a mtl * i * 'a mtl | Until of 'a mtl * i * 'a mtl
  type 'a set
  type 'a trace_rbt
  type 'a trace
  type ('a, 'b) sum = Inl of 'a | Inr of 'b
  val nat_of_integer : Z.t -> nat
  val strmatm : (string -> nat) -> (string sproof, string vproof) sum -> nat
  val ratm :
    (string -> nat) ->
      (string sproof, string vproof) sum ->
        (string sproof, string vproof) sum -> bool
  val rratm :
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
  val rrdepth :
    (string sproof, string vproof) sum ->
      (string sproof, string vproof) sum -> bool
  val strs_at : string sproof -> nat
  val strv_at : string vproof -> nat
  val interval : nat -> enat -> i
  val is_valid :
    string trace -> string mtl -> (string sproof, string vproof) sum -> bool
  val opt_depth :
    string trace -> nat -> string mtl -> (string sproof, string vproof) sum
  val sprogress : string trace -> string mtl -> nat -> nat
  val is_opt_atm :
    (string -> nat) ->
      string trace ->
        nat -> string mtl -> (string sproof, string vproof) sum -> bool
  val is_minimal :
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
  val opt_flipped_atm :
    (string -> nat) ->
      string trace -> nat -> string mtl -> (string sproof, string vproof) sum
  val opt_maxmaxreach :
    string trace -> nat -> string mtl -> (string sproof, string vproof) sum
  val opt_maxminreach :
    string trace -> nat -> string mtl -> (string sproof, string vproof) sum
  val opt_minmaxreach :
    string trace -> nat -> string mtl -> (string sproof, string vproof) sum
  val opt_minminreach :
    string trace -> nat -> string mtl -> (string sproof, string vproof) sum
  val opt_flipped_depth :
    string trace -> nat -> string mtl -> (string sproof, string vproof) sum
  val is_opt_flipped_atm :
    (string -> nat) ->
      string trace ->
        nat -> string mtl -> (string sproof, string vproof) sum -> bool
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
  val is_opt_flipped_depth :
    string trace ->
      nat -> string mtl -> (string sproof, string vproof) sum -> bool
  val rlex_atm_minmaxreach :
    (string -> nat) ->
      (string sproof, string vproof) sum ->
        (string sproof, string vproof) sum -> bool
  val opt_lex_atm_minmaxreach :
    (string -> nat) ->
      string trace -> nat -> string mtl -> (string sproof, string vproof) sum
  val is_opt_lex_atm_minmaxreach :
    (string -> nat) ->
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
  VImpl of 'a sproof * 'a vproof | VIff_sv of 'a sproof * 'a vproof |
  VIff_vs of 'a vproof * 'a sproof | VOnce_le of nat |
  VOnce of nat * nat * 'a vproof list |
  VEventually of nat * nat * 'a vproof list | VHistorically of nat * 'a vproof |
  VAlways of nat * 'a vproof | VSince of nat * 'a vproof * 'a vproof list |
  VUntil of nat * 'a vproof list * 'a vproof |
  VSince_never of nat * nat * 'a vproof list |
  VUntil_never of nat * nat * 'a vproof list | VSince_le of nat |
  VNext of 'a vproof | VNext_ge of nat | VNext_le of nat | VPrev of 'a vproof |
  VPrev_ge of nat | VPrev_le of nat | VPrev_zero
and 'a sproof = STT of nat | SAtm of 'a * nat | SNeg of 'a vproof |
  SDisjL of 'a sproof | SDisjR of 'a sproof | SConj of 'a sproof * 'a sproof |
  SImplR of 'a sproof | SImplL of 'a vproof | SIff_ss of 'a sproof * 'a sproof |
  SIff_vv of 'a vproof * 'a vproof | SOnce of nat * 'a sproof |
  SEventually of nat * 'a sproof | SHistorically of nat * nat * 'a sproof list |
  SHistorically_le of nat | SAlways of nat * nat * 'a sproof list |
  SSince of 'a sproof * 'a sproof list | SUntil of 'a sproof list * 'a sproof |
  SNext of 'a sproof | SPrev of 'a sproof;;

let rec equal_sproof _A = ({equal = equal_sproofa _A} : 'a sproof equal)
and equal_sproofa _A
  x0 x1 = match x0, x1 with SNext x18, SPrev x19 -> false
    | SPrev x19, SNext x18 -> false
    | SUntil (x171, x172), SPrev x19 -> false
    | SPrev x19, SUntil (x171, x172) -> false
    | SUntil (x171, x172), SNext x18 -> false
    | SNext x18, SUntil (x171, x172) -> false
    | SSince (x161, x162), SPrev x19 -> false
    | SPrev x19, SSince (x161, x162) -> false
    | SSince (x161, x162), SNext x18 -> false
    | SNext x18, SSince (x161, x162) -> false
    | SSince (x161, x162), SUntil (x171, x172) -> false
    | SUntil (x171, x172), SSince (x161, x162) -> false
    | SAlways (x151, x152, x153), SPrev x19 -> false
    | SPrev x19, SAlways (x151, x152, x153) -> false
    | SAlways (x151, x152, x153), SNext x18 -> false
    | SNext x18, SAlways (x151, x152, x153) -> false
    | SAlways (x151, x152, x153), SUntil (x171, x172) -> false
    | SUntil (x171, x172), SAlways (x151, x152, x153) -> false
    | SAlways (x151, x152, x153), SSince (x161, x162) -> false
    | SSince (x161, x162), SAlways (x151, x152, x153) -> false
    | SHistorically_le x14, SPrev x19 -> false
    | SPrev x19, SHistorically_le x14 -> false
    | SHistorically_le x14, SNext x18 -> false
    | SNext x18, SHistorically_le x14 -> false
    | SHistorically_le x14, SUntil (x171, x172) -> false
    | SUntil (x171, x172), SHistorically_le x14 -> false
    | SHistorically_le x14, SSince (x161, x162) -> false
    | SSince (x161, x162), SHistorically_le x14 -> false
    | SHistorically_le x14, SAlways (x151, x152, x153) -> false
    | SAlways (x151, x152, x153), SHistorically_le x14 -> false
    | SHistorically (x131, x132, x133), SPrev x19 -> false
    | SPrev x19, SHistorically (x131, x132, x133) -> false
    | SHistorically (x131, x132, x133), SNext x18 -> false
    | SNext x18, SHistorically (x131, x132, x133) -> false
    | SHistorically (x131, x132, x133), SUntil (x171, x172) -> false
    | SUntil (x171, x172), SHistorically (x131, x132, x133) -> false
    | SHistorically (x131, x132, x133), SSince (x161, x162) -> false
    | SSince (x161, x162), SHistorically (x131, x132, x133) -> false
    | SHistorically (x131, x132, x133), SAlways (x151, x152, x153) -> false
    | SAlways (x151, x152, x153), SHistorically (x131, x132, x133) -> false
    | SHistorically (x131, x132, x133), SHistorically_le x14 -> false
    | SHistorically_le x14, SHistorically (x131, x132, x133) -> false
    | SEventually (x121, x122), SPrev x19 -> false
    | SPrev x19, SEventually (x121, x122) -> false
    | SEventually (x121, x122), SNext x18 -> false
    | SNext x18, SEventually (x121, x122) -> false
    | SEventually (x121, x122), SUntil (x171, x172) -> false
    | SUntil (x171, x172), SEventually (x121, x122) -> false
    | SEventually (x121, x122), SSince (x161, x162) -> false
    | SSince (x161, x162), SEventually (x121, x122) -> false
    | SEventually (x121, x122), SAlways (x151, x152, x153) -> false
    | SAlways (x151, x152, x153), SEventually (x121, x122) -> false
    | SEventually (x121, x122), SHistorically_le x14 -> false
    | SHistorically_le x14, SEventually (x121, x122) -> false
    | SEventually (x121, x122), SHistorically (x131, x132, x133) -> false
    | SHistorically (x131, x132, x133), SEventually (x121, x122) -> false
    | SOnce (x111, x112), SPrev x19 -> false
    | SPrev x19, SOnce (x111, x112) -> false
    | SOnce (x111, x112), SNext x18 -> false
    | SNext x18, SOnce (x111, x112) -> false
    | SOnce (x111, x112), SUntil (x171, x172) -> false
    | SUntil (x171, x172), SOnce (x111, x112) -> false
    | SOnce (x111, x112), SSince (x161, x162) -> false
    | SSince (x161, x162), SOnce (x111, x112) -> false
    | SOnce (x111, x112), SAlways (x151, x152, x153) -> false
    | SAlways (x151, x152, x153), SOnce (x111, x112) -> false
    | SOnce (x111, x112), SHistorically_le x14 -> false
    | SHistorically_le x14, SOnce (x111, x112) -> false
    | SOnce (x111, x112), SHistorically (x131, x132, x133) -> false
    | SHistorically (x131, x132, x133), SOnce (x111, x112) -> false
    | SOnce (x111, x112), SEventually (x121, x122) -> false
    | SEventually (x121, x122), SOnce (x111, x112) -> false
    | SIff_vv (x101, x102), SPrev x19 -> false
    | SPrev x19, SIff_vv (x101, x102) -> false
    | SIff_vv (x101, x102), SNext x18 -> false
    | SNext x18, SIff_vv (x101, x102) -> false
    | SIff_vv (x101, x102), SUntil (x171, x172) -> false
    | SUntil (x171, x172), SIff_vv (x101, x102) -> false
    | SIff_vv (x101, x102), SSince (x161, x162) -> false
    | SSince (x161, x162), SIff_vv (x101, x102) -> false
    | SIff_vv (x101, x102), SAlways (x151, x152, x153) -> false
    | SAlways (x151, x152, x153), SIff_vv (x101, x102) -> false
    | SIff_vv (x101, x102), SHistorically_le x14 -> false
    | SHistorically_le x14, SIff_vv (x101, x102) -> false
    | SIff_vv (x101, x102), SHistorically (x131, x132, x133) -> false
    | SHistorically (x131, x132, x133), SIff_vv (x101, x102) -> false
    | SIff_vv (x101, x102), SEventually (x121, x122) -> false
    | SEventually (x121, x122), SIff_vv (x101, x102) -> false
    | SIff_vv (x101, x102), SOnce (x111, x112) -> false
    | SOnce (x111, x112), SIff_vv (x101, x102) -> false
    | SIff_ss (x91, x92), SPrev x19 -> false
    | SPrev x19, SIff_ss (x91, x92) -> false
    | SIff_ss (x91, x92), SNext x18 -> false
    | SNext x18, SIff_ss (x91, x92) -> false
    | SIff_ss (x91, x92), SUntil (x171, x172) -> false
    | SUntil (x171, x172), SIff_ss (x91, x92) -> false
    | SIff_ss (x91, x92), SSince (x161, x162) -> false
    | SSince (x161, x162), SIff_ss (x91, x92) -> false
    | SIff_ss (x91, x92), SAlways (x151, x152, x153) -> false
    | SAlways (x151, x152, x153), SIff_ss (x91, x92) -> false
    | SIff_ss (x91, x92), SHistorically_le x14 -> false
    | SHistorically_le x14, SIff_ss (x91, x92) -> false
    | SIff_ss (x91, x92), SHistorically (x131, x132, x133) -> false
    | SHistorically (x131, x132, x133), SIff_ss (x91, x92) -> false
    | SIff_ss (x91, x92), SEventually (x121, x122) -> false
    | SEventually (x121, x122), SIff_ss (x91, x92) -> false
    | SIff_ss (x91, x92), SOnce (x111, x112) -> false
    | SOnce (x111, x112), SIff_ss (x91, x92) -> false
    | SIff_ss (x91, x92), SIff_vv (x101, x102) -> false
    | SIff_vv (x101, x102), SIff_ss (x91, x92) -> false
    | SImplL x8, SPrev x19 -> false
    | SPrev x19, SImplL x8 -> false
    | SImplL x8, SNext x18 -> false
    | SNext x18, SImplL x8 -> false
    | SImplL x8, SUntil (x171, x172) -> false
    | SUntil (x171, x172), SImplL x8 -> false
    | SImplL x8, SSince (x161, x162) -> false
    | SSince (x161, x162), SImplL x8 -> false
    | SImplL x8, SAlways (x151, x152, x153) -> false
    | SAlways (x151, x152, x153), SImplL x8 -> false
    | SImplL x8, SHistorically_le x14 -> false
    | SHistorically_le x14, SImplL x8 -> false
    | SImplL x8, SHistorically (x131, x132, x133) -> false
    | SHistorically (x131, x132, x133), SImplL x8 -> false
    | SImplL x8, SEventually (x121, x122) -> false
    | SEventually (x121, x122), SImplL x8 -> false
    | SImplL x8, SOnce (x111, x112) -> false
    | SOnce (x111, x112), SImplL x8 -> false
    | SImplL x8, SIff_vv (x101, x102) -> false
    | SIff_vv (x101, x102), SImplL x8 -> false
    | SImplL x8, SIff_ss (x91, x92) -> false
    | SIff_ss (x91, x92), SImplL x8 -> false
    | SImplR x7, SPrev x19 -> false
    | SPrev x19, SImplR x7 -> false
    | SImplR x7, SNext x18 -> false
    | SNext x18, SImplR x7 -> false
    | SImplR x7, SUntil (x171, x172) -> false
    | SUntil (x171, x172), SImplR x7 -> false
    | SImplR x7, SSince (x161, x162) -> false
    | SSince (x161, x162), SImplR x7 -> false
    | SImplR x7, SAlways (x151, x152, x153) -> false
    | SAlways (x151, x152, x153), SImplR x7 -> false
    | SImplR x7, SHistorically_le x14 -> false
    | SHistorically_le x14, SImplR x7 -> false
    | SImplR x7, SHistorically (x131, x132, x133) -> false
    | SHistorically (x131, x132, x133), SImplR x7 -> false
    | SImplR x7, SEventually (x121, x122) -> false
    | SEventually (x121, x122), SImplR x7 -> false
    | SImplR x7, SOnce (x111, x112) -> false
    | SOnce (x111, x112), SImplR x7 -> false
    | SImplR x7, SIff_vv (x101, x102) -> false
    | SIff_vv (x101, x102), SImplR x7 -> false
    | SImplR x7, SIff_ss (x91, x92) -> false
    | SIff_ss (x91, x92), SImplR x7 -> false
    | SImplR x7, SImplL x8 -> false
    | SImplL x8, SImplR x7 -> false
    | SConj (x61, x62), SPrev x19 -> false
    | SPrev x19, SConj (x61, x62) -> false
    | SConj (x61, x62), SNext x18 -> false
    | SNext x18, SConj (x61, x62) -> false
    | SConj (x61, x62), SUntil (x171, x172) -> false
    | SUntil (x171, x172), SConj (x61, x62) -> false
    | SConj (x61, x62), SSince (x161, x162) -> false
    | SSince (x161, x162), SConj (x61, x62) -> false
    | SConj (x61, x62), SAlways (x151, x152, x153) -> false
    | SAlways (x151, x152, x153), SConj (x61, x62) -> false
    | SConj (x61, x62), SHistorically_le x14 -> false
    | SHistorically_le x14, SConj (x61, x62) -> false
    | SConj (x61, x62), SHistorically (x131, x132, x133) -> false
    | SHistorically (x131, x132, x133), SConj (x61, x62) -> false
    | SConj (x61, x62), SEventually (x121, x122) -> false
    | SEventually (x121, x122), SConj (x61, x62) -> false
    | SConj (x61, x62), SOnce (x111, x112) -> false
    | SOnce (x111, x112), SConj (x61, x62) -> false
    | SConj (x61, x62), SIff_vv (x101, x102) -> false
    | SIff_vv (x101, x102), SConj (x61, x62) -> false
    | SConj (x61, x62), SIff_ss (x91, x92) -> false
    | SIff_ss (x91, x92), SConj (x61, x62) -> false
    | SConj (x61, x62), SImplL x8 -> false
    | SImplL x8, SConj (x61, x62) -> false
    | SConj (x61, x62), SImplR x7 -> false
    | SImplR x7, SConj (x61, x62) -> false
    | SDisjR x5, SPrev x19 -> false
    | SPrev x19, SDisjR x5 -> false
    | SDisjR x5, SNext x18 -> false
    | SNext x18, SDisjR x5 -> false
    | SDisjR x5, SUntil (x171, x172) -> false
    | SUntil (x171, x172), SDisjR x5 -> false
    | SDisjR x5, SSince (x161, x162) -> false
    | SSince (x161, x162), SDisjR x5 -> false
    | SDisjR x5, SAlways (x151, x152, x153) -> false
    | SAlways (x151, x152, x153), SDisjR x5 -> false
    | SDisjR x5, SHistorically_le x14 -> false
    | SHistorically_le x14, SDisjR x5 -> false
    | SDisjR x5, SHistorically (x131, x132, x133) -> false
    | SHistorically (x131, x132, x133), SDisjR x5 -> false
    | SDisjR x5, SEventually (x121, x122) -> false
    | SEventually (x121, x122), SDisjR x5 -> false
    | SDisjR x5, SOnce (x111, x112) -> false
    | SOnce (x111, x112), SDisjR x5 -> false
    | SDisjR x5, SIff_vv (x101, x102) -> false
    | SIff_vv (x101, x102), SDisjR x5 -> false
    | SDisjR x5, SIff_ss (x91, x92) -> false
    | SIff_ss (x91, x92), SDisjR x5 -> false
    | SDisjR x5, SImplL x8 -> false
    | SImplL x8, SDisjR x5 -> false
    | SDisjR x5, SImplR x7 -> false
    | SImplR x7, SDisjR x5 -> false
    | SDisjR x5, SConj (x61, x62) -> false
    | SConj (x61, x62), SDisjR x5 -> false
    | SDisjL x4, SPrev x19 -> false
    | SPrev x19, SDisjL x4 -> false
    | SDisjL x4, SNext x18 -> false
    | SNext x18, SDisjL x4 -> false
    | SDisjL x4, SUntil (x171, x172) -> false
    | SUntil (x171, x172), SDisjL x4 -> false
    | SDisjL x4, SSince (x161, x162) -> false
    | SSince (x161, x162), SDisjL x4 -> false
    | SDisjL x4, SAlways (x151, x152, x153) -> false
    | SAlways (x151, x152, x153), SDisjL x4 -> false
    | SDisjL x4, SHistorically_le x14 -> false
    | SHistorically_le x14, SDisjL x4 -> false
    | SDisjL x4, SHistorically (x131, x132, x133) -> false
    | SHistorically (x131, x132, x133), SDisjL x4 -> false
    | SDisjL x4, SEventually (x121, x122) -> false
    | SEventually (x121, x122), SDisjL x4 -> false
    | SDisjL x4, SOnce (x111, x112) -> false
    | SOnce (x111, x112), SDisjL x4 -> false
    | SDisjL x4, SIff_vv (x101, x102) -> false
    | SIff_vv (x101, x102), SDisjL x4 -> false
    | SDisjL x4, SIff_ss (x91, x92) -> false
    | SIff_ss (x91, x92), SDisjL x4 -> false
    | SDisjL x4, SImplL x8 -> false
    | SImplL x8, SDisjL x4 -> false
    | SDisjL x4, SImplR x7 -> false
    | SImplR x7, SDisjL x4 -> false
    | SDisjL x4, SConj (x61, x62) -> false
    | SConj (x61, x62), SDisjL x4 -> false
    | SDisjL x4, SDisjR x5 -> false
    | SDisjR x5, SDisjL x4 -> false
    | SNeg x3, SPrev x19 -> false
    | SPrev x19, SNeg x3 -> false
    | SNeg x3, SNext x18 -> false
    | SNext x18, SNeg x3 -> false
    | SNeg x3, SUntil (x171, x172) -> false
    | SUntil (x171, x172), SNeg x3 -> false
    | SNeg x3, SSince (x161, x162) -> false
    | SSince (x161, x162), SNeg x3 -> false
    | SNeg x3, SAlways (x151, x152, x153) -> false
    | SAlways (x151, x152, x153), SNeg x3 -> false
    | SNeg x3, SHistorically_le x14 -> false
    | SHistorically_le x14, SNeg x3 -> false
    | SNeg x3, SHistorically (x131, x132, x133) -> false
    | SHistorically (x131, x132, x133), SNeg x3 -> false
    | SNeg x3, SEventually (x121, x122) -> false
    | SEventually (x121, x122), SNeg x3 -> false
    | SNeg x3, SOnce (x111, x112) -> false
    | SOnce (x111, x112), SNeg x3 -> false
    | SNeg x3, SIff_vv (x101, x102) -> false
    | SIff_vv (x101, x102), SNeg x3 -> false
    | SNeg x3, SIff_ss (x91, x92) -> false
    | SIff_ss (x91, x92), SNeg x3 -> false
    | SNeg x3, SImplL x8 -> false
    | SImplL x8, SNeg x3 -> false
    | SNeg x3, SImplR x7 -> false
    | SImplR x7, SNeg x3 -> false
    | SNeg x3, SConj (x61, x62) -> false
    | SConj (x61, x62), SNeg x3 -> false
    | SNeg x3, SDisjR x5 -> false
    | SDisjR x5, SNeg x3 -> false
    | SNeg x3, SDisjL x4 -> false
    | SDisjL x4, SNeg x3 -> false
    | SAtm (x21, x22), SPrev x19 -> false
    | SPrev x19, SAtm (x21, x22) -> false
    | SAtm (x21, x22), SNext x18 -> false
    | SNext x18, SAtm (x21, x22) -> false
    | SAtm (x21, x22), SUntil (x171, x172) -> false
    | SUntil (x171, x172), SAtm (x21, x22) -> false
    | SAtm (x21, x22), SSince (x161, x162) -> false
    | SSince (x161, x162), SAtm (x21, x22) -> false
    | SAtm (x21, x22), SAlways (x151, x152, x153) -> false
    | SAlways (x151, x152, x153), SAtm (x21, x22) -> false
    | SAtm (x21, x22), SHistorically_le x14 -> false
    | SHistorically_le x14, SAtm (x21, x22) -> false
    | SAtm (x21, x22), SHistorically (x131, x132, x133) -> false
    | SHistorically (x131, x132, x133), SAtm (x21, x22) -> false
    | SAtm (x21, x22), SEventually (x121, x122) -> false
    | SEventually (x121, x122), SAtm (x21, x22) -> false
    | SAtm (x21, x22), SOnce (x111, x112) -> false
    | SOnce (x111, x112), SAtm (x21, x22) -> false
    | SAtm (x21, x22), SIff_vv (x101, x102) -> false
    | SIff_vv (x101, x102), SAtm (x21, x22) -> false
    | SAtm (x21, x22), SIff_ss (x91, x92) -> false
    | SIff_ss (x91, x92), SAtm (x21, x22) -> false
    | SAtm (x21, x22), SImplL x8 -> false
    | SImplL x8, SAtm (x21, x22) -> false
    | SAtm (x21, x22), SImplR x7 -> false
    | SImplR x7, SAtm (x21, x22) -> false
    | SAtm (x21, x22), SConj (x61, x62) -> false
    | SConj (x61, x62), SAtm (x21, x22) -> false
    | SAtm (x21, x22), SDisjR x5 -> false
    | SDisjR x5, SAtm (x21, x22) -> false
    | SAtm (x21, x22), SDisjL x4 -> false
    | SDisjL x4, SAtm (x21, x22) -> false
    | SAtm (x21, x22), SNeg x3 -> false
    | SNeg x3, SAtm (x21, x22) -> false
    | STT x1, SPrev x19 -> false
    | SPrev x19, STT x1 -> false
    | STT x1, SNext x18 -> false
    | SNext x18, STT x1 -> false
    | STT x1, SUntil (x171, x172) -> false
    | SUntil (x171, x172), STT x1 -> false
    | STT x1, SSince (x161, x162) -> false
    | SSince (x161, x162), STT x1 -> false
    | STT x1, SAlways (x151, x152, x153) -> false
    | SAlways (x151, x152, x153), STT x1 -> false
    | STT x1, SHistorically_le x14 -> false
    | SHistorically_le x14, STT x1 -> false
    | STT x1, SHistorically (x131, x132, x133) -> false
    | SHistorically (x131, x132, x133), STT x1 -> false
    | STT x1, SEventually (x121, x122) -> false
    | SEventually (x121, x122), STT x1 -> false
    | STT x1, SOnce (x111, x112) -> false
    | SOnce (x111, x112), STT x1 -> false
    | STT x1, SIff_vv (x101, x102) -> false
    | SIff_vv (x101, x102), STT x1 -> false
    | STT x1, SIff_ss (x91, x92) -> false
    | SIff_ss (x91, x92), STT x1 -> false
    | STT x1, SImplL x8 -> false
    | SImplL x8, STT x1 -> false
    | STT x1, SImplR x7 -> false
    | SImplR x7, STT x1 -> false
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
    | SPrev x19, SPrev y19 -> equal_sproofa _A x19 y19
    | SNext x18, SNext y18 -> equal_sproofa _A x18 y18
    | SUntil (x171, x172), SUntil (y171, y172) ->
        equal_list (equal_sproof _A) x171 y171 && equal_sproofa _A x172 y172
    | SSince (x161, x162), SSince (y161, y162) ->
        equal_sproofa _A x161 y161 && equal_list (equal_sproof _A) x162 y162
    | SAlways (x151, x152, x153), SAlways (y151, y152, y153) ->
        equal_nata x151 y151 &&
          (equal_nata x152 y152 && equal_list (equal_sproof _A) x153 y153)
    | SHistorically_le x14, SHistorically_le y14 -> equal_nata x14 y14
    | SHistorically (x131, x132, x133), SHistorically (y131, y132, y133) ->
        equal_nata x131 y131 &&
          (equal_nata x132 y132 && equal_list (equal_sproof _A) x133 y133)
    | SEventually (x121, x122), SEventually (y121, y122) ->
        equal_nata x121 y121 && equal_sproofa _A x122 y122
    | SOnce (x111, x112), SOnce (y111, y112) ->
        equal_nata x111 y111 && equal_sproofa _A x112 y112
    | SIff_vv (x101, x102), SIff_vv (y101, y102) ->
        equal_vproofa _A x101 y101 && equal_vproofa _A x102 y102
    | SIff_ss (x91, x92), SIff_ss (y91, y92) ->
        equal_sproofa _A x91 y91 && equal_sproofa _A x92 y92
    | SImplL x8, SImplL y8 -> equal_vproofa _A x8 y8
    | SImplR x7, SImplR y7 -> equal_sproofa _A x7 y7
    | SConj (x61, x62), SConj (y61, y62) ->
        equal_sproofa _A x61 y61 && equal_sproofa _A x62 y62
    | SDisjR x5, SDisjR y5 -> equal_sproofa _A x5 y5
    | SDisjL x4, SDisjL y4 -> equal_sproofa _A x4 y4
    | SNeg x3, SNeg y3 -> equal_vproofa _A x3 y3
    | SAtm (x21, x22), SAtm (y21, y22) -> eq _A x21 y21 && equal_nata x22 y22
    | STT x1, STT y1 -> equal_nata x1 y1
and equal_vproofa _A
  x0 x1 = match x0, x1 with VPrev_le x25, VPrev_zero -> false
    | VPrev_zero, VPrev_le x25 -> false
    | VPrev_ge x24, VPrev_zero -> false
    | VPrev_zero, VPrev_ge x24 -> false
    | VPrev_ge x24, VPrev_le x25 -> false
    | VPrev_le x25, VPrev_ge x24 -> false
    | VPrev x23, VPrev_zero -> false
    | VPrev_zero, VPrev x23 -> false
    | VPrev x23, VPrev_le x25 -> false
    | VPrev_le x25, VPrev x23 -> false
    | VPrev x23, VPrev_ge x24 -> false
    | VPrev_ge x24, VPrev x23 -> false
    | VNext_le x22a, VPrev_zero -> false
    | VPrev_zero, VNext_le x22a -> false
    | VNext_le x22a, VPrev_le x25 -> false
    | VPrev_le x25, VNext_le x22a -> false
    | VNext_le x22a, VPrev_ge x24 -> false
    | VPrev_ge x24, VNext_le x22a -> false
    | VNext_le x22a, VPrev x23 -> false
    | VPrev x23, VNext_le x22a -> false
    | VNext_ge x21a, VPrev_zero -> false
    | VPrev_zero, VNext_ge x21a -> false
    | VNext_ge x21a, VPrev_le x25 -> false
    | VPrev_le x25, VNext_ge x21a -> false
    | VNext_ge x21a, VPrev_ge x24 -> false
    | VPrev_ge x24, VNext_ge x21a -> false
    | VNext_ge x21a, VPrev x23 -> false
    | VPrev x23, VNext_ge x21a -> false
    | VNext_ge x21a, VNext_le x22a -> false
    | VNext_le x22a, VNext_ge x21a -> false
    | VNext x20, VPrev_zero -> false
    | VPrev_zero, VNext x20 -> false
    | VNext x20, VPrev_le x25 -> false
    | VPrev_le x25, VNext x20 -> false
    | VNext x20, VPrev_ge x24 -> false
    | VPrev_ge x24, VNext x20 -> false
    | VNext x20, VPrev x23 -> false
    | VPrev x23, VNext x20 -> false
    | VNext x20, VNext_le x22a -> false
    | VNext_le x22a, VNext x20 -> false
    | VNext x20, VNext_ge x21a -> false
    | VNext_ge x21a, VNext x20 -> false
    | VSince_le x19, VPrev_zero -> false
    | VPrev_zero, VSince_le x19 -> false
    | VSince_le x19, VPrev_le x25 -> false
    | VPrev_le x25, VSince_le x19 -> false
    | VSince_le x19, VPrev_ge x24 -> false
    | VPrev_ge x24, VSince_le x19 -> false
    | VSince_le x19, VPrev x23 -> false
    | VPrev x23, VSince_le x19 -> false
    | VSince_le x19, VNext_le x22a -> false
    | VNext_le x22a, VSince_le x19 -> false
    | VSince_le x19, VNext_ge x21a -> false
    | VNext_ge x21a, VSince_le x19 -> false
    | VSince_le x19, VNext x20 -> false
    | VNext x20, VSince_le x19 -> false
    | VUntil_never (x181, x182, x183), VPrev_zero -> false
    | VPrev_zero, VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VPrev_le x25 -> false
    | VPrev_le x25, VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VPrev_ge x24 -> false
    | VPrev_ge x24, VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VPrev x23 -> false
    | VPrev x23, VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VNext_le x22a -> false
    | VNext_le x22a, VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VNext_ge x21a -> false
    | VNext_ge x21a, VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VNext x20 -> false
    | VNext x20, VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VSince_le x19 -> false
    | VSince_le x19, VUntil_never (x181, x182, x183) -> false
    | VSince_never (x171, x172, x173), VPrev_zero -> false
    | VPrev_zero, VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VPrev_le x25 -> false
    | VPrev_le x25, VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VPrev_ge x24 -> false
    | VPrev_ge x24, VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VPrev x23 -> false
    | VPrev x23, VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VNext_le x22a -> false
    | VNext_le x22a, VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VNext_ge x21a -> false
    | VNext_ge x21a, VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VNext x20 -> false
    | VNext x20, VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VSince_le x19 -> false
    | VSince_le x19, VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VSince_never (x171, x172, x173) -> false
    | VUntil (x161, x162, x163), VPrev_zero -> false
    | VPrev_zero, VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VPrev_le x25 -> false
    | VPrev_le x25, VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VPrev_ge x24 -> false
    | VPrev_ge x24, VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VPrev x23 -> false
    | VPrev x23, VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VNext_le x22a -> false
    | VNext_le x22a, VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VNext_ge x21a -> false
    | VNext_ge x21a, VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VNext x20 -> false
    | VNext x20, VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VSince_le x19 -> false
    | VSince_le x19, VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VUntil (x161, x162, x163) -> false
    | VSince (x151, x152, x153), VPrev_zero -> false
    | VPrev_zero, VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VPrev_le x25 -> false
    | VPrev_le x25, VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VPrev_ge x24 -> false
    | VPrev_ge x24, VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VPrev x23 -> false
    | VPrev x23, VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VNext_le x22a -> false
    | VNext_le x22a, VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VNext_ge x21a -> false
    | VNext_ge x21a, VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VNext x20 -> false
    | VNext x20, VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VSince_le x19 -> false
    | VSince_le x19, VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VSince (x151, x152, x153) -> false
    | VAlways (x141, x142), VPrev_zero -> false
    | VPrev_zero, VAlways (x141, x142) -> false
    | VAlways (x141, x142), VPrev_le x25 -> false
    | VPrev_le x25, VAlways (x141, x142) -> false
    | VAlways (x141, x142), VPrev_ge x24 -> false
    | VPrev_ge x24, VAlways (x141, x142) -> false
    | VAlways (x141, x142), VPrev x23 -> false
    | VPrev x23, VAlways (x141, x142) -> false
    | VAlways (x141, x142), VNext_le x22a -> false
    | VNext_le x22a, VAlways (x141, x142) -> false
    | VAlways (x141, x142), VNext_ge x21a -> false
    | VNext_ge x21a, VAlways (x141, x142) -> false
    | VAlways (x141, x142), VNext x20 -> false
    | VNext x20, VAlways (x141, x142) -> false
    | VAlways (x141, x142), VSince_le x19 -> false
    | VSince_le x19, VAlways (x141, x142) -> false
    | VAlways (x141, x142), VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VAlways (x141, x142) -> false
    | VAlways (x141, x142), VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VAlways (x141, x142) -> false
    | VAlways (x141, x142), VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VAlways (x141, x142) -> false
    | VAlways (x141, x142), VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VAlways (x141, x142) -> false
    | VHistorically (x131, x132), VPrev_zero -> false
    | VPrev_zero, VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VPrev_le x25 -> false
    | VPrev_le x25, VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VPrev_ge x24 -> false
    | VPrev_ge x24, VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VPrev x23 -> false
    | VPrev x23, VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VNext_le x22a -> false
    | VNext_le x22a, VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VNext_ge x21a -> false
    | VNext_ge x21a, VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VNext x20 -> false
    | VNext x20, VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VSince_le x19 -> false
    | VSince_le x19, VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VAlways (x141, x142) -> false
    | VAlways (x141, x142), VHistorically (x131, x132) -> false
    | VEventually (x121, x122, x123), VPrev_zero -> false
    | VPrev_zero, VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VPrev_le x25 -> false
    | VPrev_le x25, VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VPrev_ge x24 -> false
    | VPrev_ge x24, VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VPrev x23 -> false
    | VPrev x23, VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VNext_le x22a -> false
    | VNext_le x22a, VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VNext_ge x21a -> false
    | VNext_ge x21a, VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VNext x20 -> false
    | VNext x20, VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VSince_le x19 -> false
    | VSince_le x19, VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VAlways (x141, x142) -> false
    | VAlways (x141, x142), VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VEventually (x121, x122, x123) -> false
    | VOnce (x111, x112, x113), VPrev_zero -> false
    | VPrev_zero, VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VPrev_le x25 -> false
    | VPrev_le x25, VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VPrev_ge x24 -> false
    | VPrev_ge x24, VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VPrev x23 -> false
    | VPrev x23, VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VNext_le x22a -> false
    | VNext_le x22a, VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VNext_ge x21a -> false
    | VNext_ge x21a, VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VNext x20 -> false
    | VNext x20, VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VSince_le x19 -> false
    | VSince_le x19, VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VAlways (x141, x142) -> false
    | VAlways (x141, x142), VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VOnce (x111, x112, x113) -> false
    | VOnce_le x10, VPrev_zero -> false
    | VPrev_zero, VOnce_le x10 -> false
    | VOnce_le x10, VPrev_le x25 -> false
    | VPrev_le x25, VOnce_le x10 -> false
    | VOnce_le x10, VPrev_ge x24 -> false
    | VPrev_ge x24, VOnce_le x10 -> false
    | VOnce_le x10, VPrev x23 -> false
    | VPrev x23, VOnce_le x10 -> false
    | VOnce_le x10, VNext_le x22a -> false
    | VNext_le x22a, VOnce_le x10 -> false
    | VOnce_le x10, VNext_ge x21a -> false
    | VNext_ge x21a, VOnce_le x10 -> false
    | VOnce_le x10, VNext x20 -> false
    | VNext x20, VOnce_le x10 -> false
    | VOnce_le x10, VSince_le x19 -> false
    | VSince_le x19, VOnce_le x10 -> false
    | VOnce_le x10, VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VOnce_le x10 -> false
    | VOnce_le x10, VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VOnce_le x10 -> false
    | VOnce_le x10, VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VOnce_le x10 -> false
    | VOnce_le x10, VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VOnce_le x10 -> false
    | VOnce_le x10, VAlways (x141, x142) -> false
    | VAlways (x141, x142), VOnce_le x10 -> false
    | VOnce_le x10, VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VOnce_le x10 -> false
    | VOnce_le x10, VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VOnce_le x10 -> false
    | VOnce_le x10, VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VOnce_le x10 -> false
    | VIff_vs (x91, x92), VPrev_zero -> false
    | VPrev_zero, VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VPrev_le x25 -> false
    | VPrev_le x25, VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VPrev_ge x24 -> false
    | VPrev_ge x24, VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VPrev x23 -> false
    | VPrev x23, VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VNext_le x22a -> false
    | VNext_le x22a, VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VNext_ge x21a -> false
    | VNext_ge x21a, VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VNext x20 -> false
    | VNext x20, VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VSince_le x19 -> false
    | VSince_le x19, VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VAlways (x141, x142) -> false
    | VAlways (x141, x142), VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VOnce_le x10 -> false
    | VOnce_le x10, VIff_vs (x91, x92) -> false
    | VIff_sv (x81, x82), VPrev_zero -> false
    | VPrev_zero, VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VPrev_le x25 -> false
    | VPrev_le x25, VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VPrev_ge x24 -> false
    | VPrev_ge x24, VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VPrev x23 -> false
    | VPrev x23, VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VNext_le x22a -> false
    | VNext_le x22a, VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VNext_ge x21a -> false
    | VNext_ge x21a, VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VNext x20 -> false
    | VNext x20, VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VSince_le x19 -> false
    | VSince_le x19, VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VAlways (x141, x142) -> false
    | VAlways (x141, x142), VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VOnce_le x10 -> false
    | VOnce_le x10, VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VIff_sv (x81, x82) -> false
    | VImpl (x71, x72), VPrev_zero -> false
    | VPrev_zero, VImpl (x71, x72) -> false
    | VImpl (x71, x72), VPrev_le x25 -> false
    | VPrev_le x25, VImpl (x71, x72) -> false
    | VImpl (x71, x72), VPrev_ge x24 -> false
    | VPrev_ge x24, VImpl (x71, x72) -> false
    | VImpl (x71, x72), VPrev x23 -> false
    | VPrev x23, VImpl (x71, x72) -> false
    | VImpl (x71, x72), VNext_le x22a -> false
    | VNext_le x22a, VImpl (x71, x72) -> false
    | VImpl (x71, x72), VNext_ge x21a -> false
    | VNext_ge x21a, VImpl (x71, x72) -> false
    | VImpl (x71, x72), VNext x20 -> false
    | VNext x20, VImpl (x71, x72) -> false
    | VImpl (x71, x72), VSince_le x19 -> false
    | VSince_le x19, VImpl (x71, x72) -> false
    | VImpl (x71, x72), VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VImpl (x71, x72) -> false
    | VImpl (x71, x72), VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VImpl (x71, x72) -> false
    | VImpl (x71, x72), VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VImpl (x71, x72) -> false
    | VImpl (x71, x72), VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VImpl (x71, x72) -> false
    | VImpl (x71, x72), VAlways (x141, x142) -> false
    | VAlways (x141, x142), VImpl (x71, x72) -> false
    | VImpl (x71, x72), VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VImpl (x71, x72) -> false
    | VImpl (x71, x72), VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VImpl (x71, x72) -> false
    | VImpl (x71, x72), VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VImpl (x71, x72) -> false
    | VImpl (x71, x72), VOnce_le x10 -> false
    | VOnce_le x10, VImpl (x71, x72) -> false
    | VImpl (x71, x72), VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VImpl (x71, x72) -> false
    | VImpl (x71, x72), VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VImpl (x71, x72) -> false
    | VConjR x6, VPrev_zero -> false
    | VPrev_zero, VConjR x6 -> false
    | VConjR x6, VPrev_le x25 -> false
    | VPrev_le x25, VConjR x6 -> false
    | VConjR x6, VPrev_ge x24 -> false
    | VPrev_ge x24, VConjR x6 -> false
    | VConjR x6, VPrev x23 -> false
    | VPrev x23, VConjR x6 -> false
    | VConjR x6, VNext_le x22a -> false
    | VNext_le x22a, VConjR x6 -> false
    | VConjR x6, VNext_ge x21a -> false
    | VNext_ge x21a, VConjR x6 -> false
    | VConjR x6, VNext x20 -> false
    | VNext x20, VConjR x6 -> false
    | VConjR x6, VSince_le x19 -> false
    | VSince_le x19, VConjR x6 -> false
    | VConjR x6, VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VConjR x6 -> false
    | VConjR x6, VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VConjR x6 -> false
    | VConjR x6, VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VConjR x6 -> false
    | VConjR x6, VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VConjR x6 -> false
    | VConjR x6, VAlways (x141, x142) -> false
    | VAlways (x141, x142), VConjR x6 -> false
    | VConjR x6, VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VConjR x6 -> false
    | VConjR x6, VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VConjR x6 -> false
    | VConjR x6, VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VConjR x6 -> false
    | VConjR x6, VOnce_le x10 -> false
    | VOnce_le x10, VConjR x6 -> false
    | VConjR x6, VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VConjR x6 -> false
    | VConjR x6, VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VConjR x6 -> false
    | VConjR x6, VImpl (x71, x72) -> false
    | VImpl (x71, x72), VConjR x6 -> false
    | VConjL x5, VPrev_zero -> false
    | VPrev_zero, VConjL x5 -> false
    | VConjL x5, VPrev_le x25 -> false
    | VPrev_le x25, VConjL x5 -> false
    | VConjL x5, VPrev_ge x24 -> false
    | VPrev_ge x24, VConjL x5 -> false
    | VConjL x5, VPrev x23 -> false
    | VPrev x23, VConjL x5 -> false
    | VConjL x5, VNext_le x22a -> false
    | VNext_le x22a, VConjL x5 -> false
    | VConjL x5, VNext_ge x21a -> false
    | VNext_ge x21a, VConjL x5 -> false
    | VConjL x5, VNext x20 -> false
    | VNext x20, VConjL x5 -> false
    | VConjL x5, VSince_le x19 -> false
    | VSince_le x19, VConjL x5 -> false
    | VConjL x5, VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VConjL x5 -> false
    | VConjL x5, VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VConjL x5 -> false
    | VConjL x5, VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VConjL x5 -> false
    | VConjL x5, VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VConjL x5 -> false
    | VConjL x5, VAlways (x141, x142) -> false
    | VAlways (x141, x142), VConjL x5 -> false
    | VConjL x5, VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VConjL x5 -> false
    | VConjL x5, VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VConjL x5 -> false
    | VConjL x5, VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VConjL x5 -> false
    | VConjL x5, VOnce_le x10 -> false
    | VOnce_le x10, VConjL x5 -> false
    | VConjL x5, VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VConjL x5 -> false
    | VConjL x5, VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VConjL x5 -> false
    | VConjL x5, VImpl (x71, x72) -> false
    | VImpl (x71, x72), VConjL x5 -> false
    | VConjL x5, VConjR x6 -> false
    | VConjR x6, VConjL x5 -> false
    | VDisj (x41, x42), VPrev_zero -> false
    | VPrev_zero, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VPrev_le x25 -> false
    | VPrev_le x25, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VPrev_ge x24 -> false
    | VPrev_ge x24, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VPrev x23 -> false
    | VPrev x23, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VNext_le x22a -> false
    | VNext_le x22a, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VNext_ge x21a -> false
    | VNext_ge x21a, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VNext x20 -> false
    | VNext x20, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VSince_le x19 -> false
    | VSince_le x19, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VDisj (x41, x42) -> false
    | VDisj (x41, x42), VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VDisj (x41, x42) -> false
    | VDisj (x41, x42), VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VDisj (x41, x42) -> false
    | VDisj (x41, x42), VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VDisj (x41, x42) -> false
    | VDisj (x41, x42), VAlways (x141, x142) -> false
    | VAlways (x141, x142), VDisj (x41, x42) -> false
    | VDisj (x41, x42), VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VDisj (x41, x42) -> false
    | VDisj (x41, x42), VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VDisj (x41, x42) -> false
    | VDisj (x41, x42), VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VDisj (x41, x42) -> false
    | VDisj (x41, x42), VOnce_le x10 -> false
    | VOnce_le x10, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VDisj (x41, x42) -> false
    | VDisj (x41, x42), VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VDisj (x41, x42) -> false
    | VDisj (x41, x42), VImpl (x71, x72) -> false
    | VImpl (x71, x72), VDisj (x41, x42) -> false
    | VDisj (x41, x42), VConjR x6 -> false
    | VConjR x6, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VConjL x5 -> false
    | VConjL x5, VDisj (x41, x42) -> false
    | VNeg x3, VPrev_zero -> false
    | VPrev_zero, VNeg x3 -> false
    | VNeg x3, VPrev_le x25 -> false
    | VPrev_le x25, VNeg x3 -> false
    | VNeg x3, VPrev_ge x24 -> false
    | VPrev_ge x24, VNeg x3 -> false
    | VNeg x3, VPrev x23 -> false
    | VPrev x23, VNeg x3 -> false
    | VNeg x3, VNext_le x22a -> false
    | VNext_le x22a, VNeg x3 -> false
    | VNeg x3, VNext_ge x21a -> false
    | VNext_ge x21a, VNeg x3 -> false
    | VNeg x3, VNext x20 -> false
    | VNext x20, VNeg x3 -> false
    | VNeg x3, VSince_le x19 -> false
    | VSince_le x19, VNeg x3 -> false
    | VNeg x3, VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VNeg x3 -> false
    | VNeg x3, VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VNeg x3 -> false
    | VNeg x3, VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VNeg x3 -> false
    | VNeg x3, VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VNeg x3 -> false
    | VNeg x3, VAlways (x141, x142) -> false
    | VAlways (x141, x142), VNeg x3 -> false
    | VNeg x3, VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VNeg x3 -> false
    | VNeg x3, VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VNeg x3 -> false
    | VNeg x3, VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VNeg x3 -> false
    | VNeg x3, VOnce_le x10 -> false
    | VOnce_le x10, VNeg x3 -> false
    | VNeg x3, VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VNeg x3 -> false
    | VNeg x3, VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VNeg x3 -> false
    | VNeg x3, VImpl (x71, x72) -> false
    | VImpl (x71, x72), VNeg x3 -> false
    | VNeg x3, VConjR x6 -> false
    | VConjR x6, VNeg x3 -> false
    | VNeg x3, VConjL x5 -> false
    | VConjL x5, VNeg x3 -> false
    | VNeg x3, VDisj (x41, x42) -> false
    | VDisj (x41, x42), VNeg x3 -> false
    | VAtm (x21, x22), VPrev_zero -> false
    | VPrev_zero, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VPrev_le x25 -> false
    | VPrev_le x25, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VPrev_ge x24 -> false
    | VPrev_ge x24, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VPrev x23 -> false
    | VPrev x23, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VNext_le x22a -> false
    | VNext_le x22a, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VNext_ge x21a -> false
    | VNext_ge x21a, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VNext x20 -> false
    | VNext x20, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VSince_le x19 -> false
    | VSince_le x19, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VAtm (x21, x22) -> false
    | VAtm (x21, x22), VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VAtm (x21, x22) -> false
    | VAtm (x21, x22), VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VAtm (x21, x22) -> false
    | VAtm (x21, x22), VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VAtm (x21, x22) -> false
    | VAtm (x21, x22), VAlways (x141, x142) -> false
    | VAlways (x141, x142), VAtm (x21, x22) -> false
    | VAtm (x21, x22), VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VAtm (x21, x22) -> false
    | VAtm (x21, x22), VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VAtm (x21, x22) -> false
    | VAtm (x21, x22), VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VAtm (x21, x22) -> false
    | VAtm (x21, x22), VOnce_le x10 -> false
    | VOnce_le x10, VAtm (x21, x22) -> false
    | VAtm (x21, x22), VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VAtm (x21, x22) -> false
    | VAtm (x21, x22), VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VAtm (x21, x22) -> false
    | VAtm (x21, x22), VImpl (x71, x72) -> false
    | VImpl (x71, x72), VAtm (x21, x22) -> false
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
    | VFF x1, VPrev_le x25 -> false
    | VPrev_le x25, VFF x1 -> false
    | VFF x1, VPrev_ge x24 -> false
    | VPrev_ge x24, VFF x1 -> false
    | VFF x1, VPrev x23 -> false
    | VPrev x23, VFF x1 -> false
    | VFF x1, VNext_le x22a -> false
    | VNext_le x22a, VFF x1 -> false
    | VFF x1, VNext_ge x21a -> false
    | VNext_ge x21a, VFF x1 -> false
    | VFF x1, VNext x20 -> false
    | VNext x20, VFF x1 -> false
    | VFF x1, VSince_le x19 -> false
    | VSince_le x19, VFF x1 -> false
    | VFF x1, VUntil_never (x181, x182, x183) -> false
    | VUntil_never (x181, x182, x183), VFF x1 -> false
    | VFF x1, VSince_never (x171, x172, x173) -> false
    | VSince_never (x171, x172, x173), VFF x1 -> false
    | VFF x1, VUntil (x161, x162, x163) -> false
    | VUntil (x161, x162, x163), VFF x1 -> false
    | VFF x1, VSince (x151, x152, x153) -> false
    | VSince (x151, x152, x153), VFF x1 -> false
    | VFF x1, VAlways (x141, x142) -> false
    | VAlways (x141, x142), VFF x1 -> false
    | VFF x1, VHistorically (x131, x132) -> false
    | VHistorically (x131, x132), VFF x1 -> false
    | VFF x1, VEventually (x121, x122, x123) -> false
    | VEventually (x121, x122, x123), VFF x1 -> false
    | VFF x1, VOnce (x111, x112, x113) -> false
    | VOnce (x111, x112, x113), VFF x1 -> false
    | VFF x1, VOnce_le x10 -> false
    | VOnce_le x10, VFF x1 -> false
    | VFF x1, VIff_vs (x91, x92) -> false
    | VIff_vs (x91, x92), VFF x1 -> false
    | VFF x1, VIff_sv (x81, x82) -> false
    | VIff_sv (x81, x82), VFF x1 -> false
    | VFF x1, VImpl (x71, x72) -> false
    | VImpl (x71, x72), VFF x1 -> false
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
    | VPrev_le x25, VPrev_le y25 -> equal_nata x25 y25
    | VPrev_ge x24, VPrev_ge y24 -> equal_nata x24 y24
    | VPrev x23, VPrev y23 -> equal_vproofa _A x23 y23
    | VNext_le x22a, VNext_le y22a -> equal_nata x22a y22a
    | VNext_ge x21a, VNext_ge y21a -> equal_nata x21a y21a
    | VNext x20, VNext y20 -> equal_vproofa _A x20 y20
    | VSince_le x19, VSince_le y19 -> equal_nata x19 y19
    | VUntil_never (x181, x182, x183), VUntil_never (y181, y182, y183) ->
        equal_nata x181 y181 &&
          (equal_nata x182 y182 && equal_list (equal_vproof _A) x183 y183)
    | VSince_never (x171, x172, x173), VSince_never (y171, y172, y173) ->
        equal_nata x171 y171 &&
          (equal_nata x172 y172 && equal_list (equal_vproof _A) x173 y173)
    | VUntil (x161, x162, x163), VUntil (y161, y162, y163) ->
        equal_nata x161 y161 &&
          (equal_list (equal_vproof _A) x162 y162 && equal_vproofa _A x163 y163)
    | VSince (x151, x152, x153), VSince (y151, y152, y153) ->
        equal_nata x151 y151 &&
          (equal_vproofa _A x152 y152 && equal_list (equal_vproof _A) x153 y153)
    | VAlways (x141, x142), VAlways (y141, y142) ->
        equal_nata x141 y141 && equal_vproofa _A x142 y142
    | VHistorically (x131, x132), VHistorically (y131, y132) ->
        equal_nata x131 y131 && equal_vproofa _A x132 y132
    | VEventually (x121, x122, x123), VEventually (y121, y122, y123) ->
        equal_nata x121 y121 &&
          (equal_nata x122 y122 && equal_list (equal_vproof _A) x123 y123)
    | VOnce (x111, x112, x113), VOnce (y111, y112, y113) ->
        equal_nata x111 y111 &&
          (equal_nata x112 y112 && equal_list (equal_vproof _A) x113 y113)
    | VOnce_le x10, VOnce_le y10 -> equal_nata x10 y10
    | VIff_vs (x91, x92), VIff_vs (y91, y92) ->
        equal_vproofa _A x91 y91 && equal_sproofa _A x92 y92
    | VIff_sv (x81, x82), VIff_sv (y81, y82) ->
        equal_sproofa _A x81 y81 && equal_vproofa _A x82 y82
    | VImpl (x71, x72), VImpl (y71, y72) ->
        equal_sproofa _A x71 y71 && equal_vproofa _A x72 y72
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
  compa x1 x2 = match compa, x1, x2 with compa, [], [] -> Eq
    | compa, [], y :: ys -> Lt
    | compa, x :: xs, [] -> Gt
    | compa, x :: xs, y :: ys ->
        (match compa x y with Eq -> comparator_list compa xs ys | Lt -> Lt
          | Gt -> Gt);;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec comparator_sproof _A
  compa x1 rhs = match compa, x1, rhs with
    compa, STT i, rhs ->
      (match rhs with STT a -> comparator_of (equal_nat, linorder_nat) i a
        | SAtm (_, _) -> Lt | SNeg _ -> Lt | SDisjL _ -> Lt | SDisjR _ -> Lt
        | SConj (_, _) -> Lt | SImplR _ -> Lt | SImplL _ -> Lt
        | SIff_ss (_, _) -> Lt | SIff_vv (_, _) -> Lt | SOnce (_, _) -> Lt
        | SEventually (_, _) -> Lt | SHistorically (_, _, _) -> Lt
        | SHistorically_le _ -> Lt | SAlways (_, _, _) -> Lt
        | SSince (_, _) -> Lt | SUntil (_, _) -> Lt | SNext _ -> Lt
        | SPrev _ -> Lt)
    | compa, SAtm (p, i), rhs ->
        (match rhs with STT _ -> Gt
          | SAtm (q, j) ->
            (match compa p q
              with Eq -> comparator_of (equal_nat, linorder_nat) i j | Lt -> Lt
              | Gt -> Gt)
          | SNeg _ -> Lt | SDisjL _ -> Lt | SDisjR _ -> Lt | SConj (_, _) -> Lt
          | SImplR _ -> Lt | SImplL _ -> Lt | SIff_ss (_, _) -> Lt
          | SIff_vv (_, _) -> Lt | SOnce (_, _) -> Lt | SEventually (_, _) -> Lt
          | SHistorically (_, _, _) -> Lt | SHistorically_le _ -> Lt
          | SAlways (_, _, _) -> Lt | SSince (_, _) -> Lt | SUntil (_, _) -> Lt
          | SNext _ -> Lt | SPrev _ -> Lt)
    | compa, SNeg vp, rhs ->
        (match rhs with STT _ -> Gt | SAtm (_, _) -> Gt
          | SNeg a -> comparator_vproof _A compa vp a | SDisjL _ -> Lt
          | SDisjR _ -> Lt | SConj (_, _) -> Lt | SImplR _ -> Lt
          | SImplL _ -> Lt | SIff_ss (_, _) -> Lt | SIff_vv (_, _) -> Lt
          | SOnce (_, _) -> Lt | SEventually (_, _) -> Lt
          | SHistorically (_, _, _) -> Lt | SHistorically_le _ -> Lt
          | SAlways (_, _, _) -> Lt | SSince (_, _) -> Lt | SUntil (_, _) -> Lt
          | SNext _ -> Lt | SPrev _ -> Lt)
    | compa, SDisjL sp, rhs ->
        (match rhs with STT _ -> Gt | SAtm (_, _) -> Gt | SNeg _ -> Gt
          | SDisjL a -> comparator_sproof _A compa sp a | SDisjR _ -> Lt
          | SConj (_, _) -> Lt | SImplR _ -> Lt | SImplL _ -> Lt
          | SIff_ss (_, _) -> Lt | SIff_vv (_, _) -> Lt | SOnce (_, _) -> Lt
          | SEventually (_, _) -> Lt | SHistorically (_, _, _) -> Lt
          | SHistorically_le _ -> Lt | SAlways (_, _, _) -> Lt
          | SSince (_, _) -> Lt | SUntil (_, _) -> Lt | SNext _ -> Lt
          | SPrev _ -> Lt)
    | compa, SDisjR sp, rhs ->
        (match rhs with STT _ -> Gt | SAtm (_, _) -> Gt | SNeg _ -> Gt
          | SDisjL _ -> Gt | SDisjR a -> comparator_sproof _A compa sp a
          | SConj (_, _) -> Lt | SImplR _ -> Lt | SImplL _ -> Lt
          | SIff_ss (_, _) -> Lt | SIff_vv (_, _) -> Lt | SOnce (_, _) -> Lt
          | SEventually (_, _) -> Lt | SHistorically (_, _, _) -> Lt
          | SHistorically_le _ -> Lt | SAlways (_, _, _) -> Lt
          | SSince (_, _) -> Lt | SUntil (_, _) -> Lt | SNext _ -> Lt
          | SPrev _ -> Lt)
    | compa, SConj (sp1, sp2), rhs ->
        (match rhs with STT _ -> Gt | SAtm (_, _) -> Gt | SNeg _ -> Gt
          | SDisjL _ -> Gt | SDisjR _ -> Gt
          | SConj (sp1a, sp2a) ->
            (match comparator_sproof _A compa sp1 sp1a
              with Eq -> comparator_sproof _A compa sp2 sp2a | Lt -> Lt
              | Gt -> Gt)
          | SImplR _ -> Lt | SImplL _ -> Lt | SIff_ss (_, _) -> Lt
          | SIff_vv (_, _) -> Lt | SOnce (_, _) -> Lt | SEventually (_, _) -> Lt
          | SHistorically (_, _, _) -> Lt | SHistorically_le _ -> Lt
          | SAlways (_, _, _) -> Lt | SSince (_, _) -> Lt | SUntil (_, _) -> Lt
          | SNext _ -> Lt | SPrev _ -> Lt)
    | compa, SImplR sp, rhs ->
        (match rhs with STT _ -> Gt | SAtm (_, _) -> Gt | SNeg _ -> Gt
          | SDisjL _ -> Gt | SDisjR _ -> Gt | SConj (_, _) -> Gt
          | SImplR a -> comparator_sproof _A compa sp a | SImplL _ -> Lt
          | SIff_ss (_, _) -> Lt | SIff_vv (_, _) -> Lt | SOnce (_, _) -> Lt
          | SEventually (_, _) -> Lt | SHistorically (_, _, _) -> Lt
          | SHistorically_le _ -> Lt | SAlways (_, _, _) -> Lt
          | SSince (_, _) -> Lt | SUntil (_, _) -> Lt | SNext _ -> Lt
          | SPrev _ -> Lt)
    | compa, SImplL vp, rhs ->
        (match rhs with STT _ -> Gt | SAtm (_, _) -> Gt | SNeg _ -> Gt
          | SDisjL _ -> Gt | SDisjR _ -> Gt | SConj (_, _) -> Gt
          | SImplR _ -> Gt | SImplL a -> comparator_vproof _A compa vp a
          | SIff_ss (_, _) -> Lt | SIff_vv (_, _) -> Lt | SOnce (_, _) -> Lt
          | SEventually (_, _) -> Lt | SHistorically (_, _, _) -> Lt
          | SHistorically_le _ -> Lt | SAlways (_, _, _) -> Lt
          | SSince (_, _) -> Lt | SUntil (_, _) -> Lt | SNext _ -> Lt
          | SPrev _ -> Lt)
    | compa, SIff_ss (sp1, sp2), rhs ->
        (match rhs with STT _ -> Gt | SAtm (_, _) -> Gt | SNeg _ -> Gt
          | SDisjL _ -> Gt | SDisjR _ -> Gt | SConj (_, _) -> Gt
          | SImplR _ -> Gt | SImplL _ -> Gt
          | SIff_ss (sp1a, sp2a) ->
            (match comparator_sproof _A compa sp1 sp1a
              with Eq -> comparator_sproof _A compa sp2 sp2a | Lt -> Lt
              | Gt -> Gt)
          | SIff_vv (_, _) -> Lt | SOnce (_, _) -> Lt | SEventually (_, _) -> Lt
          | SHistorically (_, _, _) -> Lt | SHistorically_le _ -> Lt
          | SAlways (_, _, _) -> Lt | SSince (_, _) -> Lt | SUntil (_, _) -> Lt
          | SNext _ -> Lt | SPrev _ -> Lt)
    | compa, SIff_vv (vp1, vp2), rhs ->
        (match rhs with STT _ -> Gt | SAtm (_, _) -> Gt | SNeg _ -> Gt
          | SDisjL _ -> Gt | SDisjR _ -> Gt | SConj (_, _) -> Gt
          | SImplR _ -> Gt | SImplL _ -> Gt | SIff_ss (_, _) -> Gt
          | SIff_vv (vp1a, vp2a) ->
            (match comparator_vproof _A compa vp1 vp1a
              with Eq -> comparator_vproof _A compa vp2 vp2a | Lt -> Lt
              | Gt -> Gt)
          | SOnce (_, _) -> Lt | SEventually (_, _) -> Lt
          | SHistorically (_, _, _) -> Lt | SHistorically_le _ -> Lt
          | SAlways (_, _, _) -> Lt | SSince (_, _) -> Lt | SUntil (_, _) -> Lt
          | SNext _ -> Lt | SPrev _ -> Lt)
    | compa, SOnce (i, sp), rhs ->
        (match rhs with STT _ -> Gt | SAtm (_, _) -> Gt | SNeg _ -> Gt
          | SDisjL _ -> Gt | SDisjR _ -> Gt | SConj (_, _) -> Gt
          | SImplR _ -> Gt | SImplL _ -> Gt | SIff_ss (_, _) -> Gt
          | SIff_vv (_, _) -> Gt
          | SOnce (ia, spa) ->
            (match comparator_of (equal_nat, linorder_nat) i ia
              with Eq -> comparator_sproof _A compa sp spa | Lt -> Lt
              | Gt -> Gt)
          | SEventually (_, _) -> Lt | SHistorically (_, _, _) -> Lt
          | SHistorically_le _ -> Lt | SAlways (_, _, _) -> Lt
          | SSince (_, _) -> Lt | SUntil (_, _) -> Lt | SNext _ -> Lt
          | SPrev _ -> Lt)
    | compa, SEventually (i, sp), rhs ->
        (match rhs with STT _ -> Gt | SAtm (_, _) -> Gt | SNeg _ -> Gt
          | SDisjL _ -> Gt | SDisjR _ -> Gt | SConj (_, _) -> Gt
          | SImplR _ -> Gt | SImplL _ -> Gt | SIff_ss (_, _) -> Gt
          | SIff_vv (_, _) -> Gt | SOnce (_, _) -> Gt
          | SEventually (ia, spa) ->
            (match comparator_of (equal_nat, linorder_nat) i ia
              with Eq -> comparator_sproof _A compa sp spa | Lt -> Lt
              | Gt -> Gt)
          | SHistorically (_, _, _) -> Lt | SHistorically_le _ -> Lt
          | SAlways (_, _, _) -> Lt | SSince (_, _) -> Lt | SUntil (_, _) -> Lt
          | SNext _ -> Lt | SPrev _ -> Lt)
    | compa, SHistorically (i, t, sps), rhs ->
        (match rhs with STT _ -> Gt | SAtm (_, _) -> Gt | SNeg _ -> Gt
          | SDisjL _ -> Gt | SDisjR _ -> Gt | SConj (_, _) -> Gt
          | SImplR _ -> Gt | SImplL _ -> Gt | SIff_ss (_, _) -> Gt
          | SIff_vv (_, _) -> Gt | SOnce (_, _) -> Gt | SEventually (_, _) -> Gt
          | SHistorically (ia, ta, spsa) ->
            (match comparator_of (equal_nat, linorder_nat) i ia
              with Eq ->
                (match comparator_of (equal_nat, linorder_nat) t ta
                  with Eq ->
                    comparator_list (fun f -> f)
                      (map (comparator_sproof _A compa) sps) spsa
                  | Lt -> Lt | Gt -> Gt)
              | Lt -> Lt | Gt -> Gt)
          | SHistorically_le _ -> Lt | SAlways (_, _, _) -> Lt
          | SSince (_, _) -> Lt | SUntil (_, _) -> Lt | SNext _ -> Lt
          | SPrev _ -> Lt)
    | compa, SHistorically_le i, rhs ->
        (match rhs with STT _ -> Gt | SAtm (_, _) -> Gt | SNeg _ -> Gt
          | SDisjL _ -> Gt | SDisjR _ -> Gt | SConj (_, _) -> Gt
          | SImplR _ -> Gt | SImplL _ -> Gt | SIff_ss (_, _) -> Gt
          | SIff_vv (_, _) -> Gt | SOnce (_, _) -> Gt | SEventually (_, _) -> Gt
          | SHistorically (_, _, _) -> Gt
          | SHistorically_le a -> comparator_of (equal_nat, linorder_nat) i a
          | SAlways (_, _, _) -> Lt | SSince (_, _) -> Lt | SUntil (_, _) -> Lt
          | SNext _ -> Lt | SPrev _ -> Lt)
    | compa, SAlways (i, t, sps), rhs ->
        (match rhs with STT _ -> Gt | SAtm (_, _) -> Gt | SNeg _ -> Gt
          | SDisjL _ -> Gt | SDisjR _ -> Gt | SConj (_, _) -> Gt
          | SImplR _ -> Gt | SImplL _ -> Gt | SIff_ss (_, _) -> Gt
          | SIff_vv (_, _) -> Gt | SOnce (_, _) -> Gt | SEventually (_, _) -> Gt
          | SHistorically (_, _, _) -> Gt | SHistorically_le _ -> Gt
          | SAlways (ia, ta, spsa) ->
            (match comparator_of (equal_nat, linorder_nat) i ia
              with Eq ->
                (match comparator_of (equal_nat, linorder_nat) t ta
                  with Eq ->
                    comparator_list (fun f -> f)
                      (map (comparator_sproof _A compa) sps) spsa
                  | Lt -> Lt | Gt -> Gt)
              | Lt -> Lt | Gt -> Gt)
          | SSince (_, _) -> Lt | SUntil (_, _) -> Lt | SNext _ -> Lt
          | SPrev _ -> Lt)
    | compa, SSince (sp2, sp1s), rhs ->
        (match rhs with STT _ -> Gt | SAtm (_, _) -> Gt | SNeg _ -> Gt
          | SDisjL _ -> Gt | SDisjR _ -> Gt | SConj (_, _) -> Gt
          | SImplR _ -> Gt | SImplL _ -> Gt | SIff_ss (_, _) -> Gt
          | SIff_vv (_, _) -> Gt | SOnce (_, _) -> Gt | SEventually (_, _) -> Gt
          | SHistorically (_, _, _) -> Gt | SHistorically_le _ -> Gt
          | SAlways (_, _, _) -> Gt
          | SSince (sp2a, sp1sa) ->
            (match comparator_sproof _A compa sp2 sp2a
              with Eq ->
                comparator_list (fun f -> f)
                  (map (comparator_sproof _A compa) sp1s) sp1sa
              | Lt -> Lt | Gt -> Gt)
          | SUntil (_, _) -> Lt | SNext _ -> Lt | SPrev _ -> Lt)
    | compa, SUntil (sp1s, sp2), rhs ->
        (match rhs with STT _ -> Gt | SAtm (_, _) -> Gt | SNeg _ -> Gt
          | SDisjL _ -> Gt | SDisjR _ -> Gt | SConj (_, _) -> Gt
          | SImplR _ -> Gt | SImplL _ -> Gt | SIff_ss (_, _) -> Gt
          | SIff_vv (_, _) -> Gt | SOnce (_, _) -> Gt | SEventually (_, _) -> Gt
          | SHistorically (_, _, _) -> Gt | SHistorically_le _ -> Gt
          | SAlways (_, _, _) -> Gt | SSince (_, _) -> Gt
          | SUntil (sp1sa, sp2a) ->
            (match comparator_sproof _A compa sp2 sp2a
              with Eq ->
                comparator_list (fun f -> f)
                  (map (comparator_sproof _A compa) sp1s) sp1sa
              | Lt -> Lt | Gt -> Gt)
          | SNext _ -> Lt | SPrev _ -> Lt)
    | compa, SPrev sp, rhs ->
        (match rhs with STT _ -> Gt | SAtm (_, _) -> Gt | SNeg _ -> Gt
          | SDisjL _ -> Gt | SDisjR _ -> Gt | SConj (_, _) -> Gt
          | SImplR _ -> Gt | SImplL _ -> Gt | SIff_ss (_, _) -> Gt
          | SIff_vv (_, _) -> Gt | SOnce (_, _) -> Gt | SEventually (_, _) -> Gt
          | SHistorically (_, _, _) -> Gt | SHistorically_le _ -> Gt
          | SAlways (_, _, _) -> Gt | SSince (_, _) -> Gt | SUntil (_, _) -> Gt
          | SNext _ -> Lt | SPrev a -> comparator_sproof _A compa sp a)
    | compa, SNext sp, rhs ->
        (match rhs with STT _ -> Gt | SAtm (_, _) -> Gt | SNeg _ -> Gt
          | SDisjL _ -> Gt | SDisjR _ -> Gt | SConj (_, _) -> Gt
          | SImplR _ -> Gt | SImplL _ -> Gt | SIff_ss (_, _) -> Gt
          | SIff_vv (_, _) -> Gt | SOnce (_, _) -> Gt | SEventually (_, _) -> Gt
          | SHistorically (_, _, _) -> Gt | SHistorically_le _ -> Gt
          | SAlways (_, _, _) -> Gt | SSince (_, _) -> Gt | SUntil (_, _) -> Gt
          | SNext a -> comparator_sproof _A compa sp a | SPrev _ -> Gt)
and comparator_vproof _A
  compa x1 rhs = match compa, x1, rhs with
    compa, VFF i, rhs ->
      (match rhs with VFF a -> comparator_of (equal_nat, linorder_nat) i a
        | VAtm (_, _) -> Lt | VNeg _ -> Lt | VDisj (_, _) -> Lt | VConjL _ -> Lt
        | VConjR _ -> Lt | VImpl (_, _) -> Lt | VIff_sv (_, _) -> Lt
        | VIff_vs (_, _) -> Lt | VOnce_le _ -> Lt | VOnce (_, _, _) -> Lt
        | VEventually (_, _, _) -> Lt | VHistorically (_, _) -> Lt
        | VAlways (_, _) -> Lt | VSince (_, _, _) -> Lt | VUntil (_, _, _) -> Lt
        | VSince_never (_, _, _) -> Lt | VUntil_never (_, _, _) -> Lt
        | VSince_le _ -> Lt | VNext _ -> Lt | VNext_ge _ -> Lt
        | VNext_le _ -> Lt | VPrev _ -> Lt | VPrev_ge _ -> Lt | VPrev_le _ -> Lt
        | VPrev_zero -> Lt)
    | compa, VAtm (p, i), rhs ->
        (match rhs with VFF _ -> Gt
          | VAtm (q, j) ->
            (match compa p q
              with Eq -> comparator_of (equal_nat, linorder_nat) i j | Lt -> Lt
              | Gt -> Gt)
          | VNeg _ -> Lt | VDisj (_, _) -> Lt | VConjL _ -> Lt | VConjR _ -> Lt
          | VImpl (_, _) -> Lt | VIff_sv (_, _) -> Lt | VIff_vs (_, _) -> Lt
          | VOnce_le _ -> Lt | VOnce (_, _, _) -> Lt
          | VEventually (_, _, _) -> Lt | VHistorically (_, _) -> Lt
          | VAlways (_, _) -> Lt | VSince (_, _, _) -> Lt
          | VUntil (_, _, _) -> Lt | VSince_never (_, _, _) -> Lt
          | VUntil_never (_, _, _) -> Lt | VSince_le _ -> Lt | VNext _ -> Lt
          | VNext_ge _ -> Lt | VNext_le _ -> Lt | VPrev _ -> Lt
          | VPrev_ge _ -> Lt | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VNeg sp, rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt
          | VNeg a -> comparator_sproof _A compa sp a | VDisj (_, _) -> Lt
          | VConjL _ -> Lt | VConjR _ -> Lt | VImpl (_, _) -> Lt
          | VIff_sv (_, _) -> Lt | VIff_vs (_, _) -> Lt | VOnce_le _ -> Lt
          | VOnce (_, _, _) -> Lt | VEventually (_, _, _) -> Lt
          | VHistorically (_, _) -> Lt | VAlways (_, _) -> Lt
          | VSince (_, _, _) -> Lt | VUntil (_, _, _) -> Lt
          | VSince_never (_, _, _) -> Lt | VUntil_never (_, _, _) -> Lt
          | VSince_le _ -> Lt | VNext _ -> Lt | VNext_ge _ -> Lt
          | VNext_le _ -> Lt | VPrev _ -> Lt | VPrev_ge _ -> Lt
          | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VDisj (vp1, vp2), rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (vp1a, vp2a) ->
            (match comparator_vproof _A compa vp1 vp1a
              with Eq -> comparator_vproof _A compa vp2 vp2a | Lt -> Lt
              | Gt -> Gt)
          | VConjL _ -> Lt | VConjR _ -> Lt | VImpl (_, _) -> Lt
          | VIff_sv (_, _) -> Lt | VIff_vs (_, _) -> Lt | VOnce_le _ -> Lt
          | VOnce (_, _, _) -> Lt | VEventually (_, _, _) -> Lt
          | VHistorically (_, _) -> Lt | VAlways (_, _) -> Lt
          | VSince (_, _, _) -> Lt | VUntil (_, _, _) -> Lt
          | VSince_never (_, _, _) -> Lt | VUntil_never (_, _, _) -> Lt
          | VSince_le _ -> Lt | VNext _ -> Lt | VNext_ge _ -> Lt
          | VNext_le _ -> Lt | VPrev _ -> Lt | VPrev_ge _ -> Lt
          | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VConjL vp, rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL a -> comparator_vproof _A compa vp a
          | VConjR _ -> Lt | VImpl (_, _) -> Lt | VIff_sv (_, _) -> Lt
          | VIff_vs (_, _) -> Lt | VOnce_le _ -> Lt | VOnce (_, _, _) -> Lt
          | VEventually (_, _, _) -> Lt | VHistorically (_, _) -> Lt
          | VAlways (_, _) -> Lt | VSince (_, _, _) -> Lt
          | VUntil (_, _, _) -> Lt | VSince_never (_, _, _) -> Lt
          | VUntil_never (_, _, _) -> Lt | VSince_le _ -> Lt | VNext _ -> Lt
          | VNext_ge _ -> Lt | VNext_le _ -> Lt | VPrev _ -> Lt
          | VPrev_ge _ -> Lt | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VConjR vp, rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt
          | VConjR a -> comparator_vproof _A compa vp a | VImpl (_, _) -> Lt
          | VIff_sv (_, _) -> Lt | VIff_vs (_, _) -> Lt | VOnce_le _ -> Lt
          | VOnce (_, _, _) -> Lt | VEventually (_, _, _) -> Lt
          | VHistorically (_, _) -> Lt | VAlways (_, _) -> Lt
          | VSince (_, _, _) -> Lt | VUntil (_, _, _) -> Lt
          | VSince_never (_, _, _) -> Lt | VUntil_never (_, _, _) -> Lt
          | VSince_le _ -> Lt | VNext _ -> Lt | VNext_ge _ -> Lt
          | VNext_le _ -> Lt | VPrev _ -> Lt | VPrev_ge _ -> Lt
          | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VImpl (sp1, vp2), rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (sp1a, vp2a) ->
            (match comparator_sproof _A compa sp1 sp1a
              with Eq -> comparator_vproof _A compa vp2 vp2a | Lt -> Lt
              | Gt -> Gt)
          | VIff_sv (_, _) -> Lt | VIff_vs (_, _) -> Lt | VOnce_le _ -> Lt
          | VOnce (_, _, _) -> Lt | VEventually (_, _, _) -> Lt
          | VHistorically (_, _) -> Lt | VAlways (_, _) -> Lt
          | VSince (_, _, _) -> Lt | VUntil (_, _, _) -> Lt
          | VSince_never (_, _, _) -> Lt | VUntil_never (_, _, _) -> Lt
          | VSince_le _ -> Lt | VNext _ -> Lt | VNext_ge _ -> Lt
          | VNext_le _ -> Lt | VPrev _ -> Lt | VPrev_ge _ -> Lt
          | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VIff_sv (sp1, vp2), rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt
          | VIff_sv (sp1a, vp2a) ->
            (match comparator_sproof _A compa sp1 sp1a
              with Eq -> comparator_vproof _A compa vp2 vp2a | Lt -> Lt
              | Gt -> Gt)
          | VIff_vs (_, _) -> Lt | VOnce_le _ -> Lt | VOnce (_, _, _) -> Lt
          | VEventually (_, _, _) -> Lt | VHistorically (_, _) -> Lt
          | VAlways (_, _) -> Lt | VSince (_, _, _) -> Lt
          | VUntil (_, _, _) -> Lt | VSince_never (_, _, _) -> Lt
          | VUntil_never (_, _, _) -> Lt | VSince_le _ -> Lt | VNext _ -> Lt
          | VNext_ge _ -> Lt | VNext_le _ -> Lt | VPrev _ -> Lt
          | VPrev_ge _ -> Lt | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VIff_vs (vp1, sp2), rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt
          | VIff_vs (vp1a, sp2a) ->
            (match comparator_vproof _A compa vp1 vp1a
              with Eq -> comparator_sproof _A compa sp2 sp2a | Lt -> Lt
              | Gt -> Gt)
          | VOnce_le _ -> Lt | VOnce (_, _, _) -> Lt
          | VEventually (_, _, _) -> Lt | VHistorically (_, _) -> Lt
          | VAlways (_, _) -> Lt | VSince (_, _, _) -> Lt
          | VUntil (_, _, _) -> Lt | VSince_never (_, _, _) -> Lt
          | VUntil_never (_, _, _) -> Lt | VSince_le _ -> Lt | VNext _ -> Lt
          | VNext_ge _ -> Lt | VNext_le _ -> Lt | VPrev _ -> Lt
          | VPrev_ge _ -> Lt | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VOnce_le i, rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt | VIff_vs (_, _) -> Gt
          | VOnce_le a -> comparator_of (equal_nat, linorder_nat) i a
          | VOnce (_, _, _) -> Lt | VEventually (_, _, _) -> Lt
          | VHistorically (_, _) -> Lt | VAlways (_, _) -> Lt
          | VSince (_, _, _) -> Lt | VUntil (_, _, _) -> Lt
          | VSince_never (_, _, _) -> Lt | VUntil_never (_, _, _) -> Lt
          | VSince_le _ -> Lt | VNext _ -> Lt | VNext_ge _ -> Lt
          | VNext_le _ -> Lt | VPrev _ -> Lt | VPrev_ge _ -> Lt
          | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VOnce (i, t, vps), rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt | VIff_vs (_, _) -> Gt
          | VOnce_le _ -> Gt
          | VOnce (ia, ta, vpsa) ->
            (match comparator_of (equal_nat, linorder_nat) i ia
              with Eq ->
                (match comparator_of (equal_nat, linorder_nat) t ta
                  with Eq ->
                    comparator_list (fun f -> f)
                      (map (comparator_vproof _A compa) vps) vpsa
                  | Lt -> Lt | Gt -> Gt)
              | Lt -> Lt | Gt -> Gt)
          | VEventually (_, _, _) -> Lt | VHistorically (_, _) -> Lt
          | VAlways (_, _) -> Lt | VSince (_, _, _) -> Lt
          | VUntil (_, _, _) -> Lt | VSince_never (_, _, _) -> Lt
          | VUntil_never (_, _, _) -> Lt | VSince_le _ -> Lt | VNext _ -> Lt
          | VNext_ge _ -> Lt | VNext_le _ -> Lt | VPrev _ -> Lt
          | VPrev_ge _ -> Lt | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VEventually (i, t, vps), rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt | VIff_vs (_, _) -> Gt
          | VOnce_le _ -> Gt | VOnce (_, _, _) -> Gt
          | VEventually (ia, ta, vpsa) ->
            (match comparator_of (equal_nat, linorder_nat) i ia
              with Eq ->
                (match comparator_of (equal_nat, linorder_nat) t ta
                  with Eq ->
                    comparator_list (fun f -> f)
                      (map (comparator_vproof _A compa) vps) vpsa
                  | Lt -> Lt | Gt -> Gt)
              | Lt -> Lt | Gt -> Gt)
          | VHistorically (_, _) -> Lt | VAlways (_, _) -> Lt
          | VSince (_, _, _) -> Lt | VUntil (_, _, _) -> Lt
          | VSince_never (_, _, _) -> Lt | VUntil_never (_, _, _) -> Lt
          | VSince_le _ -> Lt | VNext _ -> Lt | VNext_ge _ -> Lt
          | VNext_le _ -> Lt | VPrev _ -> Lt | VPrev_ge _ -> Lt
          | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VHistorically (i, vp), rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt | VIff_vs (_, _) -> Gt
          | VOnce_le _ -> Gt | VOnce (_, _, _) -> Gt
          | VEventually (_, _, _) -> Gt
          | VHistorically (ia, vpa) ->
            (match comparator_of (equal_nat, linorder_nat) i ia
              with Eq -> comparator_vproof _A compa vp vpa | Lt -> Lt
              | Gt -> Gt)
          | VAlways (_, _) -> Lt | VSince (_, _, _) -> Lt
          | VUntil (_, _, _) -> Lt | VSince_never (_, _, _) -> Lt
          | VUntil_never (_, _, _) -> Lt | VSince_le _ -> Lt | VNext _ -> Lt
          | VNext_ge _ -> Lt | VNext_le _ -> Lt | VPrev _ -> Lt
          | VPrev_ge _ -> Lt | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VAlways (i, vp), rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt | VIff_vs (_, _) -> Gt
          | VOnce_le _ -> Gt | VOnce (_, _, _) -> Gt
          | VEventually (_, _, _) -> Gt | VHistorically (_, _) -> Gt
          | VAlways (ia, vpa) ->
            (match comparator_of (equal_nat, linorder_nat) i ia
              with Eq -> comparator_vproof _A compa vp vpa | Lt -> Lt
              | Gt -> Gt)
          | VSince (_, _, _) -> Lt | VUntil (_, _, _) -> Lt
          | VSince_never (_, _, _) -> Lt | VUntil_never (_, _, _) -> Lt
          | VSince_le _ -> Lt | VNext _ -> Lt | VNext_ge _ -> Lt
          | VNext_le _ -> Lt | VPrev _ -> Lt | VPrev_ge _ -> Lt
          | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VSince (i, vp1, vp2s), rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt | VIff_vs (_, _) -> Gt
          | VOnce_le _ -> Gt | VOnce (_, _, _) -> Gt
          | VEventually (_, _, _) -> Gt | VHistorically (_, _) -> Gt
          | VAlways (_, _) -> Gt
          | VSince (ia, vp1a, vp2sa) ->
            (match comparator_of (equal_nat, linorder_nat) i ia
              with Eq ->
                (match comparator_vproof _A compa vp1 vp1a
                  with Eq ->
                    comparator_list (fun f -> f)
                      (map (comparator_vproof _A compa) vp2s) vp2sa
                  | Lt -> Lt | Gt -> Gt)
              | Lt -> Lt | Gt -> Gt)
          | VUntil (_, _, _) -> Lt | VSince_never (_, _, _) -> Lt
          | VUntil_never (_, _, _) -> Lt | VSince_le _ -> Lt | VNext _ -> Lt
          | VNext_ge _ -> Lt | VNext_le _ -> Lt | VPrev _ -> Lt
          | VPrev_ge _ -> Lt | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VUntil (i, vp2s, vp1), rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt | VIff_vs (_, _) -> Gt
          | VOnce_le _ -> Gt | VOnce (_, _, _) -> Gt
          | VEventually (_, _, _) -> Gt | VHistorically (_, _) -> Gt
          | VAlways (_, _) -> Gt | VSince (_, _, _) -> Gt
          | VUntil (ia, vp2sa, vp1a) ->
            (match comparator_of (equal_nat, linorder_nat) i ia
              with Eq ->
                (match comparator_vproof _A compa vp1 vp1a
                  with Eq ->
                    comparator_list (fun f -> f)
                      (map (comparator_vproof _A compa) vp2s) vp2sa
                  | Lt -> Lt | Gt -> Gt)
              | Lt -> Lt | Gt -> Gt)
          | VSince_never (_, _, _) -> Lt | VUntil_never (_, _, _) -> Lt
          | VSince_le _ -> Lt | VNext _ -> Lt | VNext_ge _ -> Lt
          | VNext_le _ -> Lt | VPrev _ -> Lt | VPrev_ge _ -> Lt
          | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VSince_never (i, t, vp2s), rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt | VIff_vs (_, _) -> Gt
          | VOnce_le _ -> Gt | VOnce (_, _, _) -> Gt
          | VEventually (_, _, _) -> Gt | VHistorically (_, _) -> Gt
          | VAlways (_, _) -> Gt | VSince (_, _, _) -> Gt
          | VUntil (_, _, _) -> Gt
          | VSince_never (ia, ta, vp2sa) ->
            (match comparator_of (equal_nat, linorder_nat) i ia
              with Eq ->
                (match comparator_of (equal_nat, linorder_nat) t ta
                  with Eq ->
                    comparator_list (fun f -> f)
                      (map (comparator_vproof _A compa) vp2s) vp2sa
                  | Lt -> Lt | Gt -> Gt)
              | Lt -> Lt | Gt -> Gt)
          | VUntil_never (_, _, _) -> Lt | VSince_le _ -> Lt | VNext _ -> Lt
          | VNext_ge _ -> Lt | VNext_le _ -> Lt | VPrev _ -> Lt
          | VPrev_ge _ -> Lt | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VUntil_never (i, t, vp2s), rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt | VIff_vs (_, _) -> Gt
          | VOnce_le _ -> Gt | VOnce (_, _, _) -> Gt
          | VEventually (_, _, _) -> Gt | VHistorically (_, _) -> Gt
          | VAlways (_, _) -> Gt | VSince (_, _, _) -> Gt
          | VUntil (_, _, _) -> Gt | VSince_never (_, _, _) -> Gt
          | VUntil_never (ia, ta, vp2sa) ->
            (match comparator_of (equal_nat, linorder_nat) i ia
              with Eq ->
                (match comparator_of (equal_nat, linorder_nat) t ta
                  with Eq ->
                    comparator_list (fun f -> f)
                      (map (comparator_vproof _A compa) vp2s) vp2sa
                  | Lt -> Lt | Gt -> Gt)
              | Lt -> Lt | Gt -> Gt)
          | VSince_le _ -> Lt | VNext _ -> Lt | VNext_ge _ -> Lt
          | VNext_le _ -> Lt | VPrev _ -> Lt | VPrev_ge _ -> Lt
          | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VSince_le i, rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt | VIff_vs (_, _) -> Gt
          | VOnce_le _ -> Gt | VOnce (_, _, _) -> Gt
          | VEventually (_, _, _) -> Gt | VHistorically (_, _) -> Gt
          | VAlways (_, _) -> Gt | VSince (_, _, _) -> Gt
          | VUntil (_, _, _) -> Gt | VSince_never (_, _, _) -> Gt
          | VUntil_never (_, _, _) -> Gt
          | VSince_le a -> comparator_of (equal_nat, linorder_nat) i a
          | VNext _ -> Lt | VNext_ge _ -> Lt | VNext_le _ -> Lt | VPrev _ -> Lt
          | VPrev_ge _ -> Lt | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VNext vp, rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt | VIff_vs (_, _) -> Gt
          | VOnce_le _ -> Gt | VOnce (_, _, _) -> Gt
          | VEventually (_, _, _) -> Gt | VHistorically (_, _) -> Gt
          | VAlways (_, _) -> Gt | VSince (_, _, _) -> Gt
          | VUntil (_, _, _) -> Gt | VSince_never (_, _, _) -> Gt
          | VUntil_never (_, _, _) -> Gt | VSince_le _ -> Gt
          | VNext a -> comparator_vproof _A compa vp a | VNext_ge _ -> Lt
          | VNext_le _ -> Lt | VPrev _ -> Lt | VPrev_ge _ -> Lt
          | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VNext_ge i, rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt | VIff_vs (_, _) -> Gt
          | VOnce_le _ -> Gt | VOnce (_, _, _) -> Gt
          | VEventually (_, _, _) -> Gt | VHistorically (_, _) -> Gt
          | VAlways (_, _) -> Gt | VSince (_, _, _) -> Gt
          | VUntil (_, _, _) -> Gt | VSince_never (_, _, _) -> Gt
          | VUntil_never (_, _, _) -> Gt | VSince_le _ -> Gt | VNext _ -> Gt
          | VNext_ge a -> comparator_of (equal_nat, linorder_nat) i a
          | VNext_le _ -> Lt | VPrev _ -> Lt | VPrev_ge _ -> Lt
          | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VNext_le i, rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt | VIff_vs (_, _) -> Gt
          | VOnce_le _ -> Gt | VOnce (_, _, _) -> Gt
          | VEventually (_, _, _) -> Gt | VHistorically (_, _) -> Gt
          | VAlways (_, _) -> Gt | VSince (_, _, _) -> Gt
          | VUntil (_, _, _) -> Gt | VSince_never (_, _, _) -> Gt
          | VUntil_never (_, _, _) -> Gt | VSince_le _ -> Gt | VNext _ -> Gt
          | VNext_ge _ -> Gt
          | VNext_le a -> comparator_of (equal_nat, linorder_nat) i a
          | VPrev _ -> Lt | VPrev_ge _ -> Lt | VPrev_le _ -> Lt
          | VPrev_zero -> Lt)
    | compa, VPrev vp, rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt | VIff_vs (_, _) -> Gt
          | VOnce_le _ -> Gt | VOnce (_, _, _) -> Gt
          | VEventually (_, _, _) -> Gt | VHistorically (_, _) -> Gt
          | VAlways (_, _) -> Gt | VSince (_, _, _) -> Gt
          | VUntil (_, _, _) -> Gt | VSince_never (_, _, _) -> Gt
          | VUntil_never (_, _, _) -> Gt | VSince_le _ -> Gt | VNext _ -> Gt
          | VNext_ge _ -> Gt | VNext_le _ -> Gt
          | VPrev a -> comparator_vproof _A compa vp a | VPrev_ge _ -> Lt
          | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VPrev_ge i, rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt | VIff_vs (_, _) -> Gt
          | VOnce_le _ -> Gt | VOnce (_, _, _) -> Gt
          | VEventually (_, _, _) -> Gt | VHistorically (_, _) -> Gt
          | VAlways (_, _) -> Gt | VSince (_, _, _) -> Gt
          | VUntil (_, _, _) -> Gt | VSince_never (_, _, _) -> Gt
          | VUntil_never (_, _, _) -> Gt | VSince_le _ -> Gt | VNext _ -> Gt
          | VNext_ge _ -> Gt | VNext_le _ -> Gt | VPrev _ -> Gt
          | VPrev_ge a -> comparator_of (equal_nat, linorder_nat) i a
          | VPrev_le _ -> Lt | VPrev_zero -> Lt)
    | compa, VPrev_le i, rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt | VIff_vs (_, _) -> Gt
          | VOnce_le _ -> Gt | VOnce (_, _, _) -> Gt
          | VEventually (_, _, _) -> Gt | VHistorically (_, _) -> Gt
          | VAlways (_, _) -> Gt | VSince (_, _, _) -> Gt
          | VUntil (_, _, _) -> Gt | VSince_never (_, _, _) -> Gt
          | VUntil_never (_, _, _) -> Gt | VSince_le _ -> Gt | VNext _ -> Gt
          | VNext_ge _ -> Gt | VNext_le _ -> Gt | VPrev _ -> Gt
          | VPrev_ge _ -> Gt
          | VPrev_le a -> comparator_of (equal_nat, linorder_nat) i a
          | VPrev_zero -> Lt)
    | compa, VPrev_zero, rhs ->
        (match rhs with VFF _ -> Gt | VAtm (_, _) -> Gt | VNeg _ -> Gt
          | VDisj (_, _) -> Gt | VConjL _ -> Gt | VConjR _ -> Gt
          | VImpl (_, _) -> Gt | VIff_sv (_, _) -> Gt | VIff_vs (_, _) -> Gt
          | VOnce_le _ -> Gt | VOnce (_, _, _) -> Gt
          | VEventually (_, _, _) -> Gt | VHistorically (_, _) -> Gt
          | VAlways (_, _) -> Gt | VSince (_, _, _) -> Gt
          | VUntil (_, _, _) -> Gt | VSince_never (_, _, _) -> Gt
          | VUntil_never (_, _, _) -> Gt | VSince_le _ -> Gt | VNext _ -> Gt
          | VNext_ge _ -> Gt | VNext_le _ -> Gt | VPrev _ -> Gt
          | VPrev_ge _ -> Gt | VPrev_le _ -> Gt | VPrev_zero -> Eq);;

let rec ccompare_sproofa _A
  = (match ccompare _A with None -> None
      | Some comp_a -> Some (comparator_sproof _A comp_a));;

let rec ccompare_sproof _A =
  ({ccompare = ccompare_sproofa _A} : 'a sproof ccompare);;

let rec ceq_vproofa _A = Some (equal_vproofa _A);;

let rec ceq_vproof _A = ({ceq = ceq_vproofa _A} : 'a vproof ceq);;

let set_impl_vproofa : ('a vproof, set_impla) phantom = Phantom Set_RBT;;

let set_impl_vproof = ({set_impl = set_impl_vproofa} : 'a vproof set_impl);;

let rec ccompare_vproofa _A
  = (match ccompare _A with None -> None
      | Some comp_a -> Some (comparator_vproof _A comp_a));;

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
  Conj of 'a mtl * 'a mtl | Impl of 'a mtl * 'a mtl | Iff of 'a mtl * 'a mtl |
  Next of i * 'a mtl | Prev of i * 'a mtl | Once of i * 'a mtl |
  Historically of i * 'a mtl | Eventually of i * 'a mtl | Always of i * 'a mtl |
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
               | VImpl (sphi, vpsi) -> s_at sphi
               | VIff_sv (sphi, vpsi) -> s_at sphi
               | VIff_vs (vphi, spsi) -> v_at vphi
               | VNext vphi -> minus_nat (v_at vphi) one_nat
               | VNext_ge n -> n
               | VNext_le n -> n
               | VPrev vphi -> plus_nata (v_at vphi) one_nat
               | VPrev_ge n -> n
               | VPrev_le n -> n
               | VPrev_zero -> zero_nata
               | VOnce_le n -> n
               | VOnce (n, li, vphi) -> n
               | VEventually (n, li, vphi) -> n
               | VHistorically (n, vphi) -> n
               | VAlways (n, vphi) -> n
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
    | SImplL vphi -> v_at vphi
    | SImplR spsi -> s_at spsi
    | SIff_ss (sphi, spsi) -> s_at sphi
    | SIff_vv (vphi, vpsi) -> v_at vphi
    | SNext sphi -> minus_nat (s_at sphi) one_nat
    | SPrev sphi -> plus_nata (s_at sphi) one_nat
    | SOnce (n, sphi) -> n
    | SEventually (n, sphi) -> n
    | SHistorically (n, li, sphis) -> n
    | SHistorically_le n -> n
    | SAlways (n, hi, sphis) -> n
    | SSince (spsi, sphis) ->
        (match sphis with [] -> s_at spsi | _ :: _ -> s_at (last sphis))
    | SUntil (sphis, spsi) ->
        (match sphis with [] -> s_at spsi | x :: _ -> s_at x);;

let rec p_at
  x = (fun a -> (match a with Inl aa -> s_at aa | Inr aa -> v_at aa)) x;;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec doIff
  p1 p2 =
    (match (p1, p2) with (Inl p1a, Inl p2a) -> [Inl (SIff_ss (p1a, p2a))]
      | (Inl p1a, Inr p2a) -> [Inr (VIff_sv (p1a, p2a))]
      | (Inr p1a, Inl p2a) -> [Inr (VIff_vs (p1a, p2a))]
      | (Inr p1a, Inr p2a) -> [Inl (SIff_vv (p1a, p2a))]);;

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
    rho, Eventually (i, phi), p ->
      (match p with VFF _ -> false | VAtm (_, _) -> false | VNeg _ -> false
        | VDisj (_, _) -> false | VConjL _ -> false | VConjR _ -> false
        | VImpl (_, _) -> false | VIff_sv (_, _) -> false
        | VIff_vs (_, _) -> false | VOnce_le _ -> false
        | VOnce (_, _, _) -> false
        | VEventually (ia, hi, vphis) ->
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
            (check_upt_lu (_A1, _A2, _A4) rho i ia (map v_at vphis) hi &&
              list_all (v_check (_A1, _A2, _A3, _A4) rho phi) vphis)
        | VHistorically (_, _) -> false | VAlways (_, _) -> false
        | VSince (_, _, _) -> false | VUntil (_, _, _) -> false
        | VSince_never (_, _, _) -> false | VUntil_never (_, _, _) -> false
        | VSince_le _ -> false | VNext _ -> false | VNext_ge _ -> false
        | VNext_le _ -> false | VPrev _ -> false | VPrev_ge _ -> false
        | VPrev_le _ -> false | VPrev_zero -> false)
    | rho, Until (phi, i, psi), p ->
        (match p with VFF _ -> false | VAtm (_, _) -> false | VNeg _ -> false
          | VDisj (_, _) -> false | VConjL _ -> false | VConjR _ -> false
          | VImpl (_, _) -> false | VIff_sv (_, _) -> false
          | VIff_vs (_, _) -> false | VOnce_le _ -> false
          | VOnce (_, _, _) -> false | VEventually (_, _, _) -> false
          | VHistorically (_, _) -> false | VAlways (_, _) -> false
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
    | rho, Once (i, phi), p ->
        (match p with VFF _ -> false | VAtm (_, _) -> false | VNeg _ -> false
          | VDisj (_, _) -> false | VConjL _ -> false | VConjR _ -> false
          | VImpl (_, _) -> false | VIff_sv (_, _) -> false
          | VIff_vs (_, _) -> false
          | VOnce_le ia ->
            less_nat (tau (_A1, _A2, _A4) rho ia)
              (plus_nata (tau (_A1, _A2, _A4) rho zero_nata) (left i))
          | VOnce (ia, li, vphis) ->
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
                (check_upt_l (_A1, _A2, _A4) rho i li (map v_at vphis) ia &&
                  list_all (v_check (_A1, _A2, _A3, _A4) rho phi) vphis))
          | VEventually (_, _, _) -> false | VHistorically (_, _) -> false
          | VAlways (_, _) -> false | VSince (_, _, _) -> false
          | VUntil (_, _, _) -> false | VSince_never (_, _, _) -> false
          | VUntil_never (_, _, _) -> false | VSince_le _ -> false
          | VNext _ -> false | VNext_ge _ -> false | VNext_le _ -> false
          | VPrev _ -> false | VPrev_ge _ -> false | VPrev_le _ -> false
          | VPrev_zero -> false)
    | rho, Since (phi, i, psi), p ->
        (match p with VFF _ -> false | VAtm (_, _) -> false | VNeg _ -> false
          | VDisj (_, _) -> false | VConjL _ -> false | VConjR _ -> false
          | VImpl (_, _) -> false | VIff_sv (_, _) -> false
          | VIff_vs (_, _) -> false | VOnce_le _ -> false
          | VOnce (_, _, _) -> false | VEventually (_, _, _) -> false
          | VHistorically (_, _) -> false | VAlways (_, _) -> false
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
    | rho, Always (x, xa), VPrev_zero -> false
    | rho, Always (xa, xaa), VPrev_le x -> false
    | rho, Always (xa, xaa), VPrev_ge x -> false
    | rho, Always (xa, xaa), VPrev x -> false
    | rho, Always (xa, xaa), VNext_le x -> false
    | rho, Always (xa, xaa), VNext_ge x -> false
    | rho, Always (xa, xaa), VNext x -> false
    | rho, Always (xa, xaa), VSince_le x -> false
    | rho, Always (xc, xaa), VUntil_never (xb, xa, x) -> false
    | rho, Always (xc, xaa), VSince_never (xb, xa, x) -> false
    | rho, Always (xc, xaa), VUntil (xb, xa, x) -> false
    | rho, Always (xc, xaa), VSince (xb, xa, x) -> false
    | rho, Always (xb, xaa), VAlways (xa, x) ->
        (let j = v_at x in
          less_eq_nat xa j &&
            (less_eq_nat (left xb)
               (minus_nat (tau (_A1, _A2, _A4) rho j)
                 (tau (_A1, _A2, _A4) rho xa)) &&
               less_eq_enat
                 (Enat (minus_nat (tau (_A1, _A2, _A4) rho j)
                         (tau (_A1, _A2, _A4) rho xa)))
                 (right xb) &&
              v_check (_A1, _A2, _A3, _A4) rho xaa x))
    | rho, Always (xb, xaa), VHistorically (xa, x) -> false
    | rho, Always (xc, xaa), VEventually (xb, xa, x) -> false
    | rho, Always (xc, xaa), VOnce (xb, xa, x) -> false
    | rho, Always (xa, xaa), VOnce_le x -> false
    | rho, Always (xb, xaa), VIff_vs (xa, x) -> false
    | rho, Always (xb, xaa), VIff_sv (xa, x) -> false
    | rho, Always (xb, xaa), VImpl (xa, x) -> false
    | rho, Always (xa, xaa), VConjR x -> false
    | rho, Always (xa, xaa), VConjL x -> false
    | rho, Always (xb, xaa), VDisj (xa, x) -> false
    | rho, Always (xa, xaa), VNeg x -> false
    | rho, Always (xb, xaa), VAtm (xa, x) -> false
    | rho, Always (xa, xaa), VFF x -> false
    | rho, Historically (x, xa), VPrev_zero -> false
    | rho, Historically (xa, xaa), VPrev_le x -> false
    | rho, Historically (xa, xaa), VPrev_ge x -> false
    | rho, Historically (xa, xaa), VPrev x -> false
    | rho, Historically (xa, xaa), VNext_le x -> false
    | rho, Historically (xa, xaa), VNext_ge x -> false
    | rho, Historically (xa, xaa), VNext x -> false
    | rho, Historically (xa, xaa), VSince_le x -> false
    | rho, Historically (xc, xaa), VUntil_never (xb, xa, x) -> false
    | rho, Historically (xc, xaa), VSince_never (xb, xa, x) -> false
    | rho, Historically (xc, xaa), VUntil (xb, xa, x) -> false
    | rho, Historically (xc, xaa), VSince (xb, xa, x) -> false
    | rho, Historically (xb, xaa), VAlways (xa, x) -> false
    | rho, Historically (xb, xaa), VHistorically (xa, x) ->
        (let j = v_at x in
          less_eq_nat j xa &&
            (less_eq_nat (left xb)
               (minus_nat (tau (_A1, _A2, _A4) rho xa)
                 (tau (_A1, _A2, _A4) rho j)) &&
               less_eq_enat
                 (Enat (minus_nat (tau (_A1, _A2, _A4) rho xa)
                         (tau (_A1, _A2, _A4) rho j)))
                 (right xb) &&
              v_check (_A1, _A2, _A3, _A4) rho xaa x))
    | rho, Historically (xc, xaa), VEventually (xb, xa, x) -> false
    | rho, Historically (xc, xaa), VOnce (xb, xa, x) -> false
    | rho, Historically (xa, xaa), VOnce_le x -> false
    | rho, Historically (xb, xaa), VIff_vs (xa, x) -> false
    | rho, Historically (xb, xaa), VIff_sv (xa, x) -> false
    | rho, Historically (xb, xaa), VImpl (xa, x) -> false
    | rho, Historically (xa, xaa), VConjR x -> false
    | rho, Historically (xa, xaa), VConjL x -> false
    | rho, Historically (xb, xaa), VDisj (xa, x) -> false
    | rho, Historically (xa, xaa), VNeg x -> false
    | rho, Historically (xb, xaa), VAtm (xa, x) -> false
    | rho, Historically (xa, xaa), VFF x -> false
    | rho, Prev (x, xa), VPrev_zero -> equal_nata (v_at VPrev_zero) zero_nata
    | rho, Prev (xa, xaa), VPrev_le x ->
        less_nat zero_nata x &&
          less_nat
            (minus_nat (tau (_A1, _A2, _A4) rho x)
              (tau (_A1, _A2, _A4) rho (minus_nat x one_nat)))
            (left xa)
    | rho, Prev (xa, xaa), VPrev_ge x ->
        less_nat zero_nata x &&
          less_enat (right xa)
            (Enat (minus_nat (tau (_A1, _A2, _A4) rho x)
                    (tau (_A1, _A2, _A4) rho (minus_nat x one_nat))))
    | rho, Prev (xa, xaa), VPrev x ->
        (let j = v_at x in
         let i = v_at (VPrev x) in
          equal_nata i (suc j) && v_check (_A1, _A2, _A3, _A4) rho xaa x)
    | rho, Prev (xa, xaa), VNext_le x -> false
    | rho, Prev (xa, xaa), VNext_ge x -> false
    | rho, Prev (xa, xaa), VNext x -> false
    | rho, Prev (xa, xaa), VSince_le x -> false
    | rho, Prev (xc, xaa), VUntil_never (xb, xa, x) -> false
    | rho, Prev (xc, xaa), VSince_never (xb, xa, x) -> false
    | rho, Prev (xc, xaa), VUntil (xb, xa, x) -> false
    | rho, Prev (xc, xaa), VSince (xb, xa, x) -> false
    | rho, Prev (xb, xaa), VAlways (xa, x) -> false
    | rho, Prev (xb, xaa), VHistorically (xa, x) -> false
    | rho, Prev (xc, xaa), VEventually (xb, xa, x) -> false
    | rho, Prev (xc, xaa), VOnce (xb, xa, x) -> false
    | rho, Prev (xa, xaa), VOnce_le x -> false
    | rho, Prev (xb, xaa), VIff_vs (xa, x) -> false
    | rho, Prev (xb, xaa), VIff_sv (xa, x) -> false
    | rho, Prev (xb, xaa), VImpl (xa, x) -> false
    | rho, Prev (xa, xaa), VConjR x -> false
    | rho, Prev (xa, xaa), VConjL x -> false
    | rho, Prev (xb, xaa), VDisj (xa, x) -> false
    | rho, Prev (xa, xaa), VNeg x -> false
    | rho, Prev (xb, xaa), VAtm (xa, x) -> false
    | rho, Prev (xa, xaa), VFF x -> false
    | rho, Next (x, xa), VPrev_zero -> false
    | rho, Next (xa, xaa), VPrev_le x -> false
    | rho, Next (xa, xaa), VPrev_ge x -> false
    | rho, Next (xa, xaa), VPrev x -> false
    | rho, Next (xa, xaa), VNext_le x ->
        less_nat
          (minus_nat (tau (_A1, _A2, _A4) rho (suc x))
            (tau (_A1, _A2, _A4) rho (minus_nat (suc x) one_nat)))
          (left xa)
    | rho, Next (xa, xaa), VNext_ge x ->
        less_enat (right xa)
          (Enat (minus_nat (tau (_A1, _A2, _A4) rho (suc x))
                  (tau (_A1, _A2, _A4) rho (minus_nat (suc x) one_nat))))
    | rho, Next (xa, xaa), VNext x ->
        (let j = v_at x in
         let i = v_at (VNext x) in
          equal_nata j (suc i) && v_check (_A1, _A2, _A3, _A4) rho xaa x)
    | rho, Next (xa, xaa), VSince_le x -> false
    | rho, Next (xc, xaa), VUntil_never (xb, xa, x) -> false
    | rho, Next (xc, xaa), VSince_never (xb, xa, x) -> false
    | rho, Next (xc, xaa), VUntil (xb, xa, x) -> false
    | rho, Next (xc, xaa), VSince (xb, xa, x) -> false
    | rho, Next (xb, xaa), VAlways (xa, x) -> false
    | rho, Next (xb, xaa), VHistorically (xa, x) -> false
    | rho, Next (xc, xaa), VEventually (xb, xa, x) -> false
    | rho, Next (xc, xaa), VOnce (xb, xa, x) -> false
    | rho, Next (xa, xaa), VOnce_le x -> false
    | rho, Next (xb, xaa), VIff_vs (xa, x) -> false
    | rho, Next (xb, xaa), VIff_sv (xa, x) -> false
    | rho, Next (xb, xaa), VImpl (xa, x) -> false
    | rho, Next (xa, xaa), VConjR x -> false
    | rho, Next (xa, xaa), VConjL x -> false
    | rho, Next (xb, xaa), VDisj (xa, x) -> false
    | rho, Next (xa, xaa), VNeg x -> false
    | rho, Next (xb, xaa), VAtm (xa, x) -> false
    | rho, Next (xa, xaa), VFF x -> false
    | rho, Iff (x, xa), VPrev_zero -> false
    | rho, Iff (xa, xaa), VPrev_le x -> false
    | rho, Iff (xa, xaa), VPrev_ge x -> false
    | rho, Iff (xa, xaa), VPrev x -> false
    | rho, Iff (xa, xaa), VNext_le x -> false
    | rho, Iff (xa, xaa), VNext_ge x -> false
    | rho, Iff (xa, xaa), VNext x -> false
    | rho, Iff (xa, xaa), VSince_le x -> false
    | rho, Iff (xc, xaa), VUntil_never (xb, xa, x) -> false
    | rho, Iff (xc, xaa), VSince_never (xb, xa, x) -> false
    | rho, Iff (xc, xaa), VUntil (xb, xa, x) -> false
    | rho, Iff (xc, xaa), VSince (xb, xa, x) -> false
    | rho, Iff (xb, xaa), VAlways (xa, x) -> false
    | rho, Iff (xb, xaa), VHistorically (xa, x) -> false
    | rho, Iff (xc, xaa), VEventually (xb, xa, x) -> false
    | rho, Iff (xc, xaa), VOnce (xb, xa, x) -> false
    | rho, Iff (xa, xaa), VOnce_le x -> false
    | rho, Iff (xb, xaa), VIff_vs (xa, x) ->
        v_check (_A1, _A2, _A3, _A4) rho xb xa &&
          (s_check (_A1, _A2, _A3, _A4) rho xaa x &&
            equal_nata (v_at xa) (s_at x))
    | rho, Iff (xb, xaa), VIff_sv (xa, x) ->
        s_check (_A1, _A2, _A3, _A4) rho xb xa &&
          (v_check (_A1, _A2, _A3, _A4) rho xaa x &&
            equal_nata (s_at xa) (v_at x))
    | rho, Iff (xb, xaa), VImpl (xa, x) -> false
    | rho, Iff (xa, xaa), VConjR x -> false
    | rho, Iff (xa, xaa), VConjL x -> false
    | rho, Iff (xb, xaa), VDisj (xa, x) -> false
    | rho, Iff (xa, xaa), VNeg x -> false
    | rho, Iff (xb, xaa), VAtm (xa, x) -> false
    | rho, Iff (xa, xaa), VFF x -> false
    | rho, Impl (x, xa), VPrev_zero -> false
    | rho, Impl (xa, xaa), VPrev_le x -> false
    | rho, Impl (xa, xaa), VPrev_ge x -> false
    | rho, Impl (xa, xaa), VPrev x -> false
    | rho, Impl (xa, xaa), VNext_le x -> false
    | rho, Impl (xa, xaa), VNext_ge x -> false
    | rho, Impl (xa, xaa), VNext x -> false
    | rho, Impl (xa, xaa), VSince_le x -> false
    | rho, Impl (xc, xaa), VUntil_never (xb, xa, x) -> false
    | rho, Impl (xc, xaa), VSince_never (xb, xa, x) -> false
    | rho, Impl (xc, xaa), VUntil (xb, xa, x) -> false
    | rho, Impl (xc, xaa), VSince (xb, xa, x) -> false
    | rho, Impl (xb, xaa), VAlways (xa, x) -> false
    | rho, Impl (xb, xaa), VHistorically (xa, x) -> false
    | rho, Impl (xc, xaa), VEventually (xb, xa, x) -> false
    | rho, Impl (xc, xaa), VOnce (xb, xa, x) -> false
    | rho, Impl (xa, xaa), VOnce_le x -> false
    | rho, Impl (xb, xaa), VIff_vs (xa, x) -> false
    | rho, Impl (xb, xaa), VIff_sv (xa, x) -> false
    | rho, Impl (xb, xaa), VImpl (xa, x) ->
        s_check (_A1, _A2, _A3, _A4) rho xb xa &&
          (v_check (_A1, _A2, _A3, _A4) rho xaa x &&
            equal_nata (s_at xa) (v_at x))
    | rho, Impl (xa, xaa), VConjR x -> false
    | rho, Impl (xa, xaa), VConjL x -> false
    | rho, Impl (xb, xaa), VDisj (xa, x) -> false
    | rho, Impl (xa, xaa), VNeg x -> false
    | rho, Impl (xb, xaa), VAtm (xa, x) -> false
    | rho, Impl (xa, xaa), VFF x -> false
    | rho, Conj (x, xa), VPrev_zero -> false
    | rho, Conj (xa, xaa), VPrev_le x -> false
    | rho, Conj (xa, xaa), VPrev_ge x -> false
    | rho, Conj (xa, xaa), VPrev x -> false
    | rho, Conj (xa, xaa), VNext_le x -> false
    | rho, Conj (xa, xaa), VNext_ge x -> false
    | rho, Conj (xa, xaa), VNext x -> false
    | rho, Conj (xa, xaa), VSince_le x -> false
    | rho, Conj (xc, xaa), VUntil_never (xb, xa, x) -> false
    | rho, Conj (xc, xaa), VSince_never (xb, xa, x) -> false
    | rho, Conj (xc, xaa), VUntil (xb, xa, x) -> false
    | rho, Conj (xc, xaa), VSince (xb, xa, x) -> false
    | rho, Conj (xb, xaa), VAlways (xa, x) -> false
    | rho, Conj (xb, xaa), VHistorically (xa, x) -> false
    | rho, Conj (xc, xaa), VEventually (xb, xa, x) -> false
    | rho, Conj (xc, xaa), VOnce (xb, xa, x) -> false
    | rho, Conj (xa, xaa), VOnce_le x -> false
    | rho, Conj (xb, xaa), VIff_vs (xa, x) -> false
    | rho, Conj (xb, xaa), VIff_sv (xa, x) -> false
    | rho, Conj (xb, xaa), VImpl (xa, x) -> false
    | rho, Conj (xa, xaa), VConjR x -> v_check (_A1, _A2, _A3, _A4) rho xaa x
    | rho, Conj (xa, xaa), VConjL x -> v_check (_A1, _A2, _A3, _A4) rho xa x
    | rho, Conj (xb, xaa), VDisj (xa, x) -> false
    | rho, Conj (xa, xaa), VNeg x -> false
    | rho, Conj (xb, xaa), VAtm (xa, x) -> false
    | rho, Conj (xa, xaa), VFF x -> false
    | rho, Disj (x, xa), VPrev_zero -> false
    | rho, Disj (xa, xaa), VPrev_le x -> false
    | rho, Disj (xa, xaa), VPrev_ge x -> false
    | rho, Disj (xa, xaa), VPrev x -> false
    | rho, Disj (xa, xaa), VNext_le x -> false
    | rho, Disj (xa, xaa), VNext_ge x -> false
    | rho, Disj (xa, xaa), VNext x -> false
    | rho, Disj (xa, xaa), VSince_le x -> false
    | rho, Disj (xc, xaa), VUntil_never (xb, xa, x) -> false
    | rho, Disj (xc, xaa), VSince_never (xb, xa, x) -> false
    | rho, Disj (xc, xaa), VUntil (xb, xa, x) -> false
    | rho, Disj (xc, xaa), VSince (xb, xa, x) -> false
    | rho, Disj (xb, xaa), VAlways (xa, x) -> false
    | rho, Disj (xb, xaa), VHistorically (xa, x) -> false
    | rho, Disj (xc, xaa), VEventually (xb, xa, x) -> false
    | rho, Disj (xc, xaa), VOnce (xb, xa, x) -> false
    | rho, Disj (xa, xaa), VOnce_le x -> false
    | rho, Disj (xb, xaa), VIff_vs (xa, x) -> false
    | rho, Disj (xb, xaa), VIff_sv (xa, x) -> false
    | rho, Disj (xb, xaa), VImpl (xa, x) -> false
    | rho, Disj (xa, xaa), VConjR x -> false
    | rho, Disj (xa, xaa), VConjL x -> false
    | rho, Disj (xb, xaa), VDisj (xa, x) ->
        v_check (_A1, _A2, _A3, _A4) rho xb xa &&
          (v_check (_A1, _A2, _A3, _A4) rho xaa x &&
            equal_nata (v_at xa) (v_at x))
    | rho, Disj (xa, xaa), VNeg x -> false
    | rho, Disj (xb, xaa), VAtm (xa, x) -> false
    | rho, Disj (xa, xaa), VFF x -> false
    | rho, Neg x, VPrev_zero -> false
    | rho, Neg xa, VPrev_le x -> false
    | rho, Neg xa, VPrev_ge x -> false
    | rho, Neg xa, VPrev x -> false
    | rho, Neg xa, VNext_le x -> false
    | rho, Neg xa, VNext_ge x -> false
    | rho, Neg xa, VNext x -> false
    | rho, Neg xa, VSince_le x -> false
    | rho, Neg xc, VUntil_never (xb, xa, x) -> false
    | rho, Neg xc, VSince_never (xb, xa, x) -> false
    | rho, Neg xc, VUntil (xb, xa, x) -> false
    | rho, Neg xc, VSince (xb, xa, x) -> false
    | rho, Neg xb, VAlways (xa, x) -> false
    | rho, Neg xb, VHistorically (xa, x) -> false
    | rho, Neg xc, VEventually (xb, xa, x) -> false
    | rho, Neg xc, VOnce (xb, xa, x) -> false
    | rho, Neg xa, VOnce_le x -> false
    | rho, Neg xb, VIff_vs (xa, x) -> false
    | rho, Neg xb, VIff_sv (xa, x) -> false
    | rho, Neg xb, VImpl (xa, x) -> false
    | rho, Neg xa, VConjR x -> false
    | rho, Neg xa, VConjL x -> false
    | rho, Neg xb, VDisj (xa, x) -> false
    | rho, Neg xa, VNeg x -> s_check (_A1, _A2, _A3, _A4) rho xa x
    | rho, Neg xb, VAtm (xa, x) -> false
    | rho, Neg xa, VFF x -> false
    | rho, Atom x, VPrev_zero -> false
    | rho, Atom xa, VPrev_le x -> false
    | rho, Atom xa, VPrev_ge x -> false
    | rho, Atom xa, VPrev x -> false
    | rho, Atom xa, VNext_le x -> false
    | rho, Atom xa, VNext_ge x -> false
    | rho, Atom xa, VNext x -> false
    | rho, Atom xa, VSince_le x -> false
    | rho, Atom xc, VUntil_never (xb, xa, x) -> false
    | rho, Atom xc, VSince_never (xb, xa, x) -> false
    | rho, Atom xc, VUntil (xb, xa, x) -> false
    | rho, Atom xc, VSince (xb, xa, x) -> false
    | rho, Atom xb, VAlways (xa, x) -> false
    | rho, Atom xb, VHistorically (xa, x) -> false
    | rho, Atom xc, VEventually (xb, xa, x) -> false
    | rho, Atom xc, VOnce (xb, xa, x) -> false
    | rho, Atom xa, VOnce_le x -> false
    | rho, Atom xb, VIff_vs (xa, x) -> false
    | rho, Atom xb, VIff_sv (xa, x) -> false
    | rho, Atom xb, VImpl (xa, x) -> false
    | rho, Atom xa, VConjR x -> false
    | rho, Atom xa, VConjL x -> false
    | rho, Atom xb, VDisj (xa, x) -> false
    | rho, Atom xa, VNeg x -> false
    | rho, Atom xb, VAtm (xa, x) ->
        eq _A3 xb xa && not (member (_A1, _A2) xb (gamma (_A1, _A2, _A4) rho x))
    | rho, Atom xa, VFF x -> false
    | rho, FF, VPrev_zero -> false
    | rho, FF, VPrev_le x -> false
    | rho, FF, VPrev_ge x -> false
    | rho, FF, VPrev x -> false
    | rho, FF, VNext_le x -> false
    | rho, FF, VNext_ge x -> false
    | rho, FF, VNext x -> false
    | rho, FF, VSince_le x -> false
    | rho, FF, VUntil_never (xb, xa, x) -> false
    | rho, FF, VSince_never (xb, xa, x) -> false
    | rho, FF, VUntil (xb, xa, x) -> false
    | rho, FF, VSince (xb, xa, x) -> false
    | rho, FF, VAlways (xa, x) -> false
    | rho, FF, VHistorically (xa, x) -> false
    | rho, FF, VEventually (xb, xa, x) -> false
    | rho, FF, VOnce (xb, xa, x) -> false
    | rho, FF, VOnce_le x -> false
    | rho, FF, VIff_vs (xa, x) -> false
    | rho, FF, VIff_sv (xa, x) -> false
    | rho, FF, VImpl (xa, x) -> false
    | rho, FF, VConjR x -> false
    | rho, FF, VConjL x -> false
    | rho, FF, VDisj (xa, x) -> false
    | rho, FF, VNeg x -> false
    | rho, FF, VAtm (xa, x) -> false
    | rho, FF, VFF x -> true
    | rho, TT, p -> false
and s_check (_A1, _A2, _A3, _A4)
  rho x1 p = match rho, x1, p with
    rho, Always (i, phi), p ->
      (match p with STT _ -> false | SAtm (_, _) -> false | SNeg _ -> false
        | SDisjL _ -> false | SDisjR _ -> false | SConj (_, _) -> false
        | SImplR _ -> false | SImplL _ -> false | SIff_ss (_, _) -> false
        | SIff_vv (_, _) -> false | SOnce (_, _) -> false
        | SEventually (_, _) -> false | SHistorically (_, _, _) -> false
        | SHistorically_le _ -> false
        | SAlways (ia, hi, sphis) ->
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
            (check_upt_lu (_A1, _A2, _A4) rho i ia (map s_at sphis) hi &&
              list_all (s_check (_A1, _A2, _A3, _A4) rho phi) sphis)
        | SSince (_, _) -> false | SUntil (_, _) -> false | SNext _ -> false
        | SPrev _ -> false)
    | rho, Historically (i, phi), p ->
        (match p with STT _ -> false | SAtm (_, _) -> false | SNeg _ -> false
          | SDisjL _ -> false | SDisjR _ -> false | SConj (_, _) -> false
          | SImplR _ -> false | SImplL _ -> false | SIff_ss (_, _) -> false
          | SIff_vv (_, _) -> false | SOnce (_, _) -> false
          | SEventually (_, _) -> false
          | SHistorically (ia, li, vphis) ->
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
                (check_upt_l (_A1, _A2, _A4) rho i li (map s_at vphis) ia &&
                  list_all (s_check (_A1, _A2, _A3, _A4) rho phi) vphis))
          | SHistorically_le ia ->
            less_nat (tau (_A1, _A2, _A4) rho ia)
              (plus_nata (tau (_A1, _A2, _A4) rho zero_nata) (left i))
          | SAlways (_, _, _) -> false | SSince (_, _) -> false
          | SUntil (_, _) -> false | SNext _ -> false | SPrev _ -> false)
    | rho, Until (xa, xaa, xb), SPrev x -> false
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
    | rho, Until (xc, xaa, xba), SAlways (xb, xa, x) -> false
    | rho, Until (xa, xaa, xb), SHistorically_le x -> false
    | rho, Until (xc, xaa, xba), SHistorically (xb, xa, x) -> false
    | rho, Until (xb, xaa, xba), SEventually (xa, x) -> false
    | rho, Until (xb, xaa, xba), SOnce (xa, x) -> false
    | rho, Until (xb, xaa, xba), SIff_vv (xa, x) -> false
    | rho, Until (xb, xaa, xba), SIff_ss (xa, x) -> false
    | rho, Until (xa, xaa, xb), SImplL x -> false
    | rho, Until (xa, xaa, xb), SImplR x -> false
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
    | rho, Since (xc, xaa, xba), SAlways (xb, xa, x) -> false
    | rho, Since (xa, xaa, xb), SHistorically_le x -> false
    | rho, Since (xc, xaa, xba), SHistorically (xb, xa, x) -> false
    | rho, Since (xb, xaa, xba), SEventually (xa, x) -> false
    | rho, Since (xb, xaa, xba), SOnce (xa, x) -> false
    | rho, Since (xb, xaa, xba), SIff_vv (xa, x) -> false
    | rho, Since (xb, xaa, xba), SIff_ss (xa, x) -> false
    | rho, Since (xa, xaa, xb), SImplL x -> false
    | rho, Since (xa, xaa, xb), SImplR x -> false
    | rho, Since (xb, xaa, xba), SConj (xa, x) -> false
    | rho, Since (xa, xaa, xb), SDisjR x -> false
    | rho, Since (xa, xaa, xb), SDisjL x -> false
    | rho, Since (xa, xaa, xb), SNeg x -> false
    | rho, Since (xb, xaa, xba), SAtm (xa, x) -> false
    | rho, Since (xa, xaa, xb), STT x -> false
    | rho, Eventually (xa, xaa), SPrev x -> false
    | rho, Eventually (xa, xaa), SNext x -> false
    | rho, Eventually (xb, xaa), SUntil (xa, x) -> false
    | rho, Eventually (xb, xaa), SSince (xa, x) -> false
    | rho, Eventually (xc, xaa), SAlways (xb, xa, x) -> false
    | rho, Eventually (xa, xaa), SHistorically_le x -> false
    | rho, Eventually (xc, xaa), SHistorically (xb, xa, x) -> false
    | rho, Eventually (xb, xaa), SEventually (xa, x) ->
        (let j = s_at x in
          less_eq_nat xa j &&
            (less_eq_nat (left xb)
               (minus_nat (tau (_A1, _A2, _A4) rho j)
                 (tau (_A1, _A2, _A4) rho xa)) &&
               less_eq_enat
                 (Enat (minus_nat (tau (_A1, _A2, _A4) rho j)
                         (tau (_A1, _A2, _A4) rho xa)))
                 (right xb) &&
              s_check (_A1, _A2, _A3, _A4) rho xaa x))
    | rho, Eventually (xb, xaa), SOnce (xa, x) -> false
    | rho, Eventually (xb, xaa), SIff_vv (xa, x) -> false
    | rho, Eventually (xb, xaa), SIff_ss (xa, x) -> false
    | rho, Eventually (xa, xaa), SImplL x -> false
    | rho, Eventually (xa, xaa), SImplR x -> false
    | rho, Eventually (xb, xaa), SConj (xa, x) -> false
    | rho, Eventually (xa, xaa), SDisjR x -> false
    | rho, Eventually (xa, xaa), SDisjL x -> false
    | rho, Eventually (xa, xaa), SNeg x -> false
    | rho, Eventually (xb, xaa), SAtm (xa, x) -> false
    | rho, Eventually (xa, xaa), STT x -> false
    | rho, Once (xa, xaa), SPrev x -> false
    | rho, Once (xa, xaa), SNext x -> false
    | rho, Once (xb, xaa), SUntil (xa, x) -> false
    | rho, Once (xb, xaa), SSince (xa, x) -> false
    | rho, Once (xc, xaa), SAlways (xb, xa, x) -> false
    | rho, Once (xa, xaa), SHistorically_le x -> false
    | rho, Once (xc, xaa), SHistorically (xb, xa, x) -> false
    | rho, Once (xb, xaa), SEventually (xa, x) -> false
    | rho, Once (xb, xaa), SOnce (xa, x) ->
        (let j = s_at x in
          less_eq_nat j xa &&
            (less_eq_nat (left xb)
               (minus_nat (tau (_A1, _A2, _A4) rho xa)
                 (tau (_A1, _A2, _A4) rho j)) &&
               less_eq_enat
                 (Enat (minus_nat (tau (_A1, _A2, _A4) rho xa)
                         (tau (_A1, _A2, _A4) rho j)))
                 (right xb) &&
              s_check (_A1, _A2, _A3, _A4) rho xaa x))
    | rho, Once (xb, xaa), SIff_vv (xa, x) -> false
    | rho, Once (xb, xaa), SIff_ss (xa, x) -> false
    | rho, Once (xa, xaa), SImplL x -> false
    | rho, Once (xa, xaa), SImplR x -> false
    | rho, Once (xb, xaa), SConj (xa, x) -> false
    | rho, Once (xa, xaa), SDisjR x -> false
    | rho, Once (xa, xaa), SDisjL x -> false
    | rho, Once (xa, xaa), SNeg x -> false
    | rho, Once (xb, xaa), SAtm (xa, x) -> false
    | rho, Once (xa, xaa), STT x -> false
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
    | rho, Prev (xc, xaa), SAlways (xb, xa, x) -> false
    | rho, Prev (xa, xaa), SHistorically_le x -> false
    | rho, Prev (xc, xaa), SHistorically (xb, xa, x) -> false
    | rho, Prev (xb, xaa), SEventually (xa, x) -> false
    | rho, Prev (xb, xaa), SOnce (xa, x) -> false
    | rho, Prev (xb, xaa), SIff_vv (xa, x) -> false
    | rho, Prev (xb, xaa), SIff_ss (xa, x) -> false
    | rho, Prev (xa, xaa), SImplL x -> false
    | rho, Prev (xa, xaa), SImplR x -> false
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
    | rho, Next (xc, xaa), SAlways (xb, xa, x) -> false
    | rho, Next (xa, xaa), SHistorically_le x -> false
    | rho, Next (xc, xaa), SHistorically (xb, xa, x) -> false
    | rho, Next (xb, xaa), SEventually (xa, x) -> false
    | rho, Next (xb, xaa), SOnce (xa, x) -> false
    | rho, Next (xb, xaa), SIff_vv (xa, x) -> false
    | rho, Next (xb, xaa), SIff_ss (xa, x) -> false
    | rho, Next (xa, xaa), SImplL x -> false
    | rho, Next (xa, xaa), SImplR x -> false
    | rho, Next (xb, xaa), SConj (xa, x) -> false
    | rho, Next (xa, xaa), SDisjR x -> false
    | rho, Next (xa, xaa), SDisjL x -> false
    | rho, Next (xa, xaa), SNeg x -> false
    | rho, Next (xb, xaa), SAtm (xa, x) -> false
    | rho, Next (xa, xaa), STT x -> false
    | rho, Iff (xa, xaa), SPrev x -> false
    | rho, Iff (xa, xaa), SNext x -> false
    | rho, Iff (xb, xaa), SUntil (xa, x) -> false
    | rho, Iff (xb, xaa), SSince (xa, x) -> false
    | rho, Iff (xc, xaa), SAlways (xb, xa, x) -> false
    | rho, Iff (xa, xaa), SHistorically_le x -> false
    | rho, Iff (xc, xaa), SHistorically (xb, xa, x) -> false
    | rho, Iff (xb, xaa), SEventually (xa, x) -> false
    | rho, Iff (xb, xaa), SOnce (xa, x) -> false
    | rho, Iff (xb, xaa), SIff_vv (xa, x) ->
        v_check (_A1, _A2, _A3, _A4) rho xb xa &&
          (v_check (_A1, _A2, _A3, _A4) rho xaa x &&
            equal_nata (v_at xa) (v_at x))
    | rho, Iff (xb, xaa), SIff_ss (xa, x) ->
        s_check (_A1, _A2, _A3, _A4) rho xb xa &&
          (s_check (_A1, _A2, _A3, _A4) rho xaa x &&
            equal_nata (s_at xa) (s_at x))
    | rho, Iff (xa, xaa), SImplL x -> false
    | rho, Iff (xa, xaa), SImplR x -> false
    | rho, Iff (xb, xaa), SConj (xa, x) -> false
    | rho, Iff (xa, xaa), SDisjR x -> false
    | rho, Iff (xa, xaa), SDisjL x -> false
    | rho, Iff (xa, xaa), SNeg x -> false
    | rho, Iff (xb, xaa), SAtm (xa, x) -> false
    | rho, Iff (xa, xaa), STT x -> false
    | rho, Impl (xa, xaa), SPrev x -> false
    | rho, Impl (xa, xaa), SNext x -> false
    | rho, Impl (xb, xaa), SUntil (xa, x) -> false
    | rho, Impl (xb, xaa), SSince (xa, x) -> false
    | rho, Impl (xc, xaa), SAlways (xb, xa, x) -> false
    | rho, Impl (xa, xaa), SHistorically_le x -> false
    | rho, Impl (xc, xaa), SHistorically (xb, xa, x) -> false
    | rho, Impl (xb, xaa), SEventually (xa, x) -> false
    | rho, Impl (xb, xaa), SOnce (xa, x) -> false
    | rho, Impl (xb, xaa), SIff_vv (xa, x) -> false
    | rho, Impl (xb, xaa), SIff_ss (xa, x) -> false
    | rho, Impl (xa, xaa), SImplL x -> v_check (_A1, _A2, _A3, _A4) rho xa x
    | rho, Impl (xa, xaa), SImplR x -> s_check (_A1, _A2, _A3, _A4) rho xaa x
    | rho, Impl (xb, xaa), SConj (xa, x) -> false
    | rho, Impl (xa, xaa), SDisjR x -> false
    | rho, Impl (xa, xaa), SDisjL x -> false
    | rho, Impl (xa, xaa), SNeg x -> false
    | rho, Impl (xb, xaa), SAtm (xa, x) -> false
    | rho, Impl (xa, xaa), STT x -> false
    | rho, Conj (xa, xaa), SPrev x -> false
    | rho, Conj (xa, xaa), SNext x -> false
    | rho, Conj (xb, xaa), SUntil (xa, x) -> false
    | rho, Conj (xb, xaa), SSince (xa, x) -> false
    | rho, Conj (xc, xaa), SAlways (xb, xa, x) -> false
    | rho, Conj (xa, xaa), SHistorically_le x -> false
    | rho, Conj (xc, xaa), SHistorically (xb, xa, x) -> false
    | rho, Conj (xb, xaa), SEventually (xa, x) -> false
    | rho, Conj (xb, xaa), SOnce (xa, x) -> false
    | rho, Conj (xb, xaa), SIff_vv (xa, x) -> false
    | rho, Conj (xb, xaa), SIff_ss (xa, x) -> false
    | rho, Conj (xa, xaa), SImplL x -> false
    | rho, Conj (xa, xaa), SImplR x -> false
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
    | rho, Disj (xc, xaa), SAlways (xb, xa, x) -> false
    | rho, Disj (xa, xaa), SHistorically_le x -> false
    | rho, Disj (xc, xaa), SHistorically (xb, xa, x) -> false
    | rho, Disj (xb, xaa), SEventually (xa, x) -> false
    | rho, Disj (xb, xaa), SOnce (xa, x) -> false
    | rho, Disj (xb, xaa), SIff_vv (xa, x) -> false
    | rho, Disj (xb, xaa), SIff_ss (xa, x) -> false
    | rho, Disj (xa, xaa), SImplL x -> false
    | rho, Disj (xa, xaa), SImplR x -> false
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
    | rho, Neg xc, SAlways (xb, xa, x) -> false
    | rho, Neg xa, SHistorically_le x -> false
    | rho, Neg xc, SHistorically (xb, xa, x) -> false
    | rho, Neg xb, SEventually (xa, x) -> false
    | rho, Neg xb, SOnce (xa, x) -> false
    | rho, Neg xb, SIff_vv (xa, x) -> false
    | rho, Neg xb, SIff_ss (xa, x) -> false
    | rho, Neg xa, SImplL x -> false
    | rho, Neg xa, SImplR x -> false
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
    | rho, Atom xc, SAlways (xb, xa, x) -> false
    | rho, Atom xa, SHistorically_le x -> false
    | rho, Atom xc, SHistorically (xb, xa, x) -> false
    | rho, Atom xb, SEventually (xa, x) -> false
    | rho, Atom xb, SOnce (xa, x) -> false
    | rho, Atom xb, SIff_vv (xa, x) -> false
    | rho, Atom xb, SIff_ss (xa, x) -> false
    | rho, Atom xa, SImplL x -> false
    | rho, Atom xa, SImplR x -> false
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
    | rho, TT, SAlways (xb, xa, x) -> false
    | rho, TT, SHistorically_le x -> false
    | rho, TT, SHistorically (xb, xa, x) -> false
    | rho, TT, SEventually (xa, x) -> false
    | rho, TT, SOnce (xa, x) -> false
    | rho, TT, SIff_vv (xa, x) -> false
    | rho, TT, SIff_ss (xa, x) -> false
    | rho, TT, SImplL x -> false
    | rho, TT, SImplR x -> false
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

let rec doImpl
  p1 p2 =
    (match (p1, p2) with (Inl _, Inl p2a) -> [Inl (SImplR p2a)]
      | (Inl p1a, Inr p2a) -> [Inr (VImpl (p1a, p2a))]
      | (Inr p1a, Inl p2a) -> [Inl (SImplL p1a); Inl (SImplR p2a)]
      | (Inr p1a, Inr _) -> [Inl (SImplL p1a)]);;

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

let rec proofApp
  p r = (match (p, r)
          with (Inl (SHistorically (i, li, p1)), Inl ra) ->
            Inl (SHistorically (suc i, li, p1 @ [ra]))
          | (Inl (SAlways (i, hi, p1)), Inl ra) ->
            Inl (SAlways (minus_nat i one_nat, hi, ra :: p1))
          | (Inl (SSince (p1, p2)), Inl ra) -> Inl (SSince (p1, p2 @ [ra]))
          | (Inl (SUntil (p1, p2)), Inl ra) -> Inl (SUntil (ra :: p1, p2))
          | (Inr (VOnce (i, li, p1)), Inr ra) ->
            Inr (VOnce (suc i, li, p1 @ [ra]))
          | (Inr (VEventually (i, hi, p1)), Inr ra) ->
            Inr (VEventually (minus_nat i one_nat, hi, ra :: p1))
          | (Inr (VSince (i, p1, p2)), Inr ra) ->
            Inr (VSince (suc i, p1, p2 @ [ra]))
          | (Inr (VUntil (i, p1, p2)), Inr ra) ->
            Inr (VUntil (minus_nat i one_nat, ra :: p1, p2))
          | (Inr (VSince_never (i, li, p1)), Inr ra) ->
            Inr (VSince_never (suc i, li, p1 @ [ra]))
          | (Inr (VUntil_never (i, hi, p1)), Inr ra) ->
            Inr (VUntil_never (minus_nat i one_nat, hi, ra :: p1)));;

let rec doOnce
  i a pa p =
    (match (pa, (equal_nata a zero_nata, p))
      with (Inl pb, aa) ->
        (match aa
          with (true, Inl (SOnce (_, paa))) ->
            [Inl (SOnce (i, paa)); Inl (SOnce (i, pb))]
          | (true, Inr (VOnce (_, _, _))) -> [Inl (SOnce (i, pb))]
          | (false, Inl (SOnce (_, pc))) -> [Inl (SOnce (i, pc))]
          | (false, Inr (VOnce (_, li, q))) -> [Inr (VOnce (i, li, q))])
      | (Inr pb, aa) ->
        (match aa with (true, Inl (SOnce (_, pc))) -> [Inl (SOnce (i, pc))]
          | (true, Inr paa) -> [proofApp (Inr paa) (Inr pb)]
          | (false, Inl (SOnce (_, pc))) -> [Inl (SOnce (i, pc))]
          | (false, Inr (VOnce (_, li, q))) -> [Inr (VOnce (i, li, q))]));;

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

let rec uminus_set = function Complement b -> b
                     | Collect_set p -> Collect_set (fun x -> not (p x))
                     | a -> Complement a;;

let rec rbt_baliR
  t1 ab bb x3 = match t1, ab, bb, x3 with
    t1, ab, bb, Branch (R, t2, aa, ba, Branch (R, t3, a, b, t4)) ->
      Branch (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
    | t1, ab, bb, Branch (R, Branch (R, t2, aa, ba, t3), a, b, Empty) ->
        Branch
          (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, Empty))
    | t1, ab, bb,
        Branch (R, Branch (R, t2, aa, ba, t3), a, b, Branch (B, va, vb, vc, vd))
        -> Branch
             (R, Branch (B, t1, ab, bb, t2), aa, ba,
               Branch (B, t3, a, b, Branch (B, va, vb, vc, vd)))
    | t1, a, b, Empty -> Branch (B, t1, a, b, Empty)
    | t1, a, b, Branch (B, va, vb, vc, vd) ->
        Branch (B, t1, a, b, Branch (B, va, vb, vc, vd))
    | t1, a, b, Branch (v, Empty, vb, vc, Empty) ->
        Branch (B, t1, a, b, Branch (v, Empty, vb, vc, Empty))
    | t1, a, b, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty) ->
        Branch
          (B, t1, a, b, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
    | t1, a, b, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)) ->
        Branch
          (B, t1, a, b, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
    | t1, a, b,
        Branch
          (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi))
        -> Branch
             (B, t1, a, b,
               Branch
                 (v, Branch (B, ve, vj, vk, vl), vb, vc,
                   Branch (B, vf, vg, vh, vi)));;

let rec equal_color x0 x1 = match x0, x1 with R, B -> false
                      | B, R -> false
                      | B, B -> true
                      | R, R -> true;;

let rec bheight
  = function Empty -> zero_nata
    | Branch (c, lt, k, v, rt) ->
        (if equal_color c B then suc (bheight lt) else bheight lt);;

let rec rbt_joinR
  l a b r =
    (if less_eq_nat (bheight l) (bheight r) then Branch (R, l, a, b, r)
      else (match l
             with Branch (R, la, ab, ba, ra) ->
               Branch (R, la, ab, ba, rbt_joinR ra a b r)
             | Branch (B, la, ab, ba, ra) ->
               rbt_baliR la ab ba (rbt_joinR ra a b r)));;

let rec rbt_baliL
  x0 a b t4 = match x0, a, b, t4 with
    Branch (R, Branch (R, t1, ab, bb, t2), aa, ba, t3), a, b, t4 ->
      Branch (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
    | Branch (R, Empty, ab, bb, Branch (R, t2, aa, ba, t3)), a, b, t4 ->
        Branch
          (R, Branch (B, Empty, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
    | Branch
        (R, Branch (B, va, vb, vc, vd), ab, bb, Branch (R, t2, aa, ba, t3)),
        a, b, t4
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), ab, bb, t2), aa, ba,
               Branch (B, t3, a, b, t4))
    | Empty, a, b, t2 -> Branch (B, Empty, a, b, t2)
    | Branch (B, va, vb, vc, vd), a, b, t2 ->
        Branch (B, Branch (B, va, vb, vc, vd), a, b, t2)
    | Branch (v, Empty, vb, vc, Empty), a, b, t2 ->
        Branch (B, Branch (v, Empty, vb, vc, Empty), a, b, t2)
    | Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), a, b, t2 ->
        Branch
          (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), a, b, t2)
    | Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), a, b, t2 ->
        Branch
          (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), a, b, t2)
    | Branch
        (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        a, b, t2
        -> Branch
             (B, Branch
                   (v, Branch (B, vf, vg, vh, vi), vb, vc,
                     Branch (B, ve, vj, vk, vl)),
               a, b, t2);;

let rec rbt_joinL
  l a b r =
    (if less_eq_nat (bheight r) (bheight l) then Branch (R, l, a, b, r)
      else (match r
             with Branch (R, la, ab, ba, ra) ->
               Branch (R, rbt_joinL l a b la, ab, ba, ra)
             | Branch (B, la, ab, ba, ra) ->
               rbt_baliL (rbt_joinL l a b la) ab ba ra));;

let rec rbt_join
  l a b r =
    (let bhl = bheight l in
     let bhr = bheight r in
      (if less_nat bhr bhl then paint B (rbt_joinR l a b r)
        else (if less_nat bhl bhr then paint B (rbt_joinL l a b r)
               else Branch (B, l, a, b, r))));;

let rec rbt_split_comp
  c x1 k = match c, x1, k with c, Empty, k -> (Empty, (None, Empty))
    | c, Branch (uu, l, a, b, r), x ->
        (match c x a with Eq -> (l, (Some b, r))
          | Lt ->
            (let (l1, (beta, l2)) = rbt_split_comp c l x in
              (l1, (beta, rbt_join l2 a b r)))
          | Gt ->
            (let (r1, (beta, r2)) = rbt_split_comp c r x in
              (rbt_join l a b r1, (beta, r2))));;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let rec rbt_comp_union_swap_rec
  c f gamma t1 t2 =
    (let bh1 = bheight t1 in
     let bh2 = bheight t2 in
     let (gammaa, (t2a, (bh2a, (t1a, _)))) =
       (if less_nat bh1 bh2 then (not gamma, (t1, (bh1, (t2, bh2))))
         else (gamma, (t2, (bh2, (t1, bh1)))))
       in
     let fa = (if gammaa then (fun k v va -> f k va v) else f) in
      (if less_nat bh2a (nat_of_integer (Z.of_int 4))
        then folda (rbt_comp_insert_with_key c fa) t2a t1a
        else (match t1a with Empty -> t2a
               | Branch (_, l1, a, b, r1) ->
                 (let (l2, (beta, r2)) = rbt_split_comp c t2a a in
                   rbt_join (rbt_comp_union_swap_rec c f gammaa l1 l2) a
                     (match beta with None -> b | Some ca -> fa a b ca)
                     (rbt_comp_union_swap_rec c f gammaa r1 r2)))));;

let rec rbt_comp_union_with_key
  c f t1 t2 = paint B (rbt_comp_union_swap_rec c f false t1 t2);;

let rec join _A
  xc xd xe =
    Mapping_RBTa
      (rbt_comp_union_with_key (the (ccompare _A)) xc (impl_ofa _A xd)
        (impl_ofa _A xe));;

let rec union _A = foldc _A (inserta _A);;

let rec is_none = function Some x -> false
                  | None -> true;;

let rec filtera
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filtera p xs else filtera p xs);;

let rec inter_list _A
  xb xc =
    Mapping_RBTa
      (fold (fun k -> rbt_comp_insert (the (ccompare _A)) k ())
        (filtera
          (fun x ->
            not (is_none
                  (rbt_comp_lookup (the (ccompare _A)) (impl_ofa _A xb) x)))
          xc)
        Empty);;

let rec apfst f (x, y) = (f x, y);;

let rec map_prod f g (a, b) = (f a, g b);;

let rec divmod_nat
  m n = (let k = integer_of_nat m in
         let l = integer_of_nat n in
          map_prod nat_of_integer nat_of_integer
            (if Z.equal k Z.zero then (Z.zero, Z.zero)
              else (if Z.equal l Z.zero then (Z.zero, k)
                     else (fun k l -> if Z.equal Z.zero l then (Z.zero, l) else
                            Z.div_rem (Z.abs k) (Z.abs l))
                            k l)));;

let rec rbtreeify_g
  n kvs =
    (if equal_nata n zero_nata || equal_nata n one_nat then (Empty, kvs)
      else (let (na, r) = divmod_nat n (nat_of_integer (Z.of_int 2)) in
             (if equal_nata r zero_nata
               then (let (t1, (k, v) :: kvsa) = rbtreeify_g na kvs in
                      apfst (fun a -> Branch (B, t1, k, v, a))
                        (rbtreeify_g na kvsa))
               else (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                      apfst (fun a -> Branch (B, t1, k, v, a))
                        (rbtreeify_g na kvsa)))))
and rbtreeify_f
  n kvs =
    (if equal_nata n zero_nata then (Empty, kvs)
      else (if equal_nata n one_nat
             then (let (k, v) :: kvsa = kvs in
                    (Branch (R, Empty, k, v, Empty), kvsa))
             else (let (na, r) = divmod_nat n (nat_of_integer (Z.of_int 2)) in
                    (if equal_nata r zero_nata
                      then (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                             apfst (fun a -> Branch (B, t1, k, v, a))
                               (rbtreeify_g na kvsa))
                      else (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                             apfst (fun a -> Branch (B, t1, k, v, a))
                               (rbtreeify_f na kvsa))))));;

let rec rbtreeify kvs = fst (rbtreeify_g (suc (size_list kvs)) kvs);;

let rec gen_entries
  kvts x1 = match kvts, x1 with
    kvts, Branch (c, l, k, v, r) -> gen_entries (((k, v), r) :: kvts) l
    | (kv, t) :: kvts, Empty -> kv :: gen_entries kvts t
    | [], Empty -> [];;

let rec entries x = gen_entries [] x;;

let rec filterc _A
  xb xc = Mapping_RBTa (rbtreeify (filtera xb (entries (impl_ofa _A xc))));;

let rec map_filter
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> map_filter f xs
          | Some y -> y :: map_filter f xs);;

let rec map_filter_comp_inter
  c f t1 t2 =
    map_filter
      (fun (k, v) ->
        (match rbt_comp_lookup c t1 k with None -> None
          | Some va -> Some (k, f k va v)))
      (entries t2);;

let rec is_rbt_empty
  t = (match t with Empty -> true | Branch (_, _, _, _, _) -> false);;

let rec rbt_split_min
  = function Empty -> failwith "undefined"
    | Branch (uu, l, a, b, r) ->
        (if is_rbt_empty l then (a, (b, r))
          else (let (aa, (ba, la)) = rbt_split_min l in
                 (aa, (ba, rbt_join la a b r))));;

let rec rbt_join2
  l r = (if is_rbt_empty r then l
          else (let a = rbt_split_min r in
                let (aa, b) = a in
                let (ba, c) = b in
                 rbt_join l aa ba c));;

let rec rbt_comp_inter_swap_rec
  c f gamma t1 t2 =
    (let bh1 = bheight t1 in
     let bh2 = bheight t2 in
     let (gammaa, (t2a, (bh2a, (t1a, _)))) =
       (if less_nat bh1 bh2 then (not gamma, (t1, (bh1, (t2, bh2))))
         else (gamma, (t2, (bh2, (t1, bh1)))))
       in
     let fa = (if gammaa then (fun k v va -> f k va v) else f) in
      (if less_nat bh2a (nat_of_integer (Z.of_int 4))
        then rbtreeify (map_filter_comp_inter c fa t1a t2a)
        else (match t1a with Empty -> Empty
               | Branch (_, l1, a, b, r1) ->
                 (let (l2, (beta, r2)) = rbt_split_comp c t2a a in
                  let l = rbt_comp_inter_swap_rec c f gammaa l1 l2 in
                  let r = rbt_comp_inter_swap_rec c f gammaa r1 r2 in
                   (match beta with None -> rbt_join2 l r
                     | Some ba -> rbt_join l a (fa a b ba) r)))));;

let rec rbt_comp_inter_with_key
  c f t1 t2 = paint B (rbt_comp_inter_swap_rec c f false t1 t2);;

let rec meet _A
  xc xd xe =
    Mapping_RBTa
      (rbt_comp_inter_with_key (the (ccompare _A)) xc (impl_ofa _A xd)
        (impl_ofa _A xe));;

let rec filterb _A xb xc = Abs_dlist (filtera xb (list_of_dlist _A xc));;

let rec inf_set (_A1, _A2)
  g ga = match g, ga with
    RBT_set rbt1, Set_Monad xs ->
      (match ccompare _A2
        with None ->
          failwith "inter RBT_set Set_Monad: ccompare = None"
            (fun _ -> inf_set (_A1, _A2) (RBT_set rbt1) (Set_Monad xs))
        | Some _ -> RBT_set (inter_list _A2 rbt1 xs))
    | RBT_set rbt, DList_set dxs ->
        (match ccompare _A2
          with None ->
            failwith "inter RBT_set DList_set: ccompare = None"
              (fun _ -> inf_set (_A1, _A2) (RBT_set rbt) (DList_set dxs))
          | Some _ ->
            (match ceq _A1
              with None ->
                failwith "inter RBT_set DList_set: ceq = None"
                  (fun _ -> inf_set (_A1, _A2) (RBT_set rbt) (DList_set dxs))
              | Some _ -> RBT_set (inter_list _A2 rbt (list_of_dlist _A1 dxs))))
    | RBT_set rbt1, RBT_set rbt2 ->
        (match ccompare _A2
          with None ->
            failwith "inter RBT_set RBT_set: ccompare = None"
              (fun _ -> inf_set (_A1, _A2) (RBT_set rbt1) (RBT_set rbt2))
          | Some _ -> RBT_set (meet _A2 (fun _ _ -> id) rbt1 rbt2))
    | DList_set dxs1, Set_Monad xs ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set Set_Monad: ceq = None"
              (fun _ -> inf_set (_A1, _A2) (DList_set dxs1) (Set_Monad xs))
          | Some eq -> DList_set (filterb _A1 (list_member eq xs) dxs1))
    | DList_set dxs1, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set DList_set: ceq = None"
              (fun _ -> inf_set (_A1, _A2) (DList_set dxs1) (DList_set dxs2))
          | Some _ -> DList_set (filterb _A1 (memberb _A1 dxs2) dxs1))
    | DList_set dxs, RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "inter DList_set RBT_set: ccompare = None"
              (fun _ -> inf_set (_A1, _A2) (DList_set dxs) (RBT_set rbt))
          | Some _ ->
            (match ceq _A1
              with None ->
                failwith "inter DList_set RBT_set: ceq = None"
                  (fun _ -> inf_set (_A1, _A2) (DList_set dxs) (RBT_set rbt))
              | Some _ -> RBT_set (inter_list _A2 rbt (list_of_dlist _A1 dxs))))
    | Set_Monad xs1, Set_Monad xs2 ->
        (match ceq _A1
          with None ->
            failwith "inter Set_Monad Set_Monad: ceq = None"
              (fun _ -> inf_set (_A1, _A2) (Set_Monad xs1) (Set_Monad xs2))
          | Some eq -> Set_Monad (filtera (list_member eq xs2) xs1))
    | Set_Monad xs, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "inter Set_Monad DList_set: ceq = None"
              (fun _ -> inf_set (_A1, _A2) (Set_Monad xs) (DList_set dxs2))
          | Some eq -> DList_set (filterb _A1 (list_member eq xs) dxs2))
    | Set_Monad xs, RBT_set rbt1 ->
        (match ccompare _A2
          with None ->
            failwith "inter Set_Monad RBT_set: ccompare = None"
              (fun _ -> inf_set (_A1, _A2) (RBT_set rbt1) (Set_Monad xs))
          | Some _ -> RBT_set (inter_list _A2 rbt1 xs))
    | Complement ba, Complement b -> Complement (sup_set (_A1, _A2) ba b)
    | g, RBT_set rbt2 ->
        (match ccompare _A2
          with None ->
            failwith "inter RBT_set2: ccompare = None"
              (fun _ -> inf_set (_A1, _A2) g (RBT_set rbt2))
          | Some _ ->
            RBT_set
              (filterc _A2 (comp (fun x -> member (_A1, _A2) x g) fst) rbt2))
    | RBT_set rbt1, g ->
        (match ccompare _A2
          with None ->
            failwith "inter RBT_set1: ccompare = None"
              (fun _ -> inf_set (_A1, _A2) (RBT_set rbt1) g)
          | Some _ ->
            RBT_set
              (filterc _A2 (comp (fun x -> member (_A1, _A2) x g) fst) rbt1))
    | h, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set2: ceq = None"
              (fun _ -> inf_set (_A1, _A2) h (DList_set dxs2))
          | Some _ ->
            DList_set (filterb _A1 (fun x -> member (_A1, _A2) x h) dxs2))
    | DList_set dxs1, h ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set1: ceq = None"
              (fun _ -> inf_set (_A1, _A2) (DList_set dxs1) h)
          | Some _ ->
            DList_set (filterb _A1 (fun x -> member (_A1, _A2) x h) dxs1))
    | i, Set_Monad xs -> Set_Monad (filtera (fun x -> member (_A1, _A2) x i) xs)
    | Set_Monad xs, i -> Set_Monad (filtera (fun x -> member (_A1, _A2) x i) xs)
    | j, Collect_set a -> Collect_set (fun x -> a x && member (_A1, _A2) x j)
    | Collect_set a, j -> Collect_set (fun x -> a x && member (_A1, _A2) x j)
and sup_set (_A1, _A2)
  ba b = match ba, b with
    ba, Complement b -> Complement (inf_set (_A1, _A2) (uminus_set ba) b)
    | Complement ba, b -> Complement (inf_set (_A1, _A2) ba (uminus_set b))
    | b, Collect_set a -> Collect_set (fun x -> a x || member (_A1, _A2) x b)
    | Collect_set a, b -> Collect_set (fun x -> a x || member (_A1, _A2) x b)
    | Set_Monad xs, Set_Monad ys -> Set_Monad (xs @ ys)
    | DList_set dxs1, Set_Monad ws ->
        (match ceq _A1
          with None ->
            failwith "union DList_set Set_Monad: ceq = None"
              (fun _ -> sup_set (_A1, _A2) (DList_set dxs1) (Set_Monad ws))
          | Some _ -> DList_set (fold (inserta _A1) ws dxs1))
    | Set_Monad ws, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "union Set_Monad DList_set: ceq = None"
              (fun _ -> sup_set (_A1, _A2) (Set_Monad ws) (DList_set dxs2))
          | Some _ -> DList_set (fold (inserta _A1) ws dxs2))
    | RBT_set rbt1, Set_Monad zs ->
        (match ccompare _A2
          with None ->
            failwith "union RBT_set Set_Monad: ccompare = None"
              (fun _ -> sup_set (_A1, _A2) (RBT_set rbt1) (Set_Monad zs))
          | Some _ -> RBT_set (fold (fun k -> insertb _A2 k ()) zs rbt1))
    | Set_Monad zs, RBT_set rbt2 ->
        (match ccompare _A2
          with None ->
            failwith "union Set_Monad RBT_set: ccompare = None"
              (fun _ -> sup_set (_A1, _A2) (Set_Monad zs) (RBT_set rbt2))
          | Some _ -> RBT_set (fold (fun k -> insertb _A2 k ()) zs rbt2))
    | DList_set dxs1, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "union DList_set DList_set: ceq = None"
              (fun _ -> sup_set (_A1, _A2) (DList_set dxs1) (DList_set dxs2))
          | Some _ -> DList_set (union _A1 dxs1 dxs2))
    | DList_set dxs, RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "union DList_set RBT_set: ccompare = None"
              (fun _ -> sup_set (_A1, _A2) (RBT_set rbt) (DList_set dxs))
          | Some _ ->
            (match ceq _A1
              with None ->
                failwith "union DList_set RBT_set: ceq = None"
                  (fun _ -> sup_set (_A1, _A2) (RBT_set rbt) (DList_set dxs))
              | Some _ ->
                RBT_set (foldc _A1 (fun k -> insertb _A2 k ()) dxs rbt)))
    | RBT_set rbt, DList_set dxs ->
        (match ccompare _A2
          with None ->
            failwith "union RBT_set DList_set: ccompare = None"
              (fun _ -> sup_set (_A1, _A2) (RBT_set rbt) (DList_set dxs))
          | Some _ ->
            (match ceq _A1
              with None ->
                failwith "union RBT_set DList_set: ceq = None"
                  (fun _ -> sup_set (_A1, _A2) (RBT_set rbt) (DList_set dxs))
              | Some _ ->
                RBT_set (foldc _A1 (fun k -> insertb _A2 k ()) dxs rbt)))
    | RBT_set rbt1, RBT_set rbt2 ->
        (match ccompare _A2
          with None ->
            failwith "union RBT_set RBT_set: ccompare = None"
              (fun _ -> sup_set (_A1, _A2) (RBT_set rbt1) (RBT_set rbt2))
          | Some _ -> RBT_set (join _A2 (fun _ _ -> id) rbt1 rbt2));;

let rec filter (_A1, _A2) p a = inf_set (_A1, _A2) a (Collect_set p);;

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

let rec p_check (_A1, _A2, _A3, _A4)
  rho = (fun phi a ->
          (match a with Inl aa -> s_check (_A1, _A2, _A3, _A4) rho phi aa
            | Inr aa -> v_check (_A1, _A2, _A3, _A4) rho phi aa));;

let empty : ('a, 'b) alist = Alist [];;

let rec hda (x21 :: x22) = x21;;

let rec hd _A xa = hda (list_of_dlist _A xa);;

let rec tla = function [] -> []
              | x21 :: x22 -> x22;;

let rec tl _A xa = Abs_dlist (tla (list_of_dlist _A xa));;

let rec doAlways
  i a pa p =
    (match (pa, (equal_nata a zero_nata, p))
      with (Inl pb, aa) ->
        (match aa with (true, Inl paa) -> [proofApp (Inl paa) (Inl pb)]
          | (true, Inr (VAlways (_, pc))) -> [Inr (VAlways (i, pc))]
          | (false, Inl (SAlways (_, li, q))) -> [Inl (SAlways (i, li, q))]
          | (false, Inr (VAlways (_, pc))) -> [Inr (VAlways (i, pc))])
      | (Inr pb, aa) ->
        (match aa
          with (true, Inl (SAlways (_, _, _))) -> [Inr (VAlways (i, pb))]
          | (true, Inr (VAlways (_, paa))) ->
            [Inr (VAlways (i, pb)); Inr (VAlways (i, paa))]
          | (false, Inl (SAlways (_, li, q))) -> [Inl (SAlways (i, li, q))]
          | (false, Inr (VAlways (_, pc))) -> [Inr (VAlways (i, pc))]));;

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
    | w, VImpl (p, q) -> suc (plus_nata (s_atm w p) (v_atm w q))
    | w, VIff_sv (p, q) -> suc (plus_nata (s_atm w p) (v_atm w q))
    | w, VIff_vs (p, q) -> suc (plus_nata (v_atm w p) (s_atm w q))
    | w, VOnce_le i -> one_nat
    | w, VOnce (i, li, qs) -> suc (sum_proofs monoid_add_nat (v_atm w) qs)
    | w, VEventually (i, hi, qs) -> suc (sum_proofs monoid_add_nat (v_atm w) qs)
    | w, VHistorically (i, p) -> suc (v_atm w p)
    | w, VAlways (i, p) -> suc (v_atm w p)
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
    | w, SPrev p -> suc (s_atm w p)
    | w, SImplL p -> suc (v_atm w p)
    | w, SImplR q -> suc (s_atm w q)
    | w, SIff_ss (p, q) -> suc (plus_nata (s_atm w p) (s_atm w q))
    | w, SIff_vv (p, q) -> suc (plus_nata (v_atm w p) (v_atm w q))
    | w, SOnce (i, p) -> suc (s_atm w p)
    | w, SEventually (i, p) -> suc (s_atm w p)
    | w, SHistorically (i, li, qs) ->
        suc (sum_proofs monoid_add_nat (s_atm w) qs)
    | w, SHistorically_le i -> one_nat
    | w, SAlways (i, hi, qs) -> suc (sum_proofs monoid_add_nat (s_atm w) qs);;

let rec matm
  w = (fun a -> (match a with Inl aa -> s_atm w aa | Inr aa -> v_atm w aa));;

let rec strmatm x = matm x;;

let rec ratm f p1 p2 = less_eq_nat (strmatm f p1) (strmatm f p2);;

let rec nulla _A xa = null (list_of_dlist _A xa);;

let rec doOnceBase
  i a p =
    (match (p, equal_nata a zero_nata)
      with (Inl pa, true) -> [Inl (SOnce (i, pa))]
      | (Inl _, false) -> [Inr (VOnce (i, i, []))]
      | (Inr pa, true) -> [Inr (VOnce (i, i, [pa]))]
      | (Inr _, false) -> [Inr (VOnce (i, i, []))]);;

let rec conversep p = (fun x y -> p y x);;

let rec rratm w = conversep (ratm w);;

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
    | SImplL p -> v_htp (_A1, _A2) p
    | SImplR q -> s_htp (_A1, _A2) q
    | SIff_ss (p, q) -> max ord_nat (s_htp (_A1, _A2) p) (s_htp (_A1, _A2) q)
    | SIff_vv (p, q) -> max ord_nat (v_htp (_A1, _A2) p) (v_htp (_A1, _A2) q)
    | SOnce (i, p) -> max ord_nat i (s_htp (_A1, _A2) p)
    | SEventually (i, p) -> max ord_nat i (s_htp (_A1, _A2) p)
    | SHistorically (i, li, qs) ->
        max ord_nat (max ord_nat i li)
          (max_proofs ((ceq_sproof _A2), (ccompare_sproof _A1), set_impl_sproof)
            (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
              set_impl_nat)
            (s_htp (_A1, _A2)) qs)
    | SHistorically_le i -> i
    | SAlways (i, hi, qs) ->
        max ord_nat (max ord_nat i (suc hi))
          (max_proofs ((ceq_sproof _A2), (ccompare_sproof _A1), set_impl_sproof)
            (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
              set_impl_nat)
            (s_htp (_A1, _A2)) qs)
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
    | VPrev_zero -> zero_nata
    | VImpl (p, q) -> max ord_nat (s_htp (_A1, _A2) p) (v_htp (_A1, _A2) q)
    | VIff_sv (p, q) -> max ord_nat (s_htp (_A1, _A2) p) (v_htp (_A1, _A2) q)
    | VIff_vs (p, q) -> max ord_nat (v_htp (_A1, _A2) p) (s_htp (_A1, _A2) q)
    | VOnce_le i -> i
    | VOnce (i, li, qs) ->
        max ord_nat (max ord_nat i li)
          (max_proofs ((ceq_vproof _A2), (ccompare_vproof _A1), set_impl_vproof)
            (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
              set_impl_nat)
            (v_htp (_A1, _A2)) qs)
    | VEventually (i, hi, qs) ->
        max ord_nat (max ord_nat i (suc hi))
          (max_proofs ((ceq_vproof _A2), (ccompare_vproof _A1), set_impl_vproof)
            (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
              set_impl_nat)
            (v_htp (_A1, _A2)) qs)
    | VHistorically (i, p) -> max ord_nat i (v_htp (_A1, _A2) p)
    | VAlways (i, p) -> max ord_nat i (v_htp (_A1, _A2) p);;

let zero_enat : enat = Enat zero_nata;;

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
    | SImplL p -> v_ltp (_A1, _A2) p
    | SImplR q -> s_ltp (_A1, _A2) q
    | SIff_ss (p, q) -> min ord_enat (s_ltp (_A1, _A2) p) (s_ltp (_A1, _A2) q)
    | SIff_vv (p, q) -> min ord_enat (v_ltp (_A1, _A2) p) (v_ltp (_A1, _A2) q)
    | SOnce (i, p) -> zero_enat
    | SEventually (i, p) -> min ord_enat (Enat i) (s_ltp (_A1, _A2) p)
    | SHistorically (i, li, qs) -> zero_enat
    | SHistorically_le i -> zero_enat
    | SAlways (i, hi, qs) ->
        min ord_enat (min ord_enat (Enat i) (Enat hi))
          (min_proofs ((ceq_sproof _A2), (ccompare_sproof _A1), set_impl_sproof)
            (ceq_enat, ccompare_enat, infinity_enat, lattice_enat,
              linorder_enat, set_impl_enat)
            (s_ltp (_A1, _A2)) qs)
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
    | VPrev_zero -> zero_enat
    | VImpl (p, q) -> min ord_enat (s_ltp (_A1, _A2) p) (v_ltp (_A1, _A2) q)
    | VIff_sv (p, q) -> min ord_enat (s_ltp (_A1, _A2) p) (v_ltp (_A1, _A2) q)
    | VIff_vs (p, q) -> min ord_enat (v_ltp (_A1, _A2) p) (s_ltp (_A1, _A2) q)
    | VOnce_le i -> zero_enat
    | VOnce (i, li, qs) -> zero_enat
    | VEventually (i, hi, qs) ->
        min ord_enat (min ord_enat (Enat i) (Enat hi))
          (min_proofs ((ceq_vproof _A2), (ccompare_vproof _A1), set_impl_vproof)
            (ceq_enat, ccompare_enat, infinity_enat, lattice_enat,
              linorder_enat, set_impl_enat)
            (v_ltp (_A1, _A2)) qs)
    | VHistorically (i, p) -> zero_enat
    | VAlways (i, p) -> min ord_enat (Enat i) (v_ltp (_A1, _A2) p);;

let rec sorted_wrt p x1 = match p, x1 with p, [] -> true
                     | p, x :: ys -> list_all (p x) ys && sorted_wrt p ys;;

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
    | VImpl (p, q) ->
        suc (max ord_nat (s_depth (_A1, _A2) p) (v_depth (_A1, _A2) q))
    | VIff_sv (p, q) ->
        suc (max ord_nat (s_depth (_A1, _A2) p) (v_depth (_A1, _A2) q))
    | VIff_vs (p, q) ->
        suc (max ord_nat (v_depth (_A1, _A2) p) (s_depth (_A1, _A2) q))
    | VOnce_le i -> one_nat
    | VOnce (i, li, qs) ->
        suc (max_proofs
              ((ceq_vproof _A2), (ccompare_vproof _A1), set_impl_vproof)
              (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
                set_impl_nat)
              (v_depth (_A1, _A2)) qs)
    | VEventually (i, hi, qs) ->
        suc (max_proofs
              ((ceq_vproof _A2), (ccompare_vproof _A1), set_impl_vproof)
              (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
                set_impl_nat)
              (v_depth (_A1, _A2)) qs)
    | VHistorically (i, p) -> suc (v_depth (_A1, _A2) p)
    | VAlways (i, p) -> suc (v_depth (_A1, _A2) p)
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
    | SPrev p -> suc (s_depth (_A1, _A2) p)
    | SImplL p -> suc (v_depth (_A1, _A2) p)
    | SImplR q -> suc (s_depth (_A1, _A2) q)
    | SIff_ss (p, q) ->
        suc (max ord_nat (s_depth (_A1, _A2) p) (s_depth (_A1, _A2) q))
    | SIff_vv (p, q) ->
        suc (max ord_nat (v_depth (_A1, _A2) p) (v_depth (_A1, _A2) q))
    | SOnce (i, p) -> suc (s_depth (_A1, _A2) p)
    | SEventually (i, p) -> suc (s_depth (_A1, _A2) p)
    | SHistorically (i, li, qs) ->
        suc (max_proofs
              ((ceq_sproof _A2), (ccompare_sproof _A1), set_impl_sproof)
              (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
                set_impl_nat)
              (s_depth (_A1, _A2)) qs)
    | SHistorically_le i -> one_nat
    | SAlways (i, hi, qs) ->
        suc (max_proofs
              ((ceq_sproof _A2), (ccompare_sproof _A1), set_impl_sproof)
              (ceq_nat, ccompare_nat, zero_nat, lattice_nat, linorder_nat,
                set_impl_nat)
              (s_depth (_A1, _A2)) qs);;

let rec mdepth (_A1, _A2)
  = (fun a ->
      (match a with Inl aa -> s_depth (_A1, _A2) aa
        | Inr aa -> v_depth (_A1, _A2) aa));;

let rec strmdepth x = mdepth (ccompare_literal, equal_literal) x;;

let rec rdepth p1 p2 = less_eq_nat (strmdepth p1) (strmdepth p2);;

let rec strset x = set (ceq_literal, ccompare_literal, set_impl_literal) x;;

let rec doAlwaysBase
  i a p =
    (match (p, equal_nata a zero_nata)
      with (Inl pa, true) -> [Inl (SAlways (i, i, [pa]))]
      | (Inl _, false) -> [Inl (SAlways (i, i, []))]
      | (Inr pa, true) -> [Inr (VAlways (i, pa))]
      | (Inr _, false) -> [Inl (SAlways (i, i, []))]);;

let rec doEventually
  i a pa p =
    (match (pa, (equal_nata a zero_nata, p))
      with (Inl pb, aa) ->
        (match aa
          with (true, Inl (SEventually (_, paa))) ->
            [Inl (SEventually (i, paa)); Inl (SEventually (i, pb))]
          | (true, Inr (VEventually (_, _, _))) -> [Inl (SEventually (i, pb))]
          | (false, Inl (SEventually (_, pc))) -> [Inl (SEventually (i, pc))]
          | (false, Inr (VEventually (_, hi, q))) ->
            [Inr (VEventually (i, hi, q))])
      | (Inr pb, aa) ->
        (match aa
          with (true, Inl (SEventually (_, pc))) -> [Inl (SEventually (i, pc))]
          | (true, Inr paa) -> [proofApp (Inr paa) (Inr pb)]
          | (false, Inl (SEventually (_, pc))) -> [Inl (SEventually (i, pc))]
          | (false, Inr (VEventually (_, hi, q))) ->
            [Inr (VEventually (i, hi, q))]));;

let rec min_list_wrt r xs = hda (filtera (fun x -> list_all (r x) xs) xs);;

let rec lex_wqo
  wqoa wqo = (fun x y -> wqoa x y && (if wqoa y x then wqo x y else true));;

let rec doHistoricallyBase
  i a p =
    (match (p, equal_nata a zero_nata)
      with (Inl pa, true) -> [Inl (SHistorically (i, i, [pa]))]
      | (Inl _, false) -> [Inl (SHistorically (i, i, []))]
      | (Inr pa, true) -> [Inr (VHistorically (i, pa))]
      | (Inr _, false) -> [Inl (SHistorically (i, i, []))]);;

let rec doEventuallyBase
  i a p =
    (match (p, equal_nata a zero_nata)
      with (Inl pa, true) -> [Inl (SEventually (i, pa))]
      | (Inl _, false) -> [Inr (VEventually (i, i, []))]
      | (Inr pa, true) -> [Inr (VEventually (i, i, [pa]))]
      | (Inr _, false) -> [Inr (VEventually (i, i, []))]);;

let rec projr (Inr x2) = x2;;

let rec projl (Inl x1) = x1;;

let rec doHistorically
  i a pa p =
    (match (pa, (equal_nata a zero_nata, p))
      with (Inl pb, aa) ->
        (match aa with (true, Inl paa) -> [proofApp (Inl paa) (Inl pb)]
          | (true, Inr (VHistorically (_, pc))) -> [Inr (VHistorically (i, pc))]
          | (false, Inl (SHistorically (_, li, q))) ->
            [Inl (SHistorically (i, li, q))]
          | (false, Inr (VHistorically (_, pc))) ->
            [Inr (VHistorically (i, pc))])
      | (Inr pb, aa) ->
        (match aa
          with (true, Inl (SHistorically (_, _, _))) ->
            [Inr (VHistorically (i, pb))]
          | (true, Inr (VHistorically (_, paa))) ->
            [Inr (VHistorically (i, pb)); Inr (VHistorically (i, paa))]
          | (false, Inl (SHistorically (_, li, q))) ->
            [Inl (SHistorically (i, li, q))]
          | (false, Inr (VHistorically (_, pc))) ->
            [Inr (VHistorically (i, pc))]));;

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
    | w, rho, i, Impl (phi, psi) ->
        doImpl (opt_atm w rho i phi) (opt_atm w rho i psi)
    | w, rho, i, Iff (phi, psi) ->
        doIff (opt_atm w rho i phi) (opt_atm w rho i psi)
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
            else doUntilBase ia (left i) p1 p2))
    | w, rho, ia, Once (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VOnce_le ia)]
          else (let p = opt_atm w rho ia phi in
                 (if equal_nata ia zero_nata
                   then doOnceBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doOnce ia (left i) p
                                 (opt_atm w rho (minus_nat ia one_nat)
                                   (Once (subtract
    (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
      (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
        (minus_nat ia one_nat)))
    i,
   phi)))
                          else doOnceBase ia (left i) p))))
    | w, rho, ia, Historically (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inl (SHistorically_le ia)]
          else (let p = opt_atm w rho ia phi in
                 (if equal_nata ia zero_nata
                   then doHistoricallyBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doHistorically ia (left i) p
                                 (opt_atm w rho (minus_nat ia one_nat)
                                   (Historically
                                     (subtract
(minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
  (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
    (minus_nat ia one_nat)))
i,
                                       phi)))
                          else doHistoricallyBase ia (left i) p))))
    | w, rho, ia, Eventually (i, phi) ->
        (let p1 = opt_atm w rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doEventually ia (left i) p1
                   (opt_atm w rho (plus_nata ia one_nat)
                     (Eventually
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doEventuallyBase ia (left i) p1))
    | w, rho, ia, Always (i, phi) ->
        (let p1 = opt_atm w rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doAlways ia (left i) p1
                   (opt_atm w rho (plus_nata ia one_nat)
                     (Always
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doAlwaysBase ia (left i) p1));;

let rec rrdepth x = conversep rdepth x;;

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

let rec is_valid
  x = p_check (ceq_literal, ccompare_literal, equal_literal, set_impl_literal)
        x;;

let rec maxreach (_A1, _A2)
  = (fun a ->
      (match a with Inl aa -> s_htp (_A1, _A2) aa
        | Inr aa -> v_htp (_A1, _A2) aa));;

let rec minreach (_A1, _A2)
  = (fun a ->
      (match a with Inl aa -> s_ltp (_A1, _A2) aa
        | Inr aa -> v_ltp (_A1, _A2) aa));;

let rec progress (_A1, _A2, _A3)
  sigma x1 j = match sigma, x1, j with
    sigma, Until (phi, i, psi), j ->
      (let m =
         minus_nat
           (min ord_nat j
             (suc (min ord_nat (progress (_A1, _A2, _A3) sigma phi j)
                    (progress (_A1, _A2, _A3) sigma psi j))))
           one_nat
         in
        mina (ceq_nat, ccompare_nat, lattice_nat, linorder_nat)
          (filter (ceq_nat, ccompare_nat)
            (fun ia ->
              less_eq_enat
                (Enat (minus_nat (tau (_A1, _A2, _A3) sigma m)
                        (tau (_A1, _A2, _A3) sigma ia)))
                (right i))
            (set (ceq_nat, ccompare_nat, set_impl_nat)
              (upt zero_nata (suc j)))))
    | sigma, Always (i, phi), j ->
        (let m =
           minus_nat
             (min ord_nat j (suc (progress (_A1, _A2, _A3) sigma phi j)))
             one_nat
           in
          mina (ceq_nat, ccompare_nat, lattice_nat, linorder_nat)
            (filter (ceq_nat, ccompare_nat)
              (fun ia ->
                less_eq_enat
                  (Enat (minus_nat (tau (_A1, _A2, _A3) sigma m)
                          (tau (_A1, _A2, _A3) sigma ia)))
                  (right i))
              (set (ceq_nat, ccompare_nat, set_impl_nat)
                (upt zero_nata (suc j)))))
    | sigma, Eventually (i, phi), j ->
        (let m =
           minus_nat
             (min ord_nat j (suc (progress (_A1, _A2, _A3) sigma phi j)))
             one_nat
           in
          mina (ceq_nat, ccompare_nat, lattice_nat, linorder_nat)
            (filter (ceq_nat, ccompare_nat)
              (fun ia ->
                less_eq_enat
                  (Enat (minus_nat (tau (_A1, _A2, _A3) sigma m)
                          (tau (_A1, _A2, _A3) sigma ia)))
                  (right i))
              (set (ceq_nat, ccompare_nat, set_impl_nat)
                (upt zero_nata (suc j)))))
    | sigma, Since (phi, i, psi), j ->
        min ord_nat (progress (_A1, _A2, _A3) sigma phi j)
          (progress (_A1, _A2, _A3) sigma psi j)
    | sigma, Historically (i, phi), j -> progress (_A1, _A2, _A3) sigma phi j
    | sigma, Once (i, phi), j -> progress (_A1, _A2, _A3) sigma phi j
    | sigma, Next (i, phi), j ->
        minus_nat (progress (_A1, _A2, _A3) sigma phi j) one_nat
    | sigma, Prev (i, phi), j ->
        (if equal_nata j zero_nata then zero_nata
          else min ord_nat (suc (progress (_A1, _A2, _A3) sigma phi j)) j)
    | sigma, Iff (phi, psi), j ->
        min ord_nat (progress (_A1, _A2, _A3) sigma phi j)
          (progress (_A1, _A2, _A3) sigma psi j)
    | sigma, Impl (phi, psi), j ->
        min ord_nat (progress (_A1, _A2, _A3) sigma phi j)
          (progress (_A1, _A2, _A3) sigma psi j)
    | sigma, Conj (phi, psi), j ->
        min ord_nat (progress (_A1, _A2, _A3) sigma phi j)
          (progress (_A1, _A2, _A3) sigma psi j)
    | sigma, Disj (phi, psi), j ->
        min ord_nat (progress (_A1, _A2, _A3) sigma phi j)
          (progress (_A1, _A2, _A3) sigma psi j)
    | sigma, Neg phi, j -> progress (_A1, _A2, _A3) sigma phi j
    | sigma, Atom e, j -> j
    | sigma, FF, j -> j
    | sigma, TT, j -> j;;

let rec bounded_future
  = function
    Until (phi, i, psi) ->
      bounded_future phi &&
        (bounded_future psi && not (equal_enat (right i) Infinity_enat))
    | Since (phi, i, psi) -> bounded_future phi && bounded_future psi
    | Always (i, phi) ->
        bounded_future phi && not (equal_enat (right i) Infinity_enat)
    | Eventually (i, phi) ->
        bounded_future phi && not (equal_enat (right i) Infinity_enat)
    | Historically (i, phi) -> bounded_future phi
    | Once (i, phi) -> bounded_future phi
    | Prev (i, phi) -> bounded_future phi
    | Next (i, phi) -> bounded_future phi
    | Neg phi -> bounded_future phi
    | Iff (phi, psi) -> bounded_future phi && bounded_future psi
    | Impl (phi, psi) -> bounded_future phi && bounded_future psi
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
    | rho, i, Impl (phi, psi) ->
        doImpl (opt_depth rho i phi) (opt_depth rho i psi)
    | rho, i, Iff (phi, psi) ->
        doIff (opt_depth rho i phi) (opt_depth rho i psi)
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
            else doUntilBase ia (left i) p1 p2))
    | rho, ia, Once (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VOnce_le ia)]
          else (let p = opt_depth rho ia phi in
                 (if equal_nata ia zero_nata
                   then doOnceBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doOnce ia (left i) p
                                 (opt_depth rho (minus_nat ia one_nat)
                                   (Once (subtract
    (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
      (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
        (minus_nat ia one_nat)))
    i,
   phi)))
                          else doOnceBase ia (left i) p))))
    | rho, ia, Historically (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inl (SHistorically_le ia)]
          else (let p = opt_depth rho ia phi in
                 (if equal_nata ia zero_nata
                   then doHistoricallyBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doHistorically ia (left i) p
                                 (opt_depth rho (minus_nat ia one_nat)
                                   (Historically
                                     (subtract
(minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
  (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
    (minus_nat ia one_nat)))
i,
                                       phi)))
                          else doHistoricallyBase ia (left i) p))))
    | rho, ia, Eventually (i, phi) ->
        (let p1 = opt_depth rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doEventually ia (left i) p1
                   (opt_depth rho (plus_nata ia one_nat)
                     (Eventually
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doEventuallyBase ia (left i) p1))
    | rho, ia, Always (i, phi) ->
        (let p1 = opt_depth rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doAlways ia (left i) p1
                   (opt_depth rho (plus_nata ia one_nat)
                     (Always
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doAlwaysBase ia (left i) p1));;

let rec sprogress
  x = progress (ceq_literal, ccompare_literal, set_impl_literal) x;;

let rec is_opt_atm
  w rho i phi p =
    (if bounded_future phi
      then valid (ceq_literal, ccompare_literal, equal_literal,
                   set_impl_literal)
             rho i phi p &&
             ratm w p (opt_atm w rho i phi)
      else failwith "optimal: not bounded future"
             (fun _ -> is_opt_atm w rho i phi p));;

let rec is_minimal x = is_opt_atm (fun _ -> one_nat) x;;

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

let rec trace_rbt_of_list
  xa = Abs_trace_rbt
         (if sorted_wrt less_eq_nat (map snd xa)
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

let rec opt_flipped_atm
  w rho i phi = min_list_wrt (rratm w) (cand_flipped_atm w rho i phi)
and cand_flipped_atm
  w rho i x3 = match w, rho, i, x3 with w, rho, i, TT -> [Inl (STT i)]
    | w, rho, i, FF -> [Inr (VFF i)]
    | w, rho, i, Atom n ->
        (match
          member (ceq_literal, ccompare_literal) n
            (gamma (ceq_literal, ccompare_literal, set_impl_literal) rho i)
          with true -> [Inl (SAtm (n, i))] | false -> [Inr (VAtm (n, i))])
    | w, rho, i, Disj (phi, psi) ->
        doDisj (opt_flipped_atm w rho i phi) (opt_flipped_atm w rho i psi)
    | w, rho, i, Conj (phi, psi) ->
        doConj (opt_flipped_atm w rho i phi) (opt_flipped_atm w rho i psi)
    | w, rho, i, Impl (phi, psi) ->
        doImpl (opt_flipped_atm w rho i phi) (opt_flipped_atm w rho i psi)
    | w, rho, i, Iff (phi, psi) ->
        doIff (opt_flipped_atm w rho i phi) (opt_flipped_atm w rho i psi)
    | w, rho, i, Neg phi ->
        (let p = opt_flipped_atm w rho i phi in
          (if isl p then [Inr (VNeg (projl p))] else [Inl (SNeg (projr p))]))
    | w, rho, ia, Prev (i, phi) ->
        (if equal_nata ia zero_nata then [Inr VPrev_zero]
          else doPrev ia i
                 (minus_nat
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     ia)
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     (minus_nat ia one_nat)))
                 (opt_flipped_atm w rho (minus_nat ia one_nat) phi))
    | w, rho, ia, Next (i, phi) ->
        doNext ia i
          (minus_nat
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (plus_nata ia one_nat))
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (minus_nat (plus_nata ia one_nat) one_nat)))
          (opt_flipped_atm w rho (plus_nata ia one_nat) phi)
    | w, rho, ia, Since (phi, i, psi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VSince_le ia)]
          else (let p1 = opt_flipped_atm w rho ia phi in
                let p2 = opt_flipped_atm w rho ia psi in
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
                                 (opt_flipped_atm w rho (minus_nat ia one_nat)
                                   (Since
                                     (phi, subtract
     (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
       (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
         (minus_nat ia one_nat)))
     i,
                                       psi)))
                          else doSinceBase ia (left i) p1 p2))))
    | w, rho, ia, Until (phi, i, psi) ->
        (let p1 = opt_flipped_atm w rho ia phi in
         let p2 = opt_flipped_atm w rho ia psi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doUntil ia (left i) p1 p2
                   (opt_flipped_atm w rho (plus_nata ia one_nat)
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
            else doUntilBase ia (left i) p1 p2))
    | w, rho, ia, Once (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VOnce_le ia)]
          else (let p = opt_flipped_atm w rho ia phi in
                 (if equal_nata ia zero_nata
                   then doOnceBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doOnce ia (left i) p
                                 (opt_flipped_atm w rho (minus_nat ia one_nat)
                                   (Once (subtract
    (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
      (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
        (minus_nat ia one_nat)))
    i,
   phi)))
                          else doOnceBase ia (left i) p))))
    | w, rho, ia, Historically (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inl (SHistorically_le ia)]
          else (let p = opt_flipped_atm w rho ia phi in
                 (if equal_nata ia zero_nata
                   then doHistoricallyBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doHistorically ia (left i) p
                                 (opt_flipped_atm w rho (minus_nat ia one_nat)
                                   (Historically
                                     (subtract
(minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
  (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
    (minus_nat ia one_nat)))
i,
                                       phi)))
                          else doHistoricallyBase ia (left i) p))))
    | w, rho, ia, Eventually (i, phi) ->
        (let p1 = opt_flipped_atm w rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doEventually ia (left i) p1
                   (opt_flipped_atm w rho (plus_nata ia one_nat)
                     (Eventually
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doEventuallyBase ia (left i) p1))
    | w, rho, ia, Always (i, phi) ->
        (let p1 = opt_flipped_atm w rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doAlways ia (left i) p1
                   (opt_flipped_atm w rho (plus_nata ia one_nat)
                     (Always
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doAlwaysBase ia (left i) p1));;

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
    | rho, i, Impl (phi, psi) ->
        doImpl (opt_maxmaxreach rho i phi) (opt_maxmaxreach rho i psi)
    | rho, i, Iff (phi, psi) ->
        doIff (opt_maxmaxreach rho i phi) (opt_maxmaxreach rho i psi)
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
            else doUntilBase ia (left i) p1 p2))
    | rho, ia, Once (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VOnce_le ia)]
          else (let p = opt_maxmaxreach rho ia phi in
                 (if equal_nata ia zero_nata
                   then doOnceBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doOnce ia (left i) p
                                 (opt_maxmaxreach rho (minus_nat ia one_nat)
                                   (Once (subtract
    (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
      (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
        (minus_nat ia one_nat)))
    i,
   phi)))
                          else doOnceBase ia (left i) p))))
    | rho, ia, Historically (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inl (SHistorically_le ia)]
          else (let p = opt_maxmaxreach rho ia phi in
                 (if equal_nata ia zero_nata
                   then doHistoricallyBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doHistorically ia (left i) p
                                 (opt_maxmaxreach rho (minus_nat ia one_nat)
                                   (Historically
                                     (subtract
(minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
  (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
    (minus_nat ia one_nat)))
i,
                                       phi)))
                          else doHistoricallyBase ia (left i) p))))
    | rho, ia, Eventually (i, phi) ->
        (let p1 = opt_maxmaxreach rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doEventually ia (left i) p1
                   (opt_maxmaxreach rho (plus_nata ia one_nat)
                     (Eventually
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doEventuallyBase ia (left i) p1))
    | rho, ia, Always (i, phi) ->
        (let p1 = opt_maxmaxreach rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doAlways ia (left i) p1
                   (opt_maxmaxreach rho (plus_nata ia one_nat)
                     (Always
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doAlwaysBase ia (left i) p1));;

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
    | rho, i, Impl (phi, psi) ->
        doImpl (opt_maxminreach rho i phi) (opt_maxminreach rho i psi)
    | rho, i, Iff (phi, psi) ->
        doIff (opt_maxminreach rho i phi) (opt_maxminreach rho i psi)
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
            else doUntilBase ia (left i) p1 p2))
    | rho, ia, Once (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VOnce_le ia)]
          else (let p = opt_maxminreach rho ia phi in
                 (if equal_nata ia zero_nata
                   then doOnceBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doOnce ia (left i) p
                                 (opt_maxminreach rho (minus_nat ia one_nat)
                                   (Once (subtract
    (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
      (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
        (minus_nat ia one_nat)))
    i,
   phi)))
                          else doOnceBase ia (left i) p))))
    | rho, ia, Historically (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inl (SHistorically_le ia)]
          else (let p = opt_maxminreach rho ia phi in
                 (if equal_nata ia zero_nata
                   then doHistoricallyBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doHistorically ia (left i) p
                                 (opt_maxminreach rho (minus_nat ia one_nat)
                                   (Historically
                                     (subtract
(minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
  (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
    (minus_nat ia one_nat)))
i,
                                       phi)))
                          else doHistoricallyBase ia (left i) p))))
    | rho, ia, Eventually (i, phi) ->
        (let p1 = opt_maxminreach rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doEventually ia (left i) p1
                   (opt_maxminreach rho (plus_nata ia one_nat)
                     (Eventually
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doEventuallyBase ia (left i) p1))
    | rho, ia, Always (i, phi) ->
        (let p1 = opt_maxminreach rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doAlways ia (left i) p1
                   (opt_maxminreach rho (plus_nata ia one_nat)
                     (Always
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doAlwaysBase ia (left i) p1));;

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
    | rho, i, Impl (phi, psi) ->
        doImpl (opt_minmaxreach rho i phi) (opt_minmaxreach rho i psi)
    | rho, i, Iff (phi, psi) ->
        doIff (opt_minmaxreach rho i phi) (opt_minmaxreach rho i psi)
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
            else doUntilBase ia (left i) p1 p2))
    | rho, ia, Once (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VOnce_le ia)]
          else (let p = opt_minmaxreach rho ia phi in
                 (if equal_nata ia zero_nata
                   then doOnceBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doOnce ia (left i) p
                                 (opt_minmaxreach rho (minus_nat ia one_nat)
                                   (Once (subtract
    (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
      (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
        (minus_nat ia one_nat)))
    i,
   phi)))
                          else doOnceBase ia (left i) p))))
    | rho, ia, Historically (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inl (SHistorically_le ia)]
          else (let p = opt_minmaxreach rho ia phi in
                 (if equal_nata ia zero_nata
                   then doHistoricallyBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doHistorically ia (left i) p
                                 (opt_minmaxreach rho (minus_nat ia one_nat)
                                   (Historically
                                     (subtract
(minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
  (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
    (minus_nat ia one_nat)))
i,
                                       phi)))
                          else doHistoricallyBase ia (left i) p))))
    | rho, ia, Eventually (i, phi) ->
        (let p1 = opt_minmaxreach rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doEventually ia (left i) p1
                   (opt_minmaxreach rho (plus_nata ia one_nat)
                     (Eventually
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doEventuallyBase ia (left i) p1))
    | rho, ia, Always (i, phi) ->
        (let p1 = opt_minmaxreach rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doAlways ia (left i) p1
                   (opt_minmaxreach rho (plus_nata ia one_nat)
                     (Always
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doAlwaysBase ia (left i) p1));;

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
    | rho, i, Impl (phi, psi) ->
        doImpl (opt_minminreach rho i phi) (opt_minminreach rho i psi)
    | rho, i, Iff (phi, psi) ->
        doIff (opt_minminreach rho i phi) (opt_minminreach rho i psi)
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
            else doUntilBase ia (left i) p1 p2))
    | rho, ia, Once (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VOnce_le ia)]
          else (let p = opt_minminreach rho ia phi in
                 (if equal_nata ia zero_nata
                   then doOnceBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doOnce ia (left i) p
                                 (opt_minminreach rho (minus_nat ia one_nat)
                                   (Once (subtract
    (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
      (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
        (minus_nat ia one_nat)))
    i,
   phi)))
                          else doOnceBase ia (left i) p))))
    | rho, ia, Historically (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inl (SHistorically_le ia)]
          else (let p = opt_minminreach rho ia phi in
                 (if equal_nata ia zero_nata
                   then doHistoricallyBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doHistorically ia (left i) p
                                 (opt_minminreach rho (minus_nat ia one_nat)
                                   (Historically
                                     (subtract
(minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
  (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
    (minus_nat ia one_nat)))
i,
                                       phi)))
                          else doHistoricallyBase ia (left i) p))))
    | rho, ia, Eventually (i, phi) ->
        (let p1 = opt_minminreach rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doEventually ia (left i) p1
                   (opt_minminreach rho (plus_nata ia one_nat)
                     (Eventually
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doEventuallyBase ia (left i) p1))
    | rho, ia, Always (i, phi) ->
        (let p1 = opt_minminreach rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doAlways ia (left i) p1
                   (opt_minminreach rho (plus_nata ia one_nat)
                     (Always
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doAlwaysBase ia (left i) p1));;

let rec opt_flipped_depth
  rho i phi = min_list_wrt rrdepth (cand_flipped_depth rho i phi)
and cand_flipped_depth
  rho i x2 = match rho, i, x2 with rho, i, TT -> [Inl (STT i)]
    | rho, i, FF -> [Inr (VFF i)]
    | rho, i, Atom n ->
        (match
          member (ceq_literal, ccompare_literal) n
            (gamma (ceq_literal, ccompare_literal, set_impl_literal) rho i)
          with true -> [Inl (SAtm (n, i))] | false -> [Inr (VAtm (n, i))])
    | rho, i, Disj (phi, psi) ->
        doDisj (opt_flipped_depth rho i phi) (opt_flipped_depth rho i psi)
    | rho, i, Conj (phi, psi) ->
        doConj (opt_flipped_depth rho i phi) (opt_flipped_depth rho i psi)
    | rho, i, Impl (phi, psi) ->
        doImpl (opt_flipped_depth rho i phi) (opt_flipped_depth rho i psi)
    | rho, i, Iff (phi, psi) ->
        doIff (opt_flipped_depth rho i phi) (opt_flipped_depth rho i psi)
    | rho, i, Neg phi ->
        (let p = opt_flipped_depth rho i phi in
          (if isl p then [Inr (VNeg (projl p))] else [Inl (SNeg (projr p))]))
    | rho, ia, Prev (i, phi) ->
        (if equal_nata ia zero_nata then [Inr VPrev_zero]
          else doPrev ia i
                 (minus_nat
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     ia)
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     (minus_nat ia one_nat)))
                 (opt_flipped_depth rho (minus_nat ia one_nat) phi))
    | rho, ia, Next (i, phi) ->
        doNext ia i
          (minus_nat
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (plus_nata ia one_nat))
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (minus_nat (plus_nata ia one_nat) one_nat)))
          (opt_flipped_depth rho (plus_nata ia one_nat) phi)
    | rho, ia, Since (phi, i, psi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VSince_le ia)]
          else (let p1 = opt_flipped_depth rho ia phi in
                let p2 = opt_flipped_depth rho ia psi in
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
                                 (opt_flipped_depth rho (minus_nat ia one_nat)
                                   (Since
                                     (phi, subtract
     (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
       (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
         (minus_nat ia one_nat)))
     i,
                                       psi)))
                          else doSinceBase ia (left i) p1 p2))))
    | rho, ia, Until (phi, i, psi) ->
        (let p1 = opt_flipped_depth rho ia phi in
         let p2 = opt_flipped_depth rho ia psi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doUntil ia (left i) p1 p2
                   (opt_flipped_depth rho (plus_nata ia one_nat)
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
            else doUntilBase ia (left i) p1 p2))
    | rho, ia, Once (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VOnce_le ia)]
          else (let p = opt_flipped_depth rho ia phi in
                 (if equal_nata ia zero_nata
                   then doOnceBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doOnce ia (left i) p
                                 (opt_flipped_depth rho (minus_nat ia one_nat)
                                   (Once (subtract
    (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
      (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
        (minus_nat ia one_nat)))
    i,
   phi)))
                          else doOnceBase ia (left i) p))))
    | rho, ia, Historically (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inl (SHistorically_le ia)]
          else (let p = opt_flipped_depth rho ia phi in
                 (if equal_nata ia zero_nata
                   then doHistoricallyBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doHistorically ia (left i) p
                                 (opt_flipped_depth rho (minus_nat ia one_nat)
                                   (Historically
                                     (subtract
(minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
  (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
    (minus_nat ia one_nat)))
i,
                                       phi)))
                          else doHistoricallyBase ia (left i) p))))
    | rho, ia, Eventually (i, phi) ->
        (let p1 = opt_flipped_depth rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doEventually ia (left i) p1
                   (opt_flipped_depth rho (plus_nata ia one_nat)
                     (Eventually
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doEventuallyBase ia (left i) p1))
    | rho, ia, Always (i, phi) ->
        (let p1 = opt_flipped_depth rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doAlways ia (left i) p1
                   (opt_flipped_depth rho (plus_nata ia one_nat)
                     (Always
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doAlwaysBase ia (left i) p1));;

let rec is_opt_flipped_atm
  w rho i phi p =
    (if bounded_future phi
      then valid (ceq_literal, ccompare_literal, equal_literal,
                   set_impl_literal)
             rho i phi p &&
             rratm w p (opt_flipped_atm w rho i phi)
      else failwith "optimal: not bounded future"
             (fun _ -> is_opt_flipped_atm w rho i phi p));;

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

let rec is_opt_flipped_depth
  rho i phi p =
    (if bounded_future phi
      then valid (ceq_literal, ccompare_literal, equal_literal,
                   set_impl_literal)
             rho i phi p &&
             rrdepth p (opt_flipped_depth rho i phi)
      else failwith "optimal: not bounded future"
             (fun _ -> is_opt_flipped_depth rho i phi p));;

let rec rlex_atm_minmaxreach w = lex_wqo (ratm w) rminmaxreach;;

let rec opt_lex_atm_minmaxreach
  w rho i phi =
    min_list_wrt (rlex_atm_minmaxreach w) (cand_lex_atm_minmaxreach w rho i phi)
and cand_lex_atm_minmaxreach
  w rho i x3 = match w, rho, i, x3 with w, rho, i, TT -> [Inl (STT i)]
    | w, rho, i, FF -> [Inr (VFF i)]
    | w, rho, i, Atom n ->
        (match
          member (ceq_literal, ccompare_literal) n
            (gamma (ceq_literal, ccompare_literal, set_impl_literal) rho i)
          with true -> [Inl (SAtm (n, i))] | false -> [Inr (VAtm (n, i))])
    | w, rho, i, Disj (phi, psi) ->
        doDisj (opt_lex_atm_minmaxreach w rho i phi)
          (opt_lex_atm_minmaxreach w rho i psi)
    | w, rho, i, Conj (phi, psi) ->
        doConj (opt_lex_atm_minmaxreach w rho i phi)
          (opt_lex_atm_minmaxreach w rho i psi)
    | w, rho, i, Impl (phi, psi) ->
        doImpl (opt_lex_atm_minmaxreach w rho i phi)
          (opt_lex_atm_minmaxreach w rho i psi)
    | w, rho, i, Iff (phi, psi) ->
        doIff (opt_lex_atm_minmaxreach w rho i phi)
          (opt_lex_atm_minmaxreach w rho i psi)
    | w, rho, i, Neg phi ->
        (let p = opt_lex_atm_minmaxreach w rho i phi in
          (if isl p then [Inr (VNeg (projl p))] else [Inl (SNeg (projr p))]))
    | w, rho, ia, Prev (i, phi) ->
        (if equal_nata ia zero_nata then [Inr VPrev_zero]
          else doPrev ia i
                 (minus_nat
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     ia)
                   (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                     (minus_nat ia one_nat)))
                 (opt_lex_atm_minmaxreach w rho (minus_nat ia one_nat) phi))
    | w, rho, ia, Next (i, phi) ->
        doNext ia i
          (minus_nat
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (plus_nata ia one_nat))
            (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
              (minus_nat (plus_nata ia one_nat) one_nat)))
          (opt_lex_atm_minmaxreach w rho (plus_nata ia one_nat) phi)
    | w, rho, ia, Since (phi, i, psi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VSince_le ia)]
          else (let p1 = opt_lex_atm_minmaxreach w rho ia phi in
                let p2 = opt_lex_atm_minmaxreach w rho ia psi in
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
                                 (opt_lex_atm_minmaxreach w rho
                                   (minus_nat ia one_nat)
                                   (Since
                                     (phi, subtract
     (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
       (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
         (minus_nat ia one_nat)))
     i,
                                       psi)))
                          else doSinceBase ia (left i) p1 p2))))
    | w, rho, ia, Until (phi, i, psi) ->
        (let p1 = opt_lex_atm_minmaxreach w rho ia phi in
         let p2 = opt_lex_atm_minmaxreach w rho ia psi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doUntil ia (left i) p1 p2
                   (opt_lex_atm_minmaxreach w rho (plus_nata ia one_nat)
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
            else doUntilBase ia (left i) p1 p2))
    | w, rho, ia, Once (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inr (VOnce_le ia)]
          else (let p = opt_lex_atm_minmaxreach w rho ia phi in
                 (if equal_nata ia zero_nata
                   then doOnceBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doOnce ia (left i) p
                                 (opt_lex_atm_minmaxreach w rho
                                   (minus_nat ia one_nat)
                                   (Once (subtract
    (minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
      (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
        (minus_nat ia one_nat)))
    i,
   phi)))
                          else doOnceBase ia (left i) p))))
    | w, rho, ia, Historically (i, phi) ->
        (if less_nat
              (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
              (plus_nata
                (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
                  zero_nata)
                (left i))
          then [Inl (SHistorically_le ia)]
          else (let p = opt_lex_atm_minmaxreach w rho ia phi in
                 (if equal_nata ia zero_nata
                   then doHistoricallyBase zero_nata zero_nata p
                   else (if less_eq_enat
                              (Enat (minus_nat
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho ia)
                                      (tau
(ceq_literal, ccompare_literal, set_impl_literal) rho (minus_nat ia one_nat))))
                              (right i)
                          then doHistorically ia (left i) p
                                 (opt_lex_atm_minmaxreach w rho
                                   (minus_nat ia one_nat)
                                   (Historically
                                     (subtract
(minus_nat (tau (ceq_literal, ccompare_literal, set_impl_literal) rho ia)
  (tau (ceq_literal, ccompare_literal, set_impl_literal) rho
    (minus_nat ia one_nat)))
i,
                                       phi)))
                          else doHistoricallyBase ia (left i) p))))
    | w, rho, ia, Eventually (i, phi) ->
        (let p1 = opt_lex_atm_minmaxreach w rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doEventually ia (left i) p1
                   (opt_lex_atm_minmaxreach w rho (plus_nata ia one_nat)
                     (Eventually
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doEventuallyBase ia (left i) p1))
    | w, rho, ia, Always (i, phi) ->
        (let p1 = opt_lex_atm_minmaxreach w rho ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (plus_nata ia one_nat))
                        (tau (ceq_literal, ccompare_literal, set_impl_literal)
                          rho (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then doAlways ia (left i) p1
                   (opt_lex_atm_minmaxreach w rho (plus_nata ia one_nat)
                     (Always
                       (subtract
                          (minus_nat
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (plus_nata ia one_nat))
                            (tau (ceq_literal, ccompare_literal,
                                   set_impl_literal)
                              rho (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else doAlwaysBase ia (left i) p1));;

let rec is_opt_lex_atm_minmaxreach
  w rho i phi p =
    (if bounded_future phi
      then valid (ceq_literal, ccompare_literal, equal_literal,
                   set_impl_literal)
             rho i phi p &&
             rlex_atm_minmaxreach w p (opt_lex_atm_minmaxreach w rho i phi)
      else failwith "optimal: not bounded future"
             (fun _ -> is_opt_lex_atm_minmaxreach w rho i phi p));;

end;; (*struct VerifiedExplanator2*)
