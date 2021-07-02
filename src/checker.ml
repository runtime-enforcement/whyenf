module Verified_checker : sig
  type nat
  val integer_of_nat : nat -> Z.t
  type enat = Enat of nat | Infinity_enat
  type i
  type 'a mtl = TT | FF | Atom of 'a | Neg of 'a mtl | Disj of 'a mtl * 'a mtl |
    Conj of 'a mtl * 'a mtl | Next of i * 'a mtl | Prev of i * 'a mtl |
    Since of 'a mtl * i * 'a mtl | Until of 'a mtl * i * 'a mtl
  type 'a set = Set of 'a list | Coset of 'a list
  type 'a sproof = STT of nat | SAtm of 'a * nat | SNeg of 'a vproof |
    SDisjL of 'a sproof | SDisjR of 'a sproof | SConj of 'a sproof * 'a sproof |
    SSince of 'a sproof * 'a sproof list | SUntil of 'a sproof list * 'a sproof
    | SNext of 'a sproof | SPrev of 'a sproof
  and 'a vproof = VFF of nat | VAtm of 'a * nat | VNeg of 'a sproof |
    VDisj of 'a vproof * 'a vproof | VConjL of 'a vproof | VConjR of 'a vproof |
    VSince of nat * 'a vproof * 'a vproof list |
    VUntil of nat * 'a vproof list * 'a vproof |
    VSince_never of nat * 'a vproof list | VUntil_never of nat * 'a vproof list
    | VSince_le of nat | VNext of 'a vproof | VNext_ge of nat | VNext_le of nat
    | VPrev of 'a vproof | VPrev_ge of nat | VPrev_le of nat | VPrev_zero
  type 'a trace
  type ('a, 'b) sum = Inl of 'a | Inr of 'b
  type 'a prefix
  val opt :
    string trace -> nat -> string mtl -> (string sproof, string vproof) sum
  val strs_at : string sproof -> nat
  val strv_at : string vproof -> nat
  val interval : nat -> enat -> i
  val to_trace : (string set * nat) list -> string trace
  val strs_check : string trace -> string mtl -> string sproof -> bool
  val strv_check : string trace -> string mtl -> string vproof -> bool
  val nat_of_integer : Z.t -> nat
end = struct

type nat = Nat of Z.t;;

let rec integer_of_nat (Nat x) = x;;

let rec equal_nata m n = Z.equal (integer_of_nat m) (integer_of_nat n);;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_nat = ({equal = equal_nata} : nat equal);;

let rec less_eq_nat m n = Z.leq (integer_of_nat m) (integer_of_nat n);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec less_nat m n = Z.lt (integer_of_nat m) (integer_of_nat n);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

let preorder_nat = ({ord_preorder = ord_nat} : nat preorder);;

let order_nat = ({preorder_order = preorder_nat} : nat order);;

type 'a linorder = {order_linorder : 'a order};;

let linorder_nat = ({order_linorder = order_nat} : nat linorder);;

let equal_literal = ({equal = (fun a b -> ((a : string) = b))} : string equal);;

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

type enat = Enat of nat | Infinity_enat;;

type i = Abs_I of (nat * enat);;

type 'a mtl = TT | FF | Atom of 'a | Neg of 'a mtl | Disj of 'a mtl * 'a mtl |
  Conj of 'a mtl * 'a mtl | Next of i * 'a mtl | Prev of i * 'a mtl |
  Since of 'a mtl * i * 'a mtl | Until of 'a mtl * i * 'a mtl;;

type num = One | Bit0 of num | Bit1 of num;;

type 'a set = Set of 'a list | Coset of 'a list;;

type 'a sproof = STT of nat | SAtm of 'a * nat | SNeg of 'a vproof |
  SDisjL of 'a sproof | SDisjR of 'a sproof | SConj of 'a sproof * 'a sproof |
  SSince of 'a sproof * 'a sproof list | SUntil of 'a sproof list * 'a sproof |
  SNext of 'a sproof | SPrev of 'a sproof
and 'a vproof = VFF of nat | VAtm of 'a * nat | VNeg of 'a sproof |
  VDisj of 'a vproof * 'a vproof | VConjL of 'a vproof | VConjR of 'a vproof |
  VSince of nat * 'a vproof * 'a vproof list |
  VUntil of nat * 'a vproof list * 'a vproof |
  VSince_never of nat * 'a vproof list | VUntil_never of nat * 'a vproof list |
  VSince_le of nat | VNext of 'a vproof | VNext_ge of nat | VNext_le of nat |
  VPrev of 'a vproof | VPrev_ge of nat | VPrev_le of nat | VPrev_zero;;

type 'a stream = Lazy_stream of 'a stream_lazy Lazy.t
and 'a stream_lazy = SCons_Lazy of 'a * 'a stream;;

type 'a trace = Abs_trace of ('a set * nat) stream;;

type ('a, 'b) sum = Inl of 'a | Inr of 'b;;

type 'a prefix = Abs_prefix of ('a set * nat) list;;

let rec eq _A a b = equal _A a b;;

let zero_nat : nat = Nat Z.zero;;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let one_nat : nat = Nat (Z.of_int 1);;

let rec rep_trace (Abs_trace x) = x;;

let rec snd (x1, x2) = x2;;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec minus_nat
  m n = Nat (max ord_integer Z.zero
              (Z.sub (integer_of_nat m) (integer_of_nat n)));;

let rec unlazy_stream (Lazy_stream uu) = uu;;

let rec stl
  xa = (let SCons_Lazy (_, x1aa) = Lazy.force (unlazy_stream xa) in x1aa);;

let rec shd
  xa = (let SCons_Lazy (x2aa, _) = Lazy.force (unlazy_stream xa) in x2aa);;

let rec snth
  s n = (if equal_nata n zero_nat then shd s
          else snth (stl s) (minus_nat n one_nat));;

let rec tau x = (fun i -> snd (snth (rep_trace x) i));;

let rec etp_rec
  rho t i =
    (if less_eq_nat t (tau rho i) then i
      else etp_rec rho t (plus_nat i one_nat));;

let rec etp rho t = etp_rec rho t zero_nat;;

let rec suc n = plus_nat n one_nat;;

let rec ltp_rec
  rho t i =
    (if less_eq_nat (tau rho (suc i)) t then ltp_rec rho t (plus_nat i one_nat)
      else i);;

let rec ltp
  rho t =
    (if less_nat t (tau rho zero_nat)
      then failwith "LTP: undefined" (fun _ -> ltp rho t)
      else ltp_rec rho t zero_nat);;

let rec upt i j = (if less_nat i j then i :: upt (suc i) j else []);;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec last (x :: xs) = (if null xs then x else last xs);;

let rec s_at
  = function STT n -> n
    | SAtm (uu, n) -> n
    | SNeg vphi -> v_at vphi
    | SDisjL sphi -> s_at sphi
    | SDisjR spsi -> s_at spsi
    | SConj (sphi, spsi) -> s_at sphi
    | SNext sphi -> minus_nat (s_at sphi) one_nat
    | SPrev sphi -> plus_nat (s_at sphi) one_nat
    | SSince (spsi, sphis) ->
        (match sphis with [] -> s_at spsi | _ :: _ -> s_at (last sphis))
    | SUntil (sphis, spsi) ->
        (match sphis with [] -> s_at spsi | x :: _ -> s_at x)
and v_at = function VFF n -> n
           | VAtm (uv, n) -> n
           | VNeg sphi -> s_at sphi
           | VDisj (vphi, vpsi) -> v_at vphi
           | VConjL vphi -> v_at vphi
           | VConjR vpsi -> v_at vpsi
           | VNext vphi -> minus_nat (v_at vphi) one_nat
           | VNext_ge n -> n
           | VNext_le n -> n
           | VPrev vphi -> plus_nat (v_at vphi) one_nat
           | VPrev_ge n -> n
           | VPrev_le n -> n
           | VPrev_zero -> zero_nat
           | VSince (n, vpsi, vphis) -> n
           | VSince_le n -> n
           | VUntil (n, vphis, vpsi) -> n
           | VSince_never (n, vpsis) -> n
           | VUntil_never (n, vpsis) -> n;;

let rec size_list
  x xa1 = match x, xa1 with x, [] -> zero_nat
    | x, x21 :: x22 ->
        plus_nat (plus_nat (x x21) (size_list x x22)) (suc zero_nat);;

let rec size_vproof
  = function VFF x21 -> suc zero_nat
    | VAtm (x221, x222) -> suc zero_nat
    | VNeg x23 -> plus_nat (size_sproof x23) (suc zero_nat)
    | VDisj (x241, x242) ->
        plus_nat (plus_nat (size_vproof x241) (size_vproof x242)) (suc zero_nat)
    | VConjL x25 -> plus_nat (size_vproof x25) (suc zero_nat)
    | VConjR x26 -> plus_nat (size_vproof x26) (suc zero_nat)
    | VSince (x271, x272, x273) ->
        plus_nat (plus_nat (size_list size_vproof x273) (size_vproof x272))
          (suc zero_nat)
    | VUntil (x281, x282, x283) ->
        plus_nat (plus_nat (size_list size_vproof x282) (size_vproof x283))
          (suc zero_nat)
    | VSince_never (x291, x292) ->
        plus_nat (size_list size_vproof x292) (suc zero_nat)
    | VUntil_never (x2101, x2102) ->
        plus_nat (size_list size_vproof x2102) (suc zero_nat)
    | VSince_le x211 -> suc zero_nat
    | VNext x212 -> plus_nat (size_vproof x212) (suc zero_nat)
    | VNext_ge x213 -> suc zero_nat
    | VNext_le x214 -> suc zero_nat
    | VPrev x215 -> plus_nat (size_vproof x215) (suc zero_nat)
    | VPrev_ge x216 -> suc zero_nat
    | VPrev_le x217 -> suc zero_nat
    | VPrev_zero -> suc zero_nat
and size_sproof
  = function STT x11 -> suc zero_nat
    | SAtm (x121, x122) -> suc zero_nat
    | SNeg x13 -> plus_nat (size_vproof x13) (suc zero_nat)
    | SDisjL x14 -> plus_nat (size_sproof x14) (suc zero_nat)
    | SDisjR x15 -> plus_nat (size_sproof x15) (suc zero_nat)
    | SConj (x161, x162) ->
        plus_nat (plus_nat (size_sproof x161) (size_sproof x162)) (suc zero_nat)
    | SSince (x171, x172) ->
        plus_nat (plus_nat (size_list size_sproof x172) (size_sproof x171))
          (suc zero_nat)
    | SUntil (x181, x182) ->
        plus_nat (plus_nat (size_list size_sproof x181) (size_sproof x182))
          (suc zero_nat)
    | SNext x19 -> plus_nat (size_sproof x19) (suc zero_nat)
    | SPrev x110 -> plus_nat (size_sproof x110) (suc zero_nat);;

let rec size = function Inl p -> size_sproof p
               | Inr p -> size_vproof p;;

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

let rec less_eq_enat q x1 = match q, x1 with Infinity_enat, Enat n -> false
                       | q, Infinity_enat -> true
                       | Enat m, Enat n -> less_eq_nat m n;;

let rec rep_I (Abs_I x) = x;;

let rec right x = snd (rep_I x);;

let rec fst (x1, x2) = x1;;

let rec left x = fst (rep_I x);;

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

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec member _A
  x xa1 = match x, xa1 with x, Coset xs -> not (membera _A xs x)
    | x, Set xs -> membera _A xs x;;

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
          | (Inr (VSince_never (i, p1)), Inr ra) ->
            Inr (VSince_never (suc i, p1 @ [ra]))
          | (Inr (VUntil_never (i, p1)), Inr ra) ->
            Inr (VUntil_never (minus_nat i one_nat, ra :: p1)));;

let rec doSince
  i a p1 p2 p =
    (match (p1, (p2, (equal_nata a zero_nat, p)))
      with (Inl p1a, (Inl aa, (true, Inl pa))) ->
        [proofApp (Inl pa) (Inl p1a); Inl (SSince (aa, []))]
      | (Inl _, (Inl aa, (true, Inr (VSince (_, _, _))))) ->
        [Inl (SSince (aa, []))]
      | (Inl _, (Inl aa, (true, Inr (VSince_never (_, _))))) ->
        [Inl (SSince (aa, []))]
      | (Inl p1a, (Inl _, (false, Inl pa))) -> [proofApp (Inl pa) (Inl p1a)]
      | (Inl _, (Inl _, (false, Inr (VSince (_, q1, q2))))) ->
        [Inr (VSince (i, q1, q2))]
      | (Inl _, (Inl _, (false, Inr (VSince_never (_, q))))) ->
        [Inr (VSince_never (i, q))]
      | (Inl p1a, (Inr _, (true, Inl pa))) -> [proofApp (Inl pa) (Inl p1a)]
      | (Inl _, (Inr p2a, (true, Inr (VSince (_, _, _))))) ->
        [proofApp p (Inr p2a)]
      | (Inl _, (Inr p2a, (true, Inr (VSince_never (_, _))))) ->
        [proofApp p (Inr p2a)]
      | (Inl p1a, (Inr _, (false, Inl pa))) -> [proofApp (Inl pa) (Inl p1a)]
      | (Inl _, (Inr _, (false, Inr (VSince (_, q1, q2))))) ->
        [Inr (VSince (i, q1, q2))]
      | (Inl _, (Inr _, (false, Inr (VSince_never (_, q))))) ->
        [Inr (VSince_never (i, q))]
      | (Inr _, (Inl aa, (true, Inl _))) -> [Inl (SSince (aa, []))]
      | (Inr _, (Inl aa, (true, Inr (VSince (_, _, _))))) ->
        [Inl (SSince (aa, []))]
      | (Inr _, (Inl aa, (true, Inr (VSince_never (_, _))))) ->
        [Inl (SSince (aa, []))]
      | (Inr p1a, (Inl _, (false, Inl _))) -> [Inr (VSince (i, p1a, []))]
      | (Inr p1a, (Inl _, (false, Inr (VSince (_, q1, q2))))) ->
        [Inr (VSince (i, p1a, [])); Inr (VSince (i, q1, q2))]
      | (Inr p1a, (Inl _, (false, Inr (VSince_never (_, q))))) ->
        [Inr (VSince (i, p1a, [])); Inr (VSince_never (i, q))]
      | (Inr p1a, (Inr p2a, (true, Inl _))) -> [Inr (VSince (i, p1a, [p2a]))]
      | (Inr p1a, (Inr p2a, (true, Inr (VSince (_, _, _))))) ->
        [Inr (VSince (i, p1a, [p2a])); proofApp p (Inr p2a)]
      | (Inr p1a, (Inr p2a, (true, Inr (VSince_never (_, _))))) ->
        [Inr (VSince (i, p1a, [p2a])); proofApp p (Inr p2a)]
      | (Inr p1a, (Inr _, (false, Inl _))) -> [Inr (VSince (i, p1a, []))]
      | (Inr p1a, (Inr _, (false, Inr (VSince (_, q1, q2))))) ->
        [Inr (VSince (i, p1a, [])); Inr (VSince (i, q1, q2))]
      | (Inr p1a, (Inr _, (false, Inr (VSince_never (_, q))))) ->
        [Inr (VSince (i, p1a, [])); Inr (VSince_never (i, q))]);;

let rec doUntil
  i a p1 p2 p =
    (match (p1, (p2, (equal_nata a zero_nat, p)))
      with (Inl p1a, (Inl aa, (true, Inl (SUntil (_, _))))) ->
        [proofApp p (Inl p1a); Inl (SUntil ([], aa))]
      | (Inl _, (Inl aa, (true, Inr (VUntil (_, _, _))))) ->
        [Inl (SUntil ([], aa))]
      | (Inl _, (Inl aa, (true, Inr (VUntil_never (_, _))))) ->
        [Inl (SUntil ([], aa))]
      | (Inl p1a, (Inl _, (false, Inl (SUntil (_, _))))) ->
        [proofApp p (Inl p1a)]
      | (Inl _, (Inl _, (false, Inr (VUntil (_, q1, q2))))) ->
        [Inr (VUntil (i, q1, q2))]
      | (Inl _, (Inl _, (false, Inr (VUntil_never (_, q))))) ->
        [Inr (VUntil_never (i, q))]
      | (Inl p1a, (Inr _, (true, Inl (SUntil (_, _))))) ->
        [proofApp p (Inl p1a)]
      | (Inl _, (Inr p2a, (true, Inr (VUntil (_, _, _))))) ->
        [proofApp p (Inr p2a)]
      | (Inl _, (Inr p2a, (true, Inr (VUntil_never (_, _))))) ->
        [proofApp p (Inr p2a)]
      | (Inl p1a, (Inr _, (false, Inl (SUntil (_, _))))) ->
        [proofApp p (Inl p1a)]
      | (Inl _, (Inr _, (false, Inr (VUntil (_, q1, q2))))) ->
        [Inr (VUntil (i, q1, q2))]
      | (Inl _, (Inr _, (false, Inr (VUntil_never (_, q))))) ->
        [Inr (VUntil_never (i, q))]
      | (Inr _, (Inl aa, (true, Inl (SUntil (_, _))))) ->
        [Inl (SUntil ([], aa))]
      | (Inr _, (Inl aa, (true, Inr (VUntil (_, _, _))))) ->
        [Inl (SUntil ([], aa))]
      | (Inr _, (Inl aa, (true, Inr (VUntil_never (_, _))))) ->
        [Inl (SUntil ([], aa))]
      | (Inr p1a, (Inl _, (false, Inl (SUntil (_, _))))) ->
        [Inr (VUntil (i, [], p1a))]
      | (Inr p1a, (Inl _, (false, Inr (VUntil (_, q1, q2))))) ->
        [Inr (VUntil (i, [], p1a)); Inr (VUntil (i, q1, q2))]
      | (Inr p1a, (Inl _, (false, Inr (VUntil_never (_, q))))) ->
        [Inr (VUntil (i, [], p1a)); Inr (VUntil_never (i, q))]
      | (Inr p1a, (Inr p2a, (true, Inl (SUntil (_, _))))) ->
        [Inr (VUntil (i, [p2a], p1a))]
      | (Inr p1a, (Inr p2a, (true, Inr (VUntil (_, _, _))))) ->
        [Inr (VUntil (i, [p2a], p1a)); proofApp p (Inr p2a)]
      | (Inr p1a, (Inr p2a, (true, Inr (VUntil_never (_, _))))) ->
        [Inr (VUntil (i, [p2a], p1a)); proofApp p (Inr p2a)]
      | (Inr p1a, (Inr _, (false, Inl (SUntil (_, _))))) ->
        [Inr (VUntil (i, [], p1a))]
      | (Inr p1a, (Inr _, (false, Inr (VUntil (_, q1, q2))))) ->
        [Inr (VUntil (i, [], p1a)); Inr (VUntil (i, q1, q2))]
      | (Inr p1a, (Inr _, (false, Inr (VUntil_never (_, q))))) ->
        [Inr (VUntil (i, [], p1a)); Inr (VUntil_never (i, q))]);;

let rec equal_list _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_list _A x22 y22
    | [], [] -> true;;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec gamma x = (fun i -> fst (snth (rep_trace x) i));;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec less_enat x0 q = match x0, q with Infinity_enat, q -> false
                    | Enat m, Infinity_enat -> true
                    | Enat m, Enat n -> less_nat m n;;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec s_check _A
  rho x1 p = match rho, x1, p with rho, Until (xa, xaa, xb), SPrev x -> false
    | rho, Until (xa, xaa, xb), SNext x -> false
    | rho, Until (xb, xaa, xba), SUntil (xa, x) ->
        (let i = s_at (SUntil (xa, x)) in
         let j = s_at x in
          less_eq_nat i j &&
            (less_eq_nat (left xaa) (minus_nat (tau rho j) (tau rho i)) &&
               less_eq_enat (Enat (minus_nat (tau rho j) (tau rho i)))
                 (right xaa) &&
              (equal_list equal_nat (map s_at xa) (upt i j) &&
                (s_check _A rho xba x && list_all (s_check _A rho xb) xa))))
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
            (less_eq_nat (left xaa) (minus_nat (tau rho i) (tau rho j)) &&
               less_eq_enat (Enat (minus_nat (tau rho i) (tau rho j)))
                 (right xaa) &&
              (equal_list equal_nat (map s_at x) (upt (suc j) (suc i)) &&
                (s_check _A rho xba xa && list_all (s_check _A rho xb) x))))
    | rho, Since (xb, xaa, xba), SConj (xa, x) -> false
    | rho, Since (xa, xaa, xb), SDisjR x -> false
    | rho, Since (xa, xaa, xb), SDisjL x -> false
    | rho, Since (xa, xaa, xb), SNeg x -> false
    | rho, Since (xb, xaa, xba), SAtm (xa, x) -> false
    | rho, Since (xa, xaa, xb), STT x -> false
    | rho, Prev (xa, xaa), SPrev x ->
        (let j = s_at x in
         let i = s_at (SPrev x) in
          less_nat zero_nat i &&
            (equal_nata i (plus_nat j one_nat) &&
              (less_eq_nat (left xa) (minus_nat (tau rho i) (tau rho j)) &&
                 less_eq_enat (Enat (minus_nat (tau rho i) (tau rho j)))
                   (right xa) &&
                s_check _A rho xaa x)))
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
          equal_nata j (plus_nat i one_nat) &&
            (less_eq_nat (left xa)
               (minus_nat (tau rho j) (tau rho (minus_nat j one_nat))) &&
               less_eq_enat
                 (Enat (minus_nat (tau rho j) (tau rho (minus_nat j one_nat))))
                 (right xa) &&
              s_check _A rho xaa x))
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
        s_check _A rho xb xa &&
          (s_check _A rho xaa x && equal_nata (s_at xa) (s_at x))
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
    | rho, Disj (xa, xaa), SDisjR x -> s_check _A rho xaa x
    | rho, Disj (xa, xaa), SDisjL x -> s_check _A rho xa x
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
    | rho, Neg xa, SNeg x -> v_check _A rho xa x
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
    | rho, Atom xb, SAtm (xa, x) -> eq _A xb xa && member _A xb (gamma rho x)
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
    | rho, TT, STT x -> true
and v_check _A
  rho x1 p = match rho, x1, p with
    rho, Until (xb, xa, x), p ->
      (match p with VFF _ -> false | VAtm (_, _) -> false | VNeg _ -> false
        | VDisj (_, _) -> false | VConjL _ -> false | VConjR _ -> false
        | VSince (_, _, _) -> false
        | VUntil (i, vpsis, vphi) ->
          (let j = v_at vphi in
            less_eq_nat i j &&
              (less_eq_nat j
                 (ltp rho
                   (match right xa with Enat a -> plus_nat (tau rho i) a
                     | Infinity_enat -> zero_nat)) &&
                (equal_list equal_nat (map v_at vpsis)
                   (upt (max ord_nat i
                          (etp rho (plus_nat (tau rho i) (left xa))))
                     (suc j)) &&
                  (v_check _A rho xb vphi &&
                    list_all (v_check _A rho x) vpsis))))
        | VSince_never (_, _) -> false
        | VUntil_never (i, vpsis) ->
          (let j =
             ltp rho
               (match right xa with Enat a -> plus_nat (tau rho i) a
                 | Infinity_enat -> zero_nat)
             in
            equal_list equal_nat (map v_at vpsis)
              (upt (max ord_nat i (etp rho (plus_nat (tau rho i) (left xa))))
                (suc j)) &&
              list_all (v_check _A rho x) vpsis)
        | VSince_le _ -> false | VNext _ -> false | VNext_ge _ -> false
        | VNext_le _ -> false | VPrev _ -> false | VPrev_ge _ -> false
        | VPrev_le _ -> false | VPrev_zero -> false)
    | rho, Since (xb, xa, x), p ->
        (match p with VFF _ -> false | VAtm (_, _) -> false | VNeg _ -> false
          | VDisj (_, _) -> false | VConjL _ -> false | VConjR _ -> false
          | VSince (i, vphi, vpsis) ->
            (let j = v_at vphi in
              less_eq_nat
                (etp rho
                  (match right xa with Enat a -> minus_nat (tau rho i) a
                    | Infinity_enat -> zero_nat))
                j &&
                (less_eq_nat j i &&
                  (less_eq_nat (plus_nat (tau rho zero_nat) (left xa))
                     (tau rho i) &&
                    (equal_list equal_nat (map v_at vpsis)
                       (upt j
                         (suc (min ord_nat i
                                (ltp rho
                                  (minus_nat (tau rho i) (left xa)))))) &&
                      (v_check _A rho xb vphi &&
                        list_all (v_check _A rho x) vpsis)))))
          | VUntil (_, _, _) -> false
          | VSince_never (i, vpsis) ->
            (let j =
               etp rho
                 (match right xa with Enat a -> minus_nat (tau rho i) a
                   | Infinity_enat -> zero_nat)
               in
              less_eq_nat (plus_nat (tau rho zero_nat) (left xa)) (tau rho i) &&
                (equal_list equal_nat (map v_at vpsis)
                   (upt j
                     (suc (min ord_nat i
                            (ltp rho (minus_nat (tau rho i) (left xa)))))) &&
                  list_all (v_check _A rho x) vpsis))
          | VUntil_never (_, _) -> false
          | VSince_le i ->
            less_nat (tau rho i) (plus_nat (tau rho zero_nat) (left xa))
          | VNext _ -> false | VNext_ge _ -> false | VNext_le _ -> false
          | VPrev _ -> false | VPrev_ge _ -> false | VPrev_le _ -> false
          | VPrev_zero -> false)
    | rho, Prev (xa, x), p ->
        (match p with VFF _ -> false | VAtm (_, _) -> false | VNeg _ -> false
          | VDisj (_, _) -> false | VConjL _ -> false | VConjR _ -> false
          | VSince (_, _, _) -> false | VUntil (_, _, _) -> false
          | VSince_never (_, _) -> false | VUntil_never (_, _) -> false
          | VSince_le _ -> false | VNext _ -> false | VNext_ge _ -> false
          | VNext_le _ -> false
          | VPrev vphi ->
            (let j = v_at vphi in
             let i = v_at (VPrev vphi) in
              less_nat zero_nat i &&
                (equal_nata i (plus_nat j one_nat) && v_check _A rho x vphi))
          | VPrev_ge i ->
            less_nat zero_nat i &&
              less_enat (right xa)
                (Enat (minus_nat (tau rho i) (tau rho (minus_nat i one_nat))))
          | VPrev_le i ->
            less_nat zero_nat i &&
              less_nat (minus_nat (tau rho i) (tau rho (minus_nat i one_nat)))
                (left xa)
          | VPrev_zero -> equal_nata (v_at VPrev_zero) zero_nat)
    | rho, Next (xa, x), p ->
        (match p with VFF _ -> false | VAtm (_, _) -> false | VNeg _ -> false
          | VDisj (_, _) -> false | VConjL _ -> false | VConjR _ -> false
          | VSince (_, _, _) -> false | VUntil (_, _, _) -> false
          | VSince_never (_, _) -> false | VUntil_never (_, _) -> false
          | VSince_le _ -> false
          | VNext vphi ->
            (let j = v_at vphi in
             let i = v_at (VNext vphi) in
              equal_nata j (plus_nat i one_nat) && v_check _A rho x vphi)
          | VNext_ge i ->
            less_enat (right xa)
              (Enat (minus_nat (tau rho (plus_nat i one_nat))
                      (tau rho (minus_nat (plus_nat i one_nat) one_nat))))
          | VNext_le i ->
            less_nat
              (minus_nat (tau rho (plus_nat i one_nat))
                (tau rho (minus_nat (plus_nat i one_nat) one_nat)))
              (left xa)
          | VPrev _ -> false | VPrev_ge _ -> false | VPrev_le _ -> false
          | VPrev_zero -> false)
    | rho, Conj (xa, x), p ->
        (match p with VFF _ -> false | VAtm (_, _) -> false | VNeg _ -> false
          | VDisj (_, _) -> false | VConjL a -> v_check _A rho xa a
          | VConjR a -> v_check _A rho x a | VSince (_, _, _) -> false
          | VUntil (_, _, _) -> false | VSince_never (_, _) -> false
          | VUntil_never (_, _) -> false | VSince_le _ -> false
          | VNext _ -> false | VNext_ge _ -> false | VNext_le _ -> false
          | VPrev _ -> false | VPrev_ge _ -> false | VPrev_le _ -> false
          | VPrev_zero -> false)
    | rho, Disj (xa, x), p ->
        (match p with VFF _ -> false | VAtm (_, _) -> false | VNeg _ -> false
          | VDisj (vphi, vpsi) ->
            v_check _A rho xa vphi &&
              (v_check _A rho x vpsi && equal_nata (v_at vphi) (v_at vpsi))
          | VConjL _ -> false | VConjR _ -> false | VSince (_, _, _) -> false
          | VUntil (_, _, _) -> false | VSince_never (_, _) -> false
          | VUntil_never (_, _) -> false | VSince_le _ -> false
          | VNext _ -> false | VNext_ge _ -> false | VNext_le _ -> false
          | VPrev _ -> false | VPrev_ge _ -> false | VPrev_le _ -> false
          | VPrev_zero -> false)
    | rho, Neg x, p ->
        (match p with VFF _ -> false | VAtm (_, _) -> false
          | VNeg a -> s_check _A rho x a | VDisj (_, _) -> false
          | VConjL _ -> false | VConjR _ -> false | VSince (_, _, _) -> false
          | VUntil (_, _, _) -> false | VSince_never (_, _) -> false
          | VUntil_never (_, _) -> false | VSince_le _ -> false
          | VNext _ -> false | VNext_ge _ -> false | VNext_le _ -> false
          | VPrev _ -> false | VPrev_ge _ -> false | VPrev_le _ -> false
          | VPrev_zero -> false)
    | rho, Atom x, p ->
        (match p with VFF _ -> false
          | VAtm (b, i) -> eq _A x b && not (member _A x (gamma rho i))
          | VNeg _ -> false | VDisj (_, _) -> false | VConjL _ -> false
          | VConjR _ -> false | VSince (_, _, _) -> false
          | VUntil (_, _, _) -> false | VSince_never (_, _) -> false
          | VUntil_never (_, _) -> false | VSince_le _ -> false
          | VNext _ -> false | VNext_ge _ -> false | VNext_le _ -> false
          | VPrev _ -> false | VPrev_ge _ -> false | VPrev_le _ -> false
          | VPrev_zero -> false)
    | rho, FF, p ->
        (match p with VFF _ -> true | VAtm (_, _) -> false | VNeg _ -> false
          | VDisj (_, _) -> false | VConjL _ -> false | VConjR _ -> false
          | VSince (_, _, _) -> false | VUntil (_, _, _) -> false
          | VSince_never (_, _) -> false | VUntil_never (_, _) -> false
          | VSince_le _ -> false | VNext _ -> false | VNext_ge _ -> false
          | VNext_le _ -> false | VPrev _ -> false | VPrev_ge _ -> false
          | VPrev_le _ -> false | VPrev_zero -> false)
    | rho, TT, p -> false;;

let rec hd (x21 :: x22) = x21;;

let rec min_list_wrt r xs = hd (filter (fun x -> list_all (r x) xs) xs);;

let rec equal_enat x0 x1 = match x0, x1 with Enat nat, Infinity_enat -> false
                     | Infinity_enat, Enat nat -> false
                     | Enat nata, Enat nat -> equal_nata nata nat
                     | Infinity_enat, Infinity_enat -> true;;

let rec projr (Inr x2) = x2;;

let rec projl (Inl x1) = x1;;

let zero_enat : enat = Enat zero_nat;;

let rec minus_enat x0 n = match x0, n with Enat a, Infinity_enat -> zero_enat
                     | Infinity_enat, n -> Infinity_enat
                     | Enat a, Enat b -> Enat (minus_nat a b);;

let rec subtract
  xb xc =
    Abs_I (let (i, j) = rep_I xc in (minus_nat i xb, minus_enat j (Enat xb)));;

let rec isl = function Inl x1 -> true
              | Inr x2 -> false;;

let rec doUntilBase
  i a p1 p2 =
    (match (p1, (p2, equal_nata a zero_nat))
      with (Inl _, (Inl p2a, true)) -> [Inl (SUntil ([], p2a))]
      | (Inl _, (Inl _, false)) -> [Inr (VUntil_never (i, []))]
      | (Inl _, (Inr ba, true)) -> [Inr (VUntil_never (i, [ba]))]
      | (Inl _, (Inr _, false)) -> [Inr (VUntil_never (i, []))]
      | (Inr _, (Inl p2a, true)) -> [Inl (SUntil ([], p2a))]
      | (Inr ba, (Inl _, false)) ->
        [Inr (VUntil (i, [], ba)); Inr (VUntil_never (i, []))]
      | (Inr ba, (Inr baa, true)) ->
        [Inr (VUntil (i, [baa], ba)); Inr (VUntil_never (i, [baa]))]
      | (Inr ba, (Inr _, false)) ->
        [Inr (VUntil (i, [], ba)); Inr (VUntil_never (i, []))]);;

let rec doSinceBase
  i a p1 p2 =
    (match (p1, (p2, equal_nata a zero_nat))
      with (Inl _, (Inl p2a, true)) -> [Inl (SSince (p2a, []))]
      | (Inl _, (Inl _, false)) -> [Inr (VSince_never (i, []))]
      | (Inl _, (Inr ba, true)) -> [Inr (VSince_never (i, [ba]))]
      | (Inl _, (Inr _, false)) -> [Inr (VSince_never (i, []))]
      | (Inr _, (Inl p2a, true)) -> [Inl (SSince (p2a, []))]
      | (Inr ba, (Inl _, false)) ->
        [Inr (VSince (i, ba, [])); Inr (VSince_never (i, []))]
      | (Inr ba, (Inr baa, true)) ->
        [Inr (VSince (i, ba, [baa])); Inr (VSince_never (i, [baa]))]
      | (Inr ba, (Inr _, false)) ->
        [Inr (VSince (i, ba, [])); Inr (VSince_never (i, []))]);;

let rec opt
  rho i phi =
    min_list_wrt (fun p q -> less_eq_nat (size p) (size q)) (cand rho i phi)
and cand
  rho i x2 = match rho, i, x2 with rho, i, TT -> [Inl (STT i)]
    | rho, i, FF -> [Inr (VFF i)]
    | rho, i, Atom n ->
        (match member equal_literal n (gamma rho i)
          with true -> [Inl (SAtm (n, i))] | false -> [Inr (VAtm (n, i))])
    | rho, i, Disj (phi, psi) -> doDisj (opt rho i phi) (opt rho i psi)
    | rho, i, Conj (phi, psi) -> doConj (opt rho i phi) (opt rho i psi)
    | rho, i, Neg phi ->
        (let p = opt rho i phi in
          (if isl p then [Inr (VNeg (projl p))] else [Inl (SNeg (projr p))]))
    | rho, ia, Prev (i, phi) ->
        (if equal_nata ia zero_nat then [Inr VPrev_zero]
          else doPrev ia i
                 (minus_nat (tau rho ia) (tau rho (minus_nat ia one_nat)))
                 (opt rho (minus_nat ia one_nat) phi))
    | rho, ia, Next (i, phi) ->
        doNext ia i
          (minus_nat (tau rho (plus_nat ia one_nat))
            (tau rho (minus_nat (plus_nat ia one_nat) one_nat)))
          (opt rho (plus_nat ia one_nat) phi)
    | rho, ia, Since (phi, i, psi) ->
        (if less_nat (tau rho ia) (plus_nat (tau rho zero_nat) (left i))
          then [Inr (VSince_le ia)]
          else (let p1 = opt rho ia phi in
                let p2 = opt rho ia psi in
                 (if equal_nata ia zero_nat
                   then doSinceBase zero_nat zero_nat p1 p2
                   else (if less_eq_enat
                              (Enat (minus_nat (tau rho ia)
                                      (tau rho (minus_nat ia one_nat))))
                              (right i)
                          then doSince ia (left i) p1 p2
                                 (opt rho (minus_nat ia one_nat)
                                   (Since
                                     (phi, subtract
     (minus_nat (tau rho ia) (tau rho (minus_nat ia one_nat))) i,
                                       psi)))
                          else doSinceBase ia (left i) p1 p2))))
    | rho, ia, Until (phi, i, psi) ->
        (let p1 = opt rho ia phi in
         let p2 = opt rho ia psi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat (tau rho (plus_nat ia one_nat))
                        (tau rho (minus_nat (plus_nat ia one_nat) one_nat))))
                (right i)
            then doUntil ia (left i) p1 p2
                   (opt rho (plus_nat ia one_nat)
                     (Until
                       (phi, subtract
                               (minus_nat (tau rho (plus_nat ia one_nat))
                                 (tau rho
                                   (minus_nat (plus_nat ia one_nat) one_nat)))
                               i,
                         psi)))
            else doUntilBase ia (left i) p1 p2));;

let rec shift
  x0 s = match x0, s with [], s -> s
    | x :: xs, s ->
        Lazy_stream (Lazy.from_fun (fun _ -> SCons_Lazy (x, shift xs s)));;

let rec siterate
  f x = Lazy_stream
          (Lazy.from_fun (fun _ -> SCons_Lazy (x, siterate f (f x))));;

let rec strs_at x = s_at x;;

let rec strv_at x = v_at x;;

let rec interval
  l r = Abs_I (if less_eq_enat (Enat l) r then (l, r)
                else rep_I (failwith "undefined"));;

let bot_set : 'a set = Set [];;

let rec rep_prefix (Abs_prefix x) = x;;

let rec smap
  x1ba xa =
    (let SCons_Lazy (x3a, x2ba) = Lazy.force (unlazy_stream xa) in
      Lazy_stream
        (Lazy.from_fun (fun _ -> SCons_Lazy (x1ba x3a, smap x1ba x2ba))));;

let rec extend_prefix
  xa = Abs_trace
         (match rep_prefix xa
           with [] -> smap (fun a -> (bot_set, a)) (siterate suc zero_nat)
           | _ :: _ ->
             (let m = snd (last (rep_prefix xa)) in
               shift (rep_prefix xa)
                 (smap (fun n -> (bot_set, plus_nat n m))
                   (siterate suc zero_nat))));;

let rec sorted _A
  = function
    x :: y :: zs ->
      less_eq _A.order_linorder.preorder_order.ord_preorder x y &&
        sorted _A (y :: zs)
    | [x] -> true
    | [] -> true;;

let rec to_prefix
  xa = Abs_prefix (if sorted linorder_nat (map snd xa) then xa else []);;

let rec to_trace xs = extend_prefix (to_prefix xs);;

let rec strs_check x = s_check equal_literal x;;

let rec strv_check x = v_check equal_literal x;;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

end;; (*struct Explanator*)
