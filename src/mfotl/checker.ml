module Uint32 : sig
  val less : int32 -> int32 -> bool
  val less_eq : int32 -> int32 -> bool
  val set_bit : int32 -> Z.t -> bool -> int32
  val shiftl : int32 -> Z.t -> int32
  val shiftr : int32 -> Z.t -> int32
  val shiftr_signed : int32 -> Z.t -> int32
  val test_bit : int32 -> Z.t -> bool
end = struct

(* negative numbers have their highest bit set, 
   so they are greater than positive ones *)
let less x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y < 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y < 0;;

let less_eq x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y <= 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y <= 0;;

let set_bit x n b =
  let mask = Int32.shift_left Int32.one (Z.to_int n)
  in if b then Int32.logor x mask
     else Int32.logand x (Int32.lognot mask);;

let shiftl x n = Int32.shift_left x (Z.to_int n);;

let shiftr x n = Int32.shift_right_logical x (Z.to_int n);;

let shiftr_signed x n = Int32.shift_right x (Z.to_int n);;

let test_bit x n =
  Int32.compare 
    (Int32.logand x (Int32.shift_left Int32.one (Z.to_int n)))
    Int32.zero
  <> 0;;

end;; (*struct Uint32*)

module Integer_Bit : sig
  val test_bit : Z.t -> Z.t -> bool
  val shiftl : Z.t -> Z.t -> Z.t
  val shiftr : Z.t -> Z.t -> Z.t
end = struct

(* We do not need an explicit range checks here,
   because Big_int.int_of_big_int raises Failure
   if the argument does not fit into an int. *)
let test_bit x n =  Z.testbit x (Z.to_int n);;

let shiftl x n = Z.shift_left x (Z.to_int n);;

let shiftr x n = Z.shift_right x (Z.to_int n);;

end;; (*struct Integer_Bit*)

module Str_Literal =
struct

let implode f xs =
  let rec length xs = match xs with
      [] -> 0
    | x :: xs -> 1 + length xs in
  let rec nth xs n = match xs with
    (x :: xs) -> if n <= 0 then x else nth xs (n - 1)
  in String.init (length xs) (fun n -> f (nth xs n));;

let explode f s =
  let rec map_range f n =
    if n <= 0 then [] else map_range f (n - 1) @ [f n]
  in map_range (fun n -> f (String.get s n)) (String.length s);;

let z_128 = Z.of_int 128;;

let check_ascii (k : Z.t) =
  if Z.leq Z.zero k && Z.lt k z_128
  then k
  else failwith "Non-ASCII character in literal";;

let char_of_ascii k = Char.chr (Z.to_int (check_ascii k));;

let ascii_of_char c = check_ascii (Z.of_int (Char.code c));;

let literal_of_asciis ks = implode char_of_ascii ks;;

let asciis_of_literal s = explode ascii_of_char s;;

end;;

module MFOTL_VerifiedExplanator2 : sig
  type 'a infinite
  type nat
  val integer_of_nat : nat -> Z.t
  type 'a equal
  type 'a linorder
  type 'a set
  type char
  type 'a default
  type 'a trace_rbt
  type 'a trace
  type ('a, 'b) sum
  type enat = Enat of nat | Infinity_enat
  type i
  type 'a formula
  type ('a, 'b) pdt
  type 'a sproof
  type 'a vproof
  val interval : nat -> enat -> i
  val is_valid :
    (char list * string list) trace ->
      (char list -> string set) ->
        string formula -> (string sproof, string vproof) sum -> bool
  val str_s_at : string sproof -> nat
  val str_v_at : string vproof -> nat
  val str_s_check :
    (char list * string list) trace ->
      (char list -> string set) -> string formula -> string sproof -> bool
  val str_v_check :
    (char list * string list) trace ->
      (char list -> string set) -> string formula -> string vproof -> bool
  val trace_of_list : 'a infinite -> ('a set * nat) list -> 'a trace
  val nat_of_integer : Z.t -> nat
  val execute_trivial_eval :
    'a default * 'a equal * 'a infinite * 'a linorder ->
      (char list * 'a list) trace ->
        (char list) list ->
          nat -> 'a formula -> ('a, ('a sproof, 'a vproof) sum) pdt
end = struct

type 'a nonunit = unit;;

type 'a infinite = {nonunit_infinite : 'a nonunit};;

let rec nonunit_fun _A _B = (() : ('a -> 'b) nonunit);;

let rec infinite_fun _A _B =
  ({nonunit_infinite = (nonunit_fun _A _B)} : ('a -> 'b) infinite);;

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

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

let semigroup_add_nat = ({plus_semigroup_add = plus_nat} : nat semigroup_add);;

let monoid_add_nat =
  ({semigroup_add_monoid_add = semigroup_add_nat; zero_monoid_add = zero_nat} :
    nat monoid_add);;

type 'a linorder = {order_linorder : 'a order};;

let linorder_nat = ({order_linorder = order_nat} : nat linorder);;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

type 'a set = Set of 'a list | Coset of 'a list;;

let rec eq _A a b = equal _A a b;;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec member _A
  x xa1 = match x, xa1 with x, Coset xs -> not (membera _A xs x)
    | x, Set xs -> membera _A xs x;;

let rec less_eq_set (_A1, _A2)
  a b = match a, b with Coset xs, Set ys -> false
    | a, Coset ys -> list_all (fun y -> not (member _A1 y a)) ys
    | Set xs, b -> list_all (fun x -> member _A1 x b) xs;;

let rec equal_seta (_A1, _A2)
  a b = less_eq_set (_A1, _A2) a b && less_eq_set (_A1, _A2) b a;;

let rec equal_set (_A1, _A2) =
  ({equal = equal_seta (_A1, _A2)} : 'a set equal);;

let rec equal_lista _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_lista _A x22 y22
    | [], [] -> true;;

let rec equal_list _A = ({equal = equal_lista _A} : ('a list) equal);;

let rec nonunit_list _A = (() : ('a list) nonunit);;

let rec infinite_list _A =
  ({nonunit_infinite = (nonunit_list _A)} : ('a list) infinite);;

type char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;;

type 'a trm = Var of char list | Const of 'a;;

let rec equal_bool p pa = match p, pa with p, true -> p
                     | p, false -> not p
                     | true, p -> p
                     | false, p -> not p;;

let rec equal_chara
  (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
    (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
    equal_bool x1 y1 &&
      (equal_bool x2 y2 &&
        (equal_bool x3 y3 &&
          (equal_bool x4 y4 &&
            (equal_bool x5 y5 &&
              (equal_bool x6 y6 && (equal_bool x7 y7 && equal_bool x8 y8))))));;

let equal_char = ({equal = equal_chara} : char equal);;

let rec equal_trma _A x0 x1 = match x0, x1 with Var x1, Const x2 -> false
                        | Const x2, Var x1 -> false
                        | Const x2, Const y2 -> eq _A x2 y2
                        | Var x1, Var y1 -> equal_lista equal_char x1 y1;;

let rec equal_trm _A = ({equal = equal_trma _A} : 'a trm equal);;

let nonunit_char = (() : char nonunit);;

let nonunit_option = (() : ('a option) nonunit);;

let equal_literal = ({equal = (fun a b -> ((a : string) = b))} : string equal);;

let default_literala : string = "";;

type 'a default = {default : 'a};;
let default _A = _A.default;;

let default_literal = ({default = default_literala} : string default);;

let ord_literal =
  ({less_eq = (fun a b -> ((a : string) <= b));
     less = (fun a b -> ((a : string) < b))}
    : string ord);;

let preorder_literal = ({ord_preorder = ord_literal} : string preorder);;

let order_literal = ({preorder_order = preorder_literal} : string order);;

let linorder_literal = ({order_linorder = order_literal} : string linorder);;

let nonunit_literal = (() : string nonunit);;

let infinite_literal =
  ({nonunit_infinite = nonunit_literal} : string infinite);;

let rec equal_proda _A _B (x1, x2) (y1, y2) = eq _A x1 y1 && eq _B x2 y2;;

let rec equal_prod _A _B = ({equal = equal_proda _A _B} : ('a * 'b) equal);;

let rec nonunit_prod _B = (() : ('a * 'b) nonunit);;

let rec infinite_prod _B =
  ({nonunit_infinite = (nonunit_prod _B)} : ('a * 'b) infinite);;

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

type num = One | Bit0 of num | Bit1 of num;;

type ('a, 'b) mapping = Mapping of ('a * 'b) list;;

type 'a trace_rbt =
  Abs_trace_rbt of (nat * (nat * (nat, ('a set * nat)) mapping));;

type 'a trace = Trace_RBT of 'a trace_rbt;;

type ('a, 'b) sum = Inl of 'a | Inr of 'b;;

type enat = Enat of nat | Infinity_enat;;

type i = Abs_I of (nat * enat);;

type 'a formula = TT | FF | Pred of char list * 'a trm list | Neg of 'a formula
  | Or of 'a formula * 'a formula | And of 'a formula * 'a formula |
  Imp of 'a formula * 'a formula | Iff of 'a formula * 'a formula |
  Exists of char list * 'a formula | Forall of char list * 'a formula |
  Prev of i * 'a formula | Next of i * 'a formula | Once of i * 'a formula |
  Historically of i * 'a formula | Eventually of i * 'a formula |
  Always of i * 'a formula | Since of 'a formula * i * 'a formula |
  Until of 'a formula * i * 'a formula;;

type ('b, 'a) part = Abs_part of ('b set * 'a) list;;

type ('a, 'b) pdt = Leaf of 'b | Node of char list * ('a, ('a, 'b) pdt) part;;

type 'a sproof = STT of nat | SPred of nat * char list * 'a trm list |
  SNeg of 'a vproof | SOrL of 'a sproof | SOrR of 'a sproof |
  SAnd of 'a sproof * 'a sproof | SImpL of 'a vproof | SImpR of 'a sproof |
  SIffSS of 'a sproof * 'a sproof | SIffVV of 'a vproof * 'a vproof |
  SExists of char list * 'a * 'a sproof |
  SForall of char list * ('a, 'a sproof) part | SPrev of 'a sproof |
  SNext of 'a sproof | SOnce of nat * 'a sproof | SEventually of nat * 'a sproof
  | SHistorically of nat * nat * 'a sproof list | SHistoricallyOut of nat |
  SAlways of nat * nat * 'a sproof list | SSince of 'a sproof * 'a sproof list |
  SUntil of 'a sproof list * 'a sproof
and 'a vproof = VFF of nat | VPred of nat * char list * 'a trm list |
  VNeg of 'a sproof | VOr of 'a vproof * 'a vproof | VAndL of 'a vproof |
  VAndR of 'a vproof | VImp of 'a sproof * 'a vproof |
  VIffSV of 'a sproof * 'a vproof | VIffVS of 'a vproof * 'a sproof |
  VExists of char list * ('a, 'a vproof) part |
  VForall of char list * 'a * 'a vproof | VPrev of 'a vproof | VPrevZ |
  VPrevOutL of nat | VPrevOutR of nat | VNext of 'a vproof | VNextOutL of nat |
  VNextOutR of nat | VOnceOut of nat | VOnce of nat * nat * 'a vproof list |
  VEventually of nat * nat * 'a vproof list | VHistorically of nat * 'a vproof |
  VAlways of nat * 'a vproof | VSinceOut of nat |
  VSince of nat * 'a vproof * 'a vproof list |
  VSinceInf of nat * nat * 'a vproof list |
  VUntil of nat * 'a vproof list * 'a vproof |
  VUntilInf of nat * nat * 'a vproof list;;

let rec id x = (fun xa -> xa) x;;

let one_nat : nat = Nat (Z.of_int 1);;

let rec suc n = plus_nata n one_nat;;

let rec list_ex p x1 = match p, x1 with p, [] -> false
                  | p, x :: xs -> p x || list_ex p xs;;

let rec bex (Set xs) p = list_ex p xs;;

let rec comp f g = (fun x -> f (g x));;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec minus_nat
  m n = Nat (max ord_integer Z.zero
              (Z.sub (integer_of_nat m) (integer_of_nat n)));;

let rec nth
  (x :: xs) n =
    (if equal_nata n zero_nata then x else nth xs (minus_nat n one_nat));;

let rec upt i j = (if less_nat i j then i :: upt (suc i) j else []);;

let rec filtera
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filtera p xs else filtera p xs);;

let rec removeAll _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: xs ->
        (if eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec inserta _A x xs = (if membera _A xs x then xs else x :: xs);;

let rec insert _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (removeAll _A x xs)
    | x, Set xs -> Set (inserta _A x xs);;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec sup_set _A
  x0 a = match x0, a with
    Coset xs, a -> Coset (filtera (fun x -> not (member _A x a)) xs)
    | Set xs, a -> fold (insert _A) xs a;;

let bot_set : 'a set = Set [];;

let rec sup_seta _A (Set xs) = fold (sup_set _A) xs bot_set;;

let rec fv_trm = function Var x -> insert (equal_list equal_char) x bot_set
                 | Const uu -> bot_set;;

let rec remove _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (inserta _A x xs)
    | x, Set xs -> Set (removeAll _A x xs);;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec image f (Set xs) = Set (map f xs);;

let rec fv
  = function
    Pred (r, ts) -> sup_seta (equal_list equal_char) (image fv_trm (Set ts))
    | TT -> bot_set
    | FF -> bot_set
    | Neg phi -> fv phi
    | Or (phi, psi) -> sup_set (equal_list equal_char) (fv phi) (fv psi)
    | And (phi, psi) -> sup_set (equal_list equal_char) (fv phi) (fv psi)
    | Imp (phi, psi) -> sup_set (equal_list equal_char) (fv phi) (fv psi)
    | Iff (phi, psi) -> sup_set (equal_list equal_char) (fv phi) (fv psi)
    | Exists (x, phi) -> remove (equal_list equal_char) x (fv phi)
    | Forall (x, phi) -> remove (equal_list equal_char) x (fv phi)
    | Prev (i, phi) -> fv phi
    | Next (i, phi) -> fv phi
    | Once (i, phi) -> fv phi
    | Historically (i, phi) -> fv phi
    | Eventually (i, phi) -> fv phi
    | Always (i, phi) -> fv phi
    | Since (phi, i, psi) -> sup_set (equal_list equal_char) (fv phi) (fv psi)
    | Until (phi, i, psi) -> sup_set (equal_list equal_char) (fv phi) (fv psi);;

let rec ball (Set xs) p = list_all p xs;;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec last (x :: xs) = (if null xs then x else last xs);;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec map_of _A
  x0 k = match x0, k with
    (l, v) :: ps, k -> (if eq _A l k then Some v else map_of _A ps k)
    | [], k -> None;;

let rec filter p (Set xs) = Set (filtera p xs);;

let rec fun_upd _A f a b = (fun x -> (if eq _A x a then b else f x));;

let rec hd (x21 :: x22) = x21;;

let rec remdups _A
  = function [] -> []
    | x :: xs ->
        (if membera _A xs x then remdups _A xs else x :: remdups _A xs);;

let rec less_eq_enat q x1 = match q, x1 with Infinity_enat, Enat n -> false
                       | q, Infinity_enat -> true
                       | Enat m, Enat n -> less_eq_nat m n;;

let rec equal_enat x0 x1 = match x0, x1 with Enat nat, Infinity_enat -> false
                     | Infinity_enat, Enat nat -> false
                     | Enat nata, Enat nat -> equal_nata nata nat
                     | Infinity_enat, Infinity_enat -> true;;

let rec do_historically_base
  i a p =
    (match (p, equal_nata a zero_nata)
      with (Inl sp, true) -> [Inl (SHistorically (i, i, [sp]))]
      | (Inl _, false) -> [Inl (SHistorically (i, i, []))]
      | (Inr vp, true) -> [Inr (VHistorically (i, vp))]
      | (Inr _, false) -> [Inl (SHistorically (i, i, []))]);;

let rec do_eventually_base
  i a p =
    (match (p, equal_nata a zero_nata)
      with (Inl sp, true) -> [Inl (SEventually (i, sp))]
      | (Inl _, false) -> [Inr (VEventually (i, i, []))]
      | (Inr vp, true) -> [Inr (VEventually (i, i, [vp]))]
      | (Inr _, false) -> [Inr (VEventually (i, i, []))]);;

let rec proof_app
  p q = (match (p, q)
          with (Inl (SHistorically (i, li, sps)), Inl qa) ->
            Inl (SHistorically (plus_nata i one_nat, li, sps @ [qa]))
          | (Inl (SAlways (i, hi, sps)), Inl qa) ->
            Inl (SAlways (minus_nat i one_nat, hi, qa :: sps))
          | (Inl (SSince (sp2, sp1s)), Inl qa) ->
            Inl (SSince (sp2, sp1s @ [qa]))
          | (Inl (SUntil (sp1s, sp2)), Inl qa) -> Inl (SUntil (qa :: sp1s, sp2))
          | (Inr (VOnce (i, li, vps)), Inr qa) ->
            Inr (VOnce (plus_nata i one_nat, li, vps @ [qa]))
          | (Inr (VEventually (i, hi, vps)), Inr qa) ->
            Inr (VEventually (minus_nat i one_nat, hi, qa :: vps))
          | (Inr (VSince (i, vp1, vp2s)), Inr qa) ->
            Inr (VSince (plus_nata i one_nat, vp1, vp2s @ [qa]))
          | (Inr (VSinceInf (i, li, vp2s)), Inr qa) ->
            Inr (VSinceInf (plus_nata i one_nat, li, vp2s @ [qa]))
          | (Inr (VUntil (i, vp2s, vp1)), Inr qa) ->
            Inr (VUntil (minus_nat i one_nat, qa :: vp2s, vp1))
          | (Inr (VUntilInf (i, hi, vp2s)), Inr qa) ->
            Inr (VUntilInf (minus_nat i one_nat, hi, qa :: vp2s)));;

let rec do_historically
  i a pa p =
    (match (pa, (equal_nata a zero_nata, p))
      with (Inl x, (true, Inl sp)) -> [proof_app (Inl sp) (Inl x)]
      | (Inl _, (true, Inr (VHistorically (_, vp)))) ->
        [Inr (VHistorically (i, vp))]
      | (Inl _, (false, Inl (SHistorically (_, li, sps)))) ->
        [Inl (SHistorically (i, li, sps))]
      | (Inl _, (false, Inr (VHistorically (_, vp)))) ->
        [Inr (VHistorically (i, vp))]
      | (Inr vp, aa) ->
        (match aa with (true, Inl _) -> [Inr (VHistorically (i, vp))]
          | (true, Inr (VHistorically (_, vpa))) ->
            [Inr (VHistorically (i, vp)); Inr (VHistorically (i, vpa))]
          | (false, Inl (SHistorically (_, li, sps))) ->
            [Inl (SHistorically (i, li, sps))]
          | (false, Inr (VHistorically (_, vpa))) ->
            [Inr (VHistorically (i, vpa))]));;

let rec do_always_base
  i a p =
    (match (p, equal_nata a zero_nata)
      with (Inl sp, true) -> [Inl (SAlways (i, i, [sp]))]
      | (Inl _, false) -> [Inl (SAlways (i, i, []))]
      | (Inr vp, true) -> [Inr (VAlways (i, vp))]
      | (Inr _, false) -> [Inl (SAlways (i, i, []))]);;

let rec snd (x1, x2) = x2;;

let rec fst (x1, x2) = x1;;

let rec do_until_base
  i a p1 p2 =
    (match (p1, (p2, equal_nata a zero_nata))
      with (Inl _, (Inl sp2, true)) -> [Inl (SUntil ([], sp2))]
      | (Inl _, (Inl _, false)) -> [Inr (VUntilInf (i, i, []))]
      | (Inl _, (Inr ba, true)) -> [Inr (VUntilInf (i, i, [ba]))]
      | (Inl _, (Inr _, false)) -> [Inr (VUntilInf (i, i, []))]
      | (Inr _, (Inl sp2, true)) -> [Inl (SUntil ([], sp2))]
      | (Inr ba, (Inl _, false)) ->
        [Inr (VUntil (i, [], ba)); Inr (VUntilInf (i, i, []))]
      | (Inr ba, (Inr baa, true)) ->
        [Inr (VUntil (i, [baa], ba)); Inr (VUntilInf (i, i, [baa]))]
      | (Inr ba, (Inr _, false)) ->
        [Inr (VUntil (i, [], ba)); Inr (VUntilInf (i, i, []))]);;

let rec do_since_base
  i a p1 p2 =
    (match (p1, (p2, equal_nata a zero_nata))
      with (Inl _, (Inl sp2, true)) -> [Inl (SSince (sp2, []))]
      | (Inl _, (Inl _, false)) -> [Inr (VSinceInf (i, i, []))]
      | (Inl _, (Inr ba, true)) -> [Inr (VSinceInf (i, i, [ba]))]
      | (Inl _, (Inr _, false)) -> [Inr (VSinceInf (i, i, []))]
      | (Inr _, (Inl sp2, true)) -> [Inl (SSince (sp2, []))]
      | (Inr ba, (Inl _, false)) ->
        [Inr (VSince (i, ba, [])); Inr (VSinceInf (i, i, []))]
      | (Inr ba, (Inr baa, true)) ->
        [Inr (VSince (i, ba, [baa])); Inr (VSinceInf (i, i, [baa]))]
      | (Inr ba, (Inr _, false)) ->
        [Inr (VSince (i, ba, [])); Inr (VSinceInf (i, i, []))]);;

let rec do_eventually
  i a pa p =
    (match (pa, (equal_nata a zero_nata, p))
      with (Inl sp, aa) ->
        (match aa
          with (true, Inl (SEventually (_, spa))) ->
            [Inl (SEventually (i, spa)); Inl (SEventually (i, sp))]
          | (true, Inr _) -> [Inl (SEventually (i, sp))]
          | (false, Inl (SEventually (_, spa))) -> [Inl (SEventually (i, spa))]
          | (false, Inr (VEventually (_, hi, vps))) ->
            [Inr (VEventually (i, hi, vps))])
      | (Inr _, (true, Inl (SEventually (_, sp)))) ->
        [Inl (SEventually (i, sp))]
      | (Inr x, (true, Inr vp)) -> [proof_app (Inr vp) (Inr x)]
      | (Inr _, (false, Inl (SEventually (_, sp)))) ->
        [Inl (SEventually (i, sp))]
      | (Inr _, (false, Inr (VEventually (_, hi, vps)))) ->
        [Inr (VEventually (i, hi, vps))]);;

let rec min_list_wrt r xs = hd (filtera (fun x -> list_all (r x) xs) xs);;

let rec do_once_base
  i a p =
    (match (p, equal_nata a zero_nata)
      with (Inl sp, true) -> [Inl (SOnce (i, sp))]
      | (Inl _, false) -> [Inr (VOnce (i, i, []))]
      | (Inr vp, true) -> [Inr (VOnce (i, i, [vp]))]
      | (Inr _, false) -> [Inr (VOnce (i, i, []))]);;

let rec rep_part (Abs_part x) = x;;

let rec map_prod f g (a, b) = (f a, g b);;

let rec map_part f xs = Abs_part (map (map_prod id f) (rep_part xs));;

let rec minus_set _A
  a x1 = match a, x1 with
    a, Coset xs -> Set (filtera (fun x -> member _A x a) xs)
    | a, Set xs -> fold (remove _A) xs a;;

let rec inf_set _A
  a x1 = match a, x1 with a, Coset xs -> fold (remove _A) xs a
    | a, Set xs -> Set (filtera (fun x -> member _A x a) xs);;

let rec map_filter
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> map_filter f xs
          | Some y -> y :: map_filter f xs);;

let rec is_empty _A = function Coset xs -> false
                      | Set xs -> null xs;;

let rec merge_part2_raw (_D1, _D2)
  f x1 uu = match f, x1, uu with f, [], uu -> []
    | f, (p1, v1) :: part1, part2 ->
        (let part12 =
           map_filter
             (fun (p2, v2) ->
               (if not (is_empty _D2 (inf_set _D1 p1 p2))
                 then Some (inf_set _D1 p1 p2, f v1 v2) else None))
             part2
           in
         let part2not1 =
           map_filter
             (fun (p2, v2) ->
               (if not (is_empty _D2 (minus_set _D1 p2 p1))
                 then Some (minus_set _D1 p2 p1, v2) else None))
             part2
           in
          part12 @ merge_part2_raw (_D1, _D2) f part1 part2not1);;

let rec merge_part3_raw (_E1, _E2)
  f x1 uu uv = match f, x1, uu, uv with f, [], uu, uv -> []
    | f, v :: va, [], ux -> []
    | f, v :: va, vb :: vc, [] -> []
    | f, v :: va, vb :: vc, vd :: ve ->
        merge_part2_raw (_E1, _E2) (fun pt3 fa -> fa pt3) (vd :: ve)
          (merge_part2_raw (_E1, _E2) f (v :: va) (vb :: vc));;

let rec merge_part3 (_A1, _A2)
  xc xd xe xf =
    Abs_part
      (merge_part3_raw (_A1, _A2) xc (rep_part xd) (rep_part xe)
        (rep_part xf));;

let rec merge_part2 (_A1, _A2)
  xc xd xe =
    Abs_part (merge_part2_raw (_A1, _A2) xc (rep_part xd) (rep_part xe));;

let rec apply_pdt1 (_A1, _A2)
  vars f x2 = match vars, f, x2 with vars, f, Leaf pt -> Leaf (f pt)
    | z :: vars, f, Node (x, part) ->
        (if equal_lista equal_char x z
          then Node (x, map_part (apply_pdt1 (_A1, _A2) vars f) part)
          else apply_pdt1 (_A1, _A2) vars f (Node (x, part)))
    | [], uu, Node (uv, uw) -> failwith "undefined";;

let rec apply_pdt2 (_A1, _A2, _A3, _A4)
  vars f x2 x3 = match vars, f, x2, x3 with
    vars, f, Leaf pt1, Leaf pt2 -> Leaf (f pt1 pt2)
    | vars, f, Leaf pt1, Node (x, part2) ->
        Node (x, map_part (apply_pdt1 (_A1, _A4) vars (f pt1)) part2)
    | vars, f, Node (x, part1), Leaf pt2 ->
        Node (x, map_part (apply_pdt1 (_A1, _A4) vars (fun pt1 -> f pt1 pt2))
                   part1)
    | z :: vars, f, Node (x, part1), Node (y, part2) ->
        (if equal_lista equal_char x z && equal_lista equal_char y z
          then Node (z, merge_part2 (_A2, _A3)
                          (apply_pdt2 (_A1, _A2, _A3, _A4) vars f) part1 part2)
          else (if equal_lista equal_char x z
                 then Node (x, map_part
                                 (fun expl1 ->
                                   apply_pdt2 (_A1, _A2, _A3, _A4) vars f expl1
                                     (Node (y, part2)))
                                 part1)
                 else (if equal_lista equal_char y z
                        then Node (y, map_part
(apply_pdt2 (_A1, _A2, _A3, _A4) vars f (Node (x, part1))) part2)
                        else apply_pdt2 (_A1, _A2, _A3, _A4) vars f
                               (Node (x, part1)) (Node (y, part2)))))
    | [], uu, Node (uv, uw), Node (ux, uy) -> failwith "undefined";;

let rec apply_pdt3 (_A1, _A2, _A3, _A4)
  vars f uv uw ux = match vars, f, uv, uw, ux with
    vars, f, Leaf pt1, Leaf pt2, Leaf pt3 -> Leaf (f pt1 pt2 pt3)
    | vars, f, Leaf pt1, Leaf pt2, Node (x, part3) ->
        Node (x, map_part
                   (apply_pdt2 (_A1, _A2, _A3, _A4) vars (f pt1) (Leaf pt2))
                   part3)
    | vars, f, Leaf pt1, Node (x, part2), Leaf pt3 ->
        Node (x, map_part
                   (apply_pdt2 (_A1, _A2, _A3, _A4) vars (f pt1) (Leaf pt3))
                   part2)
    | vars, f, Node (x, part1), Leaf pt2, Leaf pt3 ->
        Node (x, map_part
                   (apply_pdt2 (_A1, _A2, _A3, _A4) vars (fun pt1 -> f pt1 pt2)
                     (Leaf pt3))
                   part1)
    | w :: vars, f, Leaf pt1, Node (y, part2), Node (z, part3) ->
        (if equal_lista equal_char y w && equal_lista equal_char z w
          then Node (w, merge_part2 (_A2, _A3)
                          (apply_pdt2 (_A1, _A2, _A3, _A4) vars (f pt1)) part2
                          part3)
          else (if equal_lista equal_char y w
                 then Node (y, map_part
                                 (fun expl2 ->
                                   apply_pdt2 (_A1, _A2, _A3, _A4) vars (f pt1)
                                     expl2 (Node (z, part3)))
                                 part2)
                 else (if equal_lista equal_char z w
                        then Node (z, map_part
(apply_pdt2 (_A1, _A2, _A3, _A4) vars (f pt1) (Node (y, part2))) part3)
                        else apply_pdt3 (_A1, _A2, _A3, _A4) vars f (Leaf pt1)
                               (Node (y, part2)) (Node (z, part3)))))
    | w :: vars, f, Node (x, part1), Node (y, part2), Leaf pt3 ->
        (if equal_lista equal_char x w && equal_lista equal_char y w
          then Node (w, merge_part2 (_A2, _A3)
                          (apply_pdt2 (_A1, _A2, _A3, _A4) vars
                            (fun pt1 pt2 -> f pt1 pt2 pt3))
                          part1 part2)
          else (if equal_lista equal_char x w
                 then Node (x, map_part
                                 (fun expl1 ->
                                   apply_pdt2 (_A1, _A2, _A3, _A4) vars
                                     (fun pt1 pt2 -> f pt1 pt2 pt3) expl1
                                     (Node (y, part2)))
                                 part1)
                 else (if equal_lista equal_char y w
                        then Node (y, map_part
(apply_pdt2 (_A1, _A2, _A3, _A4) vars (fun pt1 pt2 -> f pt1 pt2 pt3)
  (Node (x, part1)))
part2)
                        else apply_pdt3 (_A1, _A2, _A3, _A4) vars f
                               (Node (x, part1)) (Node (y, part2)) (Leaf pt3))))
    | w :: vars, f, Node (x, part1), Leaf pt2, Node (z, part3) ->
        (if equal_lista equal_char x w && equal_lista equal_char z w
          then Node (w, merge_part2 (_A2, _A3)
                          (apply_pdt2 (_A1, _A2, _A3, _A4) vars
                            (fun pt1 -> f pt1 pt2))
                          part1 part3)
          else (if equal_lista equal_char x w
                 then Node (x, map_part
                                 (fun expl1 ->
                                   apply_pdt2 (_A1, _A2, _A3, _A4) vars
                                     (fun pt1 -> f pt1 pt2) expl1
                                     (Node (z, part3)))
                                 part1)
                 else (if equal_lista equal_char z w
                        then Node (z, map_part
(apply_pdt2 (_A1, _A2, _A3, _A4) vars (fun pt1 -> f pt1 pt2) (Node (x, part1)))
part3)
                        else apply_pdt3 (_A1, _A2, _A3, _A4) vars f
                               (Node (x, part1)) (Leaf pt2) (Node (z, part3)))))
    | w :: vars, f, Node (x, part1), Node (y, part2), Node (z, part3) ->
        (if equal_lista equal_char x w &&
              (equal_lista equal_char y w && equal_lista equal_char z w)
          then Node (z, merge_part3 (_A2, _A3)
                          (apply_pdt3 (_A1, _A2, _A3, _A4) vars f) part1 part2
                          part3)
          else (if equal_lista equal_char x w && equal_lista equal_char y w
                 then Node (w, merge_part2 (_A2, _A3)
                                 (apply_pdt3 (_A1, _A2, _A3, _A4) vars
                                   (fun pt3 pt1 pt2 -> f pt1 pt2 pt3)
                                   (Node (z, part3)))
                                 part1 part2)
                 else (if equal_lista equal_char x w &&
                            equal_lista equal_char z w
                        then Node (w, merge_part2 (_A2, _A3)
(apply_pdt3 (_A1, _A2, _A3, _A4) vars (fun pt2 pt1 -> f pt1 pt2)
  (Node (y, part2)))
part1 part3)
                        else (if equal_lista equal_char y w &&
                                   equal_lista equal_char z w
                               then Node (w,
   merge_part2 (_A2, _A3)
     (apply_pdt3 (_A1, _A2, _A3, _A4) vars f (Node (x, part1))) part2 part3)
                               else (if equal_lista equal_char x w
                                      then Node
     (x, map_part
           (fun expl1 ->
             apply_pdt3 (_A1, _A2, _A3, _A4) vars f expl1 (Node (y, part2))
               (Node (z, part3)))
           part1)
                                      else (if equal_lista equal_char y w
     then Node (y, map_part
                     (fun expl2 ->
                       apply_pdt3 (_A1, _A2, _A3, _A4) vars f (Node (x, part1))
                         expl2 (Node (z, part3)))
                     part2)
     else (if equal_lista equal_char z w
            then Node (z, map_part
                            (apply_pdt3 (_A1, _A2, _A3, _A4) vars f
                              (Node (x, part1)) (Node (y, part2)))
                            part3)
            else apply_pdt3 (_A1, _A2, _A3, _A4) vars f (Node (x, part1))
                   (Node (y, part2)) (Node (z, part3)))))))))
    | [], uu, Node (v, va), Node (vb, vc), ux -> failwith "undefined"
    | [], uu, Node (v, va), uw, Node (vb, vc) -> failwith "undefined"
    | [], uu, uv, Node (v, va), Node (vb, vc) -> failwith "undefined";;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec mina _A
  (Set (x :: xs)) =
    fold (min _A.order_linorder.preorder_order.ord_preorder) xs x;;

let rec valsa x = Set (map snd (rep_part x));;

let rec subsvals xa = rep_part xa;;

let top_set : 'a set = Coset [];;

let rec trivial_part (_A1, _A2) xa = Abs_part [(top_set, xa)];;

let rec projl (Inl x1) = x1;;

let rec isl = function Inl x1 -> true
              | Inr x2 -> false;;

let rec map_sum f1 f2 x2 = match f1, f2, x2 with f1, f2, Inl a -> Inl (f1 a)
                  | f1, f2, Inr a -> Inr (f2 a);;

let rec do_forall (_A1, _A2)
  x p_part =
    (match p_part
      with Inl (Inl sp) -> [Inl (SForall (x, trivial_part (_A1, _A2) sp))]
      | Inl (Inr vp) -> [Inr (VForall (x, default _A1, vp))]
      | Inr part ->
        (if ball (valsa part) isl then [Inl (SForall (x, map_part projl part))]
          else map_filter
                 (fun xa ->
                   (if (let (_, p) = xa in not (isl p))
                     then Some (let (d, a) = xa in
                                 map_sum id
                                   (fun aa -> VForall (x, mina _A2 d, aa)) a)
                     else None))
                 (subsvals part)));;

let rec projr (Inr x2) = x2;;

let rec do_exists (_A1, _A2)
  x p_part =
    (match p_part with Inl (Inl sp) -> [Inl (SExists (x, default _A1, sp))]
      | Inl (Inr vp) -> [Inr (VExists (x, trivial_part (_A1, _A2) vp))]
      | Inr part ->
        (if bex (valsa part) isl
          then map_filter
                 (fun xa ->
                   (if (let (_, a) = xa in isl a)
                     then Some (let (d, a) = xa in
                                 map_sum (fun aa -> SExists (x, mina _A2 d, aa))
                                   id a)
                     else None))
                 (subsvals part)
          else [Inr (VExists (x, map_part projr part))]));;

let rec do_always
  i a pa p =
    (match (pa, (equal_nata a zero_nata, p))
      with (Inl x, (true, Inl sp)) -> [proof_app (Inl sp) (Inl x)]
      | (Inl _, (true, Inr (VAlways (_, vp)))) -> [Inr (VAlways (i, vp))]
      | (Inl _, (false, Inl (SAlways (_, hi, sps)))) ->
        [Inl (SAlways (i, hi, sps))]
      | (Inl _, (false, Inr (VAlways (_, vp)))) -> [Inr (VAlways (i, vp))]
      | (Inr vp, aa) ->
        (match aa with (true, Inl _) -> [Inr (VAlways (i, vp))]
          | (true, Inr (VAlways (_, vpa))) ->
            [Inr (VAlways (i, vp)); Inr (VAlways (i, vpa))]
          | (false, Inl (SAlways (_, hi, sps))) -> [Inl (SAlways (i, hi, sps))]
          | (false, Inr (VAlways (_, vpa))) -> [Inr (VAlways (i, vpa))]));;

let zero_enat : enat = Enat zero_nata;;

let rec minus_enat x0 n = match x0, n with Enat a, Infinity_enat -> zero_enat
                     | Infinity_enat, n -> Infinity_enat
                     | Enat a, Enat b -> Enat (minus_nat a b);;

let rec rep_I (Abs_I x) = x;;

let rec subtract
  xb xc =
    Abs_I (let (i, j) = rep_I xc in (minus_nat i xb, minus_enat j (Enat xb)));;

let rec unleaf (Leaf x1) = x1;;

let rec hide_pdt (_A1, _A2)
  vars f x2 = match vars, f, x2 with vars, f, Leaf pt -> Leaf (f (Inl pt))
    | [x], f, Node (y, part) -> Leaf (f (Inr (map_part unleaf part)))
    | x :: v :: va, f, Node (y, part) ->
        (if equal_lista equal_char x y
          then Node (y, map_part (hide_pdt (_A1, _A2) (v :: va) f) part)
          else hide_pdt (_A1, _A2) (v :: va) f (Node (y, part)))
    | [], uu, Node (v, va) -> failwith "undefined";;

let rec do_until
  i a p1 p2 p =
    (match (p1, (p2, (equal_nata a zero_nata, p)))
      with (Inl sp1, (Inl aa, (true, Inl (SUntil (_, _))))) ->
        [proof_app p (Inl sp1); Inl (SUntil ([], aa))]
      | (Inl _, (Inl aa, (true, Inr (VUntil (_, _, _))))) ->
        [Inl (SUntil ([], aa))]
      | (Inl _, (Inl aa, (true, Inr (VUntilInf (_, _, _))))) ->
        [Inl (SUntil ([], aa))]
      | (Inl sp1, (Inl _, (false, Inl (SUntil (_, _))))) ->
        [proof_app p (Inl sp1)]
      | (Inl _, (Inl _, (false, Inr (VUntil (_, vp2s, vp1))))) ->
        [Inr (VUntil (i, vp2s, vp1))]
      | (Inl _, (Inl _, (false, Inr (VUntilInf (_, hi, vp2s))))) ->
        [Inr (VUntilInf (i, hi, vp2s))]
      | (Inl sp1, (Inr _, (true, Inl (SUntil (_, _))))) ->
        [proof_app p (Inl sp1)]
      | (Inl _, (Inr x, (true, Inr (VUntil (_, _, _))))) ->
        [proof_app p (Inr x)]
      | (Inl _, (Inr x, (true, Inr (VUntilInf (_, _, _))))) ->
        [proof_app p (Inr x)]
      | (Inl sp1, (Inr _, (false, Inl (SUntil (_, _))))) ->
        [proof_app p (Inl sp1)]
      | (Inl _, (Inr _, (false, Inr (VUntil (_, vp2s, vp1))))) ->
        [Inr (VUntil (i, vp2s, vp1))]
      | (Inl _, (Inr _, (false, Inr (VUntilInf (_, hi, vp2s))))) ->
        [Inr (VUntilInf (i, hi, vp2s))]
      | (Inr _, (Inl aa, (true, Inl (SUntil (_, _))))) ->
        [Inl (SUntil ([], aa))]
      | (Inr _, (Inl aa, (true, Inr (VUntil (_, _, _))))) ->
        [Inl (SUntil ([], aa))]
      | (Inr _, (Inl aa, (true, Inr (VUntilInf (_, _, _))))) ->
        [Inl (SUntil ([], aa))]
      | (Inr vp1, (Inl _, (false, Inl (SUntil (_, _))))) ->
        [Inr (VUntil (i, [], vp1))]
      | (Inr vp1, (Inl _, (false, Inr (VUntil (_, vp2s, vp1a))))) ->
        [Inr (VUntil (i, [], vp1)); Inr (VUntil (i, vp2s, vp1a))]
      | (Inr vp1, (Inl _, (false, Inr (VUntilInf (_, hi, vp2s))))) ->
        [Inr (VUntil (i, [], vp1)); Inr (VUntilInf (i, hi, vp2s))]
      | (Inr vp1, (Inr vp2, (true, Inl (SUntil (_, _))))) ->
        [Inr (VUntil (i, [vp2], vp1))]
      | (Inr vp1, (Inr vp2, (true, Inr (VUntil (_, _, _))))) ->
        [Inr (VUntil (i, [vp2], vp1)); proof_app p (Inr vp2)]
      | (Inr vp1, (Inr vp2, (true, Inr (VUntilInf (_, _, _))))) ->
        [Inr (VUntil (i, [vp2], vp1)); proof_app p (Inr vp2)]
      | (Inr vp1, (Inr _, (false, Inl (SUntil (_, _))))) ->
        [Inr (VUntil (i, [], vp1))]
      | (Inr vp1, (Inr _, (false, Inr (VUntil (_, vp2s, vp1a))))) ->
        [Inr (VUntil (i, [], vp1)); Inr (VUntil (i, vp2s, vp1a))]
      | (Inr vp1, (Inr _, (false, Inr (VUntilInf (_, hi, vp2s))))) ->
        [Inr (VUntil (i, [], vp1)); Inr (VUntilInf (i, hi, vp2s))]);;

let rec do_since
  i a p1 p2 p =
    (match (p1, (p2, (equal_nata a zero_nata, p)))
      with (Inl sp1, (Inl aa, (true, Inl sp))) ->
        [proof_app (Inl sp) (Inl sp1); Inl (SSince (aa, []))]
      | (Inl _, (Inl aa, (true, Inr (VSince (_, _, _))))) ->
        [Inl (SSince (aa, []))]
      | (Inl _, (Inl aa, (true, Inr (VSinceInf (_, _, _))))) ->
        [Inl (SSince (aa, []))]
      | (Inl sp1, (Inl _, (false, Inl sp))) -> [proof_app (Inl sp) (Inl sp1)]
      | (Inl _, (Inl _, (false, Inr (VSince (_, vp1, vp2s))))) ->
        [Inr (VSince (i, vp1, vp2s))]
      | (Inl _, (Inl _, (false, Inr (VSinceInf (_, li, vp2s))))) ->
        [Inr (VSinceInf (i, li, vp2s))]
      | (Inl sp1, (Inr _, (true, Inl sp))) -> [proof_app (Inl sp) (Inl sp1)]
      | (Inl _, (Inr x, (true, Inr (VSince (_, _, _))))) ->
        [proof_app p (Inr x)]
      | (Inl _, (Inr x, (true, Inr (VSinceInf (_, _, _))))) ->
        [proof_app p (Inr x)]
      | (Inl sp1, (Inr _, (false, Inl sp))) -> [proof_app (Inl sp) (Inl sp1)]
      | (Inl _, (Inr _, (false, Inr (VSince (_, vp1, vp2s))))) ->
        [Inr (VSince (i, vp1, vp2s))]
      | (Inl _, (Inr _, (false, Inr (VSinceInf (_, li, vp2s))))) ->
        [Inr (VSinceInf (i, li, vp2s))]
      | (Inr _, (Inl aa, (true, Inl _))) -> [Inl (SSince (aa, []))]
      | (Inr _, (Inl aa, (true, Inr (VSince (_, _, _))))) ->
        [Inl (SSince (aa, []))]
      | (Inr _, (Inl aa, (true, Inr (VSinceInf (_, _, _))))) ->
        [Inl (SSince (aa, []))]
      | (Inr vp1, (Inl _, (false, Inl _))) -> [Inr (VSince (i, vp1, []))]
      | (Inr vp1, (Inl _, (false, Inr (VSince (_, vp1a, vp2s))))) ->
        [Inr (VSince (i, vp1, [])); Inr (VSince (i, vp1a, vp2s))]
      | (Inr vp1, (Inl _, (false, Inr (VSinceInf (_, li, vp2s))))) ->
        [Inr (VSince (i, vp1, [])); Inr (VSinceInf (i, li, vp2s))]
      | (Inr vp1, (Inr vp2, (true, Inl _))) -> [Inr (VSince (i, vp1, [vp2]))]
      | (Inr vp1, (Inr vp2, (true, Inr (VSince (_, _, _))))) ->
        [Inr (VSince (i, vp1, [vp2])); proof_app p (Inr vp2)]
      | (Inr vp1, (Inr vp2, (true, Inr (VSinceInf (_, _, _))))) ->
        [Inr (VSince (i, vp1, [vp2])); proof_app p (Inr vp2)]
      | (Inr vp1, (Inr _, (false, Inl _))) -> [Inr (VSince (i, vp1, []))]
      | (Inr vp1, (Inr _, (false, Inr (VSince (_, vp1a, vp2s))))) ->
        [Inr (VSince (i, vp1, [])); Inr (VSince (i, vp1a, vp2s))]
      | (Inr vp1, (Inr _, (false, Inr (VSinceInf (_, li, vp2s))))) ->
        [Inr (VSince (i, vp1, [])); Inr (VSinceInf (i, li, vp2s))]);;

let rec right x = snd (rep_I x);;

let rec left x = fst (rep_I x);;

let rec do_prev
  ia i t p =
    (match (p, less_nat t (left i)) with (Inl _, true) -> [Inr (VPrevOutL ia)]
      | (Inl x, false) ->
        (if less_eq_nat (left i) t && less_eq_enat (Enat t) (right i)
          then [Inl (SPrev x)] else [Inr (VPrevOutR ia)])
      | (Inr vp, true) -> [Inr (VPrev vp); Inr (VPrevOutL ia)]
      | (Inr vp, false) ->
        (if less_eq_nat (left i) t && less_eq_enat (Enat t) (right i)
          then [Inr (VPrev vp)] else [Inr (VPrev vp); Inr (VPrevOutR ia)]));;

let rec do_once
  i a pa p =
    (match (pa, (equal_nata a zero_nata, p))
      with (Inl sp, aa) ->
        (match aa
          with (true, Inl (SOnce (_, spa))) ->
            [Inl (SOnce (i, spa)); Inl (SOnce (i, sp))]
          | (true, Inr _) -> [Inl (SOnce (i, sp))]
          | (false, Inl (SOnce (_, spa))) -> [Inl (SOnce (i, spa))]
          | (false, Inr (VOnce (_, li, vps))) -> [Inr (VOnce (i, li, vps))])
      | (Inr _, (true, Inl (SOnce (_, sp)))) -> [Inl (SOnce (i, sp))]
      | (Inr x, (true, Inr vp)) -> [proof_app (Inr vp) (Inr x)]
      | (Inr _, (false, Inl (SOnce (_, sp)))) -> [Inl (SOnce (i, sp))]
      | (Inr _, (false, Inr (VOnce (_, li, vps)))) ->
        [Inr (VOnce (i, li, vps))]);;

let rec do_next
  ia i t p =
    (match (p, less_nat t (left i)) with (Inl _, true) -> [Inr (VNextOutL ia)]
      | (Inl x, false) ->
        (if less_eq_nat (left i) t && less_eq_enat (Enat t) (right i)
          then [Inl (SNext x)] else [Inr (VNextOutR ia)])
      | (Inr vp, true) -> [Inr (VNext vp); Inr (VNextOutL ia)]
      | (Inr vp, false) ->
        (if less_eq_nat (left i) t && less_eq_enat (Enat t) (right i)
          then [Inr (VNext vp)] else [Inr (VNext vp); Inr (VNextOutR ia)]));;

let rec rep_trace_rbt (Abs_trace_rbt x) = x;;

let rec the (Some x2) = x2;;

let rec lookup _A (Mapping xs) = map_of _A xs;;

let rec trace_rbt_nth
  xa = (let (n, (m, t)) = rep_trace_rbt xa in
         (fun i ->
           (if less_nat i n then the (lookup equal_nat t i)
             else (bot_set, plus_nata (minus_nat i n) m))));;

let rec gamma (Trace_RBT t) i = fst (trace_rbt_nth t i);;

let rec insort_key _B
  f x xa2 = match f, x, xa2 with f, x, [] -> [x]
    | f, x, y :: ys ->
        (if less_eq _B.order_linorder.preorder_order.ord_preorder (f x) (f y)
          then x :: y :: ys else y :: insort_key _B f x ys);;

let rec sort_key _B f xs = foldr (insort_key _B f) xs [];;

let rec sorted_list_of_set (_A1, _A2)
  (Set xs) = sort_key _A2 (fun x -> x) (remdups _A1 xs);;

let rec equal_option _A x0 x1 = match x0, x1 with None, Some x2 -> false
                          | Some x2, None -> false
                          | Some x2, Some y2 -> eq _A x2 y2
                          | None, None -> true;;

let rec uminus_set = function Coset xs -> Set xs
                     | Set xs -> Coset xs;;

let rec distinct _A = function [] -> true
                      | x :: xs -> not (membera _A xs x) && distinct _A xs;;

let rec tabulate (_A1, _A2)
  xc xd xe =
    Abs_part
      (if distinct _A1 xc
        then (if eq (equal_set (_A1, _A2)) (Set xc) top_set
               then map (fun d -> (insert _A1 d bot_set, xd d)) xc
               else (uminus_set (Set xc), xe) ::
                      map (fun d -> (insert _A1 d bot_set, xd d)) xc)
        else [(top_set, xe)]);;

let rec is_none = function Some x -> false
                  | None -> true;;

let rec these a = image the (filter (fun x -> not (is_none x)) a);;

let rec pdt_of (_A1, _A2, _A3, _A4)
  i r ts x3 v = match i, r, ts, x3, v with
    i, r, ts, [], v ->
      (if is_empty (infinite_fun (infinite_list nonunit_char) nonunit_option) v
        then Leaf (Inr (VPred (i, r, ts))) else Leaf (Inl (SPred (i, r, ts))))
    | i, r, ts, x :: vars, v ->
        (let ds =
           sorted_list_of_set (_A2, _A4) (these (image (fun va -> va x) v)) in
         let a =
           tabulate (_A2, _A3) ds
             (fun d ->
               pdt_of (_A1, _A2, _A3, _A4) i r ts vars
                 (filter (fun va -> equal_option _A2 (va x) (Some d)) v))
             (pdt_of (_A1, _A2, _A3, _A4) i r ts vars bot_set)
           in
          Node (x, a));;

let rec do_neg
  p = (match p with Inl sp -> [Inr (VNeg sp)] | Inr vp -> [Inl (SNeg vp)]);;

let rec do_imp
  p1 p2 =
    (match (p1, p2) with (Inl _, Inl sp2) -> [Inl (SImpR sp2)]
      | (Inl x, Inr vp2) -> [Inr (VImp (x, vp2))]
      | (Inr vp1, Inl sp2) -> [Inl (SImpL vp1); Inl (SImpR sp2)]
      | (Inr vp1, Inr _) -> [Inl (SImpL vp1)]);;

let rec do_iff
  p1 p2 =
    (match (p1, p2) with (Inl sp1, Inl sp2) -> [Inl (SIffSS (sp1, sp2))]
      | (Inl sp1, Inr vp2) -> [Inr (VIffSV (sp1, vp2))]
      | (Inr vp1, Inl sp2) -> [Inr (VIffVS (vp1, sp2))]
      | (Inr vp1, Inr vp2) -> [Inl (SIffVV (vp1, vp2))]);;

let rec do_and
  p1 p2 =
    (match (p1, p2) with (Inl sp1, Inl sp2) -> [Inl (SAnd (sp1, sp2))]
      | (Inl _, Inr vp2) -> [Inr (VAndR vp2)]
      | (Inr vp1, Inl _) -> [Inr (VAndL vp1)]
      | (Inr vp1, Inr vp2) -> [Inr (VAndL vp1); Inr (VAndR vp2)]);;

let rec matcha (_A1, _A2, _A3)
  x0 x1 = match x0, x1 with [], [] -> Some (fun _ -> None)
    | Const x :: ts, y :: ys ->
        (if eq _A2 x y then matcha (_A1, _A2, _A3) ts ys else None)
    | Var x :: ts, y :: ys ->
        (match matcha (_A1, _A2, _A3) ts ys with None -> None
          | Some f ->
            (match f x
              with None -> Some (fun_upd (equal_list equal_char) f x (Some y))
              | Some z -> (if eq _A2 y z then Some f else None)))
    | Var vb :: va, [] -> None
    | v :: va, [] -> None
    | [], v :: va -> None;;

let rec do_or
  p1 p2 =
    (match (p1, p2) with (Inl sp1, Inl sp2) -> [Inl (SOrL sp1); Inl (SOrR sp2)]
      | (Inl sp1, Inr _) -> [Inl (SOrL sp1)]
      | (Inr _, Inl sp2) -> [Inl (SOrR sp2)]
      | (Inr x, Inr vp2) -> [Inr (VOr (x, vp2))]);;

let rec tau (Trace_RBT t) i = snd (trace_rbt_nth t i);;

let rec eval (_A1, _A2, _A3, _A4)
  sigma cmp vars i x4 = match sigma, cmp, vars, i, x4 with
    sigma, cmp, vars, i, TT -> Leaf (Inl (STT i))
    | sigma, cmp, vars, i, FF -> Leaf (Inr (VFF i))
    | sigma, cmp, vars, i, Pred (r, ts) ->
        pdt_of (_A1, _A2, _A3, _A4) i r ts
          (filtera
            (fun x -> member (equal_list equal_char) x (fv (Pred (r, ts))))
            vars)
          (these
            (image (matcha (_A1, _A2, _A4) ts)
              (image snd
                (filter (fun rd -> equal_lista equal_char (fst rd) r)
                  (gamma sigma i)))))
    | sigma, cmp, vars, i, Neg phi ->
        apply_pdt1 (_A1, _A4) vars (fun p -> min_list_wrt cmp (do_neg p))
          (eval (_A1, _A2, _A3, _A4) sigma cmp vars i phi)
    | sigma, cmp, vars, i, Or (phi, psi) ->
        apply_pdt2 (_A1, _A2, _A3, _A4) vars
          (fun p1 p2 -> min_list_wrt cmp (do_or p1 p2))
          (eval (_A1, _A2, _A3, _A4) sigma cmp vars i phi)
          (eval (_A1, _A2, _A3, _A4) sigma cmp vars i psi)
    | sigma, cmp, vars, i, And (phi, psi) ->
        apply_pdt2 (_A1, _A2, _A3, _A4) vars
          (fun p1 p2 -> min_list_wrt cmp (do_and p1 p2))
          (eval (_A1, _A2, _A3, _A4) sigma cmp vars i phi)
          (eval (_A1, _A2, _A3, _A4) sigma cmp vars i psi)
    | sigma, cmp, vars, i, Imp (phi, psi) ->
        apply_pdt2 (_A1, _A2, _A3, _A4) vars
          (fun p1 p2 -> min_list_wrt cmp (do_imp p1 p2))
          (eval (_A1, _A2, _A3, _A4) sigma cmp vars i phi)
          (eval (_A1, _A2, _A3, _A4) sigma cmp vars i psi)
    | sigma, cmp, vars, i, Iff (phi, psi) ->
        apply_pdt2 (_A1, _A2, _A3, _A4) vars
          (fun p1 p2 -> min_list_wrt cmp (do_iff p1 p2))
          (eval (_A1, _A2, _A3, _A4) sigma cmp vars i phi)
          (eval (_A1, _A2, _A3, _A4) sigma cmp vars i psi)
    | sigma, cmp, vars, i, Exists (x, phi) ->
        hide_pdt (_A1, _A4) (vars @ [x])
          (fun p -> min_list_wrt cmp (do_exists (_A1, _A4) x p))
          (eval (_A1, _A2, _A3, _A4) sigma cmp (vars @ [x]) i phi)
    | sigma, cmp, vars, i, Forall (x, phi) ->
        hide_pdt (_A1, _A4) (vars @ [x])
          (fun p -> min_list_wrt cmp (do_forall (_A1, _A4) x p))
          (eval (_A1, _A2, _A3, _A4) sigma cmp (vars @ [x]) i phi)
    | sigma, cmp, vars, ia, Prev (i, phi) ->
        (if equal_nata ia zero_nata then Leaf (Inr VPrevZ)
          else apply_pdt1 (_A1, _A4) vars
                 (fun p ->
                   min_list_wrt cmp
                     (do_prev ia i
                       (minus_nat (tau sigma ia)
                         (tau sigma (minus_nat ia one_nat)))
                       p))
                 (eval (_A1, _A2, _A3, _A4) sigma cmp vars
                   (minus_nat ia one_nat) phi))
    | sigma, cmp, vars, ia, Next (i, phi) ->
        apply_pdt1 (_A1, _A4) vars
          (fun l ->
            min_list_wrt cmp
              (do_next ia i
                (minus_nat (tau sigma (plus_nata ia one_nat))
                  (tau sigma (minus_nat (plus_nata ia one_nat) one_nat)))
                l))
          (eval (_A1, _A2, _A3, _A4) sigma cmp vars (plus_nata ia one_nat) phi)
    | sigma, cmp, vars, ia, Once (i, phi) ->
        (if less_nat (tau sigma ia) (plus_nata (tau sigma zero_nata) (left i))
          then Leaf (Inr (VOnceOut ia))
          else (let expl = eval (_A1, _A2, _A3, _A4) sigma cmp vars ia phi in
                 (if equal_nata ia zero_nata
                   then apply_pdt1 (_A1, _A4) vars
                          (fun p ->
                            min_list_wrt cmp
                              (do_once_base zero_nata zero_nata p))
                          expl
                   else (if less_eq_enat
                              (Enat (minus_nat (tau sigma ia)
                                      (tau sigma (minus_nat ia one_nat))))
                              (right i)
                          then apply_pdt2 (_A1, _A2, _A3, _A4) vars
                                 (fun p pa ->
                                   min_list_wrt cmp (do_once ia (left i) p pa))
                                 expl
                                 (eval (_A1, _A2, _A3, _A4) sigma cmp vars
                                   (minus_nat ia one_nat)
                                   (Once (subtract
    (minus_nat (tau sigma ia) (tau sigma (minus_nat ia one_nat))) i,
   phi)))
                          else apply_pdt1 (_A1, _A4) vars
                                 (fun p ->
                                   min_list_wrt cmp
                                     (do_once_base ia (left i) p))
                                 expl))))
    | sigma, cmp, vars, ia, Historically (i, phi) ->
        (if less_nat (tau sigma ia) (plus_nata (tau sigma zero_nata) (left i))
          then Leaf (Inl (SHistoricallyOut ia))
          else (let expl = eval (_A1, _A2, _A3, _A4) sigma cmp vars ia phi in
                 (if equal_nata ia zero_nata
                   then apply_pdt1 (_A1, _A4) vars
                          (fun p ->
                            min_list_wrt cmp
                              (do_historically_base zero_nata zero_nata p))
                          expl
                   else (if less_eq_enat
                              (Enat (minus_nat (tau sigma ia)
                                      (tau sigma (minus_nat ia one_nat))))
                              (right i)
                          then apply_pdt2 (_A1, _A2, _A3, _A4) vars
                                 (fun p pa ->
                                   min_list_wrt cmp
                                     (do_historically ia (left i) p pa))
                                 expl
                                 (eval (_A1, _A2, _A3, _A4) sigma cmp vars
                                   (minus_nat ia one_nat)
                                   (Historically
                                     (subtract
(minus_nat (tau sigma ia) (tau sigma (minus_nat ia one_nat))) i,
                                       phi)))
                          else apply_pdt1 (_A1, _A4) vars
                                 (fun p ->
                                   min_list_wrt cmp
                                     (do_historically_base ia (left i) p))
                                 expl))))
    | sigma, cmp, vars, ia, Eventually (i, phi) ->
        (let expl = eval (_A1, _A2, _A3, _A4) sigma cmp vars ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat (tau sigma (plus_nata ia one_nat))
                        (tau sigma (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then apply_pdt2 (_A1, _A2, _A3, _A4) vars
                   (fun p pa ->
                     min_list_wrt cmp (do_eventually ia (left i) p pa))
                   expl
                   (eval (_A1, _A2, _A3, _A4) sigma cmp vars
                     (plus_nata ia one_nat)
                     (Eventually
                       (subtract
                          (minus_nat (tau sigma (plus_nata ia one_nat))
                            (tau sigma
                              (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else apply_pdt1 (_A1, _A4) vars
                   (fun p ->
                     min_list_wrt cmp (do_eventually_base ia (left i) p))
                   expl))
    | sigma, cmp, vars, ia, Always (i, phi) ->
        (let expl = eval (_A1, _A2, _A3, _A4) sigma cmp vars ia phi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat (tau sigma (plus_nata ia one_nat))
                        (tau sigma (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then apply_pdt2 (_A1, _A2, _A3, _A4) vars
                   (fun p pa -> min_list_wrt cmp (do_always ia (left i) p pa))
                   expl
                   (eval (_A1, _A2, _A3, _A4) sigma cmp vars
                     (plus_nata ia one_nat)
                     (Always
                       (subtract
                          (minus_nat (tau sigma (plus_nata ia one_nat))
                            (tau sigma
                              (minus_nat (plus_nata ia one_nat) one_nat)))
                          i,
                         phi)))
            else apply_pdt1 (_A1, _A4) vars
                   (fun p -> min_list_wrt cmp (do_always_base ia (left i) p))
                   expl))
    | sigma, cmp, vars, ia, Since (phi, i, psi) ->
        (if less_nat (tau sigma ia) (plus_nata (tau sigma zero_nata) (left i))
          then Leaf (Inr (VSinceOut ia))
          else (let expl1 = eval (_A1, _A2, _A3, _A4) sigma cmp vars ia phi in
                let expl2 = eval (_A1, _A2, _A3, _A4) sigma cmp vars ia psi in
                 (if equal_nata ia zero_nata
                   then apply_pdt2 (_A1, _A2, _A3, _A4) vars
                          (fun p1 p2 ->
                            min_list_wrt cmp
                              (do_since_base zero_nata zero_nata p1 p2))
                          expl1 expl2
                   else (if less_eq_enat
                              (Enat (minus_nat (tau sigma ia)
                                      (tau sigma (minus_nat ia one_nat))))
                              (right i)
                          then apply_pdt3 (_A1, _A2, _A3, _A4) vars
                                 (fun p1 p2 p ->
                                   min_list_wrt cmp
                                     (do_since ia (left i) p1 p2 p))
                                 expl1 expl2
                                 (eval (_A1, _A2, _A3, _A4) sigma cmp vars
                                   (minus_nat ia one_nat)
                                   (Since
                                     (phi, subtract
     (minus_nat (tau sigma ia) (tau sigma (minus_nat ia one_nat))) i,
                                       psi)))
                          else apply_pdt2 (_A1, _A2, _A3, _A4) vars
                                 (fun p1 p2 ->
                                   min_list_wrt cmp
                                     (do_since_base ia (left i) p1 p2))
                                 expl1 expl2))))
    | sigma, cmp, vars, ia, Until (phi, i, psi) ->
        (let expl1 = eval (_A1, _A2, _A3, _A4) sigma cmp vars ia phi in
         let expl2 = eval (_A1, _A2, _A3, _A4) sigma cmp vars ia psi in
         let false = equal_enat (right i) Infinity_enat in
          (if less_eq_enat
                (Enat (minus_nat (tau sigma (plus_nata ia one_nat))
                        (tau sigma (minus_nat (plus_nata ia one_nat) one_nat))))
                (right i)
            then apply_pdt3 (_A1, _A2, _A3, _A4) vars
                   (fun p1 p2 p ->
                     min_list_wrt cmp (do_until ia (left i) p1 p2 p))
                   expl1 expl2
                   (eval (_A1, _A2, _A3, _A4) sigma cmp vars
                     (plus_nata ia one_nat)
                     (Until
                       (phi, subtract
                               (minus_nat (tau sigma (plus_nata ia one_nat))
                                 (tau sigma
                                   (minus_nat (plus_nata ia one_nat) one_nat)))
                               i,
                         psi)))
            else apply_pdt2 (_A1, _A2, _A3, _A4) vars
                   (fun p1 p2 ->
                     min_list_wrt cmp (do_until_base ia (left i) p1 p2))
                   expl1 expl2));;

let rec part_hd xa = snd (hd (rep_part xa));;

let rec s_at
  = function STT i -> i
    | SPred (i, uu, uv) -> i
    | SNeg vp -> v_at vp
    | SOrL sp1 -> s_at sp1
    | SOrR sp2 -> s_at sp2
    | SAnd (sp1, uw) -> s_at sp1
    | SImpL vp1 -> v_at vp1
    | SImpR sp2 -> s_at sp2
    | SIffSS (sp1, ux) -> s_at sp1
    | SIffVV (vp1, uy) -> v_at vp1
    | SExists (uz, va, sp) -> s_at sp
    | SForall (vb, part) -> s_at (part_hd part)
    | SPrev sp -> plus_nata (s_at sp) one_nat
    | SNext sp -> minus_nat (s_at sp) one_nat
    | SOnce (i, vc) -> i
    | SEventually (i, vd) -> i
    | SHistorically (i, ve, vf) -> i
    | SHistoricallyOut i -> i
    | SAlways (i, vg, vh) -> i
    | SSince (sp2, sp1s) ->
        (match sp1s with [] -> s_at sp2 | _ :: _ -> s_at (last sp1s))
    | SUntil (sp1s, sp2) ->
        (match sp1s with [] -> s_at sp2 | sp1 :: _ -> s_at sp1)
and v_at = function VFF i -> i
           | VPred (i, vi, vj) -> i
           | VNeg sp -> s_at sp
           | VOr (vp1, vk) -> v_at vp1
           | VAndL vp1 -> v_at vp1
           | VAndR vp2 -> v_at vp2
           | VImp (sp1, vl) -> s_at sp1
           | VIffSV (sp1, vm) -> s_at sp1
           | VIffVS (vp1, vn) -> v_at vp1
           | VExists (vo, part) -> v_at (part_hd part)
           | VForall (vq, vr, vp1) -> v_at vp1
           | VPrev vp -> plus_nata (v_at vp) one_nat
           | VPrevZ -> zero_nata
           | VPrevOutL i -> i
           | VPrevOutR i -> i
           | VNext vp -> minus_nat (v_at vp) one_nat
           | VNextOutL i -> i
           | VNextOutR i -> i
           | VOnceOut i -> i
           | VOnce (i, vs, vt) -> i
           | VEventually (i, vu, vv) -> i
           | VHistorically (i, vw) -> i
           | VAlways (i, vx) -> i
           | VSinceOut i -> i
           | VSince (i, vy, vz) -> i
           | VSinceInf (i, wa, wb) -> i
           | VUntil (i, wc, wd) -> i
           | VUntilInf (i, we, wf) -> i;;

let rec product
  (Set xs) (Set ys) = Set (maps (fun x -> map (fun a -> (x, a)) ys) xs);;

let rec set_Cons _A
  a xs =
    image (fun (aa, b) -> aa :: b)
      (product (inf_set _A (image (fun x -> x) a) top_set)
        (inf_set (equal_list _A) top_set (image (fun xsa -> xsa) xs)));;

let empty : ('a, 'b) mapping = Mapping [];;

let rec partition
  p x1 = match p, x1 with p, [] -> ([], [])
    | p, x :: xs ->
        (let (yes, no) = partition p xs in
          (if p x then (x :: yes, no) else (yes, x :: no)));;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (suc n) xs
                     | n, [] -> n;;

let rec sorted_wrt p x1 = match p, x1 with p, [] -> true
                     | p, x :: ys -> list_all (p x) ys && sorted_wrt p ys;;

let rec size_list x = gen_length zero_nata x;;

let rec bulkload
  vs = Mapping (map (fun n -> (n, nth vs n)) (upt zero_nata (size_list vs)));;

let rec lTP_rec
  sigma t i =
    (if less_eq_nat (tau sigma (suc i)) t
      then lTP_rec sigma t (plus_nata i one_nat) else i);;

let rec ltp
  sigma t =
    (if less_nat t (tau sigma zero_nata)
      then failwith "LTP: undefined" (fun _ -> ltp sigma t)
      else lTP_rec sigma t zero_nata);;

let rec finite _A = function Coset xs -> false
                    | Set xs -> true;;

let rec interval
  l r = Abs_I (if less_eq_enat (Enat l) r then (l, r)
                else rep_I (failwith "undefined"));;

let rec positions _A
  xa0 x = match xa0, x with [], x -> []
    | y :: ys, x ->
        (if eq _A x y then zero_nata :: map suc (positions _A ys x)
          else map suc (positions _A ys x));;

let rec mk_values _A _B
  = function [] -> insert (equal_list _B) [] bot_set
    | t :: ts ->
        (match t
          with (Var xa, x) ->
            (let terms = map fst ts in
              (if membera (equal_trm _A) terms (Var xa)
                then (let fst_pos = hd (positions (equal_trm _A) terms (Var xa))
                        in
                       image (fun xs -> nth xs fst_pos :: xs)
                         (mk_values _A _B ts))
                else set_Cons _B x (mk_values _A _B ts)))
          | (Const _, x) -> set_Cons _B x (mk_values _A _B ts));;

let rec vals xa = map snd (rep_part xa);;

let rec eval_trm_set _A vs x1 = match vs, x1 with vs, Var x -> (Var x, vs x)
                          | vs, Const x -> (Const x, insert _A x bot_set);;

let rec eval_trms_set _A vs ts = map (eval_trm_set _A vs) ts;;

let rec sum_list _A
  xs = foldr (plus _A.semigroup_add_monoid_add.plus_semigroup_add) xs
         (zero _A.zero_monoid_add);;

let rec sum_proofs _B f xs = sum_list _B (map f xs);;

let rec v_pred
  w x1 = match w, x1 with w, VFF vh -> one_nat
    | w, VPred (vi, r, vj) -> w r
    | w, VNeg sp -> plus_nata (s_pred w sp) one_nat
    | w, VOr (vp1, vp2) ->
        plus_nata (plus_nata (v_pred w vp1) (v_pred w vp2)) one_nat
    | w, VAndL vp1 -> plus_nata (v_pred w vp1) one_nat
    | w, VAndR vp2 -> plus_nata (v_pred w vp2) one_nat
    | w, VImp (sp1, vp2) ->
        plus_nata (plus_nata (s_pred w sp1) (v_pred w vp2)) one_nat
    | w, VIffSV (sp1, vp2) ->
        plus_nata (plus_nata (s_pred w sp1) (v_pred w vp2)) one_nat
    | w, VIffVS (vp1, sp2) ->
        plus_nata (plus_nata (v_pred w vp1) (s_pred w sp2)) one_nat
    | w, VExists (vk, part) ->
        plus_nata (sum_proofs monoid_add_nat (v_pred w) (vals part)) one_nat
    | w, VForall (vl, vm, vp) -> plus_nata (v_pred w vp) one_nat
    | w, VPrev vp -> plus_nata (v_pred w vp) one_nat
    | w, VPrevZ -> one_nat
    | w, VPrevOutL vn -> one_nat
    | w, VPrevOutR vo -> one_nat
    | w, VNext vp -> plus_nata (v_pred w vp) one_nat
    | w, VNextOutL vq -> one_nat
    | w, VNextOutR vr -> one_nat
    | w, VOnceOut vs -> one_nat
    | w, VOnce (vt, vu, vps) ->
        plus_nata (sum_proofs monoid_add_nat (v_pred w) vps) one_nat
    | w, VEventually (vv, vw, vps) ->
        plus_nata (sum_proofs monoid_add_nat (v_pred w) vps) one_nat
    | w, VHistorically (vx, vp) -> plus_nata (v_pred w vp) one_nat
    | w, VAlways (vy, vp) -> plus_nata (v_pred w vp) one_nat
    | w, VSinceOut vz -> one_nat
    | w, VSince (wa, vp1, vp2s) ->
        plus_nata (sum_proofs monoid_add_nat (v_pred w) (vp1 :: vp2s)) one_nat
    | w, VSinceInf (wb, wc, vp2s) ->
        plus_nata (sum_proofs monoid_add_nat (v_pred w) vp2s) one_nat
    | w, VUntil (wd, vp2s, vp1) ->
        plus_nata (sum_proofs monoid_add_nat (v_pred w) (vp2s @ [vp1])) one_nat
    | w, VUntilInf (we, wf, vp2s) ->
        plus_nata (sum_proofs monoid_add_nat (v_pred w) vp2s) one_nat
and s_pred
  w x1 = match w, x1 with w, STT uu -> one_nat
    | w, SPred (uv, r, uw) -> w r
    | w, SNeg vp -> plus_nata (v_pred w vp) one_nat
    | w, SOrL sp1 -> plus_nata (s_pred w sp1) one_nat
    | w, SOrR sp2 -> plus_nata (s_pred w sp2) one_nat
    | w, SAnd (sp1, sp2) ->
        plus_nata (plus_nata (s_pred w sp1) (s_pred w sp2)) one_nat
    | w, SImpL vp1 -> plus_nata (v_pred w vp1) one_nat
    | w, SImpR sp2 -> plus_nata (s_pred w sp2) one_nat
    | w, SIffSS (sp1, sp2) ->
        plus_nata (plus_nata (s_pred w sp1) (s_pred w sp2)) one_nat
    | w, SIffVV (vp1, vp2) ->
        plus_nata (plus_nata (v_pred w vp1) (v_pred w vp2)) one_nat
    | w, SExists (ux, uy, sp) -> plus_nata (s_pred w sp) one_nat
    | w, SForall (uz, part) ->
        plus_nata (sum_proofs monoid_add_nat (s_pred w) (vals part)) one_nat
    | w, SPrev sp -> plus_nata (s_pred w sp) one_nat
    | w, SNext sp -> plus_nata (s_pred w sp) one_nat
    | w, SOnce (va, sp) -> plus_nata (s_pred w sp) one_nat
    | w, SEventually (vb, sp) -> plus_nata (s_pred w sp) one_nat
    | w, SHistorically (vc, vd, sps) ->
        plus_nata (sum_proofs monoid_add_nat (s_pred w) sps) one_nat
    | w, SHistoricallyOut ve -> one_nat
    | w, SAlways (vf, vg, sps) ->
        plus_nata (sum_proofs monoid_add_nat (s_pred w) sps) one_nat
    | w, SSince (sp2, sp1s) ->
        plus_nata (sum_proofs monoid_add_nat (s_pred w) (sp2 :: sp1s)) one_nat
    | w, SUntil (sp1s, sp2) ->
        plus_nata (sum_proofs monoid_add_nat (s_pred w) (sp1s @ [sp2]))
          one_nat;;

let rec p_pred
  w = (fun a -> (match a with Inl aa -> s_pred w aa | Inr aa -> v_pred w aa));;

let rec less_enat x0 q = match x0, q with Infinity_enat, q -> false
                    | Enat m, Infinity_enat -> true
                    | Enat m, Enat n -> less_nat m n;;

let rec check_upt_LTP_p
  sigma ia li xs i =
    (match xs
      with [] ->
        (if equal_nata (left ia) zero_nata then less_nat i li
          else (if not (less_eq_nat li i) && equal_nata (left ia) zero_nata
                 then less_nat zero_nata
                        (minus_nat (tau sigma li) (tau sigma i))
                 else less_nat (minus_nat (tau sigma i) (tau sigma li))
                        (left ia)))
      | _ :: _ ->
        equal_lista equal_nat xs (upt li (plus_nata li (size_list xs))) &&
          (if equal_nata (left ia) zero_nata
            then equal_nata (minus_nat (plus_nata li (size_list xs)) one_nat) i
            else less_eq_nat (minus_nat (plus_nata li (size_list xs)) one_nat)
                   i &&
                   (less_eq_nat (left ia)
                      (minus_nat (tau sigma i)
                        (tau sigma
                          (minus_nat (plus_nata li (size_list xs)) one_nat))) &&
                     less_nat
                       (minus_nat (tau sigma i)
                         (tau sigma (plus_nata li (size_list xs))))
                       (left ia))));;

let rec check_upt_ETP_f
  sigma ia i xs hi =
    (let j = minus_nat (suc hi) (size_list xs) in
      (match xs
        with [] ->
          (if equal_nata (left ia) zero_nata then less_eq_nat (suc hi) i
            else less_nat (minus_nat (tau sigma hi) (tau sigma i)) (left ia))
        | _ :: _ ->
          equal_lista equal_nat xs (upt j (suc hi)) &&
            ((if equal_nata (left ia) zero_nata then less_eq_nat j i
               else (if equal_nata j zero_nata then true
                      else less_nat
                             (minus_nat (tau sigma (minus_nat j one_nat))
                               (tau sigma i))
                             (left ia))) &&
              (less_eq_nat i j &&
                less_eq_nat (left ia)
                  (minus_nat (tau sigma j) (tau sigma i))))));;

let rec subsVals xa = Set (rep_part xa);;

let rec maxa _A
  (Set (x :: xs)) =
    fold (max _A.order_linorder.preorder_order.ord_preorder) xs x;;

let rec mk_values_subset _A _B (_C1, _C2)
  p tXs x =
    (let (fintXs, inftXs) = partition (fun tX -> finite _C2 (snd tX)) tXs in
      (if null inftXs
        then less_eq_set
               ((equal_prod _A (equal_list _C1)),
                 (infinite_prod (infinite_list _C2.nonunit_infinite)))
               (product (insert _A p bot_set) (mk_values _B _C1 tXs)) x
        else (let inf_dups =
                filtera
                  (fun tX -> membera (equal_trm _B) (map fst fintXs) (fst tX))
                  inftXs
                in
               (if null inf_dups
                 then (if finite
                            (infinite_prod (infinite_list _C2.nonunit_infinite))
                            x
                        then false
                        else failwith "subset on infinite subset"
                               (fun _ ->
                                 less_eq_set
                                   ((equal_prod _A (equal_list _C1)),
                                     (infinite_prod
                                       (infinite_list _C2.nonunit_infinite)))
                                   (product (insert _A p bot_set)
                                     (mk_values _B _C1 tXs))
                                   x))
                 else (if list_all
                            (fun tX ->
                              less_nat
                                (maxa linorder_nat
                                  (Set (positions
 (equal_prod (equal_trm _B) (equal_set (_C1, _C2))) tXs tX)))
                                (maxa linorder_nat
                                  (Set (positions (equal_trm _B) (map fst tXs)
 (fst tX)))))
                            inf_dups
                        then less_eq_set
                               ((equal_prod _A (equal_list _C1)),
                                 (infinite_prod
                                   (infinite_list _C2.nonunit_infinite)))
                               (product (insert _A p bot_set)
                                 (mk_values _B _C1 tXs))
                               x
                        else (if finite
                                   (infinite_prod
                                     (infinite_list _C2.nonunit_infinite))
                                   x
                               then false
                               else failwith "subset on infinite subset"
                                      (fun _ ->
less_eq_set
  ((equal_prod _A (equal_list _C1)),
    (infinite_prod (infinite_list _C2.nonunit_infinite)))
  (product (insert _A p bot_set) (mk_values _B _C1 tXs)) x)))))));;

let rec v_check_exec (_A1, _A2, _A3, _A4)
  sigma vs x2 vp = match sigma, vs, x2, vp with
    sigma, vs, Until (phi, i, psi), vp ->
      (match vp with VFF _ -> false | VPred (_, _, _) -> false | VNeg _ -> false
        | VOr (_, _) -> false | VAndL _ -> false | VAndR _ -> false
        | VImp (_, _) -> false | VIffSV (_, _) -> false | VIffVS (_, _) -> false
        | VExists (_, _) -> false | VForall (_, _, _) -> false
        | VPrev _ -> false | VPrevZ -> false | VPrevOutL _ -> false
        | VPrevOutR _ -> false | VNext _ -> false | VNextOutL _ -> false
        | VNextOutR _ -> false | VOnceOut _ -> false | VOnce (_, _, _) -> false
        | VEventually (_, _, _) -> false | VHistorically (_, _) -> false
        | VAlways (_, _) -> false | VSinceOut _ -> false
        | VSince (_, _, _) -> false | VSinceInf (_, _, _) -> false
        | VUntil (ia, vp2s, vp1) ->
          (let j = v_at vp1 in
            (match right i
              with Enat b -> less_nat j (ltp sigma (plus_nata (tau sigma ia) b))
              | Infinity_enat -> true) &&
              (less_eq_nat ia j &&
                (check_upt_ETP_f sigma i ia (map v_at vp2s) j &&
                  (v_check_exec (_A1, _A2, _A3, _A4) sigma vs phi vp1 &&
                    list_all (v_check_exec (_A1, _A2, _A3, _A4) sigma vs psi)
                      vp2s))))
        | VUntilInf (ia, hi, vp2s) ->
          (match right i
            with Enat b ->
              less_eq_nat (minus_nat (tau sigma hi) (tau sigma ia)) b &&
                less_nat b (minus_nat (tau sigma (suc hi)) (tau sigma ia))
            | Infinity_enat -> false) &&
            (check_upt_ETP_f sigma i ia (map v_at vp2s) hi &&
              list_all (v_check_exec (_A1, _A2, _A3, _A4) sigma vs psi) vp2s))
    | sigma, vs, Eventually (i, phi), vp ->
        (match vp with VFF _ -> false | VPred (_, _, _) -> false
          | VNeg _ -> false | VOr (_, _) -> false | VAndL _ -> false
          | VAndR _ -> false | VImp (_, _) -> false | VIffSV (_, _) -> false
          | VIffVS (_, _) -> false | VExists (_, _) -> false
          | VForall (_, _, _) -> false | VPrev _ -> false | VPrevZ -> false
          | VPrevOutL _ -> false | VPrevOutR _ -> false | VNext _ -> false
          | VNextOutL _ -> false | VNextOutR _ -> false | VOnceOut _ -> false
          | VOnce (_, _, _) -> false
          | VEventually (ia, hi, vps) ->
            (match right i
              with Enat b ->
                less_eq_nat (minus_nat (tau sigma hi) (tau sigma ia)) b &&
                  less_nat b (minus_nat (tau sigma (suc hi)) (tau sigma ia))
              | Infinity_enat -> false) &&
              (check_upt_ETP_f sigma i ia (map v_at vps) hi &&
                list_all (v_check_exec (_A1, _A2, _A3, _A4) sigma vs phi) vps)
          | VHistorically (_, _) -> false | VAlways (_, _) -> false
          | VSinceOut _ -> false | VSince (_, _, _) -> false
          | VSinceInf (_, _, _) -> false | VUntil (_, _, _) -> false
          | VUntilInf (_, _, _) -> false)
    | sigma, vs, Since (phi, i, psi), vp ->
        (match vp with VFF _ -> false | VPred (_, _, _) -> false
          | VNeg _ -> false | VOr (_, _) -> false | VAndL _ -> false
          | VAndR _ -> false | VImp (_, _) -> false | VIffSV (_, _) -> false
          | VIffVS (_, _) -> false | VExists (_, _) -> false
          | VForall (_, _, _) -> false | VPrev _ -> false | VPrevZ -> false
          | VPrevOutL _ -> false | VPrevOutR _ -> false | VNext _ -> false
          | VNextOutL _ -> false | VNextOutR _ -> false | VOnceOut _ -> false
          | VOnce (_, _, _) -> false | VEventually (_, _, _) -> false
          | VHistorically (_, _) -> false | VAlways (_, _) -> false
          | VSinceOut ia ->
            less_nat (tau sigma ia) (plus_nata (tau sigma zero_nata) (left i))
          | VSince (ia, vp1, vp2s) ->
            (let j = v_at vp1 in
              (match right i
                with Enat a ->
                  less_eq_nat (minus_nat (tau sigma ia) (tau sigma j)) a
                | Infinity_enat -> true) &&
                (less_eq_nat j ia &&
                  (less_eq_nat (plus_nata (tau sigma zero_nata) (left i))
                     (tau sigma ia) &&
                    (check_upt_LTP_p sigma i j (map v_at vp2s) ia &&
                      (v_check_exec (_A1, _A2, _A3, _A4) sigma vs phi vp1 &&
                        list_all
                          (v_check_exec (_A1, _A2, _A3, _A4) sigma vs psi)
                          vp2s)))))
          | VSinceInf (ia, li, vp2s) ->
            (match right i
              with Enat b ->
                (equal_nata li zero_nata ||
                  less_nat b
                    (minus_nat (tau sigma ia)
                      (tau sigma (minus_nat li one_nat)))) &&
                  less_eq_nat (minus_nat (tau sigma ia) (tau sigma li)) b
              | Infinity_enat -> equal_nata li zero_nata) &&
              (less_eq_nat (plus_nata (tau sigma zero_nata) (left i))
                 (tau sigma ia) &&
                (check_upt_LTP_p sigma i li (map v_at vp2s) ia &&
                  list_all (v_check_exec (_A1, _A2, _A3, _A4) sigma vs psi)
                    vp2s))
          | VUntil (_, _, _) -> false | VUntilInf (_, _, _) -> false)
    | sigma, vs, Once (i, phi), vp ->
        (match vp with VFF _ -> false | VPred (_, _, _) -> false
          | VNeg _ -> false | VOr (_, _) -> false | VAndL _ -> false
          | VAndR _ -> false | VImp (_, _) -> false | VIffSV (_, _) -> false
          | VIffVS (_, _) -> false | VExists (_, _) -> false
          | VForall (_, _, _) -> false | VPrev _ -> false | VPrevZ -> false
          | VPrevOutL _ -> false | VPrevOutR _ -> false | VNext _ -> false
          | VNextOutL _ -> false | VNextOutR _ -> false
          | VOnceOut ia ->
            less_nat (tau sigma ia) (plus_nata (tau sigma zero_nata) (left i))
          | VOnce (ia, li, vps) ->
            (match right i
              with Enat b ->
                (equal_nata li zero_nata ||
                  less_nat b
                    (minus_nat (tau sigma ia)
                      (tau sigma (minus_nat li one_nat)))) &&
                  less_eq_nat (minus_nat (tau sigma ia) (tau sigma li)) b
              | Infinity_enat -> equal_nata li zero_nata) &&
              (less_eq_nat (plus_nata (tau sigma zero_nata) (left i))
                 (tau sigma ia) &&
                (check_upt_LTP_p sigma i li (map v_at vps) ia &&
                  list_all (v_check_exec (_A1, _A2, _A3, _A4) sigma vs phi)
                    vps))
          | VEventually (_, _, _) -> false | VHistorically (_, _) -> false
          | VAlways (_, _) -> false | VSinceOut _ -> false
          | VSince (_, _, _) -> false | VSinceInf (_, _, _) -> false
          | VUntil (_, _, _) -> false | VUntilInf (_, _, _) -> false)
    | sigma, vs, Always (xc, xaa), VUntilInf (xb, xa, x) -> false
    | sigma, vs, Always (xc, xaa), VUntil (xb, xa, x) -> false
    | sigma, vs, Always (xc, xaa), VSinceInf (xb, xa, x) -> false
    | sigma, vs, Always (xc, xaa), VSince (xb, xa, x) -> false
    | sigma, vs, Always (xa, xaa), VSinceOut x -> false
    | sigma, vs, Always (xb, xaa), VAlways (xa, x) ->
        (let j = v_at x in
          less_eq_nat xa j &&
            (less_eq_nat (left xb) (minus_nat (tau sigma j) (tau sigma xa)) &&
               less_eq_enat (Enat (minus_nat (tau sigma j) (tau sigma xa)))
                 (right xb) &&
              v_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x))
    | sigma, vs, Always (xb, xaa), VHistorically (xa, x) -> false
    | sigma, vs, Always (xc, xaa), VEventually (xb, xa, x) -> false
    | sigma, vs, Always (xc, xaa), VOnce (xb, xa, x) -> false
    | sigma, vs, Always (xa, xaa), VOnceOut x -> false
    | sigma, vs, Always (xa, xaa), VNextOutR x -> false
    | sigma, vs, Always (xa, xaa), VNextOutL x -> false
    | sigma, vs, Always (xa, xaa), VNext x -> false
    | sigma, vs, Always (xa, xaa), VPrevOutR x -> false
    | sigma, vs, Always (xa, xaa), VPrevOutL x -> false
    | sigma, vs, Always (x, xa), VPrevZ -> false
    | sigma, vs, Always (xa, xaa), VPrev x -> false
    | sigma, vs, Always (xc, xaa), VForall (xb, xa, x) -> false
    | sigma, vs, Always (xb, xaa), VExists (xa, x) -> false
    | sigma, vs, Always (xb, xaa), VIffVS (xa, x) -> false
    | sigma, vs, Always (xb, xaa), VIffSV (xa, x) -> false
    | sigma, vs, Always (xb, xaa), VImp (xa, x) -> false
    | sigma, vs, Always (xa, xaa), VAndR x -> false
    | sigma, vs, Always (xa, xaa), VAndL x -> false
    | sigma, vs, Always (xb, xaa), VOr (xa, x) -> false
    | sigma, vs, Always (xa, xaa), VNeg x -> false
    | sigma, vs, Always (xc, xaa), VPred (xb, xa, x) -> false
    | sigma, vs, Always (xa, xaa), VFF x -> false
    | sigma, vs, Historically (xc, xaa), VUntilInf (xb, xa, x) -> false
    | sigma, vs, Historically (xc, xaa), VUntil (xb, xa, x) -> false
    | sigma, vs, Historically (xc, xaa), VSinceInf (xb, xa, x) -> false
    | sigma, vs, Historically (xc, xaa), VSince (xb, xa, x) -> false
    | sigma, vs, Historically (xa, xaa), VSinceOut x -> false
    | sigma, vs, Historically (xb, xaa), VAlways (xa, x) -> false
    | sigma, vs, Historically (xb, xaa), VHistorically (xa, x) ->
        (let j = v_at x in
          less_eq_nat j xa &&
            (less_eq_nat (left xb) (minus_nat (tau sigma xa) (tau sigma j)) &&
               less_eq_enat (Enat (minus_nat (tau sigma xa) (tau sigma j)))
                 (right xb) &&
              v_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x))
    | sigma, vs, Historically (xc, xaa), VEventually (xb, xa, x) -> false
    | sigma, vs, Historically (xc, xaa), VOnce (xb, xa, x) -> false
    | sigma, vs, Historically (xa, xaa), VOnceOut x -> false
    | sigma, vs, Historically (xa, xaa), VNextOutR x -> false
    | sigma, vs, Historically (xa, xaa), VNextOutL x -> false
    | sigma, vs, Historically (xa, xaa), VNext x -> false
    | sigma, vs, Historically (xa, xaa), VPrevOutR x -> false
    | sigma, vs, Historically (xa, xaa), VPrevOutL x -> false
    | sigma, vs, Historically (x, xa), VPrevZ -> false
    | sigma, vs, Historically (xa, xaa), VPrev x -> false
    | sigma, vs, Historically (xc, xaa), VForall (xb, xa, x) -> false
    | sigma, vs, Historically (xb, xaa), VExists (xa, x) -> false
    | sigma, vs, Historically (xb, xaa), VIffVS (xa, x) -> false
    | sigma, vs, Historically (xb, xaa), VIffSV (xa, x) -> false
    | sigma, vs, Historically (xb, xaa), VImp (xa, x) -> false
    | sigma, vs, Historically (xa, xaa), VAndR x -> false
    | sigma, vs, Historically (xa, xaa), VAndL x -> false
    | sigma, vs, Historically (xb, xaa), VOr (xa, x) -> false
    | sigma, vs, Historically (xa, xaa), VNeg x -> false
    | sigma, vs, Historically (xc, xaa), VPred (xb, xa, x) -> false
    | sigma, vs, Historically (xa, xaa), VFF x -> false
    | sigma, vs, Next (xc, xaa), VUntilInf (xb, xa, x) -> false
    | sigma, vs, Next (xc, xaa), VUntil (xb, xa, x) -> false
    | sigma, vs, Next (xc, xaa), VSinceInf (xb, xa, x) -> false
    | sigma, vs, Next (xc, xaa), VSince (xb, xa, x) -> false
    | sigma, vs, Next (xa, xaa), VSinceOut x -> false
    | sigma, vs, Next (xb, xaa), VAlways (xa, x) -> false
    | sigma, vs, Next (xb, xaa), VHistorically (xa, x) -> false
    | sigma, vs, Next (xc, xaa), VEventually (xb, xa, x) -> false
    | sigma, vs, Next (xc, xaa), VOnce (xb, xa, x) -> false
    | sigma, vs, Next (xa, xaa), VOnceOut x -> false
    | sigma, vs, Next (xa, xaa), VNextOutR x ->
        less_enat (right xa)
          (Enat (minus_nat (tau sigma (plus_nata x one_nat))
                  (tau sigma (minus_nat (plus_nata x one_nat) one_nat))))
    | sigma, vs, Next (xa, xaa), VNextOutL x ->
        less_nat
          (minus_nat (tau sigma (plus_nata x one_nat))
            (tau sigma (minus_nat (plus_nata x one_nat) one_nat)))
          (left xa)
    | sigma, vs, Next (xa, xaa), VNext x ->
        (let j = v_at x in
         let i = v_at (VNext x) in
          equal_nata j (plus_nata i one_nat) &&
            v_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x)
    | sigma, vs, Next (xa, xaa), VPrevOutR x -> false
    | sigma, vs, Next (xa, xaa), VPrevOutL x -> false
    | sigma, vs, Next (x, xa), VPrevZ -> false
    | sigma, vs, Next (xa, xaa), VPrev x -> false
    | sigma, vs, Next (xc, xaa), VForall (xb, xa, x) -> false
    | sigma, vs, Next (xb, xaa), VExists (xa, x) -> false
    | sigma, vs, Next (xb, xaa), VIffVS (xa, x) -> false
    | sigma, vs, Next (xb, xaa), VIffSV (xa, x) -> false
    | sigma, vs, Next (xb, xaa), VImp (xa, x) -> false
    | sigma, vs, Next (xa, xaa), VAndR x -> false
    | sigma, vs, Next (xa, xaa), VAndL x -> false
    | sigma, vs, Next (xb, xaa), VOr (xa, x) -> false
    | sigma, vs, Next (xa, xaa), VNeg x -> false
    | sigma, vs, Next (xc, xaa), VPred (xb, xa, x) -> false
    | sigma, vs, Next (xa, xaa), VFF x -> false
    | sigma, vs, Prev (xc, xaa), VUntilInf (xb, xa, x) -> false
    | sigma, vs, Prev (xc, xaa), VUntil (xb, xa, x) -> false
    | sigma, vs, Prev (xc, xaa), VSinceInf (xb, xa, x) -> false
    | sigma, vs, Prev (xc, xaa), VSince (xb, xa, x) -> false
    | sigma, vs, Prev (xa, xaa), VSinceOut x -> false
    | sigma, vs, Prev (xb, xaa), VAlways (xa, x) -> false
    | sigma, vs, Prev (xb, xaa), VHistorically (xa, x) -> false
    | sigma, vs, Prev (xc, xaa), VEventually (xb, xa, x) -> false
    | sigma, vs, Prev (xc, xaa), VOnce (xb, xa, x) -> false
    | sigma, vs, Prev (xa, xaa), VOnceOut x -> false
    | sigma, vs, Prev (xa, xaa), VNextOutR x -> false
    | sigma, vs, Prev (xa, xaa), VNextOutL x -> false
    | sigma, vs, Prev (xa, xaa), VNext x -> false
    | sigma, vs, Prev (xa, xaa), VPrevOutR x ->
        less_nat zero_nata x &&
          less_enat (right xa)
            (Enat (minus_nat (tau sigma x) (tau sigma (minus_nat x one_nat))))
    | sigma, vs, Prev (xa, xaa), VPrevOutL x ->
        less_nat zero_nata x &&
          less_nat (minus_nat (tau sigma x) (tau sigma (minus_nat x one_nat)))
            (left xa)
    | sigma, vs, Prev (x, xa), VPrevZ -> equal_nata (v_at VPrevZ) zero_nata
    | sigma, vs, Prev (xa, xaa), VPrev x ->
        (let j = v_at x in
         let i = v_at (VPrev x) in
          equal_nata i (plus_nata j one_nat) &&
            v_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x)
    | sigma, vs, Prev (xc, xaa), VForall (xb, xa, x) -> false
    | sigma, vs, Prev (xb, xaa), VExists (xa, x) -> false
    | sigma, vs, Prev (xb, xaa), VIffVS (xa, x) -> false
    | sigma, vs, Prev (xb, xaa), VIffSV (xa, x) -> false
    | sigma, vs, Prev (xb, xaa), VImp (xa, x) -> false
    | sigma, vs, Prev (xa, xaa), VAndR x -> false
    | sigma, vs, Prev (xa, xaa), VAndL x -> false
    | sigma, vs, Prev (xb, xaa), VOr (xa, x) -> false
    | sigma, vs, Prev (xa, xaa), VNeg x -> false
    | sigma, vs, Prev (xc, xaa), VPred (xb, xa, x) -> false
    | sigma, vs, Prev (xa, xaa), VFF x -> false
    | sigma, vs, Forall (xc, xaa), VUntilInf (xb, xa, x) -> false
    | sigma, vs, Forall (xc, xaa), VUntil (xb, xa, x) -> false
    | sigma, vs, Forall (xc, xaa), VSinceInf (xb, xa, x) -> false
    | sigma, vs, Forall (xc, xaa), VSince (xb, xa, x) -> false
    | sigma, vs, Forall (xa, xaa), VSinceOut x -> false
    | sigma, vs, Forall (xb, xaa), VAlways (xa, x) -> false
    | sigma, vs, Forall (xb, xaa), VHistorically (xa, x) -> false
    | sigma, vs, Forall (xc, xaa), VEventually (xb, xa, x) -> false
    | sigma, vs, Forall (xc, xaa), VOnce (xb, xa, x) -> false
    | sigma, vs, Forall (xa, xaa), VOnceOut x -> false
    | sigma, vs, Forall (xa, xaa), VNextOutR x -> false
    | sigma, vs, Forall (xa, xaa), VNextOutL x -> false
    | sigma, vs, Forall (xa, xaa), VNext x -> false
    | sigma, vs, Forall (xa, xaa), VPrevOutR x -> false
    | sigma, vs, Forall (xa, xaa), VPrevOutL x -> false
    | sigma, vs, Forall (x, xa), VPrevZ -> false
    | sigma, vs, Forall (xa, xaa), VPrev x -> false
    | sigma, vs, Forall (xc, xaa), VForall (xb, xa, x) ->
        equal_lista equal_char xc xb &&
          v_check_exec (_A1, _A2, _A3, _A4) sigma
            (fun_upd (equal_list equal_char) vs xc (insert _A2 xa bot_set)) xaa
            x
    | sigma, vs, Forall (xb, xaa), VExists (xa, x) -> false
    | sigma, vs, Forall (xb, xaa), VIffVS (xa, x) -> false
    | sigma, vs, Forall (xb, xaa), VIffSV (xa, x) -> false
    | sigma, vs, Forall (xb, xaa), VImp (xa, x) -> false
    | sigma, vs, Forall (xa, xaa), VAndR x -> false
    | sigma, vs, Forall (xa, xaa), VAndL x -> false
    | sigma, vs, Forall (xb, xaa), VOr (xa, x) -> false
    | sigma, vs, Forall (xa, xaa), VNeg x -> false
    | sigma, vs, Forall (xc, xaa), VPred (xb, xa, x) -> false
    | sigma, vs, Forall (xa, xaa), VFF x -> false
    | sigma, vs, Exists (xc, xaa), VUntilInf (xb, xa, x) -> false
    | sigma, vs, Exists (xc, xaa), VUntil (xb, xa, x) -> false
    | sigma, vs, Exists (xc, xaa), VSinceInf (xb, xa, x) -> false
    | sigma, vs, Exists (xc, xaa), VSince (xb, xa, x) -> false
    | sigma, vs, Exists (xa, xaa), VSinceOut x -> false
    | sigma, vs, Exists (xb, xaa), VAlways (xa, x) -> false
    | sigma, vs, Exists (xb, xaa), VHistorically (xa, x) -> false
    | sigma, vs, Exists (xc, xaa), VEventually (xb, xa, x) -> false
    | sigma, vs, Exists (xc, xaa), VOnce (xb, xa, x) -> false
    | sigma, vs, Exists (xa, xaa), VOnceOut x -> false
    | sigma, vs, Exists (xa, xaa), VNextOutR x -> false
    | sigma, vs, Exists (xa, xaa), VNextOutL x -> false
    | sigma, vs, Exists (xa, xaa), VNext x -> false
    | sigma, vs, Exists (xa, xaa), VPrevOutR x -> false
    | sigma, vs, Exists (xa, xaa), VPrevOutL x -> false
    | sigma, vs, Exists (x, xa), VPrevZ -> false
    | sigma, vs, Exists (xa, xaa), VPrev x -> false
    | sigma, vs, Exists (xc, xaa), VForall (xb, xa, x) -> false
    | sigma, vs, Exists (xb, xaa), VExists (xa, x) ->
        (let i = v_at (part_hd x) in
          equal_lista equal_char xb xa &&
            ball (subsVals x)
              (fun (sub, vp) ->
                equal_nata (v_at vp) i &&
                  v_check_exec (_A1, _A2, _A3, _A4) sigma
                    (fun_upd (equal_list equal_char) vs xb sub) xaa vp))
    | sigma, vs, Exists (xb, xaa), VIffVS (xa, x) -> false
    | sigma, vs, Exists (xb, xaa), VIffSV (xa, x) -> false
    | sigma, vs, Exists (xb, xaa), VImp (xa, x) -> false
    | sigma, vs, Exists (xa, xaa), VAndR x -> false
    | sigma, vs, Exists (xa, xaa), VAndL x -> false
    | sigma, vs, Exists (xb, xaa), VOr (xa, x) -> false
    | sigma, vs, Exists (xa, xaa), VNeg x -> false
    | sigma, vs, Exists (xc, xaa), VPred (xb, xa, x) -> false
    | sigma, vs, Exists (xa, xaa), VFF x -> false
    | sigma, vs, Iff (xc, xaa), VUntilInf (xb, xa, x) -> false
    | sigma, vs, Iff (xc, xaa), VUntil (xb, xa, x) -> false
    | sigma, vs, Iff (xc, xaa), VSinceInf (xb, xa, x) -> false
    | sigma, vs, Iff (xc, xaa), VSince (xb, xa, x) -> false
    | sigma, vs, Iff (xa, xaa), VSinceOut x -> false
    | sigma, vs, Iff (xb, xaa), VAlways (xa, x) -> false
    | sigma, vs, Iff (xb, xaa), VHistorically (xa, x) -> false
    | sigma, vs, Iff (xc, xaa), VEventually (xb, xa, x) -> false
    | sigma, vs, Iff (xc, xaa), VOnce (xb, xa, x) -> false
    | sigma, vs, Iff (xa, xaa), VOnceOut x -> false
    | sigma, vs, Iff (xa, xaa), VNextOutR x -> false
    | sigma, vs, Iff (xa, xaa), VNextOutL x -> false
    | sigma, vs, Iff (xa, xaa), VNext x -> false
    | sigma, vs, Iff (xa, xaa), VPrevOutR x -> false
    | sigma, vs, Iff (xa, xaa), VPrevOutL x -> false
    | sigma, vs, Iff (x, xa), VPrevZ -> false
    | sigma, vs, Iff (xa, xaa), VPrev x -> false
    | sigma, vs, Iff (xc, xaa), VForall (xb, xa, x) -> false
    | sigma, vs, Iff (xb, xaa), VExists (xa, x) -> false
    | sigma, vs, Iff (xb, xaa), VIffVS (xa, x) ->
        v_check_exec (_A1, _A2, _A3, _A4) sigma vs xb xa &&
          (s_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x &&
            equal_nata (v_at xa) (s_at x))
    | sigma, vs, Iff (xb, xaa), VIffSV (xa, x) ->
        s_check_exec (_A1, _A2, _A3, _A4) sigma vs xb xa &&
          (v_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x &&
            equal_nata (s_at xa) (v_at x))
    | sigma, vs, Iff (xb, xaa), VImp (xa, x) -> false
    | sigma, vs, Iff (xa, xaa), VAndR x -> false
    | sigma, vs, Iff (xa, xaa), VAndL x -> false
    | sigma, vs, Iff (xb, xaa), VOr (xa, x) -> false
    | sigma, vs, Iff (xa, xaa), VNeg x -> false
    | sigma, vs, Iff (xc, xaa), VPred (xb, xa, x) -> false
    | sigma, vs, Iff (xa, xaa), VFF x -> false
    | sigma, vs, Imp (xc, xaa), VUntilInf (xb, xa, x) -> false
    | sigma, vs, Imp (xc, xaa), VUntil (xb, xa, x) -> false
    | sigma, vs, Imp (xc, xaa), VSinceInf (xb, xa, x) -> false
    | sigma, vs, Imp (xc, xaa), VSince (xb, xa, x) -> false
    | sigma, vs, Imp (xa, xaa), VSinceOut x -> false
    | sigma, vs, Imp (xb, xaa), VAlways (xa, x) -> false
    | sigma, vs, Imp (xb, xaa), VHistorically (xa, x) -> false
    | sigma, vs, Imp (xc, xaa), VEventually (xb, xa, x) -> false
    | sigma, vs, Imp (xc, xaa), VOnce (xb, xa, x) -> false
    | sigma, vs, Imp (xa, xaa), VOnceOut x -> false
    | sigma, vs, Imp (xa, xaa), VNextOutR x -> false
    | sigma, vs, Imp (xa, xaa), VNextOutL x -> false
    | sigma, vs, Imp (xa, xaa), VNext x -> false
    | sigma, vs, Imp (xa, xaa), VPrevOutR x -> false
    | sigma, vs, Imp (xa, xaa), VPrevOutL x -> false
    | sigma, vs, Imp (x, xa), VPrevZ -> false
    | sigma, vs, Imp (xa, xaa), VPrev x -> false
    | sigma, vs, Imp (xc, xaa), VForall (xb, xa, x) -> false
    | sigma, vs, Imp (xb, xaa), VExists (xa, x) -> false
    | sigma, vs, Imp (xb, xaa), VIffVS (xa, x) -> false
    | sigma, vs, Imp (xb, xaa), VIffSV (xa, x) -> false
    | sigma, vs, Imp (xb, xaa), VImp (xa, x) ->
        s_check_exec (_A1, _A2, _A3, _A4) sigma vs xb xa &&
          (v_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x &&
            equal_nata (s_at xa) (v_at x))
    | sigma, vs, Imp (xa, xaa), VAndR x -> false
    | sigma, vs, Imp (xa, xaa), VAndL x -> false
    | sigma, vs, Imp (xb, xaa), VOr (xa, x) -> false
    | sigma, vs, Imp (xa, xaa), VNeg x -> false
    | sigma, vs, Imp (xc, xaa), VPred (xb, xa, x) -> false
    | sigma, vs, Imp (xa, xaa), VFF x -> false
    | sigma, vs, And (xc, xaa), VUntilInf (xb, xa, x) -> false
    | sigma, vs, And (xc, xaa), VUntil (xb, xa, x) -> false
    | sigma, vs, And (xc, xaa), VSinceInf (xb, xa, x) -> false
    | sigma, vs, And (xc, xaa), VSince (xb, xa, x) -> false
    | sigma, vs, And (xa, xaa), VSinceOut x -> false
    | sigma, vs, And (xb, xaa), VAlways (xa, x) -> false
    | sigma, vs, And (xb, xaa), VHistorically (xa, x) -> false
    | sigma, vs, And (xc, xaa), VEventually (xb, xa, x) -> false
    | sigma, vs, And (xc, xaa), VOnce (xb, xa, x) -> false
    | sigma, vs, And (xa, xaa), VOnceOut x -> false
    | sigma, vs, And (xa, xaa), VNextOutR x -> false
    | sigma, vs, And (xa, xaa), VNextOutL x -> false
    | sigma, vs, And (xa, xaa), VNext x -> false
    | sigma, vs, And (xa, xaa), VPrevOutR x -> false
    | sigma, vs, And (xa, xaa), VPrevOutL x -> false
    | sigma, vs, And (x, xa), VPrevZ -> false
    | sigma, vs, And (xa, xaa), VPrev x -> false
    | sigma, vs, And (xc, xaa), VForall (xb, xa, x) -> false
    | sigma, vs, And (xb, xaa), VExists (xa, x) -> false
    | sigma, vs, And (xb, xaa), VIffVS (xa, x) -> false
    | sigma, vs, And (xb, xaa), VIffSV (xa, x) -> false
    | sigma, vs, And (xb, xaa), VImp (xa, x) -> false
    | sigma, vs, And (xa, xaa), VAndR x ->
        v_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x
    | sigma, vs, And (xa, xaa), VAndL x ->
        v_check_exec (_A1, _A2, _A3, _A4) sigma vs xa x
    | sigma, vs, And (xb, xaa), VOr (xa, x) -> false
    | sigma, vs, And (xa, xaa), VNeg x -> false
    | sigma, vs, And (xc, xaa), VPred (xb, xa, x) -> false
    | sigma, vs, And (xa, xaa), VFF x -> false
    | sigma, vs, Or (xc, xaa), VUntilInf (xb, xa, x) -> false
    | sigma, vs, Or (xc, xaa), VUntil (xb, xa, x) -> false
    | sigma, vs, Or (xc, xaa), VSinceInf (xb, xa, x) -> false
    | sigma, vs, Or (xc, xaa), VSince (xb, xa, x) -> false
    | sigma, vs, Or (xa, xaa), VSinceOut x -> false
    | sigma, vs, Or (xb, xaa), VAlways (xa, x) -> false
    | sigma, vs, Or (xb, xaa), VHistorically (xa, x) -> false
    | sigma, vs, Or (xc, xaa), VEventually (xb, xa, x) -> false
    | sigma, vs, Or (xc, xaa), VOnce (xb, xa, x) -> false
    | sigma, vs, Or (xa, xaa), VOnceOut x -> false
    | sigma, vs, Or (xa, xaa), VNextOutR x -> false
    | sigma, vs, Or (xa, xaa), VNextOutL x -> false
    | sigma, vs, Or (xa, xaa), VNext x -> false
    | sigma, vs, Or (xa, xaa), VPrevOutR x -> false
    | sigma, vs, Or (xa, xaa), VPrevOutL x -> false
    | sigma, vs, Or (x, xa), VPrevZ -> false
    | sigma, vs, Or (xa, xaa), VPrev x -> false
    | sigma, vs, Or (xc, xaa), VForall (xb, xa, x) -> false
    | sigma, vs, Or (xb, xaa), VExists (xa, x) -> false
    | sigma, vs, Or (xb, xaa), VIffVS (xa, x) -> false
    | sigma, vs, Or (xb, xaa), VIffSV (xa, x) -> false
    | sigma, vs, Or (xb, xaa), VImp (xa, x) -> false
    | sigma, vs, Or (xa, xaa), VAndR x -> false
    | sigma, vs, Or (xa, xaa), VAndL x -> false
    | sigma, vs, Or (xb, xaa), VOr (xa, x) ->
        v_check_exec (_A1, _A2, _A3, _A4) sigma vs xb xa &&
          (v_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x &&
            equal_nata (v_at xa) (v_at x))
    | sigma, vs, Or (xa, xaa), VNeg x -> false
    | sigma, vs, Or (xc, xaa), VPred (xb, xa, x) -> false
    | sigma, vs, Or (xa, xaa), VFF x -> false
    | sigma, vs, Neg xc, VUntilInf (xb, xa, x) -> false
    | sigma, vs, Neg xc, VUntil (xb, xa, x) -> false
    | sigma, vs, Neg xc, VSinceInf (xb, xa, x) -> false
    | sigma, vs, Neg xc, VSince (xb, xa, x) -> false
    | sigma, vs, Neg xa, VSinceOut x -> false
    | sigma, vs, Neg xb, VAlways (xa, x) -> false
    | sigma, vs, Neg xb, VHistorically (xa, x) -> false
    | sigma, vs, Neg xc, VEventually (xb, xa, x) -> false
    | sigma, vs, Neg xc, VOnce (xb, xa, x) -> false
    | sigma, vs, Neg xa, VOnceOut x -> false
    | sigma, vs, Neg xa, VNextOutR x -> false
    | sigma, vs, Neg xa, VNextOutL x -> false
    | sigma, vs, Neg xa, VNext x -> false
    | sigma, vs, Neg xa, VPrevOutR x -> false
    | sigma, vs, Neg xa, VPrevOutL x -> false
    | sigma, vs, Neg x, VPrevZ -> false
    | sigma, vs, Neg xa, VPrev x -> false
    | sigma, vs, Neg xc, VForall (xb, xa, x) -> false
    | sigma, vs, Neg xb, VExists (xa, x) -> false
    | sigma, vs, Neg xb, VIffVS (xa, x) -> false
    | sigma, vs, Neg xb, VIffSV (xa, x) -> false
    | sigma, vs, Neg xb, VImp (xa, x) -> false
    | sigma, vs, Neg xa, VAndR x -> false
    | sigma, vs, Neg xa, VAndL x -> false
    | sigma, vs, Neg xb, VOr (xa, x) -> false
    | sigma, vs, Neg xa, VNeg x ->
        s_check_exec (_A1, _A2, _A3, _A4) sigma vs xa x
    | sigma, vs, Neg xc, VPred (xb, xa, x) -> false
    | sigma, vs, Neg xa, VFF x -> false
    | sigma, vs, Pred (xc, xaa), VUntilInf (xb, xa, x) -> false
    | sigma, vs, Pred (xc, xaa), VUntil (xb, xa, x) -> false
    | sigma, vs, Pred (xc, xaa), VSinceInf (xb, xa, x) -> false
    | sigma, vs, Pred (xc, xaa), VSince (xb, xa, x) -> false
    | sigma, vs, Pred (xa, xaa), VSinceOut x -> false
    | sigma, vs, Pred (xb, xaa), VAlways (xa, x) -> false
    | sigma, vs, Pred (xb, xaa), VHistorically (xa, x) -> false
    | sigma, vs, Pred (xc, xaa), VEventually (xb, xa, x) -> false
    | sigma, vs, Pred (xc, xaa), VOnce (xb, xa, x) -> false
    | sigma, vs, Pred (xa, xaa), VOnceOut x -> false
    | sigma, vs, Pred (xa, xaa), VNextOutR x -> false
    | sigma, vs, Pred (xa, xaa), VNextOutL x -> false
    | sigma, vs, Pred (xa, xaa), VNext x -> false
    | sigma, vs, Pred (xa, xaa), VPrevOutR x -> false
    | sigma, vs, Pred (xa, xaa), VPrevOutL x -> false
    | sigma, vs, Pred (x, xa), VPrevZ -> false
    | sigma, vs, Pred (xa, xaa), VPrev x -> false
    | sigma, vs, Pred (xc, xaa), VForall (xb, xa, x) -> false
    | sigma, vs, Pred (xb, xaa), VExists (xa, x) -> false
    | sigma, vs, Pred (xb, xaa), VIffVS (xa, x) -> false
    | sigma, vs, Pred (xb, xaa), VIffSV (xa, x) -> false
    | sigma, vs, Pred (xb, xaa), VImp (xa, x) -> false
    | sigma, vs, Pred (xa, xaa), VAndR x -> false
    | sigma, vs, Pred (xa, xaa), VAndL x -> false
    | sigma, vs, Pred (xb, xaa), VOr (xa, x) -> false
    | sigma, vs, Pred (xa, xaa), VNeg x -> false
    | sigma, vs, Pred (xc, xaa), VPred (xb, xa, x) ->
        equal_lista equal_char xc xa &&
          (equal_lista (equal_trm _A2) xaa x &&
            less_eq_set
              ((equal_prod (equal_list equal_char) (equal_list _A2)),
                (infinite_prod (infinite_list _A3.nonunit_infinite)))
              (product (insert (equal_list equal_char) xc bot_set)
                (mk_values _A2 _A2 (map (eval_trm_set _A2 vs) xaa)))
              (uminus_set (gamma sigma xb)))
    | sigma, vs, Pred (xa, xaa), VFF x -> false
    | sigma, vs, FF, VUntilInf (xb, xa, x) -> false
    | sigma, vs, FF, VUntil (xb, xa, x) -> false
    | sigma, vs, FF, VSinceInf (xb, xa, x) -> false
    | sigma, vs, FF, VSince (xb, xa, x) -> false
    | sigma, vs, FF, VSinceOut x -> false
    | sigma, vs, FF, VAlways (xa, x) -> false
    | sigma, vs, FF, VHistorically (xa, x) -> false
    | sigma, vs, FF, VEventually (xb, xa, x) -> false
    | sigma, vs, FF, VOnce (xb, xa, x) -> false
    | sigma, vs, FF, VOnceOut x -> false
    | sigma, vs, FF, VNextOutR x -> false
    | sigma, vs, FF, VNextOutL x -> false
    | sigma, vs, FF, VNext x -> false
    | sigma, vs, FF, VPrevOutR x -> false
    | sigma, vs, FF, VPrevOutL x -> false
    | sigma, vs, FF, VPrevZ -> false
    | sigma, vs, FF, VPrev x -> false
    | sigma, vs, FF, VForall (xb, xa, x) -> false
    | sigma, vs, FF, VExists (xa, x) -> false
    | sigma, vs, FF, VIffVS (xa, x) -> false
    | sigma, vs, FF, VIffSV (xa, x) -> false
    | sigma, vs, FF, VImp (xa, x) -> false
    | sigma, vs, FF, VAndR x -> false
    | sigma, vs, FF, VAndL x -> false
    | sigma, vs, FF, VOr (xa, x) -> false
    | sigma, vs, FF, VNeg x -> false
    | sigma, vs, FF, VPred (xb, xa, x) -> false
    | sigma, vs, FF, VFF x -> true
    | sigma, vs, TT, p -> false
and s_check_exec (_A1, _A2, _A3, _A4)
  sigma vs x2 sp = match sigma, vs, x2, sp with
    sigma, vs, Always (i, phi), sp ->
      (match sp with STT _ -> false | SPred (_, _, _) -> false | SNeg _ -> false
        | SOrL _ -> false | SOrR _ -> false | SAnd (_, _) -> false
        | SImpL _ -> false | SImpR _ -> false | SIffSS (_, _) -> false
        | SIffVV (_, _) -> false | SExists (_, _, _) -> false
        | SForall (_, _) -> false | SPrev _ -> false | SNext _ -> false
        | SOnce (_, _) -> false | SEventually (_, _) -> false
        | SHistorically (_, _, _) -> false | SHistoricallyOut _ -> false
        | SAlways (ia, hi, sps) ->
          (match right i
            with Enat b ->
              less_eq_nat (minus_nat (tau sigma hi) (tau sigma ia)) b &&
                less_nat b (minus_nat (tau sigma (suc hi)) (tau sigma ia))
            | Infinity_enat -> false) &&
            (check_upt_ETP_f sigma i ia (map s_at sps) hi &&
              list_all (s_check_exec (_A1, _A2, _A3, _A4) sigma vs phi) sps)
        | SSince (_, _) -> false | SUntil (_, _) -> false)
    | sigma, vs, Historically (i, phi), vp ->
        (match vp with STT _ -> false | SPred (_, _, _) -> false
          | SNeg _ -> false | SOrL _ -> false | SOrR _ -> false
          | SAnd (_, _) -> false | SImpL _ -> false | SImpR _ -> false
          | SIffSS (_, _) -> false | SIffVV (_, _) -> false
          | SExists (_, _, _) -> false | SForall (_, _) -> false
          | SPrev _ -> false | SNext _ -> false | SOnce (_, _) -> false
          | SEventually (_, _) -> false
          | SHistorically (ia, li, vps) ->
            (match right i
              with Enat b ->
                (equal_nata li zero_nata ||
                  less_nat b
                    (minus_nat (tau sigma ia)
                      (tau sigma (minus_nat li one_nat)))) &&
                  less_eq_nat (minus_nat (tau sigma ia) (tau sigma li)) b
              | Infinity_enat -> equal_nata li zero_nata) &&
              (less_eq_nat (plus_nata (tau sigma zero_nata) (left i))
                 (tau sigma ia) &&
                (check_upt_LTP_p sigma i li (map s_at vps) ia &&
                  list_all (s_check_exec (_A1, _A2, _A3, _A4) sigma vs phi)
                    vps))
          | SHistoricallyOut ia ->
            less_nat (tau sigma ia) (plus_nata (tau sigma zero_nata) (left i))
          | SAlways (_, _, _) -> false | SSince (_, _) -> false
          | SUntil (_, _) -> false)
    | sigma, vs, Until (xb, xaa, xba), SUntil (xa, x) ->
        (let i = s_at (SUntil (xa, x)) in
         let j = s_at x in
          less_eq_nat i j &&
            (less_eq_nat (left xaa) (minus_nat (tau sigma j) (tau sigma i)) &&
               less_eq_enat (Enat (minus_nat (tau sigma j) (tau sigma i)))
                 (right xaa) &&
              (equal_lista equal_nat (map s_at xa) (upt i j) &&
                (s_check_exec (_A1, _A2, _A3, _A4) sigma vs xba x &&
                  list_all (s_check_exec (_A1, _A2, _A3, _A4) sigma vs xb)
                    xa))))
    | sigma, vs, Until (xb, xaa, xba), SSince (xa, x) -> false
    | sigma, vs, Until (xc, xaa, xba), SAlways (xb, xa, x) -> false
    | sigma, vs, Until (xa, xaa, xb), SHistoricallyOut x -> false
    | sigma, vs, Until (xc, xaa, xba), SHistorically (xb, xa, x) -> false
    | sigma, vs, Until (xb, xaa, xba), SEventually (xa, x) -> false
    | sigma, vs, Until (xb, xaa, xba), SOnce (xa, x) -> false
    | sigma, vs, Until (xa, xaa, xb), SNext x -> false
    | sigma, vs, Until (xa, xaa, xb), SPrev x -> false
    | sigma, vs, Until (xb, xaa, xba), SForall (xa, x) -> false
    | sigma, vs, Until (xc, xaa, xba), SExists (xb, xa, x) -> false
    | sigma, vs, Until (xb, xaa, xba), SIffVV (xa, x) -> false
    | sigma, vs, Until (xb, xaa, xba), SIffSS (xa, x) -> false
    | sigma, vs, Until (xa, xaa, xb), SImpR x -> false
    | sigma, vs, Until (xa, xaa, xb), SImpL x -> false
    | sigma, vs, Until (xb, xaa, xba), SAnd (xa, x) -> false
    | sigma, vs, Until (xa, xaa, xb), SOrR x -> false
    | sigma, vs, Until (xa, xaa, xb), SOrL x -> false
    | sigma, vs, Until (xa, xaa, xb), SNeg x -> false
    | sigma, vs, Until (xc, xaa, xba), SPred (xb, xa, x) -> false
    | sigma, vs, Until (xa, xaa, xb), STT x -> false
    | sigma, vs, Since (xb, xaa, xba), SUntil (xa, x) -> false
    | sigma, vs, Since (xb, xaa, xba), SSince (xa, x) ->
        (let i = s_at (SSince (xa, x)) in
         let j = s_at xa in
          less_eq_nat j i &&
            (less_eq_nat (left xaa) (minus_nat (tau sigma i) (tau sigma j)) &&
               less_eq_enat (Enat (minus_nat (tau sigma i) (tau sigma j)))
                 (right xaa) &&
              (equal_lista equal_nat (map s_at x)
                 (upt (plus_nata j one_nat) (plus_nata i one_nat)) &&
                (s_check_exec (_A1, _A2, _A3, _A4) sigma vs xba xa &&
                  list_all (s_check_exec (_A1, _A2, _A3, _A4) sigma vs xb) x))))
    | sigma, vs, Since (xc, xaa, xba), SAlways (xb, xa, x) -> false
    | sigma, vs, Since (xa, xaa, xb), SHistoricallyOut x -> false
    | sigma, vs, Since (xc, xaa, xba), SHistorically (xb, xa, x) -> false
    | sigma, vs, Since (xb, xaa, xba), SEventually (xa, x) -> false
    | sigma, vs, Since (xb, xaa, xba), SOnce (xa, x) -> false
    | sigma, vs, Since (xa, xaa, xb), SNext x -> false
    | sigma, vs, Since (xa, xaa, xb), SPrev x -> false
    | sigma, vs, Since (xb, xaa, xba), SForall (xa, x) -> false
    | sigma, vs, Since (xc, xaa, xba), SExists (xb, xa, x) -> false
    | sigma, vs, Since (xb, xaa, xba), SIffVV (xa, x) -> false
    | sigma, vs, Since (xb, xaa, xba), SIffSS (xa, x) -> false
    | sigma, vs, Since (xa, xaa, xb), SImpR x -> false
    | sigma, vs, Since (xa, xaa, xb), SImpL x -> false
    | sigma, vs, Since (xb, xaa, xba), SAnd (xa, x) -> false
    | sigma, vs, Since (xa, xaa, xb), SOrR x -> false
    | sigma, vs, Since (xa, xaa, xb), SOrL x -> false
    | sigma, vs, Since (xa, xaa, xb), SNeg x -> false
    | sigma, vs, Since (xc, xaa, xba), SPred (xb, xa, x) -> false
    | sigma, vs, Since (xa, xaa, xb), STT x -> false
    | sigma, vs, Eventually (xb, xaa), SUntil (xa, x) -> false
    | sigma, vs, Eventually (xb, xaa), SSince (xa, x) -> false
    | sigma, vs, Eventually (xc, xaa), SAlways (xb, xa, x) -> false
    | sigma, vs, Eventually (xa, xaa), SHistoricallyOut x -> false
    | sigma, vs, Eventually (xc, xaa), SHistorically (xb, xa, x) -> false
    | sigma, vs, Eventually (xb, xaa), SEventually (xa, x) ->
        (let j = s_at x in
          less_eq_nat xa j &&
            (less_eq_nat (left xb) (minus_nat (tau sigma j) (tau sigma xa)) &&
               less_eq_enat (Enat (minus_nat (tau sigma j) (tau sigma xa)))
                 (right xb) &&
              s_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x))
    | sigma, vs, Eventually (xb, xaa), SOnce (xa, x) -> false
    | sigma, vs, Eventually (xa, xaa), SNext x -> false
    | sigma, vs, Eventually (xa, xaa), SPrev x -> false
    | sigma, vs, Eventually (xb, xaa), SForall (xa, x) -> false
    | sigma, vs, Eventually (xc, xaa), SExists (xb, xa, x) -> false
    | sigma, vs, Eventually (xb, xaa), SIffVV (xa, x) -> false
    | sigma, vs, Eventually (xb, xaa), SIffSS (xa, x) -> false
    | sigma, vs, Eventually (xa, xaa), SImpR x -> false
    | sigma, vs, Eventually (xa, xaa), SImpL x -> false
    | sigma, vs, Eventually (xb, xaa), SAnd (xa, x) -> false
    | sigma, vs, Eventually (xa, xaa), SOrR x -> false
    | sigma, vs, Eventually (xa, xaa), SOrL x -> false
    | sigma, vs, Eventually (xa, xaa), SNeg x -> false
    | sigma, vs, Eventually (xc, xaa), SPred (xb, xa, x) -> false
    | sigma, vs, Eventually (xa, xaa), STT x -> false
    | sigma, vs, Once (xb, xaa), SUntil (xa, x) -> false
    | sigma, vs, Once (xb, xaa), SSince (xa, x) -> false
    | sigma, vs, Once (xc, xaa), SAlways (xb, xa, x) -> false
    | sigma, vs, Once (xa, xaa), SHistoricallyOut x -> false
    | sigma, vs, Once (xc, xaa), SHistorically (xb, xa, x) -> false
    | sigma, vs, Once (xb, xaa), SEventually (xa, x) -> false
    | sigma, vs, Once (xb, xaa), SOnce (xa, x) ->
        (let j = s_at x in
          less_eq_nat j xa &&
            (less_eq_nat (left xb) (minus_nat (tau sigma xa) (tau sigma j)) &&
               less_eq_enat (Enat (minus_nat (tau sigma xa) (tau sigma j)))
                 (right xb) &&
              s_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x))
    | sigma, vs, Once (xa, xaa), SNext x -> false
    | sigma, vs, Once (xa, xaa), SPrev x -> false
    | sigma, vs, Once (xb, xaa), SForall (xa, x) -> false
    | sigma, vs, Once (xc, xaa), SExists (xb, xa, x) -> false
    | sigma, vs, Once (xb, xaa), SIffVV (xa, x) -> false
    | sigma, vs, Once (xb, xaa), SIffSS (xa, x) -> false
    | sigma, vs, Once (xa, xaa), SImpR x -> false
    | sigma, vs, Once (xa, xaa), SImpL x -> false
    | sigma, vs, Once (xb, xaa), SAnd (xa, x) -> false
    | sigma, vs, Once (xa, xaa), SOrR x -> false
    | sigma, vs, Once (xa, xaa), SOrL x -> false
    | sigma, vs, Once (xa, xaa), SNeg x -> false
    | sigma, vs, Once (xc, xaa), SPred (xb, xa, x) -> false
    | sigma, vs, Once (xa, xaa), STT x -> false
    | sigma, vs, Next (xb, xaa), SUntil (xa, x) -> false
    | sigma, vs, Next (xb, xaa), SSince (xa, x) -> false
    | sigma, vs, Next (xc, xaa), SAlways (xb, xa, x) -> false
    | sigma, vs, Next (xa, xaa), SHistoricallyOut x -> false
    | sigma, vs, Next (xc, xaa), SHistorically (xb, xa, x) -> false
    | sigma, vs, Next (xb, xaa), SEventually (xa, x) -> false
    | sigma, vs, Next (xb, xaa), SOnce (xa, x) -> false
    | sigma, vs, Next (xa, xaa), SNext x ->
        (let j = s_at x in
         let i = s_at (SNext x) in
          equal_nata j (plus_nata i one_nat) &&
            (less_eq_nat (left xa)
               (minus_nat (tau sigma j) (tau sigma (minus_nat j one_nat))) &&
               less_eq_enat
                 (Enat (minus_nat (tau sigma j)
                         (tau sigma (minus_nat j one_nat))))
                 (right xa) &&
              s_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x))
    | sigma, vs, Next (xa, xaa), SPrev x -> false
    | sigma, vs, Next (xb, xaa), SForall (xa, x) -> false
    | sigma, vs, Next (xc, xaa), SExists (xb, xa, x) -> false
    | sigma, vs, Next (xb, xaa), SIffVV (xa, x) -> false
    | sigma, vs, Next (xb, xaa), SIffSS (xa, x) -> false
    | sigma, vs, Next (xa, xaa), SImpR x -> false
    | sigma, vs, Next (xa, xaa), SImpL x -> false
    | sigma, vs, Next (xb, xaa), SAnd (xa, x) -> false
    | sigma, vs, Next (xa, xaa), SOrR x -> false
    | sigma, vs, Next (xa, xaa), SOrL x -> false
    | sigma, vs, Next (xa, xaa), SNeg x -> false
    | sigma, vs, Next (xc, xaa), SPred (xb, xa, x) -> false
    | sigma, vs, Next (xa, xaa), STT x -> false
    | sigma, vs, Prev (xb, xaa), SUntil (xa, x) -> false
    | sigma, vs, Prev (xb, xaa), SSince (xa, x) -> false
    | sigma, vs, Prev (xc, xaa), SAlways (xb, xa, x) -> false
    | sigma, vs, Prev (xa, xaa), SHistoricallyOut x -> false
    | sigma, vs, Prev (xc, xaa), SHistorically (xb, xa, x) -> false
    | sigma, vs, Prev (xb, xaa), SEventually (xa, x) -> false
    | sigma, vs, Prev (xb, xaa), SOnce (xa, x) -> false
    | sigma, vs, Prev (xa, xaa), SNext x -> false
    | sigma, vs, Prev (xa, xaa), SPrev x ->
        (let j = s_at x in
         let i = s_at (SPrev x) in
          equal_nata i (plus_nata j one_nat) &&
            (less_eq_nat (left xa)
               (minus_nat (tau sigma i) (tau sigma (minus_nat i one_nat))) &&
               less_eq_enat
                 (Enat (minus_nat (tau sigma i)
                         (tau sigma (minus_nat i one_nat))))
                 (right xa) &&
              s_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x))
    | sigma, vs, Prev (xb, xaa), SForall (xa, x) -> false
    | sigma, vs, Prev (xc, xaa), SExists (xb, xa, x) -> false
    | sigma, vs, Prev (xb, xaa), SIffVV (xa, x) -> false
    | sigma, vs, Prev (xb, xaa), SIffSS (xa, x) -> false
    | sigma, vs, Prev (xa, xaa), SImpR x -> false
    | sigma, vs, Prev (xa, xaa), SImpL x -> false
    | sigma, vs, Prev (xb, xaa), SAnd (xa, x) -> false
    | sigma, vs, Prev (xa, xaa), SOrR x -> false
    | sigma, vs, Prev (xa, xaa), SOrL x -> false
    | sigma, vs, Prev (xa, xaa), SNeg x -> false
    | sigma, vs, Prev (xc, xaa), SPred (xb, xa, x) -> false
    | sigma, vs, Prev (xa, xaa), STT x -> false
    | sigma, vs, Forall (xb, xaa), SUntil (xa, x) -> false
    | sigma, vs, Forall (xb, xaa), SSince (xa, x) -> false
    | sigma, vs, Forall (xc, xaa), SAlways (xb, xa, x) -> false
    | sigma, vs, Forall (xa, xaa), SHistoricallyOut x -> false
    | sigma, vs, Forall (xc, xaa), SHistorically (xb, xa, x) -> false
    | sigma, vs, Forall (xb, xaa), SEventually (xa, x) -> false
    | sigma, vs, Forall (xb, xaa), SOnce (xa, x) -> false
    | sigma, vs, Forall (xa, xaa), SNext x -> false
    | sigma, vs, Forall (xa, xaa), SPrev x -> false
    | sigma, vs, Forall (xb, xaa), SForall (xa, x) ->
        (let i = s_at (part_hd x) in
          equal_lista equal_char xb xa &&
            ball (subsVals x)
              (fun (sub, sp) ->
                equal_nata (s_at sp) i &&
                  s_check_exec (_A1, _A2, _A3, _A4) sigma
                    (fun_upd (equal_list equal_char) vs xb sub) xaa sp))
    | sigma, vs, Forall (xc, xaa), SExists (xb, xa, x) -> false
    | sigma, vs, Forall (xb, xaa), SIffVV (xa, x) -> false
    | sigma, vs, Forall (xb, xaa), SIffSS (xa, x) -> false
    | sigma, vs, Forall (xa, xaa), SImpR x -> false
    | sigma, vs, Forall (xa, xaa), SImpL x -> false
    | sigma, vs, Forall (xb, xaa), SAnd (xa, x) -> false
    | sigma, vs, Forall (xa, xaa), SOrR x -> false
    | sigma, vs, Forall (xa, xaa), SOrL x -> false
    | sigma, vs, Forall (xa, xaa), SNeg x -> false
    | sigma, vs, Forall (xc, xaa), SPred (xb, xa, x) -> false
    | sigma, vs, Forall (xa, xaa), STT x -> false
    | sigma, vs, Exists (xb, xaa), SUntil (xa, x) -> false
    | sigma, vs, Exists (xb, xaa), SSince (xa, x) -> false
    | sigma, vs, Exists (xc, xaa), SAlways (xb, xa, x) -> false
    | sigma, vs, Exists (xa, xaa), SHistoricallyOut x -> false
    | sigma, vs, Exists (xc, xaa), SHistorically (xb, xa, x) -> false
    | sigma, vs, Exists (xb, xaa), SEventually (xa, x) -> false
    | sigma, vs, Exists (xb, xaa), SOnce (xa, x) -> false
    | sigma, vs, Exists (xa, xaa), SNext x -> false
    | sigma, vs, Exists (xa, xaa), SPrev x -> false
    | sigma, vs, Exists (xb, xaa), SForall (xa, x) -> false
    | sigma, vs, Exists (xc, xaa), SExists (xb, xa, x) ->
        equal_lista equal_char xc xb &&
          s_check_exec (_A1, _A2, _A3, _A4) sigma
            (fun_upd (equal_list equal_char) vs xc (insert _A2 xa bot_set)) xaa
            x
    | sigma, vs, Exists (xb, xaa), SIffVV (xa, x) -> false
    | sigma, vs, Exists (xb, xaa), SIffSS (xa, x) -> false
    | sigma, vs, Exists (xa, xaa), SImpR x -> false
    | sigma, vs, Exists (xa, xaa), SImpL x -> false
    | sigma, vs, Exists (xb, xaa), SAnd (xa, x) -> false
    | sigma, vs, Exists (xa, xaa), SOrR x -> false
    | sigma, vs, Exists (xa, xaa), SOrL x -> false
    | sigma, vs, Exists (xa, xaa), SNeg x -> false
    | sigma, vs, Exists (xc, xaa), SPred (xb, xa, x) -> false
    | sigma, vs, Exists (xa, xaa), STT x -> false
    | sigma, vs, Iff (xb, xaa), SUntil (xa, x) -> false
    | sigma, vs, Iff (xb, xaa), SSince (xa, x) -> false
    | sigma, vs, Iff (xc, xaa), SAlways (xb, xa, x) -> false
    | sigma, vs, Iff (xa, xaa), SHistoricallyOut x -> false
    | sigma, vs, Iff (xc, xaa), SHistorically (xb, xa, x) -> false
    | sigma, vs, Iff (xb, xaa), SEventually (xa, x) -> false
    | sigma, vs, Iff (xb, xaa), SOnce (xa, x) -> false
    | sigma, vs, Iff (xa, xaa), SNext x -> false
    | sigma, vs, Iff (xa, xaa), SPrev x -> false
    | sigma, vs, Iff (xb, xaa), SForall (xa, x) -> false
    | sigma, vs, Iff (xc, xaa), SExists (xb, xa, x) -> false
    | sigma, vs, Iff (xb, xaa), SIffVV (xa, x) ->
        v_check_exec (_A1, _A2, _A3, _A4) sigma vs xb xa &&
          (v_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x &&
            equal_nata (v_at xa) (v_at x))
    | sigma, vs, Iff (xb, xaa), SIffSS (xa, x) ->
        s_check_exec (_A1, _A2, _A3, _A4) sigma vs xb xa &&
          (s_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x &&
            equal_nata (s_at xa) (s_at x))
    | sigma, vs, Iff (xa, xaa), SImpR x -> false
    | sigma, vs, Iff (xa, xaa), SImpL x -> false
    | sigma, vs, Iff (xb, xaa), SAnd (xa, x) -> false
    | sigma, vs, Iff (xa, xaa), SOrR x -> false
    | sigma, vs, Iff (xa, xaa), SOrL x -> false
    | sigma, vs, Iff (xa, xaa), SNeg x -> false
    | sigma, vs, Iff (xc, xaa), SPred (xb, xa, x) -> false
    | sigma, vs, Iff (xa, xaa), STT x -> false
    | sigma, vs, Imp (xb, xaa), SUntil (xa, x) -> false
    | sigma, vs, Imp (xb, xaa), SSince (xa, x) -> false
    | sigma, vs, Imp (xc, xaa), SAlways (xb, xa, x) -> false
    | sigma, vs, Imp (xa, xaa), SHistoricallyOut x -> false
    | sigma, vs, Imp (xc, xaa), SHistorically (xb, xa, x) -> false
    | sigma, vs, Imp (xb, xaa), SEventually (xa, x) -> false
    | sigma, vs, Imp (xb, xaa), SOnce (xa, x) -> false
    | sigma, vs, Imp (xa, xaa), SNext x -> false
    | sigma, vs, Imp (xa, xaa), SPrev x -> false
    | sigma, vs, Imp (xb, xaa), SForall (xa, x) -> false
    | sigma, vs, Imp (xc, xaa), SExists (xb, xa, x) -> false
    | sigma, vs, Imp (xb, xaa), SIffVV (xa, x) -> false
    | sigma, vs, Imp (xb, xaa), SIffSS (xa, x) -> false
    | sigma, vs, Imp (xa, xaa), SImpR x ->
        s_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x
    | sigma, vs, Imp (xa, xaa), SImpL x ->
        v_check_exec (_A1, _A2, _A3, _A4) sigma vs xa x
    | sigma, vs, Imp (xb, xaa), SAnd (xa, x) -> false
    | sigma, vs, Imp (xa, xaa), SOrR x -> false
    | sigma, vs, Imp (xa, xaa), SOrL x -> false
    | sigma, vs, Imp (xa, xaa), SNeg x -> false
    | sigma, vs, Imp (xc, xaa), SPred (xb, xa, x) -> false
    | sigma, vs, Imp (xa, xaa), STT x -> false
    | sigma, vs, And (xb, xaa), SUntil (xa, x) -> false
    | sigma, vs, And (xb, xaa), SSince (xa, x) -> false
    | sigma, vs, And (xc, xaa), SAlways (xb, xa, x) -> false
    | sigma, vs, And (xa, xaa), SHistoricallyOut x -> false
    | sigma, vs, And (xc, xaa), SHistorically (xb, xa, x) -> false
    | sigma, vs, And (xb, xaa), SEventually (xa, x) -> false
    | sigma, vs, And (xb, xaa), SOnce (xa, x) -> false
    | sigma, vs, And (xa, xaa), SNext x -> false
    | sigma, vs, And (xa, xaa), SPrev x -> false
    | sigma, vs, And (xb, xaa), SForall (xa, x) -> false
    | sigma, vs, And (xc, xaa), SExists (xb, xa, x) -> false
    | sigma, vs, And (xb, xaa), SIffVV (xa, x) -> false
    | sigma, vs, And (xb, xaa), SIffSS (xa, x) -> false
    | sigma, vs, And (xa, xaa), SImpR x -> false
    | sigma, vs, And (xa, xaa), SImpL x -> false
    | sigma, vs, And (xb, xaa), SAnd (xa, x) ->
        s_check_exec (_A1, _A2, _A3, _A4) sigma vs xb xa &&
          (s_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x &&
            equal_nata (s_at xa) (s_at x))
    | sigma, vs, And (xa, xaa), SOrR x -> false
    | sigma, vs, And (xa, xaa), SOrL x -> false
    | sigma, vs, And (xa, xaa), SNeg x -> false
    | sigma, vs, And (xc, xaa), SPred (xb, xa, x) -> false
    | sigma, vs, And (xa, xaa), STT x -> false
    | sigma, vs, Or (xb, xaa), SUntil (xa, x) -> false
    | sigma, vs, Or (xb, xaa), SSince (xa, x) -> false
    | sigma, vs, Or (xc, xaa), SAlways (xb, xa, x) -> false
    | sigma, vs, Or (xa, xaa), SHistoricallyOut x -> false
    | sigma, vs, Or (xc, xaa), SHistorically (xb, xa, x) -> false
    | sigma, vs, Or (xb, xaa), SEventually (xa, x) -> false
    | sigma, vs, Or (xb, xaa), SOnce (xa, x) -> false
    | sigma, vs, Or (xa, xaa), SNext x -> false
    | sigma, vs, Or (xa, xaa), SPrev x -> false
    | sigma, vs, Or (xb, xaa), SForall (xa, x) -> false
    | sigma, vs, Or (xc, xaa), SExists (xb, xa, x) -> false
    | sigma, vs, Or (xb, xaa), SIffVV (xa, x) -> false
    | sigma, vs, Or (xb, xaa), SIffSS (xa, x) -> false
    | sigma, vs, Or (xa, xaa), SImpR x -> false
    | sigma, vs, Or (xa, xaa), SImpL x -> false
    | sigma, vs, Or (xb, xaa), SAnd (xa, x) -> false
    | sigma, vs, Or (xa, xaa), SOrR x ->
        s_check_exec (_A1, _A2, _A3, _A4) sigma vs xaa x
    | sigma, vs, Or (xa, xaa), SOrL x ->
        s_check_exec (_A1, _A2, _A3, _A4) sigma vs xa x
    | sigma, vs, Or (xa, xaa), SNeg x -> false
    | sigma, vs, Or (xc, xaa), SPred (xb, xa, x) -> false
    | sigma, vs, Or (xa, xaa), STT x -> false
    | sigma, vs, Neg xb, SUntil (xa, x) -> false
    | sigma, vs, Neg xb, SSince (xa, x) -> false
    | sigma, vs, Neg xc, SAlways (xb, xa, x) -> false
    | sigma, vs, Neg xa, SHistoricallyOut x -> false
    | sigma, vs, Neg xc, SHistorically (xb, xa, x) -> false
    | sigma, vs, Neg xb, SEventually (xa, x) -> false
    | sigma, vs, Neg xb, SOnce (xa, x) -> false
    | sigma, vs, Neg xa, SNext x -> false
    | sigma, vs, Neg xa, SPrev x -> false
    | sigma, vs, Neg xb, SForall (xa, x) -> false
    | sigma, vs, Neg xc, SExists (xb, xa, x) -> false
    | sigma, vs, Neg xb, SIffVV (xa, x) -> false
    | sigma, vs, Neg xb, SIffSS (xa, x) -> false
    | sigma, vs, Neg xa, SImpR x -> false
    | sigma, vs, Neg xa, SImpL x -> false
    | sigma, vs, Neg xb, SAnd (xa, x) -> false
    | sigma, vs, Neg xa, SOrR x -> false
    | sigma, vs, Neg xa, SOrL x -> false
    | sigma, vs, Neg xa, SNeg x ->
        v_check_exec (_A1, _A2, _A3, _A4) sigma vs xa x
    | sigma, vs, Neg xc, SPred (xb, xa, x) -> false
    | sigma, vs, Neg xa, STT x -> false
    | sigma, vs, Pred (xb, xaa), SUntil (xa, x) -> false
    | sigma, vs, Pred (xb, xaa), SSince (xa, x) -> false
    | sigma, vs, Pred (xc, xaa), SAlways (xb, xa, x) -> false
    | sigma, vs, Pred (xa, xaa), SHistoricallyOut x -> false
    | sigma, vs, Pred (xc, xaa), SHistorically (xb, xa, x) -> false
    | sigma, vs, Pred (xb, xaa), SEventually (xa, x) -> false
    | sigma, vs, Pred (xb, xaa), SOnce (xa, x) -> false
    | sigma, vs, Pred (xa, xaa), SNext x -> false
    | sigma, vs, Pred (xa, xaa), SPrev x -> false
    | sigma, vs, Pred (xb, xaa), SForall (xa, x) -> false
    | sigma, vs, Pred (xc, xaa), SExists (xb, xa, x) -> false
    | sigma, vs, Pred (xb, xaa), SIffVV (xa, x) -> false
    | sigma, vs, Pred (xb, xaa), SIffSS (xa, x) -> false
    | sigma, vs, Pred (xa, xaa), SImpR x -> false
    | sigma, vs, Pred (xa, xaa), SImpL x -> false
    | sigma, vs, Pred (xb, xaa), SAnd (xa, x) -> false
    | sigma, vs, Pred (xa, xaa), SOrR x -> false
    | sigma, vs, Pred (xa, xaa), SOrL x -> false
    | sigma, vs, Pred (xa, xaa), SNeg x -> false
    | sigma, vs, Pred (xc, xaa), SPred (xb, xa, x) ->
        equal_lista equal_char xc xa &&
          (equal_lista (equal_trm _A2) xaa x &&
            mk_values_subset (equal_list equal_char) _A2 (_A2, _A3) xc
              (eval_trms_set _A2 vs xaa) (gamma sigma xb))
    | sigma, vs, Pred (xa, xaa), STT x -> false
    | sigma, vs, FF, p -> false
    | sigma, vs, TT, SUntil (xa, x) -> false
    | sigma, vs, TT, SSince (xa, x) -> false
    | sigma, vs, TT, SAlways (xb, xa, x) -> false
    | sigma, vs, TT, SHistoricallyOut x -> false
    | sigma, vs, TT, SHistorically (xb, xa, x) -> false
    | sigma, vs, TT, SEventually (xa, x) -> false
    | sigma, vs, TT, SOnce (xa, x) -> false
    | sigma, vs, TT, SNext x -> false
    | sigma, vs, TT, SPrev x -> false
    | sigma, vs, TT, SForall (xa, x) -> false
    | sigma, vs, TT, SExists (xb, xa, x) -> false
    | sigma, vs, TT, SIffVV (xa, x) -> false
    | sigma, vs, TT, SIffSS (xa, x) -> false
    | sigma, vs, TT, SImpR x -> false
    | sigma, vs, TT, SImpL x -> false
    | sigma, vs, TT, SAnd (xa, x) -> false
    | sigma, vs, TT, SOrR x -> false
    | sigma, vs, TT, SOrL x -> false
    | sigma, vs, TT, SNeg x -> false
    | sigma, vs, TT, SPred (xb, xa, x) -> false
    | sigma, vs, TT, STT x -> true;;

let rec p_check_exec (_A1, _A2, _A3, _A4)
  sigma =
    (fun vs phi a ->
      (match a with Inl aa -> s_check_exec (_A1, _A2, _A3, _A4) sigma vs phi aa
        | Inr aa -> v_check_exec (_A1, _A2, _A3, _A4) sigma vs phi aa));;

let rec is_valid
  x = p_check_exec
        (default_literal, equal_literal, infinite_literal, linorder_literal) x;;

let rec str_s_at x = s_at x;;

let rec str_v_at x = v_at x;;

let rec fstfinite _A xs = list_all (finite _A) xs;;

let rec str_s_check
  x = s_check_exec
        (default_literal, equal_literal, infinite_literal, linorder_literal) x;;

let rec str_v_check
  x = v_check_exec
        (default_literal, equal_literal, infinite_literal, linorder_literal) x;;

let rec trace_rbt_of_list _A
  xa = Abs_trace_rbt
         (if sorted_wrt less_eq_nat (map snd xa) && fstfinite _A (map fst xa)
           then (if null xa then (zero_nata, (zero_nata, empty))
                  else (size_list xa, (snd (last xa), bulkload xa)))
           else (zero_nata, (zero_nata, empty)));;

let rec trace_of_list _A xs = Trace_RBT (trace_rbt_of_list _A xs);;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let rec execute_trivial_eval (_A1, _A2, _A3, _A4)
  sigma vars i phi =
    eval (_A1, _A2, _A3, _A4) sigma
      (fun p1 p2 ->
        less_eq_nat (p_pred (fun _ -> one_nat) p1)
          (p_pred (fun _ -> one_nat) p2))
      vars i phi;;

end;; (*struct MFOTL_VerifiedExplanator2*)
