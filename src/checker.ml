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

module Whymon : sig
  type nat
  val integer_of_nat : nat -> Z.t
  type 'a set = Set of 'a list | Coset of 'a list
  type 'a trm = Var of string | Const of 'a
  type event_data = EInt of Z.t | EString of string
  type 'a trace
  type ('a, 'b) sum = Inl of 'a | Inr of 'b
  type enat = Enat of nat | Infinity_enat
  type i
  type 'a formula = TT | FF | Eq_Const of string * 'a |
    Pred of string * 'a trm list | Neg of 'a formula |
    Or of 'a formula * 'a formula | And of 'a formula * 'a formula |
    Imp of 'a formula * 'a formula | Iff of 'a formula * 'a formula |
    Exists of string * 'a formula | Forall of string * 'a formula |
    Prev of i * 'a formula | Next of i * 'a formula | Once of i * 'a formula |
    Historically of i * 'a formula | Eventually of i * 'a formula |
    Always of i * 'a formula | Since of 'a formula * i * 'a formula |
    Until of 'a formula * i * 'a formula
  type ('b, 'a) part
  type ('a, 'b) pdt = Leaf of 'b | Node of string * ('a, ('a, 'b) pdt) part
  type 'a sproof = STT of nat | SPred of nat * string * 'a trm list |
    SEq_Const of nat * string * 'a | SNeg of 'a vproof | SOrL of 'a sproof |
    SOrR of 'a sproof | SAnd of 'a sproof * 'a sproof | SImpL of 'a vproof |
    SImpR of 'a sproof | SIffSS of 'a sproof * 'a sproof |
    SIffVV of 'a vproof * 'a vproof | SExists of string * 'a * 'a sproof |
    SForall of string * ('a, 'a sproof) part | SPrev of 'a sproof |
    SNext of 'a sproof | SOnce of nat * 'a sproof |
    SEventually of nat * 'a sproof | SHistorically of nat * nat * 'a sproof list
    | SHistoricallyOut of nat | SAlways of nat * nat * 'a sproof list |
    SSince of 'a sproof * 'a sproof list | SUntil of 'a sproof list * 'a sproof
  and 'a vproof = VFF of nat | VPred of nat * string * 'a trm list |
    VEq_Const of nat * string * 'a | VNeg of 'a sproof |
    VOr of 'a vproof * 'a vproof | VAndL of 'a vproof | VAndR of 'a vproof |
    VImp of 'a sproof * 'a vproof | VIffSV of 'a sproof * 'a vproof |
    VIffVS of 'a vproof * 'a sproof | VExists of string * ('a, 'a vproof) part |
    VForall of string * 'a * 'a vproof | VPrev of 'a vproof | VPrevZ |
    VPrevOutL of nat | VPrevOutR of nat | VNext of 'a vproof | VNextOutL of nat
    | VNextOutR of nat | VOnceOut of nat | VOnce of nat * nat * 'a vproof list |
    VEventually of nat * nat * 'a vproof list | VHistorically of nat * 'a vproof
    | VAlways of nat * 'a vproof | VSinceOut of nat |
    VSince of nat * 'a vproof * 'a vproof list |
    VSinceInf of nat * nat * 'a vproof list |
    VUntil of nat * 'a vproof list * 'a vproof |
    VUntilInf of nat * nat * 'a vproof list
  val interval : nat -> enat -> i
  val part_hd : ('a, 'b) part -> 'b
  val subsvals : ('a, 'b) part -> ('a set * 'b) list
  val check :
    (string * event_data list) trace ->
      event_data formula ->
        (event_data, (event_data sproof, event_data vproof) sum) pdt -> bool
  val ed_set : event_data list -> event_data set
  val sub_nat : nat -> nat -> nat
  val sum_nat : nat -> nat -> nat
  val abs_part : (event_data set * 'a) list -> (event_data, 'a) part
  val nat_of_integer : Z.t -> nat
  val specialized_set :
    (string * event_data list) list -> (string * event_data list) set
  val collect_paths_specialized :
    (string * event_data list) trace ->
      event_data formula ->
        (event_data, (event_data sproof, event_data vproof) sum) pdt ->
          (event_data set list) set option
  val trace_of_list_specialized :
    ((string * event_data list) set * nat) list ->
      (string * event_data list) trace
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

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

type 'a set = Set of 'a list | Coset of 'a list;;

let rec eq _A a b = equal _A a b;;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec member _A
  x xa1 = match x, xa1 with x, Coset xs -> not (membera _A xs x)
    | x, Set xs -> membera _A xs x;;

type 'a nonunit = unit;;

type 'a infinite = {nonunit_infinite : 'a nonunit};;

let rec less_eq_set (_A1, _A2)
  a b = match a, b with Coset xs, Set ys -> false
    | a, Coset ys -> list_all (fun y -> not (member _A2 y a)) ys
    | Set xs, b -> list_all (fun x -> member _A2 x b) xs;;

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

type 'a trm = Var of string | Const of 'a;;

let rec equal_trma _A x0 x1 = match x0, x1 with Var x1, Const x2 -> false
                        | Const x2, Var x1 -> false
                        | Const x2, Const y2 -> eq _A x2 y2
                        | Var x1, Var y1 -> Stdlib.(=) x1 y1;;

let rec equal_trm _A = ({equal = equal_trma _A} : 'a trm equal);;

let rec equal_proda _A _B (x1, x2) (y1, y2) = eq _A x1 y1 && eq _B x2 y2;;

let rec equal_prod _A _B = ({equal = equal_proda _A _B} : ('a * 'b) equal);;

let rec nonunit_prod _B = (() : ('a * 'b) nonunit);;

let rec infinite_prod _B =
  ({nonunit_infinite = (nonunit_prod _B)} : ('a * 'b) infinite);;

let equal_string8 = ({equal = Stdlib.(=)} : string equal);;

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

type event_data = EInt of Z.t | EString of string;;

let rec equal_event_dataa
  x0 x1 = match x0, x1 with EInt x1, EString x2 -> false
    | EString x2, EInt x1 -> false
    | EString x2, EString y2 -> Stdlib.(=) x2 y2
    | EInt x1, EInt y1 -> Z.equal x1 y1;;

let equal_event_data = ({equal = equal_event_dataa} : event_data equal);;

let default_event_dataa : event_data = EInt Z.zero;;

type 'a default = {default : 'a};;
let default _A = _A.default;;

let default_event_data =
  ({default = default_event_dataa} : event_data default);;

let rec less_eq_event_data
  x0 x1 = match x0, x1 with EInt x, EInt y -> Z.leq x y
    | EString x, EString y -> Stdlib.(<=) x y
    | EInt uu, EString uv -> true
    | EString v, EInt va -> false;;

let rec less_event_data
  x y = less_eq_event_data x y && not (less_eq_event_data y x);;

let ord_event_data =
  ({less_eq = less_eq_event_data; less = less_event_data} : event_data ord);;

let preorder_event_data =
  ({ord_preorder = ord_event_data} : event_data preorder);;

let order_event_data =
  ({preorder_order = preorder_event_data} : event_data order);;

let linorder_event_data =
  ({order_linorder = order_event_data} : event_data linorder);;

let nonunit_event_data = (() : event_data nonunit);;

let infinite_event_data =
  ({nonunit_infinite = nonunit_event_data} : event_data infinite);;

type num = One | Bit0 of num | Bit1 of num;;

type ('a, 'b) mapping = Mapping of ('a * 'b) list;;

type 'a trace_rbt =
  Abs_trace_rbt of (nat * (nat * (nat, ('a set * nat)) mapping));;

type 'a trace = Trace_RBT of 'a trace_rbt;;

type ('a, 'b) sum = Inl of 'a | Inr of 'b;;

type enat = Enat of nat | Infinity_enat;;

type i = Abs_I of (nat * enat);;

type 'a formula = TT | FF | Eq_Const of string * 'a |
  Pred of string * 'a trm list | Neg of 'a formula |
  Or of 'a formula * 'a formula | And of 'a formula * 'a formula |
  Imp of 'a formula * 'a formula | Iff of 'a formula * 'a formula |
  Exists of string * 'a formula | Forall of string * 'a formula |
  Prev of i * 'a formula | Next of i * 'a formula | Once of i * 'a formula |
  Historically of i * 'a formula | Eventually of i * 'a formula |
  Always of i * 'a formula | Since of 'a formula * i * 'a formula |
  Until of 'a formula * i * 'a formula;;

type ('b, 'a) part = Abs_part of ('b set * 'a) list;;

type ('a, 'b) pdt = Leaf of 'b | Node of string * ('a, ('a, 'b) pdt) part;;

type 'a sproof = STT of nat | SPred of nat * string * 'a trm list |
  SEq_Const of nat * string * 'a | SNeg of 'a vproof | SOrL of 'a sproof |
  SOrR of 'a sproof | SAnd of 'a sproof * 'a sproof | SImpL of 'a vproof |
  SImpR of 'a sproof | SIffSS of 'a sproof * 'a sproof |
  SIffVV of 'a vproof * 'a vproof | SExists of string * 'a * 'a sproof |
  SForall of string * ('a, 'a sproof) part | SPrev of 'a sproof |
  SNext of 'a sproof | SOnce of nat * 'a sproof | SEventually of nat * 'a sproof
  | SHistorically of nat * nat * 'a sproof list | SHistoricallyOut of nat |
  SAlways of nat * nat * 'a sproof list | SSince of 'a sproof * 'a sproof list |
  SUntil of 'a sproof list * 'a sproof
and 'a vproof = VFF of nat | VPred of nat * string * 'a trm list |
  VEq_Const of nat * string * 'a | VNeg of 'a sproof |
  VOr of 'a vproof * 'a vproof | VAndL of 'a vproof | VAndR of 'a vproof |
  VImp of 'a sproof * 'a vproof | VIffSV of 'a sproof * 'a vproof |
  VIffVS of 'a vproof * 'a sproof | VExists of string * ('a, 'a vproof) part |
  VForall of string * 'a * 'a vproof | VPrev of 'a vproof | VPrevZ |
  VPrevOutL of nat | VPrevOutR of nat | VNext of 'a vproof | VNextOutL of nat |
  VNextOutR of nat | VOnceOut of nat | VOnce of nat * nat * 'a vproof list |
  VEventually of nat * nat * 'a vproof list | VHistorically of nat * 'a vproof |
  VAlways of nat * 'a vproof | VSinceOut of nat |
  VSince of nat * 'a vproof * 'a vproof list |
  VSinceInf of nat * nat * 'a vproof list |
  VUntil of nat * 'a vproof list * 'a vproof |
  VUntilInf of nat * nat * 'a vproof list;;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let one_nat : nat = Nat (Z.of_int 1);;

let rec suc n = plus_nat n one_nat;;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec minus_nat
  m n = Nat (max ord_integer Z.zero
              (Z.sub (integer_of_nat m) (integer_of_nat n)));;

let zero_nat : nat = Nat Z.zero;;

let rec nth
  (x :: xs) n =
    (if equal_nata n zero_nat then x else nth xs (minus_nat n one_nat));;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec rev xs = fold (fun a b -> a :: b) xs [];;

let rec upt i j = (if less_nat i j then i :: upt (suc i) j else []);;

let rec ball (Set xs) p = list_all p xs;;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec last (x :: xs) = (if null xs then x else last xs);;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec image f (Set xs) = Set (map f xs);;

let rec map_of _A
  x0 k = match x0, k with
    (l, v) :: ps, k -> (if eq _A l k then Some v else map_of _A ps k)
    | [], k -> None;;

let rec removeAll _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: xs ->
        (if eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec inserta _A x xs = (if membera _A xs x then xs else x :: xs);;

let rec insert _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (removeAll _A x xs)
    | x, Set xs -> Set (inserta _A x xs);;

let rec remove _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (inserta _A x xs)
    | x, Set xs -> Set (removeAll _A x xs);;

let rec fun_upd _A f a b = (fun x -> (if eq _A x a then b else f x));;

let rec filter
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filter p xs else filter p xs);;

let rec hd (x21 :: x22) = x21;;

let rec list_ex p x1 = match p, x1 with p, [] -> false
                  | p, x :: xs -> p x || list_ex p xs;;

let rec rep_trace_rbt (Abs_trace_rbt x) = x;;

let bot_set : 'a set = Set [];;

let rec the (Some x2) = x2;;

let rec lookup _A (Mapping xs) = map_of _A xs;;

let rec trace_rbt_nth
  xa = (let (n, (m, t)) = rep_trace_rbt xa in
         (fun i ->
           (if less_nat i n then the (lookup equal_nat t i)
             else (bot_set, plus_nat (minus_nat i n) m))));;

let rec snd (x1, x2) = x2;;

let rec tau (Trace_RBT t) i = snd (trace_rbt_nth t i);;

let rec rep_I (Abs_I x) = x;;

let rec fst (x1, x2) = x1;;

let rec left x = fst (rep_I x);;

let rec distinct _A = function [] -> true
                      | x :: xs -> not (membera _A xs x) && distinct _A xs;;

let top_set : 'a set = Coset [];;

let rec inf_set _A
  a x1 = match a, x1 with a, Coset xs -> fold (remove _A) xs a
    | a, Set xs -> Set (filter (fun x -> member _A x a) xs);;

let rec product
  (Set xs) (Set ys) = Set (maps (fun x -> map (fun a -> (x, a)) ys) xs);;

let rec set_Cons _A
  a xs =
    image (fun (aa, b) -> aa :: b)
      (product (inf_set _A (image (fun x -> x) a) top_set)
        (inf_set (equal_list _A) top_set (image (fun xsa -> xsa) xs)));;

let empty : ('a, 'b) mapping = Mapping [];;

let rec right x = snd (rep_I x);;

let rec partition
  p x1 = match p, x1 with p, [] -> ([], [])
    | p, x :: xs ->
        (let (yes, no) = partition p xs in
          (if p x then (x :: yes, no) else (yes, x :: no)));;

let rec is_none = function Some x -> false
                  | None -> true;;

let rec gamma (Trace_RBT t) i = fst (trace_rbt_nth t i);;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (suc n) xs
                     | n, [] -> n;;

let rec sorted_wrt p x1 = match p, x1 with p, [] -> true
                     | p, x :: ys -> list_all (p x) ys && sorted_wrt p ys;;

let rec size_list x = gen_length zero_nat x;;

let rec bulkload
  vs = Mapping (map (fun n -> (n, nth vs n)) (upt zero_nat (size_list vs)));;

let rec lTP_rec
  sigma t i =
    (if less_eq_nat (tau sigma (suc i)) t
      then lTP_rec sigma t (plus_nat i one_nat) else i);;

let rec ltp
  sigma t =
    (if less_nat t (tau sigma zero_nat)
      then failwith "LTP: undefined" (fun _ -> ltp sigma t)
      else lTP_rec sigma t zero_nat);;

let rec positions _A
  xa0 x = match xa0, x with [], x -> []
    | y :: ys, x ->
        (if eq _A x y then zero_nat :: map suc (positions _A ys x)
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

let rec sup_set _A
  x0 a = match x0, a with
    Coset xs, a -> Coset (filter (fun x -> not (member _A x a)) xs)
    | Set xs, a -> fold (insert _A) xs a;;

let rec sup_seta _A (Set xs) = fold (sup_set _A) xs bot_set;;

let rec rep_part (Abs_part x) = x;;

let rec vals x = Set (map snd (rep_part x));;

let rec vars
  = function Leaf uu -> bot_set
    | Node (x, part) ->
        sup_set equal_string8 (insert equal_string8 x bot_set)
          (sup_seta equal_string8 (image vars (vals part)));;

let rec finite _A = function Coset xs -> false
                    | Set xs -> true;;

let rec less_eq_enat q x1 = match q, x1 with Infinity_enat, Enat n -> false
                       | q, Infinity_enat -> true
                       | Enat m, Enat n -> less_eq_nat m n;;

let rec interval
  l r = Abs_I (if less_eq_enat (Enat l) r then (l, r)
                else rep_I (failwith "undefined"));;

let rec part_hd xa = snd (hd (rep_part xa));;

let rec s_at
  = function STT i -> i
    | SPred (i, uu, uv) -> i
    | SEq_Const (i, uw, ux) -> i
    | SNeg vp -> v_at vp
    | SOrL sp1 -> s_at sp1
    | SOrR sp2 -> s_at sp2
    | SAnd (sp1, uy) -> s_at sp1
    | SImpL vp1 -> v_at vp1
    | SImpR sp2 -> s_at sp2
    | SIffSS (sp1, uz) -> s_at sp1
    | SIffVV (vp1, va) -> v_at vp1
    | SExists (vb, vc, sp) -> s_at sp
    | SForall (vd, part) -> s_at (part_hd part)
    | SPrev sp -> plus_nat (s_at sp) one_nat
    | SNext sp -> minus_nat (s_at sp) one_nat
    | SOnce (i, ve) -> i
    | SEventually (i, vf) -> i
    | SHistorically (i, vg, vh) -> i
    | SHistoricallyOut i -> i
    | SAlways (i, vi, vj) -> i
    | SSince (sp2, sp1s) ->
        (match sp1s with [] -> s_at sp2 | _ :: _ -> s_at (last sp1s))
    | SUntil (sp1s, sp2) ->
        (match sp1s with [] -> s_at sp2 | sp1 :: _ -> s_at sp1)
and v_at = function VFF i -> i
           | VPred (i, vk, vl) -> i
           | VEq_Const (i, vm, vn) -> i
           | VNeg sp -> s_at sp
           | VOr (vp1, vo) -> v_at vp1
           | VAndL vp1 -> v_at vp1
           | VAndR vp2 -> v_at vp2
           | VImp (sp1, vq) -> s_at sp1
           | VIffSV (sp1, vr) -> s_at sp1
           | VIffVS (vp1, vs) -> v_at vp1
           | VExists (vt, part) -> v_at (part_hd part)
           | VForall (vu, vv, vp1) -> v_at vp1
           | VPrev vp -> plus_nat (v_at vp) one_nat
           | VPrevZ -> zero_nat
           | VPrevOutL i -> i
           | VPrevOutR i -> i
           | VNext vp -> minus_nat (v_at vp) one_nat
           | VNextOutL i -> i
           | VNextOutR i -> i
           | VOnceOut i -> i
           | VOnce (i, vw, vx) -> i
           | VEventually (i, vy, vz) -> i
           | VHistorically (i, wa) -> i
           | VAlways (i, wb) -> i
           | VSinceOut i -> i
           | VSince (i, wc, wd) -> i
           | VSinceInf (i, we, wf) -> i
           | VUntil (i, wg, wh) -> i
           | VUntilInf (i, wi, wj) -> i;;

let rec distinct_paths
  = function Leaf uu -> true
    | Node (x, part) ->
        ball (vals part)
          (fun e -> not (member equal_string8 x (vars e)) && distinct_paths e);;

let rec less_enat x0 q = match x0, q with Infinity_enat, q -> false
                    | Enat m, Infinity_enat -> true
                    | Enat m, Enat n -> less_nat m n;;

let rec equal_option _A x0 x1 = match x0, x1 with None, Some x2 -> false
                          | Some x2, None -> false
                          | Some x2, Some y2 -> eq _A x2 y2
                          | None, None -> true;;

let rec check_values _A
  uu uv uw x3 = match uu, uv, uw, x3 with uu, uv, uw, None -> None
    | vs, Const c :: ts, u :: us, Some v ->
        (if eq _A c u then check_values _A vs ts us (Some v) else None)
    | vs, Var x :: ts, u :: us, Some v ->
        (if member _A u (vs x) &&
              (equal_option _A (v x) (Some u) || is_none (v x))
          then check_values _A vs ts us
                 (Some (fun_upd equal_string8 v x (Some u)))
          else None)
    | vs, [], [], Some v -> Some v
    | ux, [], va :: vb, Some v -> None
    | ux, Var vc :: vb, [], Some v -> None
    | ux, va :: vb, [], Some v -> None;;

let rec mk_values_subset_Compl (_A1, _A2, _A3)
  sigma r vs ts i =
    ball (gamma sigma i)
      (fun (q, us) ->
        not (Stdlib.(=) q r) ||
          is_none (check_values _A2 vs ts us (Some (fun _ -> None))));;

let rec check_upt_LTP_p
  sigma ia li xs i =
    (match xs
      with [] ->
        (if equal_nata (left ia) zero_nat then less_nat i li
          else (if not (less_eq_nat li i) && equal_nata (left ia) zero_nat
                 then less_nat zero_nat (minus_nat (tau sigma li) (tau sigma i))
                 else less_nat (minus_nat (tau sigma i) (tau sigma li))
                        (left ia)))
      | _ :: _ ->
        equal_lista equal_nat xs (upt li (plus_nat li (size_list xs))) &&
          (if equal_nata (left ia) zero_nat
            then equal_nata (minus_nat (plus_nat li (size_list xs)) one_nat) i
            else less_eq_nat (minus_nat (plus_nat li (size_list xs)) one_nat)
                   i &&
                   (less_eq_nat (left ia)
                      (minus_nat (tau sigma i)
                        (tau sigma
                          (minus_nat (plus_nat li (size_list xs)) one_nat))) &&
                     less_nat
                       (minus_nat (tau sigma i)
                         (tau sigma (plus_nat li (size_list xs))))
                       (left ia))));;

let rec check_upt_ETP_f
  sigma ia i xs hi =
    (let j = minus_nat (suc hi) (size_list xs) in
      (match xs
        with [] ->
          (if equal_nata (left ia) zero_nat then less_eq_nat (suc hi) i
            else less_nat (minus_nat (tau sigma hi) (tau sigma i)) (left ia))
        | _ :: _ ->
          equal_lista equal_nat xs (upt j (suc hi)) &&
            ((if equal_nata (left ia) zero_nat then less_eq_nat j i
               else (if equal_nata j zero_nat then true
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
    (let (fintXs, inftXs) = partition (fun tX -> finite _C1 (snd tX)) tXs in
      (if null inftXs
        then less_eq_set
               ((infinite_prod (infinite_list _C1.nonunit_infinite)),
                 (equal_prod _A (equal_list _C2)))
               (product (insert _A p bot_set) (mk_values _B _C2 tXs)) x
        else (let inf_dups =
                filter
                  (fun tX -> membera (equal_trm _B) (map fst fintXs) (fst tX))
                  inftXs
                in
               (if null inf_dups
                 then (if finite
                            (infinite_prod (infinite_list _C1.nonunit_infinite))
                            x
                        then false
                        else failwith "subset on infinite subset"
                               (fun _ ->
                                 less_eq_set
                                   ((infinite_prod
                                      (infinite_list _C1.nonunit_infinite)),
                                     (equal_prod _A (equal_list _C2)))
                                   (product (insert _A p bot_set)
                                     (mk_values _B _C2 tXs))
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
                               ((infinite_prod
                                  (infinite_list _C1.nonunit_infinite)),
                                 (equal_prod _A (equal_list _C2)))
                               (product (insert _A p bot_set)
                                 (mk_values _B _C2 tXs))
                               x
                        else (if finite
                                   (infinite_prod
                                     (infinite_list _C1.nonunit_infinite))
                                   x
                               then false
                               else failwith "subset on infinite subset"
                                      (fun _ ->
less_eq_set
  ((infinite_prod (infinite_list _C1.nonunit_infinite)),
    (equal_prod _A (equal_list _C2)))
  (product (insert _A p bot_set) (mk_values _B _C2 tXs)) x)))))));;

let rec eval_trm_set _A vs x1 = match vs, x1 with vs, Var x -> (Var x, vs x)
                          | vs, Const x -> (Const x, insert _A x bot_set);;

let rec eval_trms_set _A vs ts = map (eval_trm_set _A vs) ts;;

let rec set_eq (_A1, _A2)
  a b = less_eq_set (_A1, _A2) a b && less_eq_set (_A1, _A2) b a;;

let rec v_check_exec (_A1, _A2, _A3, _A4)
  sigma vs x2 vp = match sigma, vs, x2, vp with
    sigma, vs, Until (phi, i, psi), vp ->
      (match vp with VFF _ -> false | VPred (_, _, _) -> false
        | VEq_Const (_, _, _) -> false | VNeg _ -> false | VOr (_, _) -> false
        | VAndL _ -> false | VAndR _ -> false | VImp (_, _) -> false
        | VIffSV (_, _) -> false | VIffVS (_, _) -> false
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
              with Enat b -> less_nat j (ltp sigma (plus_nat (tau sigma ia) b))
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
          | VEq_Const (_, _, _) -> false | VNeg _ -> false | VOr (_, _) -> false
          | VAndL _ -> false | VAndR _ -> false | VImp (_, _) -> false
          | VIffSV (_, _) -> false | VIffVS (_, _) -> false
          | VExists (_, _) -> false | VForall (_, _, _) -> false
          | VPrev _ -> false | VPrevZ -> false | VPrevOutL _ -> false
          | VPrevOutR _ -> false | VNext _ -> false | VNextOutL _ -> false
          | VNextOutR _ -> false | VOnceOut _ -> false
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
          | VEq_Const (_, _, _) -> false | VNeg _ -> false | VOr (_, _) -> false
          | VAndL _ -> false | VAndR _ -> false | VImp (_, _) -> false
          | VIffSV (_, _) -> false | VIffVS (_, _) -> false
          | VExists (_, _) -> false | VForall (_, _, _) -> false
          | VPrev _ -> false | VPrevZ -> false | VPrevOutL _ -> false
          | VPrevOutR _ -> false | VNext _ -> false | VNextOutL _ -> false
          | VNextOutR _ -> false | VOnceOut _ -> false
          | VOnce (_, _, _) -> false | VEventually (_, _, _) -> false
          | VHistorically (_, _) -> false | VAlways (_, _) -> false
          | VSinceOut ia ->
            less_nat (tau sigma ia) (plus_nat (tau sigma zero_nat) (left i))
          | VSince (ia, vp1, vp2s) ->
            (let j = v_at vp1 in
              (match right i
                with Enat a ->
                  less_eq_nat (minus_nat (tau sigma ia) (tau sigma j)) a
                | Infinity_enat -> true) &&
                (less_eq_nat j ia &&
                  (less_eq_nat (plus_nat (tau sigma zero_nat) (left i))
                     (tau sigma ia) &&
                    (check_upt_LTP_p sigma i j (map v_at vp2s) ia &&
                      (v_check_exec (_A1, _A2, _A3, _A4) sigma vs phi vp1 &&
                        list_all
                          (v_check_exec (_A1, _A2, _A3, _A4) sigma vs psi)
                          vp2s)))))
          | VSinceInf (ia, li, vp2s) ->
            (match right i
              with Enat b ->
                (equal_nata li zero_nat ||
                  less_nat b
                    (minus_nat (tau sigma ia)
                      (tau sigma (minus_nat li one_nat)))) &&
                  less_eq_nat (minus_nat (tau sigma ia) (tau sigma li)) b
              | Infinity_enat -> equal_nata li zero_nat) &&
              (less_eq_nat (plus_nat (tau sigma zero_nat) (left i))
                 (tau sigma ia) &&
                (check_upt_LTP_p sigma i li (map v_at vp2s) ia &&
                  list_all (v_check_exec (_A1, _A2, _A3, _A4) sigma vs psi)
                    vp2s))
          | VUntil (_, _, _) -> false | VUntilInf (_, _, _) -> false)
    | sigma, vs, Once (i, phi), vp ->
        (match vp with VFF _ -> false | VPred (_, _, _) -> false
          | VEq_Const (_, _, _) -> false | VNeg _ -> false | VOr (_, _) -> false
          | VAndL _ -> false | VAndR _ -> false | VImp (_, _) -> false
          | VIffSV (_, _) -> false | VIffVS (_, _) -> false
          | VExists (_, _) -> false | VForall (_, _, _) -> false
          | VPrev _ -> false | VPrevZ -> false | VPrevOutL _ -> false
          | VPrevOutR _ -> false | VNext _ -> false | VNextOutL _ -> false
          | VNextOutR _ -> false
          | VOnceOut ia ->
            less_nat (tau sigma ia) (plus_nat (tau sigma zero_nat) (left i))
          | VOnce (ia, li, vps) ->
            (match right i
              with Enat b ->
                (equal_nata li zero_nat ||
                  less_nat b
                    (minus_nat (tau sigma ia)
                      (tau sigma (minus_nat li one_nat)))) &&
                  less_eq_nat (minus_nat (tau sigma ia) (tau sigma li)) b
              | Infinity_enat -> equal_nata li zero_nat) &&
              (less_eq_nat (plus_nat (tau sigma zero_nat) (left i))
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
    | sigma, vs, Always (xc, xaa), VEq_Const (xb, xa, x) -> false
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
    | sigma, vs, Historically (xc, xaa), VEq_Const (xb, xa, x) -> false
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
          (Enat (minus_nat (tau sigma (plus_nat x one_nat))
                  (tau sigma (minus_nat (plus_nat x one_nat) one_nat))))
    | sigma, vs, Next (xa, xaa), VNextOutL x ->
        less_nat
          (minus_nat (tau sigma (plus_nat x one_nat))
            (tau sigma (minus_nat (plus_nat x one_nat) one_nat)))
          (left xa)
    | sigma, vs, Next (xa, xaa), VNext x ->
        (let j = v_at x in
         let i = v_at (VNext x) in
          equal_nata j (plus_nat i one_nat) &&
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
    | sigma, vs, Next (xc, xaa), VEq_Const (xb, xa, x) -> false
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
        less_nat zero_nat x &&
          less_enat (right xa)
            (Enat (minus_nat (tau sigma x) (tau sigma (minus_nat x one_nat))))
    | sigma, vs, Prev (xa, xaa), VPrevOutL x ->
        less_nat zero_nat x &&
          less_nat (minus_nat (tau sigma x) (tau sigma (minus_nat x one_nat)))
            (left xa)
    | sigma, vs, Prev (x, xa), VPrevZ -> equal_nata (v_at VPrevZ) zero_nat
    | sigma, vs, Prev (xa, xaa), VPrev x ->
        (let j = v_at x in
         let i = v_at (VPrev x) in
          equal_nata i (plus_nat j one_nat) &&
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
    | sigma, vs, Prev (xc, xaa), VEq_Const (xb, xa, x) -> false
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
        Stdlib.(=) xc xb &&
          v_check_exec (_A1, _A2, _A3, _A4) sigma
            (fun_upd equal_string8 vs xc (insert _A3 xa bot_set)) xaa x
    | sigma, vs, Forall (xb, xaa), VExists (xa, x) -> false
    | sigma, vs, Forall (xb, xaa), VIffVS (xa, x) -> false
    | sigma, vs, Forall (xb, xaa), VIffSV (xa, x) -> false
    | sigma, vs, Forall (xb, xaa), VImp (xa, x) -> false
    | sigma, vs, Forall (xa, xaa), VAndR x -> false
    | sigma, vs, Forall (xa, xaa), VAndL x -> false
    | sigma, vs, Forall (xb, xaa), VOr (xa, x) -> false
    | sigma, vs, Forall (xa, xaa), VNeg x -> false
    | sigma, vs, Forall (xc, xaa), VEq_Const (xb, xa, x) -> false
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
          Stdlib.(=) xb xa &&
            ball (subsVals x)
              (fun (sub, vp) ->
                equal_nata (v_at vp) i &&
                  v_check_exec (_A1, _A2, _A3, _A4) sigma
                    (fun_upd equal_string8 vs xb sub) xaa vp))
    | sigma, vs, Exists (xb, xaa), VIffVS (xa, x) -> false
    | sigma, vs, Exists (xb, xaa), VIffSV (xa, x) -> false
    | sigma, vs, Exists (xb, xaa), VImp (xa, x) -> false
    | sigma, vs, Exists (xa, xaa), VAndR x -> false
    | sigma, vs, Exists (xa, xaa), VAndL x -> false
    | sigma, vs, Exists (xb, xaa), VOr (xa, x) -> false
    | sigma, vs, Exists (xa, xaa), VNeg x -> false
    | sigma, vs, Exists (xc, xaa), VEq_Const (xb, xa, x) -> false
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
    | sigma, vs, Iff (xc, xaa), VEq_Const (xb, xa, x) -> false
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
    | sigma, vs, Imp (xc, xaa), VEq_Const (xb, xa, x) -> false
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
    | sigma, vs, And (xc, xaa), VEq_Const (xb, xa, x) -> false
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
    | sigma, vs, Or (xc, xaa), VEq_Const (xb, xa, x) -> false
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
    | sigma, vs, Neg xc, VEq_Const (xb, xa, x) -> false
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
    | sigma, vs, Pred (xc, xaa), VEq_Const (xb, xa, x) -> false
    | sigma, vs, Pred (xc, xaa), VPred (xb, xa, x) ->
        Stdlib.(=) xc xa &&
          (equal_lista (equal_trm _A3) xaa x &&
            mk_values_subset_Compl (_A2, _A3, _A4) sigma xc vs xaa xb)
    | sigma, vs, Pred (xa, xaa), VFF x -> false
    | sigma, vs, Eq_Const (xc, xaa), VUntilInf (xb, xa, x) -> false
    | sigma, vs, Eq_Const (xc, xaa), VUntil (xb, xa, x) -> false
    | sigma, vs, Eq_Const (xc, xaa), VSinceInf (xb, xa, x) -> false
    | sigma, vs, Eq_Const (xc, xaa), VSince (xb, xa, x) -> false
    | sigma, vs, Eq_Const (xa, xaa), VSinceOut x -> false
    | sigma, vs, Eq_Const (xb, xaa), VAlways (xa, x) -> false
    | sigma, vs, Eq_Const (xb, xaa), VHistorically (xa, x) -> false
    | sigma, vs, Eq_Const (xc, xaa), VEventually (xb, xa, x) -> false
    | sigma, vs, Eq_Const (xc, xaa), VOnce (xb, xa, x) -> false
    | sigma, vs, Eq_Const (xa, xaa), VOnceOut x -> false
    | sigma, vs, Eq_Const (xa, xaa), VNextOutR x -> false
    | sigma, vs, Eq_Const (xa, xaa), VNextOutL x -> false
    | sigma, vs, Eq_Const (xa, xaa), VNext x -> false
    | sigma, vs, Eq_Const (xa, xaa), VPrevOutR x -> false
    | sigma, vs, Eq_Const (xa, xaa), VPrevOutL x -> false
    | sigma, vs, Eq_Const (x, xa), VPrevZ -> false
    | sigma, vs, Eq_Const (xa, xaa), VPrev x -> false
    | sigma, vs, Eq_Const (xc, xaa), VForall (xb, xa, x) -> false
    | sigma, vs, Eq_Const (xb, xaa), VExists (xa, x) -> false
    | sigma, vs, Eq_Const (xb, xaa), VIffVS (xa, x) -> false
    | sigma, vs, Eq_Const (xb, xaa), VIffSV (xa, x) -> false
    | sigma, vs, Eq_Const (xb, xaa), VImp (xa, x) -> false
    | sigma, vs, Eq_Const (xa, xaa), VAndR x -> false
    | sigma, vs, Eq_Const (xa, xaa), VAndL x -> false
    | sigma, vs, Eq_Const (xb, xaa), VOr (xa, x) -> false
    | sigma, vs, Eq_Const (xa, xaa), VNeg x -> false
    | sigma, vs, Eq_Const (xc, xaa), VEq_Const (xb, xa, x) ->
        eq _A3 xaa x && (Stdlib.(=) xc xa && not (member _A3 xaa (vs xc)))
    | sigma, vs, Eq_Const (xc, xaa), VPred (xb, xa, x) -> false
    | sigma, vs, Eq_Const (xa, xaa), VFF x -> false
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
    | sigma, vs, FF, VEq_Const (xb, xa, x) -> false
    | sigma, vs, FF, VPred (xb, xa, x) -> false
    | sigma, vs, FF, VFF x -> true
    | sigma, vs, TT, p -> false
and s_check_exec (_A1, _A2, _A3, _A4)
  sigma vs x2 sp = match sigma, vs, x2, sp with
    sigma, vs, Always (i, phi), sp ->
      (match sp with STT _ -> false | SPred (_, _, _) -> false
        | SEq_Const (_, _, _) -> false | SNeg _ -> false | SOrL _ -> false
        | SOrR _ -> false | SAnd (_, _) -> false | SImpL _ -> false
        | SImpR _ -> false | SIffSS (_, _) -> false | SIffVV (_, _) -> false
        | SExists (_, _, _) -> false | SForall (_, _) -> false
        | SPrev _ -> false | SNext _ -> false | SOnce (_, _) -> false
        | SEventually (_, _) -> false | SHistorically (_, _, _) -> false
        | SHistoricallyOut _ -> false
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
          | SEq_Const (_, _, _) -> false | SNeg _ -> false | SOrL _ -> false
          | SOrR _ -> false | SAnd (_, _) -> false | SImpL _ -> false
          | SImpR _ -> false | SIffSS (_, _) -> false | SIffVV (_, _) -> false
          | SExists (_, _, _) -> false | SForall (_, _) -> false
          | SPrev _ -> false | SNext _ -> false | SOnce (_, _) -> false
          | SEventually (_, _) -> false
          | SHistorically (ia, li, vps) ->
            (match right i
              with Enat b ->
                (equal_nata li zero_nat ||
                  less_nat b
                    (minus_nat (tau sigma ia)
                      (tau sigma (minus_nat li one_nat)))) &&
                  less_eq_nat (minus_nat (tau sigma ia) (tau sigma li)) b
              | Infinity_enat -> equal_nata li zero_nat) &&
              (less_eq_nat (plus_nat (tau sigma zero_nat) (left i))
                 (tau sigma ia) &&
                (check_upt_LTP_p sigma i li (map s_at vps) ia &&
                  list_all (s_check_exec (_A1, _A2, _A3, _A4) sigma vs phi)
                    vps))
          | SHistoricallyOut ia ->
            less_nat (tau sigma ia) (plus_nat (tau sigma zero_nat) (left i))
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
    | sigma, vs, Until (xc, xaa, xba), SEq_Const (xb, xa, x) -> false
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
                 (upt (plus_nat j one_nat) (plus_nat i one_nat)) &&
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
    | sigma, vs, Since (xc, xaa, xba), SEq_Const (xb, xa, x) -> false
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
    | sigma, vs, Eventually (xc, xaa), SEq_Const (xb, xa, x) -> false
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
    | sigma, vs, Once (xc, xaa), SEq_Const (xb, xa, x) -> false
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
          equal_nata j (plus_nat i one_nat) &&
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
    | sigma, vs, Next (xc, xaa), SEq_Const (xb, xa, x) -> false
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
          equal_nata i (plus_nat j one_nat) &&
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
    | sigma, vs, Prev (xc, xaa), SEq_Const (xb, xa, x) -> false
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
          Stdlib.(=) xb xa &&
            ball (subsVals x)
              (fun (sub, sp) ->
                equal_nata (s_at sp) i &&
                  s_check_exec (_A1, _A2, _A3, _A4) sigma
                    (fun_upd equal_string8 vs xb sub) xaa sp))
    | sigma, vs, Forall (xc, xaa), SExists (xb, xa, x) -> false
    | sigma, vs, Forall (xb, xaa), SIffVV (xa, x) -> false
    | sigma, vs, Forall (xb, xaa), SIffSS (xa, x) -> false
    | sigma, vs, Forall (xa, xaa), SImpR x -> false
    | sigma, vs, Forall (xa, xaa), SImpL x -> false
    | sigma, vs, Forall (xb, xaa), SAnd (xa, x) -> false
    | sigma, vs, Forall (xa, xaa), SOrR x -> false
    | sigma, vs, Forall (xa, xaa), SOrL x -> false
    | sigma, vs, Forall (xa, xaa), SNeg x -> false
    | sigma, vs, Forall (xc, xaa), SEq_Const (xb, xa, x) -> false
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
        Stdlib.(=) xc xb &&
          s_check_exec (_A1, _A2, _A3, _A4) sigma
            (fun_upd equal_string8 vs xc (insert _A3 xa bot_set)) xaa x
    | sigma, vs, Exists (xb, xaa), SIffVV (xa, x) -> false
    | sigma, vs, Exists (xb, xaa), SIffSS (xa, x) -> false
    | sigma, vs, Exists (xa, xaa), SImpR x -> false
    | sigma, vs, Exists (xa, xaa), SImpL x -> false
    | sigma, vs, Exists (xb, xaa), SAnd (xa, x) -> false
    | sigma, vs, Exists (xa, xaa), SOrR x -> false
    | sigma, vs, Exists (xa, xaa), SOrL x -> false
    | sigma, vs, Exists (xa, xaa), SNeg x -> false
    | sigma, vs, Exists (xc, xaa), SEq_Const (xb, xa, x) -> false
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
    | sigma, vs, Iff (xc, xaa), SEq_Const (xb, xa, x) -> false
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
    | sigma, vs, Imp (xc, xaa), SEq_Const (xb, xa, x) -> false
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
    | sigma, vs, And (xc, xaa), SEq_Const (xb, xa, x) -> false
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
    | sigma, vs, Or (xc, xaa), SEq_Const (xb, xa, x) -> false
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
    | sigma, vs, Neg xc, SEq_Const (xb, xa, x) -> false
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
    | sigma, vs, Pred (xc, xaa), SEq_Const (xb, xa, x) -> false
    | sigma, vs, Pred (xc, xaa), SPred (xb, xa, x) ->
        Stdlib.(=) xc xa &&
          (equal_lista (equal_trm _A3) xaa x &&
            mk_values_subset equal_string8 _A3 (_A1, _A3) xc
              (eval_trms_set _A3 vs xaa) (gamma sigma xb))
    | sigma, vs, Pred (xa, xaa), STT x -> false
    | sigma, vs, Eq_Const (xb, xaa), SUntil (xa, x) -> false
    | sigma, vs, Eq_Const (xb, xaa), SSince (xa, x) -> false
    | sigma, vs, Eq_Const (xc, xaa), SAlways (xb, xa, x) -> false
    | sigma, vs, Eq_Const (xa, xaa), SHistoricallyOut x -> false
    | sigma, vs, Eq_Const (xc, xaa), SHistorically (xb, xa, x) -> false
    | sigma, vs, Eq_Const (xb, xaa), SEventually (xa, x) -> false
    | sigma, vs, Eq_Const (xb, xaa), SOnce (xa, x) -> false
    | sigma, vs, Eq_Const (xa, xaa), SNext x -> false
    | sigma, vs, Eq_Const (xa, xaa), SPrev x -> false
    | sigma, vs, Eq_Const (xb, xaa), SForall (xa, x) -> false
    | sigma, vs, Eq_Const (xc, xaa), SExists (xb, xa, x) -> false
    | sigma, vs, Eq_Const (xb, xaa), SIffVV (xa, x) -> false
    | sigma, vs, Eq_Const (xb, xaa), SIffSS (xa, x) -> false
    | sigma, vs, Eq_Const (xa, xaa), SImpR x -> false
    | sigma, vs, Eq_Const (xa, xaa), SImpL x -> false
    | sigma, vs, Eq_Const (xb, xaa), SAnd (xa, x) -> false
    | sigma, vs, Eq_Const (xa, xaa), SOrR x -> false
    | sigma, vs, Eq_Const (xa, xaa), SOrL x -> false
    | sigma, vs, Eq_Const (xa, xaa), SNeg x -> false
    | sigma, vs, Eq_Const (xc, xaa), SEq_Const (xb, xa, x) ->
        eq _A3 xaa x &&
          (Stdlib.(=) xc xa &&
            set_eq (_A1, _A3) (vs xc) (insert _A3 xaa bot_set))
    | sigma, vs, Eq_Const (xc, xaa), SPred (xb, xa, x) -> false
    | sigma, vs, Eq_Const (xa, xaa), STT x -> false
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
    | sigma, vs, TT, SEq_Const (xb, xa, x) -> false
    | sigma, vs, TT, SPred (xb, xa, x) -> false
    | sigma, vs, TT, STT x -> true;;

let rec check_exec_p (_A1, _A2, _A3, _A4)
  sigma vs phi p =
    (match p with Inl a -> s_check_exec (_A1, _A2, _A3, _A4) sigma vs phi a
      | Inr a -> v_check_exec (_A1, _A2, _A3, _A4) sigma vs phi a);;

let rec subsvals xa = rep_part xa;;

let rec check_all_aux (_A1, _A2, _A3, _A4)
  sigma vs phi x3 = match sigma, vs, phi, x3 with
    sigma, vs, phi, Leaf p -> check_exec_p (_A1, _A2, _A3, _A4) sigma vs phi p
    | sigma, vs, phi, Node (x, part) ->
        list_all
          (fun (d, a) ->
            check_all_aux (_A1, _A2, _A3, _A4) sigma
              (fun_upd equal_string8 vs x d) phi a)
          (subsvals part);;

let rec check_all_generic (_A1, _A2, _A3, _A4)
  sigma phi e =
    distinct_paths e &&
      check_all_aux (_A1, _A2, _A3, _A4) sigma (fun _ -> top_set) phi e;;

let rec check
  x = check_all_generic
        (infinite_event_data, default_event_data, equal_event_data,
          linorder_event_data)
        x;;

let rec ed_set x = Set x;;

let rec sub_nat m n = minus_nat m n;;

let rec sum_nat m n = plus_nat m n;;

let rec abs_part
  xa = Abs_part
         (let ds = map fst xa in
           (if membera (equal_set (infinite_event_data, equal_event_data)) ds
                 bot_set ||
                 (list_ex
                    (fun d ->
                      list_ex
                        (fun e ->
                          not (set_eq (infinite_event_data, equal_event_data) d
                                e) &&
                            not (set_eq (infinite_event_data, equal_event_data)
                                  (inf_set equal_event_data d e) bot_set))
                        ds)
                    ds ||
                   (not (distinct
                          (equal_set (infinite_event_data, equal_event_data))
                          ds) ||
                     not (set_eq (infinite_event_data, equal_event_data)
                           (sup_seta equal_event_data
                             (image (fun d -> d) (Set ds)))
                           top_set)))
             then [(top_set, failwith "undefined")] else xa));;

let rec fstfinite _A xs = list_all (finite _A) xs;;

let rec collect_paths_aux (_A1, _A2, _A3, _A4)
  ds sigma vs phi x4 = match ds, sigma, vs, phi, x4 with
    ds, sigma, vs, phi, Leaf p ->
      (if check_exec_p (_A1, _A2, _A3, _A4) sigma vs phi p then bot_set
        else image rev ds)
    | ds, sigma, vs, phi, Node (x, part) ->
        sup_seta (equal_list (equal_set (_A1, _A3)))
          (image
            (fun (d, a) ->
              collect_paths_aux (_A1, _A2, _A3, _A4)
                (image (fun aa -> d :: aa) ds) sigma
                (fun_upd equal_string8 vs x d) phi a)
            (Set (subsvals part)));;

let rec collect_paths (_A1, _A2, _A3, _A4)
  sigma phi e =
    (if distinct_paths e &&
          check_all_aux (_A1, _A2, _A3, _A4) sigma (fun _ -> top_set) phi e
      then None
      else Some (collect_paths_aux (_A1, _A2, _A3, _A4)
                  (insert (equal_list (equal_set (_A1, _A3))) [] bot_set) sigma
                  (fun _ -> top_set) phi e));;

let rec trace_rbt_of_list _A
  xa = Abs_trace_rbt
         (if sorted_wrt less_eq_nat (map snd xa) && fstfinite _A (map fst xa)
           then (if null xa then (zero_nat, (zero_nat, empty))
                  else (size_list xa, (snd (last xa), bulkload xa)))
           else (zero_nat, (zero_nat, empty)));;

let rec trace_of_list _A xs = Trace_RBT (trace_rbt_of_list _A xs);;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let rec specialized_set x = Set x;;

let rec collect_paths_specialized
  x = collect_paths
        (infinite_event_data, default_event_data, equal_event_data,
          linorder_event_data)
        x;;

let rec trace_of_list_specialized
  xs = trace_of_list (infinite_prod (infinite_list nonunit_event_data)) xs;;

end;; (*struct Whymon*)
