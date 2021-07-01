open Z

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

type 'a regex = Skip of nat | Test of 'a | Plus of 'a regex * 'a regex |
                Times of 'a regex * 'a regex | Star of 'a regex;;

type 'a mtl = Atom of 'a | Neg of 'a mtl | Disj of 'a mtl * 'a mtl |
              Next of i * 'a mtl | Prev of i * 'a mtl | Since of 'a mtl * i * 'a mtl |
              Until of 'a mtl * i * 'a mtl | MatchF of i * 'a mtl regex |
              MatchP of i * 'a mtl regex;;

type num = One | Bit0 of num | Bit1 of num;;

type 'a set = Set of 'a list | Coset of 'a list;;

type 'a nelist = List_to_nelist of 'a list;;

type 'a rsproof = SSkip of nat * nat | STest of 'a | SPlusL of 'a rsproof |
                  SPlusR of 'a rsproof | STimes of 'a rsproof * 'a rsproof | SStar_eps of nat |
                  SStar of 'a rsproof nelist;;

type 'a rvproof = VSkip of nat * nat | VTest of 'a | VTest_neq of nat * nat |
                  VPlus of 'a rvproof * 'a rvproof | VTimes of 'a rvproof nelist |
                  VStar of 'a rvproof nelist | VStar_gt of nat * nat;;

type 'a sproof = SAtm of 'a * nat | SNeg of 'a vproof | SDisjL of 'a sproof |
                 SDisjR of 'a sproof | SSince of 'a sproof * 'a sproof list |
                 SUntil of 'a sproof list * 'a sproof | SNext of 'a sproof | SPrev of 'a sproof
                 | SMatchP of 'a sproof rsproof | SMatchF of 'a sproof rsproof
and 'a vproof = VAtm of 'a * nat | VNeg of 'a sproof |
                VDisj of 'a vproof * 'a vproof | VSince of nat * 'a vproof * 'a vproof list |
                VUntil of nat * 'a vproof list * 'a vproof |
                VSince_never of nat * 'a vproof list | VUntil_never of nat * 'a vproof list |
                VSince_le of nat | VNext of 'a vproof | VNext_ge of nat | VNext_le of nat |
                VPrev of 'a vproof | VPrev_ge of nat | VPrev_le of nat | VPrev_zero |
                VMatchP of nat * 'a vproof rvproof list |
                VMatchF of nat * 'a vproof rvproof list | VMatchP_le of nat;;

type 'a stream = Lazy_stream of 'a stream_lazy Lazy.t
and 'a stream_lazy = SCons_Lazy of 'a * 'a stream;;

type 'a trace = Abs_trace of ('a set * nat) stream;;

type 'a prefix = Abs_prefix of ('a set * nat) list;;

let rec eq _A a b = equal _A a b;;

let zero_nat : nat = Nat Z.zero;;

let rec rep_trace (Abs_trace x) = x;;

let rec snd (x1, x2) = x2;;

let rec unlazy_stream (Lazy_stream uu) = uu;;

let rec sdrop_while
          x1ba xa =
  (let SCons_Lazy (x3a, x2ba) = Lazy.force (unlazy_stream xa) in
   (if x1ba x3a then sdrop_while x1ba x2ba
    else Lazy_stream (Lazy.from_fun (fun _ -> SCons_Lazy (x3a, x2ba)))));;

let rec shd
          xa = (let SCons_Lazy (x2aa, _) = Lazy.force (unlazy_stream xa) in x2aa);;

let rec siterate
          f x = Lazy_stream
                  (Lazy.from_fun (fun _ -> SCons_Lazy (x, siterate f (f x))));;

let rec smap2
          x1da x1a x2a =
  (let SCons_Lazy (x3ba, x2da) = Lazy.force (unlazy_stream x1a) in
   let SCons_Lazy (x5a, x4a) = Lazy.force (unlazy_stream x2a) in
   Lazy_stream
     (Lazy.from_fun
        (fun _ -> SCons_Lazy (x1da x3ba x5a, smap2 x1da x2da x4a))));;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let one_nat : nat = Nat (Z.of_int 1);;

let rec suc n = plus_nat n one_nat;;

let rec etp
          rho t =
  snd (shd (sdrop_while (fun (tau, _) -> less_nat tau t)
              (smap2 (fun (_, a) -> (fun b -> (a, b))) (rep_trace rho)
                 (siterate suc zero_nat))));;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
                                        | f, [], s -> s;;

let rec maxa _A
          (Set (x :: xs)) =
  fold (max _A.order_linorder.preorder_order.ord_preorder) xs x;;

let rec minus_nat
          m n = Nat (max ord_integer Z.zero
                       (Z.sub (integer_of_nat m) (integer_of_nat n)));;

let bot_set : 'a set = Set [];;

let rec ltp
          rho t =
  (let n =
     snd (shd (sdrop_while (fun (tau, _) -> less_eq_nat tau t)
                 (smap2 (fun (_, a) -> (fun b -> (a, b))) (rep_trace rho)
                    (siterate suc zero_nat))))
   in
   (if equal_nata n zero_nat then maxa linorder_nat bot_set
    else minus_nat n one_nat));;

let rec comp f g = (fun x -> f (g x));;

let rec nth
          (x :: xs) n =
  (if equal_nata n zero_nat then x else nth xs (minus_nat n one_nat));;

let rec upt i j = (if less_nat i j then i :: upt (suc i) j else []);;

let rec fst (x1, x2) = x1;;

let rec nelist_to_list (List_to_nelist x) = x;;

let rec null = function [] -> true
                      | x :: xs -> false;;

let rec last (x :: xs) = (if null xs then x else last xs);;

let rec nelast xa = last (nelist_to_list xa);;

let rec hd (x21 :: x22) = x21;;

let rec nehd xa = hd (nelist_to_list xa);;

let rec rs_at
          test x1 = match test, x1 with test, SSkip (k, n) -> (k, plus_nat k n)
                                      | test, STest x -> (test x, test x)
                                      | test, SPlusL p -> rs_at test p
                                      | test, SPlusR p -> rs_at test p
                                      | test, STimes (p1, p2) -> (fst (rs_at test p1), snd (rs_at test p2))
                                      | test, SStar_eps n -> (n, n)
                                      | test, SStar ps ->
                                         (fst (rs_at test (nehd ps)), snd (rs_at test (nelast ps)));;

let rec s_at
  = function SAtm (uu, n) -> n
           | SNeg vphi -> v_at vphi
           | SDisjL sphi -> s_at sphi
           | SDisjR spsi -> s_at spsi
           | SNext sphi -> minus_nat (s_at sphi) one_nat
           | SPrev sphi -> plus_nat (s_at sphi) one_nat
           | SSince (spsi, sphis) ->
              (match sphis with [] -> s_at spsi | _ :: _ -> s_at (last sphis))
           | SUntil (sphis, spsi) ->
              (match sphis with [] -> s_at spsi | x :: _ -> s_at x)
           | SMatchP p -> snd (rs_at s_at p)
           | SMatchF p -> fst (rs_at s_at p)
and v_at = function VAtm (uv, n) -> n
                  | VNeg sphi -> s_at sphi
                  | VDisj (vphi, vpsi) -> v_at vphi
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
                  | VUntil_never (n, vpsis) -> n
                  | VMatchP (n, ps) -> n
                  | VMatchP_le n -> n
                  | VMatchF (n, ps) -> n;;

let rec membera _A x0 y = match x0, y with [], y -> false
                                         | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec member _A
          x xa1 = match x, xa1 with x, Coset xs -> not (membera _A xs x)
                                  | x, Set xs -> membera _A xs x;;

let rec less_eq_enat q x1 = match q, x1 with Infinity_enat, Enat n -> false
                                           | q, Infinity_enat -> true
                                           | Enat m, Enat n -> less_eq_nat m n;;

let rec equal_list _A
          x0 x1 = match x0, x1 with [], x21 :: x22 -> false
                                  | x21 :: x22, [] -> false
                                  | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_list _A x22 y22
                                  | [], [] -> true;;

let rec list_all p x1 = match p, x1 with p, [] -> true
                                       | p, x :: xs -> p x && list_all p xs;;

let rec stl
          xa = (let SCons_Lazy (_, x1aa) = Lazy.force (unlazy_stream xa) in x1aa);;

let rec snth
          s n = (if equal_nata n zero_nat then shd s
                 else snth (stl s) (minus_nat n one_nat));;

let rec gamma x = (fun i -> fst (snth (rep_trace x) i));;

let rec all_interval_nat
          p i j = less_eq_nat j i || p i && all_interval_nat p (suc i) j;;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (suc n) xs
                                         | n, [] -> n;;

let rec size_list x = gen_length zero_nat x;;

let rec nelength xa = size_list (nelist_to_list xa);;

let rec nenth xa = nth (nelist_to_list xa);;

let rec rs_check
          test testi x2 x3 = match test, testi, x2, x3 with
    test, testi, Skip n, SSkip (x, y) ->
     equal_nata (snd (rs_at testi (SSkip (x, y)))) (plus_nat x n)
  | test, testi, Test x, STest y -> test x y
  | test, testi, Plus (ra, r), SPlusL z -> rs_check test testi ra z
  | test, testi, Plus (ra, r), SPlusR z -> rs_check test testi r z
  | test, testi, Times (ra, r), STimes (p1, p2) ->
     equal_nata (snd (rs_at testi p1)) (fst (rs_at testi p2)) &&
       (rs_check test testi ra p1 && rs_check test testi r p2)
  | test, testi, Star r, SStar_eps n -> true
  | test, testi, Star r, SStar ps ->
     all_interval_nat
       (fun k ->
         equal_nata (fst (rs_at testi (nenth ps k)))
           (snd (rs_at testi (nenth ps (minus_nat k one_nat)))))
       one_nat (nelength ps) &&
       all_interval_nat
         (fun k ->
           less_nat (fst (rs_at testi (nenth ps k)))
             (snd (rs_at testi (nenth ps k))) &&
             rs_check test testi r (nenth ps k))
         zero_nat (nelength ps)
  | test, testi, Test v, SSkip (va, vb) -> false
  | test, testi, Test v, SPlusL va -> false
  | test, testi, Test v, SPlusR va -> false
  | test, testi, Test v, STimes (va, vb) -> false
  | test, testi, Test v, SStar_eps va -> false
  | test, testi, Test v, SStar va -> false
  | test, testi, Plus (v, va), SSkip (vb, vc) -> false
  | test, testi, Plus (v, va), STest vb -> false
  | test, testi, Plus (v, va), STimes (vb, vc) -> false
  | test, testi, Plus (v, va), SStar_eps vb -> false
  | test, testi, Plus (v, va), SStar vb -> false
  | test, testi, Times (v, va), SSkip (vb, vc) -> false
  | test, testi, Times (v, va), STest vb -> false
  | test, testi, Times (v, va), SPlusL vb -> false
  | test, testi, Times (v, va), SPlusR vb -> false
  | test, testi, Times (v, va), SStar_eps vb -> false
  | test, testi, Times (v, va), SStar vb -> false
  | test, testi, Star v, SSkip (va, vb) -> false
  | test, testi, Star v, STest va -> false
  | test, testi, Star v, SPlusL va -> false
  | test, testi, Star v, SPlusR va -> false
  | test, testi, Star v, STimes (va, vb) -> false
  | test, testi, Skip va, STest v -> false
  | test, testi, Skip va, SPlusL v -> false
  | test, testi, Skip va, SPlusR v -> false
  | test, testi, Skip vb, STimes (v, va) -> false
  | test, testi, Skip va, SStar_eps v -> false
  | test, testi, Skip va, SStar v -> false;;

let rec rep_I (Abs_I x) = x;;

let rec right x = snd (rep_I x);;

let rec map f x1 = match f, x1 with f, [] -> []
                                  | f, x21 :: x22 -> f x21 :: map f x22;;

let rec left x = fst (rep_I x);;

let rec tau x = (fun i -> snd (snth (rep_trace x) i));;

let rec less_enat x0 q = match x0, q with Infinity_enat, q -> false
                                        | Enat m, Infinity_enat -> true
                                        | Enat m, Enat n -> less_nat m n;;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rv_check _ _ _ _ = failwith "Regex.rv_check";;

let rec mina _A
          (Set (x :: xs)) =
  fold (min _A.order_linorder.preorder_order.ord_preorder) xs x;;

let rec neset xs = Set (nelist_to_list xs);;

let rec nemap f xs = List_to_nelist (map f (nelist_to_list xs));;

let rec rv_at
          test x1 = match test, x1 with test, VSkip (na, n) -> (na, n)
                                      | test, VTest p -> (test p, test p)
                                      | test, VTest_neq (na, n) -> (na, n)
                                      | test, VPlus (p1, p2) -> rv_at test p1
                                      | test, VTimes ps ->
                                         (fst (rv_at test (nehd ps)), snd (rv_at test (nelast ps)))
                                      | test, VStar ps ->
                                         (mina linorder_nat (neset (nemap (comp fst (rv_at test)) ps)),
                                          maxa linorder_nat (neset (nemap (comp snd (rv_at test)) ps)))
                                      | test, VStar_gt (na, n) -> (na, n);;

let rec s_check _A
          rho x1 x2 = match rho, x1, x2 with rho, MatchP (xa, xaa), SMatchF x -> false
                                           | rho, MatchP (xa, xaa), SMatchP x ->
                                              (let rt = rs_at s_at x in
                                               less_eq_nat (fst rt) (snd rt) &&
                                                 (less_eq_nat (left xa)
                                                    (minus_nat (tau rho (snd rt)) (tau rho (fst rt))) &&
                                                    less_eq_enat
                                                      (Enat (minus_nat (tau rho (snd rt)) (tau rho (fst rt))))
                                                      (right xa) &&
                                                      rs_check (s_check _A rho) s_at xaa x))
                                           | rho, MatchP (xa, xaa), SPrev x -> false
                                           | rho, MatchP (xa, xaa), SNext x -> false
                                           | rho, MatchP (xb, xaa), SUntil (xa, x) -> false
                                           | rho, MatchP (xb, xaa), SSince (xa, x) -> false
                                           | rho, MatchP (xa, xaa), SDisjR x -> false
                                           | rho, MatchP (xa, xaa), SDisjL x -> false
                                           | rho, MatchP (xa, xaa), SNeg x -> false
                                           | rho, MatchP (xb, xaa), SAtm (xa, x) -> false
                                           | rho, MatchF (xa, xaa), SMatchF x ->
                                              (let rt = rs_at s_at x in
                                               less_eq_nat (fst rt) (snd rt) &&
                                                 (less_eq_nat (left xa)
                                                    (minus_nat (tau rho (snd rt)) (tau rho (fst rt))) &&
                                                    less_eq_enat
                                                      (Enat (minus_nat (tau rho (snd rt)) (tau rho (fst rt))))
                                                      (right xa) &&
                                                      rs_check (s_check _A rho) s_at xaa x))
                                           | rho, MatchF (xa, xaa), SMatchP x -> false
                                           | rho, MatchF (xa, xaa), SPrev x -> false
                                           | rho, MatchF (xa, xaa), SNext x -> false
                                           | rho, MatchF (xb, xaa), SUntil (xa, x) -> false
                                           | rho, MatchF (xb, xaa), SSince (xa, x) -> false
                                           | rho, MatchF (xa, xaa), SDisjR x -> false
                                           | rho, MatchF (xa, xaa), SDisjL x -> false
                                           | rho, MatchF (xa, xaa), SNeg x -> false
                                           | rho, MatchF (xb, xaa), SAtm (xa, x) -> false
                                           | rho, Until (xa, xaa, xb), SMatchF x -> false
                                           | rho, Until (xa, xaa, xb), SMatchP x -> false
                                           | rho, Until (xa, xaa, xb), SPrev x -> false
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
                                           | rho, Until (xa, xaa, xb), SDisjR x -> false
                                           | rho, Until (xa, xaa, xb), SDisjL x -> false
                                           | rho, Until (xa, xaa, xb), SNeg x -> false
                                           | rho, Until (xb, xaa, xba), SAtm (xa, x) -> false
                                           | rho, Since (xa, xaa, xb), SMatchF x -> false
                                           | rho, Since (xa, xaa, xb), SMatchP x -> false
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
                                           | rho, Since (xa, xaa, xb), SDisjR x -> false
                                           | rho, Since (xa, xaa, xb), SDisjL x -> false
                                           | rho, Since (xa, xaa, xb), SNeg x -> false
                                           | rho, Since (xb, xaa, xba), SAtm (xa, x) -> false
                                           | rho, Prev (xa, xaa), SMatchF x -> false
                                           | rho, Prev (xa, xaa), SMatchP x -> false
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
                                           | rho, Prev (xa, xaa), SDisjR x -> false
                                           | rho, Prev (xa, xaa), SDisjL x -> false
                                           | rho, Prev (xa, xaa), SNeg x -> false
                                           | rho, Prev (xb, xaa), SAtm (xa, x) -> false
                                           | rho, Next (xa, xaa), SMatchF x -> false
                                           | rho, Next (xa, xaa), SMatchP x -> false
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
                                           | rho, Next (xa, xaa), SDisjR x -> false
                                           | rho, Next (xa, xaa), SDisjL x -> false
                                           | rho, Next (xa, xaa), SNeg x -> false
                                           | rho, Next (xb, xaa), SAtm (xa, x) -> false
                                           | rho, Disj (xa, xaa), SMatchF x -> false
                                           | rho, Disj (xa, xaa), SMatchP x -> false
                                           | rho, Disj (xa, xaa), SPrev x -> false
                                           | rho, Disj (xa, xaa), SNext x -> false
                                           | rho, Disj (xb, xaa), SUntil (xa, x) -> false
                                           | rho, Disj (xb, xaa), SSince (xa, x) -> false
                                           | rho, Disj (xa, xaa), SDisjR x -> s_check _A rho xaa x
                                           | rho, Disj (xa, xaa), SDisjL x -> s_check _A rho xa x
                                           | rho, Disj (xa, xaa), SNeg x -> false
                                           | rho, Disj (xb, xaa), SAtm (xa, x) -> false
                                           | rho, Neg xa, SMatchF x -> false
                                           | rho, Neg xa, SMatchP x -> false
                                           | rho, Neg xa, SPrev x -> false
                                           | rho, Neg xa, SNext x -> false
                                           | rho, Neg xb, SUntil (xa, x) -> false
                                           | rho, Neg xb, SSince (xa, x) -> false
                                           | rho, Neg xa, SDisjR x -> false
                                           | rho, Neg xa, SDisjL x -> false
                                           | rho, Neg xa, SNeg x -> v_check _A rho xa x
                                           | rho, Neg xb, SAtm (xa, x) -> false
                                           | rho, Atom xa, SMatchF x -> false
                                           | rho, Atom xa, SMatchP x -> false
                                           | rho, Atom xa, SPrev x -> false
                                           | rho, Atom xa, SNext x -> false
                                           | rho, Atom xb, SUntil (xa, x) -> false
                                           | rho, Atom xb, SSince (xa, x) -> false
                                           | rho, Atom xa, SDisjR x -> false
                                           | rho, Atom xa, SDisjL x -> false
                                           | rho, Atom xa, SNeg x -> false
                                           | rho, Atom xb, SAtm (xa, x) -> eq _A xb xa && member _A xb (gamma rho x)
and v_check _A
rho x1 p = match rho, x1, p with
    rho, MatchP (xa, x), p ->
     (match p with VAtm (_, _) -> false | VNeg _ -> false
                   | VDisj (_, _) -> false | VSince (_, _, _) -> false
                   | VUntil (_, _, _) -> false | VSince_never (_, _) -> false
                   | VUntil_never (_, _) -> false | VSince_le _ -> false | VNext _ -> false
                   | VNext_ge _ -> false | VNext_le _ -> false | VPrev _ -> false
                   | VPrev_ge _ -> false | VPrev_le _ -> false | VPrev_zero -> false
                   | VMatchP (i, vps) ->
                      (let j =
                         etp rho
                           (match right xa with Enat a -> minus_nat (tau rho i) a
                                              | Infinity_enat -> zero_nat)
                       in
                       less_eq_nat (plus_nat (tau rho zero_nat) (left xa)) (tau rho i) &&
                         (equal_list equal_nat (map (comp fst (rv_at v_at)) vps)
                            (upt j
                               (suc (min ord_nat i
                                       (ltp rho (minus_nat (tau rho i) (left xa)))))) &&
                            list_all
                              (fun vp ->
                                rv_check (v_check _A rho) v_at x vp &&
                                  equal_nata (snd (rv_at v_at vp)) i)
                              vps))
                   | VMatchF (_, _) -> false
                   | VMatchP_le i ->
                      less_nat (tau rho i) (plus_nat (tau rho zero_nat) (left xa)))
  | rho, MatchF (xa, x), p ->
     (match p with VAtm (_, _) -> false | VNeg _ -> false
                   | VDisj (_, _) -> false | VSince (_, _, _) -> false
                   | VUntil (_, _, _) -> false | VSince_never (_, _) -> false
                   | VUntil_never (_, _) -> false | VSince_le _ -> false
                   | VNext _ -> false | VNext_ge _ -> false | VNext_le _ -> false
                   | VPrev _ -> false | VPrev_ge _ -> false | VPrev_le _ -> false
                   | VPrev_zero -> false | VMatchP (_, _) -> false
                   | VMatchF (i, vps) ->
                      (let j =
                         ltp rho
                           (match right xa with Enat a -> plus_nat (tau rho i) a
                                              | Infinity_enat -> zero_nat)
                       in
                       equal_list equal_nat (map (comp snd (rv_at v_at)) vps)
                         (upt (max ord_nat i (etp rho (plus_nat (tau rho i) (left xa))))
                            (suc j)) &&
                         list_all
                           (fun vp ->
                             rv_check (v_check _A rho) v_at x vp &&
                               equal_nata (fst (rv_at v_at vp)) i)
                           vps)
                   | VMatchP_le _ -> false)
  | rho, Until (xb, xa, x), p ->
     (match p with VAtm (_, _) -> false | VNeg _ -> false
                   | VDisj (_, _) -> false | VSince (_, _, _) -> false
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
                   | VPrev_le _ -> false | VPrev_zero -> false | VMatchP (_, _) -> false
                   | VMatchF (_, _) -> false | VMatchP_le _ -> false)
  | rho, Since (xb, xa, x), p ->
     (match p with VAtm (_, _) -> false | VNeg _ -> false
                   | VDisj (_, _) -> false
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
                   | VPrev_zero -> false | VMatchP (_, _) -> false
                   | VMatchF (_, _) -> false | VMatchP_le _ -> false)
  | rho, Prev (xa, x), p ->
     (match p with VAtm (_, _) -> false | VNeg _ -> false
                   | VDisj (_, _) -> false | VSince (_, _, _) -> false
                   | VUntil (_, _, _) -> false | VSince_never (_, _) -> false
                   | VUntil_never (_, _) -> false | VSince_le _ -> false
                   | VNext _ -> false | VNext_ge _ -> false | VNext_le _ -> false
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
                   | VPrev_zero -> equal_nata (v_at VPrev_zero) zero_nat
                   | VMatchP (_, _) -> false | VMatchF (_, _) -> false
                   | VMatchP_le _ -> false)
  | rho, Next (xa, x), p ->
     (match p with VAtm (_, _) -> false | VNeg _ -> false
                   | VDisj (_, _) -> false | VSince (_, _, _) -> false
                   | VUntil (_, _, _) -> false | VSince_never (_, _) -> false
                   | VUntil_never (_, _) -> false | VSince_le _ -> false
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
                   | VPrev_zero -> false | VMatchP (_, _) -> false
                   | VMatchF (_, _) -> false | VMatchP_le _ -> false)
  | rho, Disj (xa, x), p ->
     (match p with VAtm (_, _) -> false | VNeg _ -> false
                   | VDisj (vphi, vpsi) ->
                      v_check _A rho xa vphi &&
                        (v_check _A rho x vpsi && equal_nata (v_at vphi) (v_at vpsi))
                   | VSince (_, _, _) -> false | VUntil (_, _, _) -> false
                   | VSince_never (_, _) -> false | VUntil_never (_, _) -> false
                   | VSince_le _ -> false | VNext _ -> false | VNext_ge _ -> false
                   | VNext_le _ -> false | VPrev _ -> false | VPrev_ge _ -> false
                   | VPrev_le _ -> false | VPrev_zero -> false | VMatchP (_, _) -> false
                   | VMatchF (_, _) -> false | VMatchP_le _ -> false)
  | rho, Neg x, p ->
     (match p with VAtm (_, _) -> false | VNeg a -> s_check _A rho x a
                   | VDisj (_, _) -> false | VSince (_, _, _) -> false
                   | VUntil (_, _, _) -> false | VSince_never (_, _) -> false
                   | VUntil_never (_, _) -> false | VSince_le _ -> false
                   | VNext _ -> false | VNext_ge _ -> false | VNext_le _ -> false
                   | VPrev _ -> false | VPrev_ge _ -> false | VPrev_le _ -> false
                   | VPrev_zero -> false | VMatchP (_, _) -> false
                   | VMatchF (_, _) -> false | VMatchP_le _ -> false)
  | rho, Atom x, p ->
     (match p
      with VAtm (b, i) -> eq _A x b && not (member _A x (gamma rho i))
         | VNeg _ -> false | VDisj (_, _) -> false | VSince (_, _, _) -> false
         | VUntil (_, _, _) -> false | VSince_never (_, _) -> false
         | VUntil_never (_, _) -> false | VSince_le _ -> false
         | VNext _ -> false | VNext_ge _ -> false | VNext_le _ -> false
         | VPrev _ -> false | VPrev_ge _ -> false | VPrev_le _ -> false
         | VPrev_zero -> false | VMatchP (_, _) -> false
         | VMatchF (_, _) -> false | VMatchP_le _ -> false);;

let rec shift
          x0 s = match x0, s with [], s -> s
                                | x :: xs, s ->
                                   Lazy_stream (Lazy.from_fun (fun _ -> SCons_Lazy (x, shift xs s)));;

let rec sorted _A
  = function
    x :: y :: zs ->
     less_eq _A.order_linorder.preorder_order.ord_preorder x y &&
       sorted _A (y :: zs)
  | [x] -> true
  | [] -> true;;

let rec to_prefix
          xa = Abs_prefix (if sorted linorder_nat (map snd xa) then xa else []);;

let rec interval
          l r = Abs_I (if less_eq_enat (Enat l) r then (l, r)
                       else rep_I (failwith "undefined"));;

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

let rec s_check_prefix
          xs = s_check equal_literal (extend_prefix (to_prefix xs));;

let rec v_check_prefix
          xs = v_check equal_literal (extend_prefix (to_prefix xs));;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;
