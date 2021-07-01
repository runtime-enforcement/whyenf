type nat
val integer_of_nat : nat -> Z.t
val nat_of_integer : Z.t -> nat
type enat = Enat of nat | Infinity_enat
type i
type 'a regex
type 'a mtl = Atom of 'a | Neg of 'a mtl | Disj of 'a mtl * 'a mtl |
              Next of i * 'a mtl | Prev of i * 'a mtl | Since of 'a mtl * i * 'a mtl |
              Until of 'a mtl * i * 'a mtl | MatchF of i * 'a mtl regex |
              MatchP of i * 'a mtl regex
type 'a set = Set of 'a list | Coset of 'a list
type 'a nelist = List_to_nelist of 'a list
type 'a rsproof = SSkip of nat * nat | STest of 'a | SPlusL of 'a rsproof
                  | SPlusR of 'a rsproof | STimes of 'a rsproof * 'a rsproof
                  | SStar_eps of nat | SStar of 'a rsproof nelist

type 'a rvproof = VSkip of nat * nat | VTest of 'a | VTest_neq of nat * nat |
                  VPlus of 'a rvproof * 'a rvproof | VTimes of 'a rvproof nelist |
                  VStar of 'a rvproof nelist | VStar_gt of nat * nat
type 'a sproof = SAtm of 'a * nat | SNeg of 'a vproof | SDisjL of 'a sproof |
                 SDisjR of 'a sproof | SSince of 'a sproof * 'a sproof list |
                 SUntil of 'a sproof list * 'a sproof | SNext of 'a sproof |
                 SPrev of 'a sproof | SMatchP of 'a sproof rsproof |
                 SMatchF of 'a sproof rsproof
and 'a vproof = VAtm of 'a * nat | VNeg of 'a sproof |
                VDisj of 'a vproof * 'a vproof | VSince of nat * 'a vproof * 'a vproof list
                | VUntil of nat * 'a vproof list * 'a vproof |
                VSince_never of nat * 'a vproof list | VUntil_never of nat * 'a vproof list
                | VSince_le of nat | VNext of 'a vproof | VNext_ge of nat | VNext_le of nat
                | VPrev of 'a vproof | VPrev_ge of nat | VPrev_le of nat | VPrev_zero |
                VMatchP of nat * 'a vproof rvproof list |
                VMatchF of nat * 'a vproof rvproof list | VMatchP_le of nat
type 'a trace
type 'a prefix
val interval : nat -> enat -> i
val s_check_prefix :
  (string set * nat) list -> string mtl -> string sproof -> bool
val v_check_prefix :
  (string set * nat) list -> string mtl -> string vproof -> bool
val nat_of_integer : Z.t -> nat
