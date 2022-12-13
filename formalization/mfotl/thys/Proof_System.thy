(*<*)
theory Proof_System
  imports MFOTL
begin
(*>*)

section \<open>Proof System\<close>

subsection \<open>Time-stamp-time-point Conversion\<close>

definition ETP:: "'a trace \<Rightarrow> nat \<Rightarrow> nat"  where
    "ETP \<sigma> ts = (LEAST i. \<tau> \<sigma> i \<ge> ts)"

definition LTP:: "'a trace \<Rightarrow> nat \<Rightarrow> nat" where
    "LTP \<sigma> ts = Max {i. (\<tau> \<sigma> i) \<le> ts}"

abbreviation "\<delta> \<sigma> i j \<equiv> (\<tau> \<sigma> i - \<tau> \<sigma> j)"

abbreviation "ETP_p \<sigma> i b \<equiv> ETP \<sigma> ((\<tau> \<sigma> i) - b)"
abbreviation "LTP_p \<sigma> i I \<equiv> min i (LTP \<sigma> ((\<tau> \<sigma> i) - left I))"
abbreviation "ETP_f \<sigma> i I \<equiv> max i (ETP \<sigma> ((\<tau> \<sigma> i) + left I))"
abbreviation "LTP_f \<sigma> i b \<equiv> LTP \<sigma> ((\<tau> \<sigma> i) + b)"

subsection \<open>Soundness and Completeness\<close>

inductive SAT and VIO :: "'a MFOTL.trace \<Rightarrow> 'a MFOTL.env \<Rightarrow> nat \<Rightarrow> 'a MFOTL.formula \<Rightarrow> bool" where
  STT: "SAT \<sigma> v i TT"
| VFF: "VIO \<sigma> v i FF"
| SPred: "(r, MFOTL.eval_trms v ts) \<in> \<Gamma> \<sigma> i \<Longrightarrow> SAT \<sigma> v i (MFOTL.Pred r ts)"
| VPred: "(r, MFOTL.eval_trms v ts) \<notin> \<Gamma> \<sigma> i \<Longrightarrow> VIO \<sigma> v i (MFOTL.Pred r ts)"
| SEq: "(MFOTL.eval_trm v t1) = (MFOTL.eval_trm v t2) \<Longrightarrow> SAT \<sigma> v i (MFOTL.Eq t1 t2)"
| VEq: "(MFOTL.eval_trm v t1) \<noteq> (MFOTL.eval_trm v t2) \<Longrightarrow> VIO \<sigma> v i (MFOTL.Eq t1 t2)"
| SNeg: "VIO \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Neg \<phi>)"
| VNeg: "SAT \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Neg \<phi>)"
| SOrL: "SAT \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Or \<phi> \<psi>)"
| SOrR: "SAT \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Or \<phi> \<psi>)"
| VOr: "VIO \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Or \<phi> \<psi>)"
| SAnd: "SAT \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.And \<phi> \<psi>)"
| VAndL: "VIO \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.And \<phi> \<psi>)"
| VAndR: "VIO \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.And \<phi> \<psi>)"
| SImplL: "VIO \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Imp \<phi> \<psi>)"
| SImplR: "SAT \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Imp \<phi> \<psi>)"
| VImpl: "SAT \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Imp \<phi> \<psi>)"
| SIffSS: "SAT \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Iff \<phi> \<psi>)"
| SIffVV: "VIO \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Iff \<phi> \<psi>)"
| VIffSV: "SAT \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Iff \<phi> \<psi>)"
| VIffVS: "VIO \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Iff \<phi> \<psi>)"
| SExists: "\<exists>z. SAT \<sigma> (v (x := z)) i \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Exists x \<phi>)"
| VExists: "\<forall>z. VIO \<sigma> (v (x := z)) i \<phi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Exists x \<phi>)"
| SForall: "\<forall>z. SAT \<sigma> (v (x := z)) i \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Forall x \<phi>)"
| VForall: "\<exists>z. VIO \<sigma> (v (x := z)) i \<phi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Forall x \<phi>)"
| SPrev: "i > 0 \<Longrightarrow> mem (\<Delta> \<sigma> i) I \<Longrightarrow> SAT \<sigma> v (i-1) \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Prev I \<phi>)"
| VPrev: "i > 0 \<Longrightarrow> VIO \<sigma> v (i-1) \<phi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Prev I \<phi>)"
| VPrevZ: "i = 0 \<Longrightarrow> VIO \<sigma> v i (MFOTL.Prev I \<phi>)"
| VPrevOutL: "i > 0 \<Longrightarrow> (\<Delta> \<sigma> i) < (left I) \<Longrightarrow> VIO \<sigma> v i (MFOTL.Prev I \<phi>)"
| VPrevOutR: "i > 0 \<Longrightarrow> enat (\<Delta> \<sigma> i) > (right I) \<Longrightarrow> VIO \<sigma> v i (MFOTL.Prev I \<phi>)"
| SNext: "mem (\<Delta> \<sigma> (i+1)) I \<Longrightarrow> SAT \<sigma> v (i+1) \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Next I \<phi>)"
| VNext: "VIO \<sigma> v (i+1) \<phi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Next I \<phi>)"
| VNextOutL: "(\<Delta> \<sigma> (i+1)) < (left I) \<Longrightarrow> VIO \<sigma> v i (MFOTL.Next I \<phi>)"
| VNextOutR: "enat (\<Delta> \<sigma> (i+1)) > (right I) \<Longrightarrow> VIO \<sigma> v i (MFOTL.Next I \<phi>)"
| SOnce: "j \<le> i \<Longrightarrow> mem (\<delta> \<sigma> i j) I \<Longrightarrow> SAT \<sigma> v j \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Once I \<phi>)"
| VOnceOut: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I \<Longrightarrow> VIO \<sigma> v i (MFOTL.Once I \<phi>)"
| VOnce: "j = (case right I of \<infinity> \<Rightarrow> 0 
               | enat b \<Rightarrow> ETP_p \<sigma> i b) \<Longrightarrow>
          (\<tau> \<sigma> i) \<ge> (\<tau> \<sigma> 0) + left I \<Longrightarrow>
          (\<And>k. k \<in> {j .. LTP_p \<sigma> i I} \<Longrightarrow> VIO \<sigma> v k \<phi>) \<Longrightarrow> VIO \<sigma> v i (MFOTL.Once I \<phi>)"
| SEventually: "j \<ge> i \<Longrightarrow> mem (\<delta> \<sigma> j i) I  \<Longrightarrow> SAT \<sigma> v j \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Eventually I \<phi>)"
| VEventually: "(\<And>k. k \<in> (case right I of \<infinity> \<Rightarrow> {ETP_f \<sigma> i I ..}
                           | enat b \<Rightarrow> {ETP_f \<sigma> i I .. LTP_f \<sigma> i b}) \<Longrightarrow> VIO \<sigma> v k \<phi>) \<Longrightarrow> 
                VIO \<sigma> v i (MFOTL.Eventually I \<phi>)"
| SHistorically: "j = (case right I of \<infinity> \<Rightarrow> 0
               | enat b \<Rightarrow> ETP_p \<sigma> i b) \<Longrightarrow>
          (\<tau> \<sigma> i) \<ge> (\<tau> \<sigma> 0) + left I \<Longrightarrow>
          (\<And>k. k \<in> {j .. LTP_p \<sigma> i I} \<Longrightarrow> SAT \<sigma> v k \<phi>) \<Longrightarrow> SAT \<sigma> v i (MFOTL.Historically I \<phi>)"
| SHistoricallyOut: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I \<Longrightarrow> SAT \<sigma> v i (MFOTL.Historically I \<phi>)"
| VHistorically: "j \<le> i \<Longrightarrow> mem (\<delta> \<sigma> i j) I  \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Historically I \<phi>)"
| SAlways: "(\<And>k. k \<in> (case right I of \<infinity> \<Rightarrow> {lu i I ..} 
                       | enat b \<Rightarrow> {ETP_f \<sigma> i I .. LTP_f \<sigma> i b}) \<Longrightarrow> SAT \<sigma> v k \<phi>) \<Longrightarrow>
            SAT \<sigma> v i (MFOTL.Always I \<phi>)"
| VAlways: "j \<ge> i \<Longrightarrow> mem (\<delta> \<sigma> j i) I  \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Always I \<phi>)"
| SSince: "j \<le> i \<Longrightarrow> mem (\<delta> \<sigma> i j) I  \<Longrightarrow> SAT \<sigma> v j \<psi> \<Longrightarrow> (\<And>k. k \<in> {j <.. i} \<Longrightarrow> 
           SAT \<sigma> v k \<phi>) \<Longrightarrow> SAT \<sigma> v i (MFOTL.Since \<phi> I \<psi>)"
| VSinceOut: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I \<Longrightarrow> VIO \<sigma> v i (MFOTL.Since \<phi> I \<psi>)"
| VSince: "(case right I of \<infinity> \<Rightarrow> True 
            | enat b \<Rightarrow> ETP \<sigma> ((\<tau> \<sigma> i) - b) \<le> j) \<Longrightarrow> 
           j \<le> i \<Longrightarrow> (\<tau> \<sigma> 0) + left I \<le> (\<tau> \<sigma> i) \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow>
           (\<And>k. k \<in> {j .. (LTP_p \<sigma> i I)} \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow> VIO \<sigma> v i (MFOTL.Since \<phi> I \<psi>)"
| VSinceInf: "j = (case right I of \<infinity> \<Rightarrow> 0 
                      | enat b \<Rightarrow> ETP_p \<sigma> i b) \<Longrightarrow>
                 (\<tau> \<sigma> i) \<ge> (\<tau> \<sigma> 0) + left I \<Longrightarrow> 
                 (\<And>k. k \<in> {j .. LTP_p \<sigma> i I} \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow> VIO \<sigma> v i (MFOTL.Since \<phi> I \<psi>)"
| SUntil: "j \<ge> i \<Longrightarrow> mem (\<delta> \<sigma> j i) I  \<Longrightarrow> SAT \<sigma> v j \<psi> \<Longrightarrow> (\<And>k. k \<in> {i ..< j} \<Longrightarrow> SAT \<sigma> v k \<phi>) \<Longrightarrow> 
           SAT \<sigma> v i (MFOTL.Until \<phi> I \<psi>)"
| VUntil: "(case right I of \<infinity> \<Rightarrow> True 
            | enat b \<Rightarrow> j \<le> LTP_f \<sigma> i b) \<Longrightarrow> 
           j \<ge> i \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow> (\<And>k. k \<in> {ETP_f \<sigma> i I .. j} \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow> 
           VIO \<sigma> v i (MFOTL.Until \<phi> I \<psi>)"
| VUntilInf: "(\<And>k. k \<in> (case right I of \<infinity> \<Rightarrow> {ETP_f \<sigma> i I ..} 
                            | enat b \<Rightarrow> {ETP_f \<sigma> i I .. LTP_f \<sigma> i b}) \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow>
              VIO \<sigma> v i (MFOTL.Until \<phi> I \<psi>)"

lemma soundness: "(SAT \<sigma> v i \<phi> \<longrightarrow> MFOTL.sat \<sigma> v i \<phi>) \<and> (VIO \<sigma> v i \<phi> \<longrightarrow> \<not> MFOTL.sat \<sigma> v i \<phi>)"
  oops

lemma completeness: "(MFOTL.sat \<sigma> v i \<phi> \<longrightarrow> SAT \<sigma> v i \<phi>) \<and> (\<not> MFOTL.sat \<sigma> v i \<phi> \<longrightarrow> VIO \<sigma> v i \<phi>)"
proof (induct \<phi> arbitrary: i)
  case (Prev x1 \<phi>)
  then show ?case sorry
next
  case (Next x1 \<phi>)
  then show ?case sorry
next
  case (Once x1 \<phi>)
  then show ?case sorry
next
  case (Historically x1 \<phi>)
  then show ?case sorry
next
  case (Eventually x1 \<phi>)
  then show ?case sorry
next
  case (Always x1 \<phi>)
  then show ?case sorry
next
  case (Since \<phi>1 x2 \<phi>2)
  then show ?case sorry
next
  case (Until \<phi>1 x2 \<phi>2)
  then show ?case sorry
qed (auto intro: SAT_VIO.intros)

subsection \<open>Proof Objects\<close>

(* 'd: domain (such that 'd sets are always singletons or the complement of the union of the remaining sets) *)
typedef ('d, 'a) part = "{xs :: ('d set \<times> 'a) list. (\<Union>X \<in> fst ` set xs. X) = UNIV
  \<and> (\<forall>i < length xs. \<forall>j < length xs. i \<noteq> j \<longrightarrow> fst (xs ! i) \<inter> fst (xs ! j) = {})}"
  by (rule exI[of _ "[(UNIV, undefined)]"]) auto

setup_lifting type_definition_part

lift_bnf (no_warn_wits, no_warn_transfer) (dead 'd, 'a) part
  by auto

datatype (dead 'd) sproof = STT nat 
  | SPred nat MFOTL.name "'d MFOTL.trm list" 
  | SEq nat "'d MFOTL.trm" "'d MFOTL.trm"
  | SNeg "'d vproof" 
  | SOrL "'d sproof" 
  | SOrR "'d sproof" 
  | SAnd "'d sproof" "'d sproof"
  | SImplL "'d vproof" 
  | SImplR "'d sproof"
  | SIffSS "'d sproof" "'d sproof" 
  | SIffVV "'d vproof" "'d vproof" 
  | SExists "'d sproof"
  | SForall "('d, 'd sproof) part" 
  | SPrev "'d sproof"
  | SNext "'d sproof"
  | SOnce nat "'d sproof"
  | SEventually nat "'d sproof" 
  | SHistorically nat nat "'d sproof list" 
  | SHistoricallyOut nat
  | SAlways nat nat "'d sproof list"
  | SSince "'d sproof" "'d sproof list" 
  | SUntil "'d sproof list" "'d sproof" 
  and 'd vproof = VFF nat 
  | VPred nat MFOTL.name "'d MFOTL.trm list" 
  | VEq nat "'d MFOTL.trm" "'d MFOTL.trm"
  | VNeg "'d sproof" 
  | VOr "'d sproof" "'d sproof"
  | VAndL "'d vproof" 
  | VAndR "'d vproof" 
  | VImpl "'d sproof" "'d vproof" 
  | VIffSV "'d sproof" "'d vproof" 
  | VIffVS "'d vproof" "'d sproof" 
  | VExists "('d, 'd vproof) part" 
  | VForall "'d vproof"
  | VPrev "'d vproof"
  | VPrevZ
  | VPrevOutL nat 
  | VPrevOutR nat
  | VNext "'d vproof" 
  | VNextOutL nat 
  | VNextOutR nat 
  | VOnceOut nat 
  | VOnce nat nat "'d vproof list" 
  | VEventually nat nat "'d vproof list"
  | VHistorically nat "'d vproof" 
  | VAlways nat "'d vproof"
  | VSinceOut nat
  | VSince nat "'d vproof" "'d vproof list" 
  | VSinceInf nat nat "'d vproof list" 
  | VUntil nat "'d vproof list" "'d vproof"
  | VUntilInf nat nat "'d vproof list"

subsection \<open>\<^const>\<open>size\<close> setup\<close>

lift_definition vals :: "('d, 'a) part \<Rightarrow> 'a list" is "map snd" .

lift_definition Vals :: "('d, 'a) part \<Rightarrow> 'a set" is "set o map snd" .

lift_definition size_part :: "('d \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('d, 'a) part \<Rightarrow> nat" is "\<lambda>f g. size_list (\<lambda>(x, y). sum f x + g y)" .

instantiation part :: (type, type) size begin

definition size_part where
size_part_overloaded_def: "size_part = Proof_System.size_part (\<lambda>_. 0) (\<lambda>_. 0)"

instance ..

end

lemma size_part_overloaded_simps[simp]: "size x = size (vals x)"
  unfolding size_part_overloaded_def
  by transfer (auto simp: size_list_conv_sum_list)

lemma part_size_o_map: "inj h \<Longrightarrow> size_part f g \<circ> map_part h = size_part f (g \<circ> h)"
  by (rule ext, transfer)
    (auto simp: fun_eq_iff map_prod_def o_def split_beta case_prod_beta[abs_def])

setup \<open>
BNF_LFP_Size.register_size_global \<^type_name>\<open>part\<close> \<^const_name>\<open>size_part\<close>
  @{thm size_part_overloaded_def} @{thms size_part_def size_part_overloaded_simps}
  @{thms part_size_o_map}
\<close>
                                                                 
subsection \<open>Partitioned Decision Trees\<close>

(* 'd: domain; 'pt: proof tree *)
datatype ('d, 'pt) pdt = Leaf 'pt | Node MFOTL.name "('d, ('d, 'pt) pdt) part"

type_synonym 'd "proof" = "'d sproof + 'd vproof"

type_synonym 'd expl = "('d, 'd proof) pdt"

lemma is_measure_size_part[measure_function]: "is_measure f \<Longrightarrow> is_measure g \<Longrightarrow> is_measure (size_part f g)"
  by (rule is_measure_trivial)

lemma size_part_estimation[termination_simp]: "x \<in> Vals xs \<Longrightarrow> y < g x \<Longrightarrow> y < size_part f g xs"
  by transfer (auto simp: termination_simp)

lemma size_part_estimation'[termination_simp]: "x \<in> Vals xs \<Longrightarrow> y \<le> g x \<Longrightarrow> y \<le> size_part f g xs"
  by transfer (auto simp: termination_simp)

lemma size_part_pointwise[termination_simp]: "(\<And>x. x \<in> Vals xs \<Longrightarrow> f x \<le> g x) \<Longrightarrow> size_part h f xs \<le> size_part h g xs"
  by transfer (force simp: image_iff intro!: size_list_pointwise)

fun vars_expl :: "'d expl \<Rightarrow> MFOTL.name set" where
  "vars_expl (Node x part) = {x} \<union> (\<Union>pdt \<in> Vals part. vars_expl pdt)"
| "vars_expl (Leaf pt) = {}"

fun merge_part_raw :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('d set \<times> 'a) list \<Rightarrow> ('d set \<times> 'a) list \<Rightarrow> ('d set \<times> 'a) list" where
  "merge_part_raw f [] part2 = part2"  
| "merge_part_raw f (p1 # part1) part2 = 
    merge_part_raw f part1 (map (\<lambda>p2. 
      if (fst p1) \<inter> (fst p2) \<noteq> {} then 
        (if card (fst p2) = 1 then 
          (fst p1, f (snd p1) (snd p2))
        else 
          ((fst p2) - (fst p1), f (snd p1) (snd p2)))
      else p2) part2)"

lift_definition merge_part :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('d, 'a) part \<Rightarrow> ('d, 'a) part \<Rightarrow> ('d, 'a) part" is merge_part_raw
  sorry

fun "apply_pdt" :: "MFOTL.name list \<Rightarrow> ('d proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof) \<Rightarrow> 'd expl \<Rightarrow> 'd expl \<Rightarrow> 'd expl" where
  "apply_pdt vs f (Leaf pt1) (Leaf pt2) = Leaf (f pt1 pt2)"
| "apply_pdt vs f (Leaf pt1) (Node x part2) = Node x (map_part (map_pdt (f pt1)) part2)"
| "apply_pdt vs f (Node x part1) (Leaf pt2) = Node x (map_part (map_pdt (\<lambda>pt1. f pt1 pt2)) part1)"
| "apply_pdt (v # vs) f (Node x part1) (Node y part2) =
    (if x = v \<and> y = v then
      Node x (merge_part (apply_pdt vs f) part1 part2)
    else if x = v then
      Node x (map_part (\<lambda>pdt1. apply_pdt vs f pdt1 (Node y part2)) part1)
    else if y = v then
      Node y (map_part (\<lambda>pdt2. apply_pdt vs f (Node x part1) pdt2) part2)
    else
      apply_pdt vs f (Node x part1) (Node y part2))"
| "apply_pdt [] _ (Node _ _) (Node _ _) = undefined"

lift_definition part_all :: "('a \<Rightarrow> bool) \<Rightarrow> ('d, 'a) part \<Rightarrow> bool" is "\<lambda>f. list_all (f \<circ> snd)" .

fun sat_vorder :: "MFOTL.name list \<Rightarrow> 'd expl \<Rightarrow> bool" where
  "sat_vorder vs (Leaf _) = True"
| "sat_vorder (v # vs) (Node x part1) =
    (if x = v then
      part_all (sat_vorder vs) part1
    else
      sat_vorder vs (Node x part1))"
| "sat_vorder [] (Node _ _) = undefined"


end