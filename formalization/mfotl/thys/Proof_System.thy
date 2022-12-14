(*<*)
theory Proof_System
  imports MFOTL "HOL-Library.Disjoint_Sets"
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

lemma part_list_set_eq: 
  "{xs :: ('d set \<times> 'a) list. (\<Union>X \<in> fst ` set xs. X) = UNIV
    \<and> (\<forall>i < length xs. \<forall>j < length xs. i \<noteq> j 
      \<longrightarrow> fst (xs ! i) \<inter> fst (xs ! j) = {}) \<and> {} \<notin> fst ` set xs}
  = {xs :: ('d set \<times> 'a) list. partition_on UNIV (set (map fst xs)) \<and> distinct (map fst xs)}"
proof ((intro set_eqI iffI; clarsimp simp: partition_on_def), goal_cases)
  case (1 xs)
  hence "disjoint (fst ` set xs)"
    by (metis disjnt_def in_set_conv_nth pairwise_imageI)
  moreover have "distinct (map fst xs)"
    using 1
    by (smt (verit) distinct_conv_nth image_iff inf.idem 
        length_map nth_map nth_mem) 
  ultimately show ?case 
    by blast
next
  case (2 xs i j)
  hence "fst (xs ! i) \<in> fst ` set xs"
    and "fst (xs ! j) \<in> fst ` set xs"
    by auto
  moreover have "fst (xs ! i) \<noteq> fst (xs ! j)"
    using 2(4-) nth_eq_iff_index_eq 
    by fastforce 
  ultimately show ?case
    using 2(2) unfolding disjoint_def
    by blast
qed

(* 'd: domain (such that the union of 'd sets form a partition) *)
typedef ('d, 'a) part = "{xs :: ('d set \<times> 'a) list. partition_on UNIV (set (map fst xs)) \<and> distinct (map fst xs)}"
  by (rule exI[of _ "[(UNIV, undefined)]"]) 
    (auto simp: partition_on_def)

setup_lifting type_definition_part

lift_bnf (no_warn_wits, no_warn_transfer) (dead 'd, 'a) part
  unfolding part_list_set_eq[symmetric]
  by (auto simp: image_iff)

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
  | VOr "'d vproof" "'d vproof"
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

thm pdt.size

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
| "merge_part_raw f ((P1, v1) # part1) part2 = 
    (let part12 = List.map_filter (\<lambda>(P2, v2). if P1 \<inter> P2 \<noteq> {} then Some(P1 \<inter> P2, f v1 v2) else None) part2 in
     let part2not1 = List.map_filter (\<lambda>(P2, v2). if P2 - P1 \<noteq> {} then Some(P2 - P1, v2) else None) part2 in
     part12 @ (merge_part_raw f part1 part2not1))"

lemma partition_on_empty_iff: 
  "partition_on X \<P> \<Longrightarrow> \<P> = {} \<longleftrightarrow> X = {}"
  "partition_on X \<P> \<Longrightarrow> \<P> \<noteq> {} \<longleftrightarrow> X \<noteq> {}"
  by (auto simp: partition_on_def)

lemma wf_part_list_filter_inter: 
  defines "inP1 P1 f v1 part2 
    \<equiv> List.map_filter (\<lambda>(P2, v2). if P1 \<inter> P2 \<noteq> {} then Some(P1 \<inter> P2, f v1 v2) else None) part2"
  assumes "partition_on X (set (map fst ((P1, v1) # part1)))"
    and "partition_on X (set (map fst part2))"
  shows "partition_on P1 (set (map fst (inP1 P1 f v1 part2)))"
    and "distinct (map fst ((P1, v1) # part1)) \<Longrightarrow> distinct (map fst (part2)) 
      \<Longrightarrow> distinct (map fst (inP1 P1 f v1 part2))"
proof (rule partition_onI)
  show "\<Union> (set (map fst (inP1 P1 f v1 part2))) = P1"
    using partition_onD1[OF assms(2)] partition_onD1[OF assms(3)] inP1_def
    by (auto simp: map_filter_def split: if_splits)
      (metis (no_types, lifting) Int_iff UN_iff Un_Int_eq(3) empty_iff prod.collapse)
  show "\<And>A1 A2. A1 \<in> set (map fst (inP1 P1 f v1 part2)) 
    \<Longrightarrow> A2 \<in> set (map fst (inP1 P1 f v1 part2)) \<Longrightarrow> A1 \<noteq> A2 \<Longrightarrow> disjnt A1 A2" 
    using partition_onD2[OF assms(2)] partition_onD2[OF assms(3)] inP1_def
    by (clarsimp simp: disjnt_def map_filter_def disjoint_def split: if_splits)
      (smt (verit, del_insts) Int_assoc Int_commute fst_conv inf_bot_right)
  show "{} \<notin> set (map fst (inP1 P1 f v1 part2))" 
    using assms
    by (auto simp: map_filter_def split: if_splits)
  show "distinct (map fst ((P1, v1) # part1)) \<Longrightarrow> distinct (map fst part2) 
    \<Longrightarrow> distinct (map fst (inP1 P1 f v1 part2))"
    using partition_onD2[OF assms(3), unfolded disjoint_def] distinct_map[of fst part2]
    by (clarsimp simp: inP1_def map_filter_def distinct_map inj_on_def split: prod.splits)
      (metis Int_assoc fst_conv inf.idem inf_bot_right prod.inject)
qed

lemma wf_part_list_filter_minus: 
  defines "notinP2 P1 f v1 part2 
    \<equiv> List.map_filter (\<lambda>(P2, v2). if P2 - P1 \<noteq> {} then Some(P2 - P1, v2) else None) part2"
  assumes "partition_on X (set (map fst ((P1, v1) # part1)))"
    and "partition_on X (set (map fst part2))"
  shows "partition_on (X - P1) (set (map fst (notinP2 P1 f v1 part2)))"
    and "distinct (map fst ((P1, v1) # part1)) \<Longrightarrow> distinct (map fst (part2)) 
      \<Longrightarrow> distinct (map fst (notinP2 P1 f v1 part2))"
proof (rule partition_onI)
  show "\<Union> (set (map fst (notinP2 P1 f v1 part2))) = X - P1"
    using partition_onD1[OF assms(2)] partition_onD1[OF assms(3)] notinP2_def
    apply (intro set_eqI iffI; clarsimp simp: map_filter_def subset_eq split: if_splits)
    by (metis (no_types, lifting) UN_iff Un_iff fst_conv prod.collapse)+
  show "\<And>A1 A2. A1 \<in> set (map fst (notinP2 P1 f v1 part2)) 
    \<Longrightarrow> A2 \<in> set (map fst (notinP2 P1 f v1 part2)) \<Longrightarrow> A1 \<noteq> A2 \<Longrightarrow> disjnt A1 A2" 
    using partition_onD2[OF assms(2)] partition_onD2[OF assms(3)] notinP2_def
    by (clarsimp simp: disjnt_def map_filter_def disjoint_def split: if_splits)
      (smt (verit, ccfv_SIG) Diff_disjoint Int_Diff Int_commute fst_conv)
  show "{} \<notin> set (map fst (notinP2 P1 f v1 part2))" 
    using assms
    by (auto simp: map_filter_def split: if_splits)
  show "distinct (map fst ((P1, v1) # part1)) \<Longrightarrow> distinct (map fst part2) 
    \<Longrightarrow> distinct (map fst ((notinP2 P1 f v1 part2)))"
    using partition_onD2[OF assms(3), unfolded disjoint_def] distinct_map[of fst part2]
    by (clarsimp simp: notinP2_def map_filter_def distinct_map inj_on_def split: prod.splits)
      (metis Diff_Diff_Int Diff_empty Diff_iff fst_conv prod.inject)
qed

lemma wf_part_list_tail: 
  assumes "partition_on X (set (map fst ((P1, v1) # part1)))"
    and "distinct (map fst ((P1, v1) # part1))"
  shows "partition_on (X - P1) (set (map fst part1))"
    and "distinct (map fst part1)"
proof (rule partition_onI)
  show "\<Union> (set (map fst part1)) = X - P1"
    using partition_onD1[OF assms(1)] partition_onD2[OF assms(1)] assms(2)
    by (auto simp: disjoint_def image_iff)
  show "\<And>A1 A2. A1 \<in> set (map fst part1) \<Longrightarrow> A2 \<in> set (map fst part1) \<Longrightarrow> A1 \<noteq> A2 \<Longrightarrow> disjnt A1 A2" 
    using partition_onD2[OF assms(1)]
    by (clarsimp simp: disjnt_def disjoint_def)
      (smt (verit, ccfv_SIG) Diff_disjoint Int_Diff Int_commute fst_conv)
  show "{} \<notin> set (map fst part1)" 
    using partition_onD3[OF assms(1)]
    by (auto simp: map_filter_def split: if_splits)
  show "distinct (map fst (part1))"
    using assms(2)
    by auto
qed

lemma partition_on_append: "partition_on X (set xs) \<Longrightarrow> partition_on Y (set ys) 
  \<Longrightarrow> X \<inter> Y = {} \<Longrightarrow> partition_on (X \<union> Y) (set (xs @ ys))"
  by (auto simp: partition_on_def disjoint_def)
    (metis disjoint_iff)+

lemma wf_part_list_merge_part_raw: 
  "partition_on X (set (map fst part1)) \<and> distinct (map fst part1) 
  \<Longrightarrow> partition_on X (set (map fst part2)) \<and> distinct (map fst part2) 
  \<Longrightarrow> partition_on X (set (map fst (merge_part_raw f part1 part2))) 
    \<and> distinct (map fst (merge_part_raw f part1 part2))"
proof(induct f part1 part2 arbitrary: X rule: merge_part_raw.induct)
  case (2 f P1 v1 part1 part2)
  let ?inP1 = "List.map_filter (\<lambda>(P2, v2). if P1 \<inter> P2 \<noteq> {} then Some (P1 \<inter> P2, f v1 v2) else None) part2"
    and ?notinP1 = "List.map_filter (\<lambda>(P2, v2). if P2 - P1 \<noteq> {} then Some (P2 - P1, v2) else None) part2"
  have "P1 \<union> X = X"
    using "2.prems"
    by (auto simp: partition_on_def)
  have wf_part1: "partition_on (X - P1) (set (map fst part1))"
    "distinct (map fst part1)"
    using wf_part_list_tail "2.prems" by auto
  moreover have wf_notinP1: "partition_on (X - P1) (set (map fst ?notinP1))" 
    "distinct (map fst (?notinP1))"
    using wf_part_list_filter_minus[OF 2(2)[THEN conjunct1]] 
      "2.prems" by auto
  ultimately have IH: "partition_on (X - P1) (set (map fst (merge_part_raw f part1 (?notinP1))))"
    "distinct (map fst (merge_part_raw f part1 (?notinP1)))"
    using "2.hyps"[OF refl refl] by auto
  moreover have wf_inP1: "partition_on P1 (set (map fst ?inP1))" "distinct (map fst ?inP1)"
    using wf_part_list_filter_inter[OF 2(2)[THEN conjunct1]]
      "2.prems" by auto
  moreover have "(fst ` set ?inP1) \<inter> (fst ` set (merge_part_raw f part1 (?notinP1))) = {}"
    using IH(1)[THEN partition_onD1]
    by (intro set_eqI iffI; clarsimp simp: map_filter_def split: prod.splits if_splits)
      (smt (z3) Diff_disjoint Int_iff UN_iff disjoint_iff fst_conv)+
  ultimately show ?case 
    using partition_on_append[OF wf_inP1(1) IH(1)] \<open>P1 \<union> X = X\<close> wf_inP1(2) IH(2)
    by simp
qed simp

thm wf_part_list_filter_inter wf_part_list_filter_minus wf_part_list_tail

lift_definition merge_part :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('d, 'a) part \<Rightarrow> ('d, 'a) part \<Rightarrow> ('d, 'a) part" is merge_part_raw
  by (rule wf_part_list_merge_part_raw)

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

inductive sat_vorder :: "MFOTL.name list \<Rightarrow> 'd expl \<Rightarrow> bool" where
  "sat_vorder vs (Leaf _)"
| "\<forall>expl \<in> Vals part1. sat_vorder vs expl \<Longrightarrow> sat_vorder (x # vs) (Node x part1)"
| "sat_vorder vs (Node x part1) \<Longrightarrow> x \<noteq> v \<Longrightarrow> sat_vorder (v # vs) (Node x part1)"


end