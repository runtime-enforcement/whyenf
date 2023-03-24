theory LTL_Explanations
  imports "HOL-Library.Stream" "HOL-Library.Simps_Case_Conv"
    "Well_Quasi_Orders.Well_Quasi_Orders"
begin

declare [[names_short]]

datatype ltl = P nat | Conj ltl ltl | Disj ltl ltl | Neg ltl | Since ltl ltl | Until ltl ltl

primrec pd where
  "pd (P n) = 0"
| "pd (Conj phi psi) = max (pd phi) (pd psi)"
| "pd (Disj phi psi) = max (pd phi) (pd psi)"
| "pd (Neg phi) = pd phi"
| "pd (Since phi psi) = 1 + max (pd phi) (pd psi)"
| "pd (Until phi psi) = max (pd phi) (pd psi)"

context
  fixes rho :: "nat set stream"
begin

primrec sat where
  "sat i (P n) = (n \<in> rho !! i)"
| "sat i (Conj phi psi) = (sat i phi \<and> sat i psi)"
| "sat i (Disj phi psi) = (sat i phi \<or> sat i psi)"
| "sat i (Neg phi) = (\<not> sat i phi)"
| "sat i (Since phi psi) = (\<exists>j \<le> i. sat j psi \<and> (\<forall>k \<in> {j <.. i}. sat k phi))"
| "sat i (Until phi psi) = (\<exists>j \<ge> i. sat j psi \<and> (\<forall>k \<in> {i ..< j}. sat k phi))"

lemma not_sat_SinceD:
  assumes unsat: "\<not> sat i (Since phi psi)" and witness: "\<exists>j \<le> i. sat j psi"
  shows "\<exists>j \<le> i. \<not> sat j phi \<and> (\<forall>k \<in> {j .. i}. \<not> sat k psi)"
proof -
  define A and j where "A \<equiv> {j. j \<le> i \<and> sat j psi}" "j \<equiv> Max A"
  with witness have "j \<le> i" "sat j psi" "\<And>k. k \<in> {j <.. i} \<Longrightarrow> \<not> sat k psi"
    using Max_in[of A] Max_ge[of A] by auto
  with unsat show ?thesis by force
qed

lemma not_sat_UntilD:
  assumes unsat: "\<not> sat i (Until phi psi)" and witness: "\<exists>j \<ge> i. sat j psi"
  shows "\<exists>j \<ge> i. \<not> sat j phi \<and> (\<forall>k \<in> {i .. j}. \<not> sat k psi)"
proof -
  from witness obtain jmax where jmax: "jmax \<ge> i" "sat jmax psi" by blast
  moreover define A and j where "A \<equiv> {j. j \<ge> i \<and> j \<le> jmax \<and> sat j psi}" "j \<equiv> Min A"
  ultimately have "j \<ge> i" "sat j psi" "\<And>k. k \<in> {i ..< j} \<Longrightarrow> \<not> sat k psi"
    using Min_in[of A] Min_le[of A] by fastforce+
  with unsat show ?thesis by force
qed

end

locale lasso =
  fixes u :: "nat set list"
    and v :: "nat set list"
  assumes v_nonempty[simp]: "v \<noteq> []"
begin

definition rho where
  "rho = u @- cycle v"

abbreviation threshold where
  "threshold i psi \<equiv> max i (length u + length v * pd psi) + length v"

inductive SAT and VIO where
  SP: "n \<in> rho !! i \<Longrightarrow> SAT i (P n)"
| VP: "n \<notin> rho !! i \<Longrightarrow> VIO i (P n)"
| SConj: "SAT i phi \<Longrightarrow> SAT i psi \<Longrightarrow> SAT i (Conj phi psi)"
| VConjL: "VIO i phi \<Longrightarrow> VIO i (Conj phi psi)"
| VConjR: "VIO i psi \<Longrightarrow> VIO i (Conj phi psi)"
| SDisjL: "SAT i phi \<Longrightarrow> SAT i (Disj phi psi)"
| SDisjR: "SAT i psi \<Longrightarrow> SAT i (Disj phi psi)"
| VDisj: "VIO i phi \<Longrightarrow> VIO i psi \<Longrightarrow> VIO i (Disj phi psi)"
| SNeg: "VIO i phi \<Longrightarrow> SAT i (Neg phi)"
| VNeg: "SAT i phi \<Longrightarrow> VIO i (Neg phi)"
| SSince: "j \<le> i \<Longrightarrow> SAT j psi \<Longrightarrow> (\<And>k. k \<in> {j <.. i} \<Longrightarrow> SAT k phi) \<Longrightarrow> SAT i (Since phi psi)"
| VSince: "j \<le> i \<Longrightarrow> VIO j phi \<Longrightarrow> (\<And>k. k \<in> {j .. i} \<Longrightarrow> VIO k psi) \<Longrightarrow> VIO i (Since phi psi)"
| VSince_never: "(\<And>k. k \<in> {0 .. i} \<Longrightarrow> VIO k psi) \<Longrightarrow> VIO i (Since phi psi)"
| SUntil: "j \<ge> i \<Longrightarrow> SAT j psi \<Longrightarrow> (\<And>k. k \<in> {i ..< j} \<Longrightarrow> SAT k phi) \<Longrightarrow> SAT i (Until phi psi)"
| VUntil: "j \<ge> i \<Longrightarrow> VIO j phi \<Longrightarrow> (\<And>k. k \<in> {i .. j} \<Longrightarrow> VIO k psi) \<Longrightarrow> VIO i (Until phi psi)"
| VUntil_never: "(\<And>k. k \<in> {i ..< threshold i psi} \<Longrightarrow> VIO k psi) \<Longrightarrow> VIO i (Until phi psi)"

lemma completeness: "(sat rho i phi \<longrightarrow> SAT i phi) \<and> (\<not> sat rho i phi \<longrightarrow> VIO i phi)"
proof (induct phi arbitrary: i)
  case (Since phi psi)
  then show ?case
  proof (cases "\<exists>j\<le>i. sat rho j psi")
    case True
    from not_sat_SinceD[OF _ True, of phi] Since show ?thesis
      by (auto elim!: VSince SSince)
  qed (auto intro: SAT_VIO.intros)
next
  case (Until phi psi)
  then show ?case
  proof (cases "\<exists>j\<ge>i. sat rho j psi")
    case True
    from not_sat_UntilD[OF _ True, of phi] Until show ?thesis
      by (auto elim!: VUntil SUntil)
  qed (auto intro: SAT_VIO.intros)
qed (auto intro: SAT_VIO.intros)

lemma snth_cycle: "xs \<noteq> [] \<Longrightarrow> cycle xs !! n = xs ! (n mod length xs)"
proof (induct n arbitrary: xs)
  case (Suc n)
  from Suc(2) show ?case
    unfolding snth.simps cycle.simps
    by (subst Suc(1)) (auto simp: neq_Nil_conv nth_append nth_Cons' mod_Suc less_antisym)
qed (auto simp: neq_Nil_conv)

lemma sat_shift1: "k \<ge> length u + length v * pd phi \<Longrightarrow>
  sat rho k phi \<longleftrightarrow> sat rho (k + length v) phi"
proof (induct phi arbitrary: k)
  case (P x)
  then show ?case apply (auto simp: rho_def snth_cycle[OF v_nonempty])
     apply (metis add_diff_assoc2 mod_add_self2)+
    done
next
  case (Conj phi1 phi2)
  from Conj(1)[of k] Conj(2)[of k] Conj(3) show ?case
    by (simp add: nat_mult_max_right)
next
  case (Disj phi1 phi2)
  from Disj(1)[of k] Disj(2)[of k] Disj(3) show ?case
    by (simp add: nat_mult_max_right)
next
  case (Neg phi)
  from Neg(1)[of k] Neg(2) show ?case by simp
next
  case (Since phi1 phi2)
  from Since(3) show ?case
    apply (simp add: nat_mult_max_right nat_mult_distrib) apply safe
    subgoal for j
      apply (cases "j < k - length v")
      subgoal
        apply (rule exI[of _ j])
        apply safe
        subgoal by simp
        subgoal for i
          apply (cases "i \<le> k")
           apply simp
          apply (drule bspec[of _ _ "i - length v"]; auto)
          apply (subst (asm) Since; auto)
          done
        done
      subgoal
        apply (rule exI[of _ "j + length v"])
        apply safe
        subgoal by simp
        subgoal by (subst Since(2)[symmetric]; auto)
        subgoal for i
          apply (drule bspec[of _ _ "i - length v"])
           apply auto []
          apply (subst (asm) Since(1); auto)
          done
        done
      done
    subgoal for j
      apply (cases "j \<le> k")
      subgoal
        apply (rule exI[of _ j])
        apply safe
        subgoal by simp
        done
      apply (rule exI[of _ "j - length v"])
      apply safe
      subgoal by auto
      subgoal by (subst Since(2); auto)
      subgoal by (subst Since(1); auto)
      done
    done
next
  case (Until phi1 phi2)
  from Until(3) show ?case
    apply (simp add: nat_mult_max_right) apply safe
    subgoal for j
      apply (rule exI[of _ "j + length v"])
      apply safe
      subgoal by simp
      subgoal by (subst Until(2)[symmetric]; simp)
      subgoal for i
        apply (drule bspec[of _ _ "i - length v"])
         apply auto []
        apply (subst (asm) Until(1); auto)
        done
      done
    subgoal for j
      apply (rule exI[of _ "j - length v"])
      apply safe
      subgoal by auto
      subgoal by (subst Until(2); auto)
      subgoal by (subst Until(1); auto)
      done
    done
qed

lemma sat_shift: "k \<ge> length u + length v * pd phi \<Longrightarrow>
  sat rho (k + n * length v) phi \<longleftrightarrow> sat rho k phi"
  by (induct n arbitrary: k)
    (simp_all add: sat_shift1[symmetric] add.assoc[symmetric])

lemma soundness: "(SAT i phi \<longrightarrow> sat rho i phi) \<and> (VIO i phi \<longrightarrow> \<not> sat rho i phi)"
proof (induct i phi rule: SAT_VIO.induct)
  case (VSince j i phi psi)
  then show ?case unfolding sat.simps
    by (meson atLeastAtMost_iff greaterThanAtMost_iff not_le)
next
  case (VUntil j i phi psi)
  then show ?case unfolding sat.simps
    by (meson atLeastAtMost_iff atLeastLessThan_iff not_le)
next
  case (VUntil_never i psi phi)
  let ?n = "max i (length u + length v * pd psi)"
  have "\<not> sat rho k psi" if "i \<le> k" for k
  proof (cases "k < ?n + length v")
    case False
    then obtain \<Delta> where "k = ?n + length v + \<Delta>"
      using le_Suc_ex le_less_linear by blast
    then have "k = (?n + \<Delta> mod length v) + (Suc (\<Delta> div length v)) * length v"
      by auto
    then have "sat rho k psi = sat rho (?n + \<Delta> mod length v) psi"
      by (simp only: sat_shift)
    then show ?thesis
      by (auto intro!: VUntil_never(2))
  qed (auto simp: that VUntil_never(2))
  then show ?case by auto
qed auto

end

typedef 'a nelist = "{xs :: 'a list. xs \<noteq> []}" by auto

setup_lifting type_definition_nelist

lift_bnf (no_warn_wits) (neset: 'a) nelist
  for map: nemap
  by auto

lift_definition nenth :: "'a nelist \<Rightarrow> nat \<Rightarrow> 'a" (infixl "ne!" 100) is nth .
lift_definition nehd :: "'a nelist \<Rightarrow> 'a" is hd .
lift_definition netl :: "'a nelist \<Rightarrow> 'a list" is tl .
lift_definition nelast :: "'a nelist \<Rightarrow> 'a" is last .
lift_definition neupto :: "nat \<Rightarrow> nat \<Rightarrow> nat nelist" is "\<lambda>i j. if i > j then [i] else [i ..< j+1]"
  by auto

lift_definition size_nelist :: "('a \<Rightarrow> nat) \<Rightarrow> 'a nelist \<Rightarrow> nat" is size_list .


instantiation nelist :: (size) size begin
definition size_nelist :: "'a nelist \<Rightarrow> nat" where
  size_nelist_overloaded_def: "size_nelist = LTL_Explanations.size_nelist size"
instance proof qed
end

lemma size_nelist_o_map: "size_nelist g \<circ> nemap f = size_nelist (g \<circ> f)"
  unfolding nemap_def
  apply (auto simp: fun_eq_iff size_nelist_def)
  by (metis (mono_tags, lifting) Abs_nelist_inverse LTL_Explanations.size_nelist.rep_eq List.list.map_disc_iff Rep_nelist mem_Collect_eq size_list_map)

setup \<open>
  BNF_LFP_Size.register_size_global \<^type_name>\<open>nelist\<close> \<^const_name>\<open>size_nelist\<close>
    @{thm size_nelist_overloaded_def}
    @{thms }
    @{thms size_nelist_o_map}
\<close>

datatype sproof = SAtm nat nat | SNeg vproof | SConj sproof sproof | SDisjL sproof | SDisjR sproof
                | SSince sproof "sproof list" | SUntil "sproof list" sproof
     and vproof = VAtm nat nat | VNeg sproof | VConjL vproof | VConjR vproof | VDisj vproof vproof
                | VSince vproof "vproof nelist" | VUntil "vproof nelist" vproof
                | VSince_never "vproof nelist" | VUntil_never "vproof nelist"

lemma neq_Nil_conv_snoc: "(xs \<noteq> []) = (\<exists>y ys. xs = ys @ [y])"
by (induct xs) auto

lemma size_last_estimation[termination_simp]: "xs \<noteq> [] \<Longrightarrow> size (last xs) < size_list size xs"
  by (induct xs) auto
lemma size_nehd_estimation[termination_simp]: "size (nehd xs) < size_nelist size xs"
  unfolding size_nelist_overloaded_def by transfer (auto simp: neq_Nil_conv)
lemma size_nelast_estimation[termination_simp]: "size (nelast xs) < size_nelist size xs"
  unfolding size_nelist_overloaded_def by transfer (auto simp: neq_Nil_conv_snoc)
lemma size_nelist_estimation[termination_simp]: "x \<in> neset xs \<Longrightarrow> y < f x \<Longrightarrow> y < size_nelist f xs"
  unfolding size_nelist_overloaded_def neset_def by transfer (simp add: size_list_estimation)
lemma size_nelist_estimation'[termination_simp]: "x \<in> neset xs \<Longrightarrow> y \<le> f x \<Longrightarrow> y \<le> size_nelist f xs"
  unfolding size_nelist_overloaded_def neset_def by transfer (simp add: size_list_estimation')
lemma nehd_neset: "nehd xs \<in> neset xs" and nelast_neset: "nelast xs \<in> neset xs"
  unfolding neset_def by (transfer, auto)+

fun s_at and v_at where
  "s_at (SAtm _ n) = n"
| "s_at (SNeg vphi) = v_at vphi"
| "s_at (SConj sphi spsi) = s_at sphi"
| "s_at (SDisjL sphi) = s_at sphi"
| "s_at (SDisjR spsi) = s_at spsi"
| "s_at (SSince spsi sphis) = (case sphis of [] \<Rightarrow> s_at spsi | _ \<Rightarrow> s_at (last sphis))"
| "s_at (SUntil sphis spsi) = (case sphis of [] \<Rightarrow> s_at spsi | x # _ \<Rightarrow> s_at x)"
| "v_at (VAtm _ n) = n"
| "v_at (VNeg sphi) = s_at sphi"
| "v_at (VConjL vphi) = v_at vphi"
| "v_at (VConjR vpsi) = v_at vpsi"
| "v_at (VDisj vphi vpsi) = v_at vphi"
| "v_at (VSince vpsi vphis) = v_at (nelast vphis)"
| "v_at (VUntil vphis vpsi) = v_at (nehd vphis)"
| "v_at (VSince_never vpsis) = v_at (nelast vpsis)"
| "v_at (VUntil_never vpsis) = v_at (nehd vpsis)"

context lasso begin

fun s_check and v_check where
  "s_check f p = (case (f, p) of
    (P a, SAtm b n) \<Rightarrow> (a = b \<and> a \<in> rho !! n)
  | (Neg phi, SNeg sphi) \<Rightarrow> v_check phi sphi
  | (Conj phi psi, SConj sphi spsi) \<Rightarrow> s_check phi sphi \<and> s_check psi spsi \<and> s_at sphi = s_at spsi
  | (Disj phi psi, SDisjL sphi) \<Rightarrow> s_check phi sphi
  | (Disj phi psi, SDisjR spsi) \<Rightarrow> s_check psi spsi
  | (Since phi psi, SSince spsi sphis) \<Rightarrow>
    (let i = s_at (SSince spsi sphis);
         j = s_at spsi
    in map s_at sphis = [Suc j ..< Suc i] \<and> s_check psi spsi \<and> (\<forall>sphi \<in> set sphis. s_check phi sphi))
  | (Until phi psi, SUntil sphis spsi) \<Rightarrow>
    (let i = s_at (SUntil sphis spsi);
         j = s_at spsi
    in map s_at sphis = [i ..< j] \<and> s_check psi spsi \<and> (\<forall>sphi \<in> set sphis. s_check phi sphi))
  | (_, _) \<Rightarrow> False)"
| "v_check f p = (case (f, p) of
    (P a, VAtm b n) \<Rightarrow> (a = b \<and> a \<notin> rho !! n)
  | (Neg phi, VNeg sphi) \<Rightarrow> s_check phi sphi
  | (Disj phi psi, VDisj vphi vpsi) \<Rightarrow> v_check phi vphi \<and> v_check psi vpsi \<and> v_at vphi = v_at vpsi
  | (Conj phi psi, VConjL vphi) \<Rightarrow> v_check phi vphi
  | (Conj phi psi, VConjR vpsi) \<Rightarrow> v_check psi vpsi
  | (Since phi psi, VSince vphi vpsis) \<Rightarrow>
    (let i = v_at (VSince vphi vpsis);
         j = v_at vphi
    in j \<le> i \<and> nemap v_at vpsis = neupto j i \<and> v_check phi vphi \<and> (\<forall>vpsi \<in> neset vpsis. v_check psi vpsi))
  | (Until phi psi, VUntil vpsis vphi) \<Rightarrow>
    (let i = v_at (VUntil vpsis vphi);
         j = v_at vphi
    in i \<le> j \<and> nemap v_at vpsis = neupto i j \<and> v_check phi vphi \<and> (\<forall>vpsi \<in> neset vpsis. v_check psi vpsi))
  | (Since phi psi, VSince_never vpsis) \<Rightarrow>
    (let i = v_at (VSince_never vpsis)
    in nemap v_at vpsis = neupto 0 i \<and> (\<forall>vpsi \<in> neset vpsis. v_check psi vpsi))
  | (Until phi psi, VUntil_never vpsis) \<Rightarrow>
    (let i = v_at (VUntil_never vpsis)
    in nemap v_at vpsis = neupto i (threshold i psi) \<and> (\<forall>vpsi \<in> neset vpsis. v_check psi vpsi))
  | (_, _) \<Rightarrow> False)"

declare s_check.simps[simp del] v_check.simps[simp del]
simps_of_case s_check_simps[simp, code]: s_check.simps[unfolded prod.case] (splits: ltl.split sproof.split)
simps_of_case v_check_simps[simp, code]: v_check.simps[unfolded prod.case] (splits: ltl.split sproof.split)

lemma Cons_eq_upt_conv: "x # xs = [m ..< n] \<longleftrightarrow> m < n \<and> x = m \<and> xs = [Suc m ..< n]"
  by (induct n arbitrary: xs) (force simp: Cons_eq_append_conv)+

lemma map_setE[elim_format]: "map f xs = ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> \<exists>x\<in>set xs. f x = y"
  by (induct xs arbitrary: ys) auto

lemma neset_neupto[simp]: "neset (neupto i j) = (if j < i then {i} else {i .. j})"
  unfolding neset_def
  by transfer (auto simp: neupto_def)

lemma nemap_nesetE[elim_format]: "nemap f xs = ys \<Longrightarrow> y \<in> neset ys \<Longrightarrow> \<exists>x\<in>neset xs. f x = y"
  unfolding neset_def nemap_def
  apply auto
  apply transfer
  subgoal for y f xs ys
    apply (induct xs arbitrary: ys)
     apply (auto simp: Abs_nelist_inverse)
    done
  done

lemma check_sound:
  "s_check phi sphi \<Longrightarrow> SAT (s_at sphi) phi"
  "v_check phi vphi \<Longrightarrow> VIO (v_at vphi) phi"
proof (induction sphi and vphi arbitrary: phi and phi)
  case SAtm
  then show ?case by (cases phi) (auto intro: SAT_VIO.SP)
next
  case SNeg
  then show ?case by (cases phi) (auto intro: SAT_VIO.SNeg)
next
  case SConj
  then show ?case by (cases phi) (auto intro: SAT_VIO.SConj)
next
  case SDisjL
  then show ?case by (cases phi) (auto intro: SAT_VIO.SDisjL)
next
  case SDisjR
  then show ?case by (cases phi) (auto intro: SAT_VIO.SDisjR)
next
  case (SSince spsi sphis)
  then show ?case
  proof (cases phi)
    case (Since phi psi)
    show ?thesis
      using SSince
      unfolding Since
      apply (intro SAT_VIO.SSince[of "s_at spsi"])
        apply (auto simp: Let_def le_Suc_eq Cons_eq_append_conv Cons_eq_upt_conv
          split: if_splits list.splits)
      subgoal for k z zs
        apply (cases "k \<le> s_at z")
         apply (fastforce simp: le_Suc_eq elim!: map_setE[of _ _ _ k])+
        done
      done
  qed auto
next
  case (SUntil sphis spsi)
  then show ?case
  proof (cases phi)
    case (Until phi psi)
    show ?thesis
      using SUntil
      unfolding Until
      apply (intro SAT_VIO.SUntil[of _ "s_at spsi"])
        apply (auto simp: Let_def le_Suc_eq Cons_eq_append_conv Cons_eq_upt_conv
          split: if_splits list.splits)
      subgoal for k z zs
        apply (cases "k \<le> s_at z")
         apply (fastforce simp: le_Suc_eq elim!: map_setE[of _ _ _ k])+
        done
      done
  qed auto
next
  case VAtm
  then show ?case by (cases phi) (auto intro: SAT_VIO.VP)
next
  case VNeg
  then show ?case by (cases phi) (auto intro: SAT_VIO.VNeg)
next
  case VConjL
  then show ?case by (cases phi) (auto intro: SAT_VIO.VConjL)
next
  case VConjR
  then show ?case by (cases phi) (auto intro: SAT_VIO.VConjR)
next
  case VDisj
  then show ?case by (cases phi) (auto intro: SAT_VIO.VDisj)
next
  case VSince
  then show ?case
    by (cases phi) (auto simp: Let_def split: if_splits elim: nemap_nesetE intro!: SAT_VIO.VSince)
next
  case VUntil
  then show ?case
    by (cases phi) (auto simp: Let_def split: if_splits elim: nemap_nesetE intro!: SAT_VIO.VUntil)
next
  case VSince_never
  then show ?case
    by (cases phi) (auto elim: nemap_nesetE intro!: SAT_VIO.VSince_never)
next
  case VUntil_never
  then show ?case
    by (cases phi) (auto 0 4 simp: Let_def elim: nemap_nesetE intro!: SAT_VIO.VUntil_never)
qed

lemma SAT_or_VIO: "SAT i \<phi> \<or> VIO i \<phi>"
  using completeness by blast

end

definition "satoms x = rec_sproof (\<lambda>a _. {a}) (\<lambda>_. id) (\<lambda>_ _. (\<union>)) (\<lambda>_. id) (\<lambda>_. id)
   (\<lambda>_ xs. (\<union>) (\<Union>(set (map snd xs)))) (\<lambda>xs _. (\<union>) (\<Union>(set (map snd xs))))
   (\<lambda>a _. {a}) (\<lambda>_. id) (\<lambda>_. id) (\<lambda>_. id) (\<lambda>_ _. (\<union>))
   (\<lambda>_ xs. (\<union>) (\<Union>(neset (nemap snd xs)))) (\<lambda>xs _. (\<union>) (\<Union>(neset (nemap snd xs))))
   (\<lambda>xs. (\<Union>(neset (nemap snd xs)))) (\<lambda>xs. (\<Union>(neset (nemap snd xs)))) x"

definition "vatoms x = rec_vproof (\<lambda>a _. {a}) (\<lambda>_. id) (\<lambda>_ _. (\<union>)) (\<lambda>_. id) (\<lambda>_. id)
   (\<lambda>_ xs. (\<union>) (\<Union>(set (map snd xs)))) (\<lambda>xs _. (\<union>) (\<Union>(set (map snd xs))))
   (\<lambda>a _. {a}) (\<lambda>_. id) (\<lambda>_. id) (\<lambda>_. id) (\<lambda>_ _. (\<union>))
   (\<lambda>_ xs. (\<union>) (\<Union>(neset (nemap snd xs)))) (\<lambda>xs _. (\<union>) (\<Union>(neset (nemap snd xs))))
   (\<lambda>xs. (\<Union>(neset (nemap snd xs)))) (\<lambda>xs. (\<Union>(neset (nemap snd xs)))) x"
lemmas satoms_simps[simp] =
   sproof.rec[THEN trans[OF satoms_def], folded satoms_def vatoms_def,
     unfolded id_apply list.map_comp o_def snd_conv list.set_map]
lemmas vatoms_simps[simp] =
   vproof.rec[THEN trans[OF vatoms_def], folded satoms_def vatoms_def,
     unfolded id_apply nelist.map_comp o_def snd_conv nelist.set_map]

end