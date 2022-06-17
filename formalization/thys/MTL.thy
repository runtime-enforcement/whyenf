theory MTL
  imports Interval Trace "HOL-Library.Simps_Case_Conv"
    "Containers.Containers"
    "Well_Quasi_Orders.Well_Quasi_Orders" (* Regex *)
begin
declare [[names_short]]
section \<open>Formulas and Satisfiability\<close>

datatype 'a mtl = TT | FF | Atom 'a | Neg "'a mtl" | Disj "'a mtl" "'a mtl" 
  | Conj "'a mtl" "'a mtl" | Impl "'a mtl" "'a mtl" | Iff "'a mtl" "'a mtl"
  | Next \<I> "'a mtl" | Prev \<I> "'a mtl" | Once \<I> "'a mtl" 
  | Since "'a mtl" \<I> "'a mtl" | Until "'a mtl" \<I> "'a mtl"
    (*  | MatchF \<I> "'a mtl Regex.regex" | MatchP \<I> "'a mtl Regex.regex" *)

fun sat :: "'a trace \<Rightarrow> nat \<Rightarrow> 'a mtl \<Rightarrow> bool" where
  "sat \<sigma> i TT = True"
| "sat \<sigma> i FF = False"
| "sat \<sigma> i (Atom a) = (a \<in> \<Gamma> \<sigma> i)"
| "sat \<sigma> i (Neg \<phi>) = (\<not> sat \<sigma> i \<phi>)"
| "sat \<sigma> i (Disj \<phi> \<psi>) = (sat \<sigma> i \<phi> \<or> sat \<sigma> i \<psi>)"
| "sat \<sigma> i (Conj \<phi> \<psi>) = (sat \<sigma> i \<phi> \<and> sat \<sigma> i \<psi>)"
| "sat \<sigma> i (Impl \<phi> \<psi>) = (sat \<sigma> i \<phi> \<longrightarrow> sat \<sigma> i \<psi>)"
| "sat \<sigma> i (Iff \<phi> \<psi>) = (sat \<sigma> i \<phi> \<longleftrightarrow> sat \<sigma> i \<psi>)"
| "sat \<sigma> i (Next I \<phi>) = (mem (\<tau> \<sigma> (i + 1) - \<tau> \<sigma> i) I \<and> sat \<sigma> (i + 1) \<phi>)"
| "sat \<sigma> i (Prev I \<phi>) = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> sat \<sigma> j \<phi>)"
| "sat \<sigma> i (Once I \<phi>) = (\<exists>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> sat \<sigma> j \<phi>)"
| "sat \<sigma> i (Since \<phi> I \<psi>) = (\<exists>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> sat \<sigma> j \<psi> \<and> (\<forall>k \<in> {j <.. i}. sat \<sigma> k \<phi>))"
| "sat \<sigma> i (Until \<phi> I \<psi>) = (\<exists>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> sat \<sigma> j \<psi> \<and> (\<forall>k \<in> {i ..< j}. sat \<sigma> k \<phi>))"
  (*
| "sat \<sigma> i (MatchF I r) = (\<exists>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> Regex.match (sat \<sigma>) r i j)"
| "sat \<sigma> i (MatchP I r) = (\<exists>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> Regex.match (sat \<sigma>) r j i)"
*)

abbreviation "delta rho i j \<equiv> (\<tau> rho i) - (\<tau> rho j)"

(* context begin

qualified abbreviation "Imp \<phi> \<psi> \<equiv> Disj (Neg \<phi>) \<psi>"
qualified abbreviation "Iff \<phi> \<psi> \<equiv> Conj (Imp \<phi> \<psi>) (Imp \<psi> \<phi>)"
qualified abbreviation "Once I \<phi> \<equiv> Since TT I \<phi>"
qualified abbreviation "Historically I \<phi> \<equiv> Neg (Once I (Neg \<phi>))"
qualified abbreviation "Eventually I \<phi> \<equiv> Until TT I \<phi>"
qualified abbreviation "Always I \<phi> \<equiv> Neg (Eventually I (Neg \<phi>))"

end *)

lemma sat_Until_rec: "sat \<sigma> i (Until \<phi> I \<psi>) \<longleftrightarrow>
  mem 0 I \<and> sat \<sigma> i \<psi> \<or>
  (\<Delta> \<sigma> (i + 1) \<le> right I \<and> sat \<sigma> i \<phi> \<and> sat \<sigma> (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>))"
  apply (auto elim!: less_enatE simp: gr0_conv_Suc le_Suc_eq not_le)
  subgoal apply (metis (no_types, lifting) Suc_leI \<tau>_mono diff_is_0_eq' diff_le_mono diff_zero order.order_iff_strict leD le_less_trans) done
  subgoal apply (metis (no_types, lifting) Suc_leI \<tau>_mono diff_le_mono order.order_iff_strict leD le_less_trans) done
  subgoal for j apply (rule exI[of _ "j"]) apply (auto simp: diff_enat_def Suc_le_eq split: enat.splits)
     apply (metis Suc_leI diff_self_eq_0 le_0_eq le_neq_implies_less nat.simps(3))
    apply (metis Suc_leI diff_self_eq_0 le_0_eq le_neq_implies_less nat.simps(3)) done
  subgoal apply (auto simp: diff_enat_def le_diff_conv2 less_Suc_eq split: enat.splits) done
  subgoal for j apply (rule exI[of _ "j"]; auto simp: diff_enat_def le_diff_conv2 Suc_le_eq split: enat.splits) done
  done

lemma sat_Since_rec: "sat \<sigma> i (Since \<phi> I \<psi>) \<longleftrightarrow>
  mem 0 I \<and> sat \<sigma> i \<psi> \<or>
  (i > 0 \<and> \<Delta> \<sigma> i \<le> right I \<and> sat \<sigma> i \<phi> \<and> sat \<sigma> (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>))"
  apply (auto elim!: less_enatE simp: gr0_conv_Suc le_Suc_eq not_le)
  subgoal apply (cases i) apply auto done
  subgoal apply (cases i) apply auto done
  subgoal for j k apply (cases i; auto simp: le_Suc_eq Suc_le_eq)
    apply (meson \<tau>_mono diff_le_mono2 order.trans enat_ord_simps(1)) done
  subgoal for j  apply (rule exI[of _ "j"]) apply (auto simp: diff_enat_def Suc_le_eq split: enat.splits)
    using not_less_eq_eq apply fastforce
    using not_less_eq_eq apply fastforce done
  subgoal for j k apply (cases i; auto simp: le_Suc_eq Suc_le_eq)
    apply (meson \<tau>_mono diff_le_mono2 le_less_trans not_le) done
  subgoal for j apply (cases i; auto simp: le_Suc_eq)
    apply (rule exI[of _ "j"]) apply (auto simp: diff_enat_def Suc_le_eq split: enat.splits)
     apply (metis Nat.le_diff_conv2 \<tau>_mono add_diff_cancel_left' diff_diff_left diff_le_mono2 le_eq_less_or_eq le_imp_less_Suc)
    apply (metis Nat.le_diff_conv2 \<tau>_mono add_diff_cancel_left' diff_diff_left diff_le_mono2 le_imp_less_Suc order_less_imp_le)
    done
  subgoal for k j apply (rule exI[of _ "j"]; auto simp: diff_enat_def le_diff_conv2 le_Suc_eq split: enat.splits) done
  done

lemma sat_Once_rec: "sat \<sigma> i (Once I \<phi>) \<longleftrightarrow>
  mem 0 I \<and> i > 0 \<and> \<Delta> \<sigma> i \<le> right I \<and> sat \<sigma> i \<phi>"
  sorry

(*
lemma sat_MatchF_rec: "sat \<sigma> i (MatchF I r) \<longleftrightarrow> mem 0 I \<and> Regex.eps (sat \<sigma>) i r \<or>
  \<Delta> \<sigma> (i + 1) \<le> right I \<and> (\<exists>s \<in> Regex.lpd (sat \<sigma>) i r. sat \<sigma> (i + 1) (MatchF (subtract (\<Delta> \<sigma> (i + 1)) I) s))"
  (is "?L \<longleftrightarrow> ?R1 \<or> ?R2")
proof (rule iffI; (elim disjE conjE bexE)?)
  assume ?L
  then obtain j where j: "j \<ge> i" "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I" and"Regex.match (sat \<sigma>) r i j" by auto
  then show "?R1 \<or> ?R2"
  proof (cases "i < j")
    case True
    with \<open>Regex.match (sat \<sigma>) r i j\<close> lpd_match[of _ _ "sat \<sigma>"] obtain s
      where "s \<in> Regex.lpd (sat \<sigma>) i r" "Regex.match (sat \<sigma>) s (i + 1) j" by auto
    with True j have ?R2
      by (cases "right I")
        (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j] elim: le_trans[rotated])
    then show ?thesis by blast
  qed (auto simp: eps_match)
next
  assume "enat (\<Delta> \<sigma> (i + 1)) \<le> right I"
  moreover
  fix s
  assume [simp]: "s \<in> Regex.lpd (sat \<sigma>) i r" and "(sat \<sigma>) (i + 1) (MatchF (subtract (\<Delta> \<sigma> (i + 1)) I) s)"
  then obtain j where "j > i" "Regex.match (sat \<sigma>) s (i + 1) j"
    "mem (\<tau> \<sigma> j - \<tau> \<sigma> (Suc i)) (subtract (\<Delta> \<sigma> (i + 1)) I)" by (auto simp: Suc_le_eq)
  ultimately show ?L
    by (cases "right I")
      (auto simp: le_diff_conv lpd_match intro!: exI[of _ j] bexI[of _ s])
qed (auto simp: eps_match intro!: exI[of _ i])

lemma sat_PossiblyP_rec: "(sat \<sigma>) i (MatchP I r) \<longleftrightarrow> mem 0 I \<and> Regex.eps (sat \<sigma>) i r \<or>
  i > 0 \<and> \<Delta> \<sigma> i \<le> right I \<and> (\<exists>s \<in> Regex.rpd (sat \<sigma>) i r. (sat \<sigma>) (i - 1) (MatchP (subtract (\<Delta> \<sigma> i) I) s))"
  (is "?L \<longleftrightarrow> ?R1 \<or> ?R2")
proof (rule iffI; (elim disjE conjE bexE)?)
  assume ?L
  then obtain j where j: "j \<le> i" "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I" and "Regex.match (sat \<sigma>) r j i" by auto
  then show "?R1 \<or> ?R2"
  proof (cases "j < i")
    case True
    with \<open>Regex.match (sat \<sigma>) r j i\<close> rpd_match[of _ _ "sat \<sigma>"] obtain s
      where "s \<in> Regex.rpd (sat \<sigma>) i r" "Regex.match (sat \<sigma>) s j (i - 1)" by auto
    with True j have ?R2
      by (cases "right I")
        (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j] elim: le_trans)
    then show ?thesis by blast
  qed (auto simp: eps_match)
next
  assume "enat (\<Delta> \<sigma> i) \<le> right I"
  moreover
  fix s
  assume [simp]: "s \<in> Regex.rpd (sat \<sigma>) i r" and "(sat \<sigma>) (i - 1) (MatchP (subtract (\<Delta> \<sigma> i) I) s)" "i > 0"
  then obtain j where "j < i" "Regex.match (sat \<sigma>) s j (i - 1)"
    "mem (\<tau> \<sigma> (i - 1) - \<tau> \<sigma> j) (subtract (\<Delta> \<sigma> i) I)" by (auto simp: gr0_conv_Suc less_Suc_eq_le)
  ultimately show ?L
    by (cases "right I")
      (auto simp: le_diff_conv rpd_match intro!: exI[of _ j] bexI[of _ s])
qed (auto simp: eps_match intro!: exI[of _ i])
*)

definition ETP:: "'a trace \<Rightarrow> nat \<Rightarrow> nat"
  where
    "ETP rho t = (LEAST i. \<tau> rho i \<ge> t)"

lemma ETP_zero[simp]: "ETP rho 0 = 0"
  by (auto simp add: ETP_def)

definition LTP:: "'a trace \<Rightarrow> nat \<Rightarrow> nat"
  where
    "LTP rho t = Max {i. (\<tau> rho i) \<le> t}"

(*ETP and LTP lemmas for arbitrary event streams*)
lemma i_etp_to_tau: "i \<ge> ETP rho n \<longleftrightarrow> \<tau> rho i \<ge> n"
proof
  assume P: "i \<ge> ETP rho n"
  define j where j_def: "j \<equiv> ETP rho n"
  then have i_j: "\<tau> rho i \<ge> \<tau> rho j" using P by auto
  from j_def have "\<tau> rho j \<ge> n"
    unfolding ETP_def using LeastI_ex ex_le_\<tau> by force
  then show "\<tau> rho i \<ge> n" using i_j by auto
next
  assume Q: "\<tau> rho i \<ge> n"
  then show "ETP rho n \<le> i" unfolding ETP_def
    by (auto simp add: Least_le)
qed

lemma i_ltp_to_tau:
  assumes n_asm: "n \<ge> \<tau> rho 0"
  shows "(i \<le> LTP rho n \<longleftrightarrow> \<tau> rho i \<le> n)"
proof
  define A and j where A_def: "A \<equiv> {i. \<tau> rho i \<le> n}"  and j_def: "j \<equiv> LTP rho n"
  assume P: "i \<le> LTP rho n"
  from n_asm A_def have A_ne: "A \<noteq> {}" by auto
  from j_def have i_j: "\<tau> rho i \<le> \<tau> rho j" using P by auto
  from A_ne j_def have "\<tau> rho j \<le> n"
    unfolding LTP_def using Max_in[of A] A_def
    by (metis \<tau>_mono finite_nat_set_iff_bounded_le le_trans mem_Collect_eq nat_le_linear)
  then show "\<tau> rho i \<le> n" using i_j by auto
next
  define A and j where A_def: "A \<equiv> {i. \<tau> rho i \<le> n}"  and j_def: "j \<equiv> LTP rho n"
  assume Q: "\<tau> rho i \<le> n"
  then have "i \<in> A" using A_def by auto
  then show "i \<le> LTP rho n" unfolding LTP_def using Max_ge[of A] A_def
    by (metis finite_Collect_le_nat i_etp_to_tau infinite_nat_iff_unbounded_le mem_Collect_eq)
qed

lemma etp_to_delta: "i \<ge> ETP rho (\<tau> rho l + n) \<Longrightarrow> delta rho i l \<ge> n"
proof -
  assume P: "i \<ge> ETP rho (\<tau> rho l + n)"
  then have "\<tau> rho i \<ge> \<tau> rho l + n" by (auto simp add: i_etp_to_tau)
  then show ?thesis by auto
qed

lemma etp_ge: "ETP rho (\<tau> rho l + n + 1) > l"
proof -
  define j where j_def: "j \<equiv> \<tau> rho l + n + 1"
  then have etp_j: "\<tau> rho (ETP rho j) \<ge> j" unfolding ETP_def
    using LeastI_ex ex_le_\<tau> by force
  then have "\<tau> rho (ETP rho j) > \<tau> rho l" using j_def by auto
  then show ?thesis using j_def less_\<tau>D by blast
qed

lemma i_le_ltpi: "i \<le> LTP rho (\<tau> rho i)"
  using \<tau>_mono i_ltp_to_tau[of rho "\<tau> rho i" i]
  by auto

lemma i_le_ltpi_add: "i \<le> LTP rho (\<tau> rho i + n)"
  using i_le_ltpi
  by (simp add: add_increasing2 i_ltp_to_tau)

lemma i_le_ltpi_minus: "\<tau> rho 0 + n \<le> \<tau> rho i \<Longrightarrow> i > 0 \<Longrightarrow> n > 0 \<Longrightarrow>
  LTP rho (\<tau> rho i - n) < i"
  unfolding LTP_def
  apply (subst Max_less_iff)
    apply (auto simp: finite_nat_set_iff_bounded_le)
  subgoal apply (rule exI[of _ i]; auto)
    apply (erule contrapos_pp) back back back
    apply (auto simp: not_le not_less dest!: \<tau>_mono[of i _ rho] less_imp_le[of i])
    done
  subgoal apply (rule exI[of _ 0]; auto) done
  subgoal for a
    apply (erule contrapos_pp)
    apply (auto simp: not_le not_less dest!: \<tau>_mono[of i a rho])
    done
  done

lemma i_ge_etpi: "ETP rho (\<tau> rho i) \<le> i"
  using \<tau>_mono i_etp_to_tau[of rho "\<tau> rho i" i]
  by auto

lemma enat_trans[simp]: "enat i \<le> enat j \<and> enat j \<le> enat k \<Longrightarrow> enat i \<le> enat k"
  by auto

(*sat lemmas*)
lemma not_sat_SinceD:
  assumes unsat: "\<not> sat rho i (Since phi I psi)" and
    witness: "\<exists>j \<le> i. mem (\<tau> rho i - \<tau> rho j) I \<and> sat rho j psi"
  shows "\<exists>j \<le> i. ETP rho (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> \<tau> rho i - n) \<le> j \<and> \<not> sat rho j phi
  \<and> (\<forall>k \<in> {j .. (min i (LTP rho (\<tau> rho i - left I)))}. \<not> sat rho k psi)"
proof -
  define A and j where A_def: "A \<equiv> {j. j \<le> i \<and> mem (\<tau> rho i - \<tau> rho j) I \<and> sat rho j psi}"
    and j_def: "j \<equiv> Max A"
  from witness have j: "j \<le> i" "sat rho j psi" "mem (\<tau> rho i - \<tau> rho j) I"
    using Max_in[of A] unfolding j_def[symmetric] unfolding A_def
    by auto
  moreover
  from j(3) have "ETP rho (case right I of enat n \<Rightarrow> \<tau> rho i - n | \<infinity> \<Rightarrow> 0) \<le> j"
    unfolding ETP_def by (intro Least_le) (auto split: enat.splits)
  moreover
  { fix j
    assume "\<tau> rho j \<le> \<tau> rho i"
    moreover obtain k where "\<tau> rho i < \<tau> rho k" "i < k"
      by (meson ex_le_\<tau> gt_ex less_le_trans)
    ultimately have "j \<le> ETP rho (Suc (\<tau> rho i))"
      unfolding ETP_def
      apply -
      apply (rule LeastI2[of _ k])
       apply (auto simp: Suc_le_eq)
      by (meson \<tau>_mono leD less_le_trans linear)
  } note * = this
  { fix k
    assume k: "k \<in> {j <.. (min i (LTP rho (\<tau> rho i - left I)))}"
    with j(3) have "mem (\<tau> rho i - \<tau> rho k) I"
      unfolding LTP_def
      apply (auto simp: le_diff_conv2 add.commute)
       apply (subst (asm) Max_ge_iff)
         apply auto
        prefer 2
      using \<tau>_mono le_trans nat_add_left_cancel_le apply blast
       apply (rule finite_subset[of _ "{0 .. ETP rho (\<tau> rho i + 1)}"])
        apply (auto simp: * Suc_le_eq) [2]
      apply (cases "right I")
       apply (auto simp: le_diff_conv)
      by (meson \<tau>_mono add_mono_thms_linordered_semiring(2) le_trans less_imp_le)

    with Max_ge[of A k] k have "\<not> sat rho k psi"
      unfolding j_def[symmetric] unfolding A_def
      by auto
  }
  ultimately show ?thesis using unsat
    by (auto dest!: spec[of _ j])
qed

lemma min_not_in: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> x < Min A \<Longrightarrow> x \<notin> A"
  by auto

lemma not_sat_UntilD:
  assumes unsat: "\<not> (sat rho i (Until phi I psi))"
    and witness: "\<exists>j \<ge> i. mem (delta rho j i) I \<and> sat rho j psi"
  shows "\<exists>j \<ge> i. (case right I of \<infinity> \<Rightarrow> True | enat n \<Rightarrow> j \<le> LTP rho (\<tau> rho i + n))
  \<and> \<not> (sat rho j phi) \<and> (\<forall>k \<in> {(max i (ETP rho (\<tau> rho i + left I))) .. j}.
   \<not> sat rho k psi)"
proof -
  from \<tau>_mono have i0: "\<tau> rho 0 \<le> \<tau> rho i" by auto
  from witness obtain jmax where jmax: "jmax \<ge> i" "sat rho jmax psi"
    "mem (delta rho jmax i) I" by blast
  define A and j where A_def: "A \<equiv> {j. j \<ge> i \<and> j \<le> jmax
  \<and> mem (delta rho j i) I \<and> sat rho j psi}" and j_def: "j \<equiv> Min A"
  have j: "j \<ge> i" "sat rho j psi" "mem (delta rho j i) I"
    using A_def j_def jmax Min_in[of A]
    unfolding j_def[symmetric] unfolding A_def
    by fastforce+
  moreover have "case right I of \<infinity> \<Rightarrow> True | enat n \<Rightarrow> j \<le> LTP rho (\<tau> rho i + n)"
    using i_ltp_to_tau[of rho j]
    apply (auto split: enat.splits)
    by (smt (verit, ccfv_SIG) \<tau>_mono add_diff_cancel_left' enat_ord_simps(1) i0 i_ltp_to_tau j(1) j(3) le_add1 le_add_diff_inverse2 le_diff_conv2 le_trans)
  moreover
  {fix k
    assume k_def: "k \<in> {(max i (ETP rho (\<tau> rho i + left I))) ..< j}"
    then have ki: "\<tau> rho k \<ge> \<tau> rho i + left I" using i_etp_to_tau by auto
    with k_def have kj: "k < j" by auto
    then have "\<tau> rho k \<le> \<tau> rho j" by auto
    then have "delta rho k i \<le> delta rho j i" by auto
    with this j(3) have "enat (delta rho k i) \<le> right I"
      by (meson enat_ord_simps(1) order_subst2)
    with this ki j(3) have mem_k: "mem (delta rho k i) I"
      unfolding ETP_def by (auto simp: Least_le)

    with j_def have "j \<le> jmax" using Min_in[of A]
      using jmax A_def
      by (metis (mono_tags, lifting) Collect_empty_eq
          finite_nat_set_iff_bounded_le mem_Collect_eq order_refl)
    with this k_def have kjm: "k \<le> jmax" by auto

    with this mem_k ki Min_le[of A k] min_not_in[of A k] k_def have "k \<notin> A"
      unfolding j_def[symmetric] unfolding A_def unfolding ETP_def
      using finite_nat_set_iff_bounded_le kj by blast
    with this mem_k k_def kjm have "\<not> sat rho k psi"
      by (simp add: A_def)}
  ultimately show ?thesis using unsat
    by (auto split: enat.splits dest!: spec[of _ j])
qed

context fixes rho:: "'a trace"
begin

(*Abbreviations for readability*)
abbreviation "l i I \<equiv> min i (LTP rho ((\<tau> rho i) - left I))"
abbreviation "lu i I \<equiv> max i (ETP rho ((\<tau> rho i) + left I))"

inductive bounded_future where
  TTBF: "bounded_future TT"
| FFBF: "bounded_future FF"
| AtomBF: "bounded_future (Atom n)"
| DisjBF: "bounded_future phi \<Longrightarrow> bounded_future psi
\<Longrightarrow> bounded_future (Disj phi psi)"
| ConjBF: "bounded_future phi \<Longrightarrow> bounded_future psi
\<Longrightarrow> bounded_future (Conj phi psi)"
| ImplBF: "bounded_future phi \<Longrightarrow> bounded_future psi
\<Longrightarrow> bounded_future (Impl phi psi)"
| IffBF: "bounded_future phi \<Longrightarrow> bounded_future psi
\<Longrightarrow> bounded_future (Iff phi psi)"
| NegBF:  "bounded_future phi \<Longrightarrow> bounded_future (Neg phi)"
| NextBF: "bounded_future phi \<Longrightarrow> bounded_future (Next I phi)"
| PrevBF: "bounded_future phi \<Longrightarrow> bounded_future (Prev I phi)"
| OnceBF: "bounded_future phi \<Longrightarrow> bounded_future (Once I phi)"
| SinceBF: "bounded_future phi \<Longrightarrow> bounded_future psi
\<Longrightarrow> bounded_future (Since phi I psi)"
| UntilBF: "right I \<noteq> \<infinity> \<Longrightarrow> bounded_future phi \<Longrightarrow> bounded_future psi
\<Longrightarrow> bounded_future (Until phi I psi)"
  (*
| MatchPBF: "\<forall>x \<in> Regex.atms r. bounded_future x
\<Longrightarrow> bounded_future (MatchP I r)"
| MatchFBF: "right I \<noteq> \<infinity> \<Longrightarrow> \<forall>x \<in> Regex.atms r. bounded_future x
\<Longrightarrow> bounded_future (MatchF I r)"
*)

lemma bounded_future_simps[simp]:
  shows
    "bounded_future TT \<longleftrightarrow> True" "bounded_future FF \<longleftrightarrow> True"
    "bounded_future (Atom n) \<longleftrightarrow> True"
    "bounded_future (Disj phi psi) \<longleftrightarrow> bounded_future phi \<and> bounded_future psi"
    "bounded_future (Conj phi psi) \<longleftrightarrow> bounded_future phi \<and> bounded_future psi"
    "bounded_future (Impl phi psi) \<longleftrightarrow> bounded_future phi \<and> bounded_future psi"
    "bounded_future (Iff phi psi) \<longleftrightarrow> bounded_future phi \<and> bounded_future psi"
    "bounded_future (Neg phi) \<longleftrightarrow> bounded_future phi"
    "bounded_future (Next I phi) \<longleftrightarrow> bounded_future phi"
    "bounded_future (Prev I phi) \<longleftrightarrow> bounded_future phi"
    "bounded_future (Once I phi) \<longleftrightarrow> bounded_future phi"
    "bounded_future (Since phi I psi) \<longleftrightarrow> bounded_future phi \<and> bounded_future psi"
    "bounded_future (Until phi I psi) \<longleftrightarrow> bounded_future phi \<and> bounded_future psi \<and> right I \<noteq> \<infinity>"
    (*
  "bounded_future (MatchP I r) \<longleftrightarrow> (\<forall>x \<in> Regex.atms r. bounded_future x)"
  "bounded_future (MatchF I r) \<longleftrightarrow> right I \<noteq> \<infinity> \<and> (\<forall>x \<in> Regex.atms r. bounded_future x)"
*)
  by (auto intro: bounded_future.intros elim: bounded_future.cases)

(*Updated definitions for temporal operators; added constraint violations*)
inductive SAT and VIO where
  STT: "SAT i TT"
| VFF: "VIO i FF"
| SP: "n \<in> \<Gamma> rho i  \<Longrightarrow> SAT i (Atom n)"
| VP: "n \<notin> \<Gamma> rho i  \<Longrightarrow> VIO i (Atom n)"
| SDisjL: "SAT i phi \<Longrightarrow> SAT i (Disj phi psi)"
| SDisjR: "SAT i psi \<Longrightarrow> SAT i (Disj phi psi)"
| VDisj: "VIO i phi \<Longrightarrow> VIO i psi \<Longrightarrow> VIO i (Disj phi psi)"
| SConj: "SAT i phi \<Longrightarrow> SAT i psi \<Longrightarrow> SAT i (Conj phi psi)"
| VConjL: "VIO i phi \<Longrightarrow> VIO i (Conj phi psi)"
| VConjR: "VIO i psi \<Longrightarrow> VIO i (Conj phi psi)"
| SNeg: "VIO i phi \<Longrightarrow> SAT i (Neg phi)"
| VNeg: "SAT i phi \<Longrightarrow> VIO i (Neg phi)"
| SImplL: "VIO i phi \<Longrightarrow> SAT i (Impl phi psi)"
| SImplR: "SAT i psi \<Longrightarrow> SAT i (Impl phi psi)"
| VImpl: "SAT i phi \<Longrightarrow> VIO i psi \<Longrightarrow> VIO i (Impl phi psi)"
| SIff_ss: "SAT i phi \<Longrightarrow> SAT i psi \<Longrightarrow> SAT i (Iff phi psi)"
| SIff_vv: "VIO i phi \<Longrightarrow> VIO i psi \<Longrightarrow> SAT i (Iff phi psi)"
| VIff_sv: "SAT i phi \<Longrightarrow> VIO i psi \<Longrightarrow> VIO i (Iff phi psi)"
| VIff_vs: "VIO i phi \<Longrightarrow> SAT i psi \<Longrightarrow> VIO i (Iff phi psi)"
| SNext: "mem (\<Delta> rho (i+1)) I \<Longrightarrow> SAT (i+1) phi \<Longrightarrow> SAT i (Next I phi)"
| VNext: "VIO (i+1) phi \<Longrightarrow> VIO i (Next I phi)"
| VNext_le: "(\<Delta> rho (i+1)) < (left I) \<Longrightarrow> VIO i (Next I phi)"
| VNext_ge: "enat (\<Delta> rho (i+1)) > (right I) \<Longrightarrow> VIO i (Next I phi)"
| SPrev: "i > 0 \<Longrightarrow> mem (\<Delta> rho i) I \<Longrightarrow> SAT (i-1) phi \<Longrightarrow> SAT i (Prev I phi)"
| VPrev: "i > 0 \<Longrightarrow> VIO (i-1) phi \<Longrightarrow> VIO i (Prev I phi)"
| VPrev_zero: "i = 0 \<Longrightarrow> VIO i (Prev I phi)"
| VPrev_le: "i > 0 \<Longrightarrow> (\<Delta> rho i) < (left I) \<Longrightarrow> VIO i (Prev I phi)"
| VPrev_ge: "i > 0 \<Longrightarrow> enat (\<Delta> rho i) > (right I) \<Longrightarrow> VIO i (Prev I phi)"
| SOnce: "j \<le> i \<Longrightarrow> mem (delta rho i j) I  \<Longrightarrow> SAT j phi \<Longrightarrow> SAT i (Once I phi)"
| VOnce_le: "\<tau> rho i < \<tau> rho 0 + left I \<Longrightarrow> VIO i (Once I phi)"
| VOnce_never: "j = (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> ETP rho ((\<tau> rho i) - n)) \<Longrightarrow>
 (\<tau> rho i) \<ge> (\<tau> rho 0) + left I \<Longrightarrow>
(\<And>k. k \<in> {j .. l i I} \<Longrightarrow> VIO k phi) \<Longrightarrow> VIO i (Once I phi)"
| SSince: "j \<le> i \<Longrightarrow> mem (delta rho i j) I  \<Longrightarrow> SAT j psi \<Longrightarrow> (\<And>k. k \<in> {j <.. i}
\<Longrightarrow> SAT k phi) \<Longrightarrow> SAT i (Since phi I psi)"
| VSince_le: "\<tau> rho i < \<tau> rho 0 + left I \<Longrightarrow> VIO i (Since phi I psi)"
| VSince: "(case right I of \<infinity> \<Rightarrow> True | enat n \<Rightarrow> ETP rho ((\<tau> rho i) - n) \<le> j)
\<Longrightarrow> j \<le> i \<Longrightarrow> (\<tau> rho 0) + left I \<le> (\<tau> rho i) \<Longrightarrow> VIO j phi
\<Longrightarrow> (\<And>k. k \<in> {j .. l i I} \<Longrightarrow> VIO k psi) \<Longrightarrow> VIO i (Since phi I psi)"
| VSince_never: "j = (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> ETP rho ((\<tau> rho i) - n)) \<Longrightarrow>
 (\<tau> rho i) \<ge> (\<tau> rho 0) + left I \<Longrightarrow>
(\<And>k. k \<in> {j .. l i I} \<Longrightarrow> VIO k psi) \<Longrightarrow> VIO i (Since phi I psi)"
| SUntil: "j \<ge> i \<Longrightarrow> mem (delta rho j i) I  \<Longrightarrow> SAT j psi \<Longrightarrow> (\<And>k. k \<in> {i ..< j} \<Longrightarrow> SAT k phi)
\<Longrightarrow> SAT i (Until phi I psi)"
| VUntil: "(case right I of \<infinity> \<Rightarrow> True | enat n \<Rightarrow> j \<le> LTP rho ((\<tau> rho i) + n)) \<Longrightarrow> j \<ge> i
\<Longrightarrow> VIO j phi \<Longrightarrow> (\<And>k. k \<in> {lu i I .. j} \<Longrightarrow> VIO k psi) \<Longrightarrow> VIO i (Until phi I psi)"
| VUntil_never: "(\<And>k. k \<in> (case right I of \<infinity> \<Rightarrow> {lu i I ..} | enat n \<Rightarrow> {lu i I .. LTP rho ((\<tau> rho i) + n)}) \<Longrightarrow> VIO k psi)
\<Longrightarrow> VIO i (Until phi I psi)"
  (*
| SMatchP: "j \<le> i \<Longrightarrow> mem (delta rho i j) I \<Longrightarrow> Regex.SAT SAT j i r
\<Longrightarrow> SAT i (MatchP I r)"
| VMatchP_le: "\<tau> rho i < \<tau> rho 0 + left I \<Longrightarrow> VIO i (MatchP I r)"
| VMatchP: "k = ETP rho (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> \<tau> rho i - n)
\<Longrightarrow> \<tau> rho i \<ge> \<tau> rho 0 + left I \<Longrightarrow> (\<And>j. j \<in> {k .. l i I} \<Longrightarrow> Regex.VIO VIO j i r)
\<Longrightarrow> VIO i (MatchP I r)"
| SMatchF: "i \<le> j \<Longrightarrow> mem (delta rho j i) I \<Longrightarrow> Regex.SAT SAT i j r
\<Longrightarrow> SAT i (MatchF I r)"
| VMatchF: "k = LTP rho (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> \<tau> rho i + n)
\<Longrightarrow> (\<And>j. j \<in> {lu i I .. k} \<Longrightarrow> Regex.VIO VIO i j r) \<Longrightarrow> VIO i (MatchF I r)"
*)

lemma completeness: "
(sat rho i phi \<longrightarrow> SAT i phi) \<and> (\<not> sat rho i phi \<longrightarrow> VIO i phi)"
proof (induct phi arbitrary: i)
  case (Prev I phi)
  show ?case using  local.Prev
    by (auto intro: SAT_VIO.SPrev SAT_VIO.VPrev SAT_VIO.VPrev_le SAT_VIO.VPrev_ge SAT_VIO.VPrev_zero split: nat.splits)
next
  case (Once I phi)
  {assume "sat rho i (Once I phi)"
    then have "SAT i (Once I phi)"
      using SAT_VIO.SOnce local.Once
      by auto}
  moreover
  {assume unsat: "\<not> sat rho i (Once I phi)"
      and i_l: "\<tau> rho i < \<tau> rho 0 + left I"
    then have "VIO i (Once I phi)"
      using SAT_VIO.VOnce_le local.Once
      by auto}
  moreover
  {assume unsat: "\<not> sat rho i (Once I phi)"
      and nw: "\<forall>j\<le>i. \<not> mem (delta rho i j) I \<or> \<not> sat rho j phi"
      and i_ge: "\<tau> rho 0 + left I \<le> \<tau> rho i"
    then have "VIO i (Once I phi)"
      using local.Once
      by (auto intro!: SAT_VIO.VOnce_never simp: i_ltp_to_tau i_etp_to_tau
          split: enat.splits)}
  ultimately show ?case
    by force
next
  case (Since phi I psi)
  {assume "sat rho i (Since phi I psi)"
    then have "SAT i (Since phi I psi)"
      using SAT_VIO.SSince local.Since
      by auto}
  moreover
  {assume unsat: "\<not> sat rho i (Since phi I psi)"
      and i_l: "\<tau> rho i < \<tau> rho 0 + left I"
    then have "VIO i (Since phi I psi)"
      using SAT_VIO.VSince_le local.Since
      by auto}
  moreover
  {assume unsat: "\<not> sat rho i (Since phi I psi)"
      and nw: "\<forall>j\<le>i. \<not> mem (delta rho i j) I \<or> \<not> sat rho j psi"
      and i_ge: "\<tau> rho 0 + left I \<le> \<tau> rho i"
    then have "VIO i (Since phi I psi)"
      using local.Since
      by (auto intro!: SAT_VIO.VSince_never simp: i_ltp_to_tau i_etp_to_tau
          split: enat.splits)}
  moreover
  {assume unsat: "\<not> sat rho i (Since phi I psi)"
      and jw: "\<exists>j\<le>i. mem (delta rho i j) I \<and> sat rho j psi"
      and i_ge: "\<tau> rho 0 + left I \<le> \<tau> rho i"
    from unsat jw not_sat_SinceD[of rho i phi I psi]
    obtain j where j: "j \<le> i"
      "case right I of \<infinity> \<Rightarrow> True | enat n \<Rightarrow> ETP rho (\<tau> rho i - n) \<le> j"
      "\<not> sat rho j phi" "(\<forall>k \<in> {j .. (min i (LTP rho (\<tau> rho i - left I)))}.
      \<not> sat rho k psi)" by (auto split: enat.splits)
    then have "VIO i (Since phi I psi)"
      using i_ge unsat jw SAT_VIO.VSince local.Since
      by auto}
  ultimately show ?case
    by (force simp del: sat.simps)
next
  case (Until phi I psi)
  from \<tau>_mono have i0: "\<tau> rho 0 \<le> \<tau> rho i" by auto
  {assume "sat rho i (Until phi I psi)"
    then have "SAT i (Until phi I psi)"
      using SAT_VIO.SUntil local.Until
      by auto}
  moreover
  {assume unsat: "\<not> sat rho i (Until phi I psi)"
      and witness: "\<exists>j \<ge> i. mem (delta rho j i) I \<and> sat rho j psi"
    from this local.Until not_sat_UntilD[of rho i phi I psi] obtain j
      where j: "j \<ge> i" "(case right I of \<infinity> \<Rightarrow> True | enat n
      \<Rightarrow> j \<le> LTP rho (\<tau> rho i + n))" "\<not> (sat rho j phi)"
        "(\<forall>k \<in> {(max i (ETP rho (\<tau> rho i + left I))) .. j}. \<not> sat rho k psi)"
      by auto
    then have "VIO i (Until phi I psi)"
      using unsat witness SAT_VIO.VUntil local.Until
      by auto}
  moreover
  {assume unsat: "\<not> sat rho i (Until phi I psi)"
      and no_witness: "\<forall>j \<ge> i. \<not> mem (delta rho j i) I \<or> \<not> sat rho j psi"
    then have "VIO i (Until phi I psi)"
      using local.Until
      by (auto intro!: SAT_VIO.VUntil_never simp: add_increasing2 i0 i_ltp_to_tau i_etp_to_tau
          split: enat.splits)
  }
  ultimately show ?case by auto
      (*
next
  case (MatchPBF r I)
  {
    assume sat: "sat rho i (MatchP I r)"
    then obtain j where j_def: "j \<le> i \<and> mem (delta rho i j) I \<and> Regex.match (sat rho) r j i"
      by auto
    then have "Regex.SAT SAT j i r" using MatchPBF Regex.completeness_SAT[of r (*bounded_future*) "sat rho" "SAT" j i]
      by auto
    then have "SAT i (MatchP I r)" using j_def
      by (auto intro: SAT_VIO.SMatchP)
  }
  moreover
  {
    assume unsat: "\<not> sat rho i (MatchP I r)"
    then have "VIO i (MatchP I r)"
    proof (cases "\<tau> rho 0 + left I \<le> \<tau> rho i")
      case True
      from unsat have "\<forall>j\<le> i. \<not> mem (delta rho i j) I \<or> \<not> Regex.match (sat rho) r j i"
        by auto
      then have "\<forall>j \<in> {ETP rho (case right I of enat n \<Rightarrow> (\<tau> rho i - n) | \<infinity> \<Rightarrow> 0) .. l i I}. \<not> Regex.match (sat rho) r j i"
        apply (auto split: enat.splits)
         apply (metis add.commute True add_leD2 i_etp_to_tau i_ltp_to_tau le_diff_conv le_diff_conv2)
        by (metis add.commute True add_leD2 i_ltp_to_tau le_diff_conv2)
      then show ?thesis
        using True MatchPBF Regex.completeness_VIO[of r (*bounded_future*) "sat rho" "VIO" _ i]
        by (auto intro: SAT_VIO.VMatchP)
    next
      case False
      then show ?thesis
        by (auto intro: SAT_VIO.VMatchP_le)
    qed
  }
  ultimately show ?case by auto
next
  case (MatchFBF I r)
  then obtain n where n_def: "right I = enat n" by auto
  {
    assume sat: "sat rho i (MatchF I r)"
    then obtain j where j_def: "i \<le> j \<and> mem (delta rho j i) I \<and> Regex.match (sat rho) r i j"
      by auto
    then have "Regex.SAT SAT i j r" using MatchFBF Regex.completeness_SAT[of r "sat rho" "SAT" i j]
      by auto
    then have "SAT i (MatchF I r)" using j_def 
      by (auto intro: SAT_VIO.SMatchF)
  }
  moreover
  {
    assume unsat: "\<not> sat rho i (MatchF I r)"
    then have j_ge_props: "\<forall>j\<ge>i. \<not> mem (delta rho j i) I \<or> \<not> Regex.match (sat rho) r i j"
      by auto
    moreover
    have "\<forall>j. j \<le> LTP rho (\<tau> rho i + n) \<longrightarrow> delta rho j i \<le> n"
      by (auto simp add: add.commute i_ltp_to_tau trans_le_add2)
    ultimately have "\<forall>j \<in> {lu i I  .. LTP rho (\<tau> rho i + n)}. \<not> Regex.match (sat rho) r i j"
      by (auto simp add: etp_to_delta n_def)
    then have "VIO i (MatchF I r)"
      using n_def MatchFBF Regex.completeness_VIO[of r "sat rho" "VIO" i _]
      by (auto intro: SAT_VIO.VMatchF)
  }
  ultimately show ?case by auto
*)
qed(auto intro: SAT_VIO.intros)

lemma soundness: "(SAT i phi \<longrightarrow> sat rho i phi) \<and> (VIO i phi \<longrightarrow> \<not> sat rho i phi)"
proof (induction phi arbitrary: i)
  case (Atom n)
  {assume "SAT i (Atom n)"
    then have "sat rho i (Atom n)" by (cases) (auto)
  }
  moreover
  {assume "VIO i (Atom n)"
    then have "\<not> sat rho i (Atom n)" by (cases) (auto)
  }
  ultimately show ?case by auto
next
  case (Disj phi psi)
  {assume "SAT i (Disj phi psi)"
    then have "sat rho i (Disj phi psi)" using Disj by (cases) (auto)
  }
  moreover
  {assume "VIO i (Disj phi psi)"
    then have "\<not> sat rho i (Disj phi psi)" using Disj by (cases) (auto)
  }
  ultimately show ?case by auto
next
  case (Conj phi psi)
  {assume "SAT i (Conj phi psi)"
    then have "sat rho i (Conj phi psi)" using Conj by (cases) (auto)
  }
  moreover
  {assume "VIO i (Conj phi psi)"
    then have "\<not> sat rho i (Conj phi psi)" using Conj by (cases) (auto)
  }
  ultimately show ?case by auto
next
  case (Impl phi psi)
  {assume "SAT i (Impl phi psi)"
    then have "sat rho i (Impl phi psi)" using Impl by (cases) (auto)
  }
  moreover
  {assume "VIO i (Impl phi psi)"
    then have "\<not> sat rho i (Impl phi psi)" using Impl by (cases) (auto)
  }
  ultimately show ?case by auto
next
  case (Iff phi psi)
  {assume "SAT i (Iff phi psi)"
    then have "sat rho i (Iff phi psi)" using Iff by (cases) (auto)
  }
  moreover
  {assume "VIO i (Iff phi psi)"
    then have "\<not> sat rho i (Iff phi psi)" using Iff by (cases) (auto)
  }
  ultimately show ?case by auto
next
  case (Neg phi)
  {assume "SAT i (Neg phi)"
    then have "sat rho i (Neg phi)" using Neg by (cases) (auto)
  }
  moreover
  {assume "VIO i (Neg phi)"
    then have "\<not> sat rho i (Neg phi)" using Neg by (cases) (auto)
  }
  ultimately show ?case by auto
next
  case (Next I phi)
  {assume "SAT i (Next I phi)"
    then have "sat rho i (Next I phi)" using Next by (cases) (auto)
  }
  moreover
  {assume "VIO i (Next I phi)"
    then have "\<not> sat rho i (Next I phi)" using Next by (cases) (auto)
  }
  ultimately show ?case by auto
next
  case (Prev I phi)
  {assume "SAT i (Prev I phi)"
    then have "sat rho i (Prev I phi)" using Prev
      by (cases) (auto split: nat.splits)
  }
  moreover
  {assume "VIO i (Prev I phi)"
    then have "\<not> sat rho i (Prev I phi)" using Prev
      by (cases) (auto split: nat.splits)
  }
  ultimately show ?case by auto
next
  case (Once I phi)
  {assume "SAT i (Once I phi)"
    then have "sat rho i (Once I phi)" using Once by (cases) (auto)
  }
  moreover
  {assume "VIO i (Once I phi)"
    then have "\<not> sat rho i (Once I phi)" using Once
    proof (cases)
      case (VOnce_le)
      {fix j
        from \<tau>_mono have j0: "\<tau> rho 0 \<le> \<tau> rho j" by auto
        then have "\<tau> rho i < \<tau> rho j + left I" using VOnce_le apply auto
          using j0 by linarith
        then have "delta rho i j < left I"
          using VOnce_le less_\<tau>D verit_comp_simplify1(3) by fastforce
        then have "\<not> mem (delta rho i j) I" by auto}
      then show ?thesis using VOnce_le OnceBF by auto
    next
      case (VOnce_never j)
      {fix k
        assume k_def: "sat rho k phi \<and> mem (delta rho i k) I \<and> k \<le> i"
        then have k_tau: "\<tau> rho k \<le> \<tau> rho i - left I"
          using diff_le_mono2 by fastforce
        then have k_ltp: "k \<le> LTP rho (\<tau> rho i - left I)"
          using VOnce_never i_ltp_to_tau add_le_imp_le_diff
          by blast
        then have "k \<notin> {j .. l i I}"
          using k_def VOnce_never Once k_tau
          by auto
        then have "k < j" using k_def k_ltp by auto
      }
      then show ?thesis
        using VOnce_never Once
        apply (cases "right I = \<infinity>")
         apply (auto)
        by (metis diff_commute diff_is_0_eq i_etp_to_tau leD)
    qed  
  }
  ultimately show ?case by auto
next
  case (Since phi I psi)
  {assume "SAT i (Since phi I psi)"
    then have "sat rho i (Since phi I psi)" using Since by (cases) (auto)
  }
  moreover
  {assume "VIO i (Since phi I psi)"
    then have "\<not> sat rho i (Since phi I psi)" using Since
    proof (cases)
      case (VSince_le)
      {fix j
        from \<tau>_mono have j0: "\<tau> rho 0 \<le> \<tau> rho j" by auto
        then have "\<tau> rho i < \<tau> rho j + left I" using VSince_le apply auto
          using j0 by linarith
        then have "delta rho i j < left I" using VSince_le j0 apply auto
          by (metis Groups.ab_semigroup_add_class.add.commute Nat.less_eq_nat.simps(1) \<open>\<tau> rho i < \<tau> rho j + left I\<close> \<tau>_mono diff_is_0_eq less_diff_conv2 linorder_neqE_nat local.VSince_le nat_le_linear not_less0)
        then have "\<not> mem (delta rho i j) I" by auto}
      then show ?thesis using VSince_le SinceBF by auto
    next
      case (VSince j)
      {fix k
        assume k_def: "sat rho k psi \<and> mem (delta rho i k) I \<and> k \<le> i"
        then have "\<tau> rho k \<le> \<tau> rho i - left I" using diff_le_mono2 by fastforce
        then have k_ltp: "k \<le> LTP rho (\<tau> rho i - left I)"
          using VSince i_ltp_to_tau add_le_imp_le_diff
          by blast
        then have "k < j" using k_def VSince Since apply auto
          by (meson diff_is_0_eq not_gr_zero zero_less_diff)
        then have "j \<in> {k <.. i} \<and> \<not> sat rho j phi" using VSince Since
          by auto
      }
      then show ?thesis using VSince Since
        by force
    next
      case (VSince_never j)
      {fix k
        assume k_def: "sat rho k psi \<and> mem (delta rho i k) I \<and> k \<le> i"
        then have k_tau: "\<tau> rho k \<le> \<tau> rho i - left I"
          using diff_le_mono2 by fastforce
        then have k_ltp: "k \<le> LTP rho (\<tau> rho i - left I)"
          using VSince_never i_ltp_to_tau add_le_imp_le_diff
          by blast
        then have "k \<notin> {j .. l i I}"
          using k_def VSince_never Since k_tau
          by auto
        then have "k < j" using k_def k_ltp by auto
      }
      then show ?thesis
        using VSince_never Since
        apply (cases "right I = \<infinity>")
         apply (auto)
        by (metis diff_commute diff_is_0_eq i_etp_to_tau leD)
    qed
  }
  ultimately show ?case by auto
next
  case (Until phi I psi)
  {assume "SAT i (Until phi I psi)"
    then have "sat rho i (Until phi I psi)" using Until
      by (cases) (auto)
  }
  moreover
  {assume "VIO i (Until phi I psi)"
    then have "\<not> sat rho i (Until phi I psi)" using Until
    proof (cases)
      case (VUntil j)
      {fix k
        assume k_def: "sat rho k psi \<and> mem (delta rho k i) I \<and> i \<le> k"
        then have "\<tau> rho k \<ge> \<tau> rho i + left I"
          using le_diff_conv2 by auto
        then have k_etp: "k \<ge> ETP rho (\<tau> rho i + left I)"
          using VUntil i_etp_to_tau by blast
        from this k_def VUntil Until have "k \<notin> {lu i I .. j}" by auto
        then have "j < k" using k_etp k_def by auto
        then have "j \<in> {i ..< k} \<and> VIO j phi" using VUntil k_def
          by auto
      }
      then show ?thesis
        using VUntil Until by force
    next
      case (VUntil_never)
      {fix k n
        assume r: "right I = enat n"
        from this VUntil_never UntilBF have tin0: "\<tau> rho i + n \<ge> \<tau> rho 0"
          by (auto simp add: trans_le_add1)
        define j where "j = LTP rho ((\<tau> rho i) + n)"
        from VUntil_never UntilBF have j_i: "i \<le> j"
          by (auto simp add: i_ltp_to_tau trans_le_add1 j_def)
        assume k_def: "sat rho k psi \<and> mem (delta rho k i) I \<and> i \<le> k"
        then have "\<tau> rho k \<ge> \<tau> rho i + left I"
          using le_diff_conv2 by auto
        then have k_etp: "k \<ge> ETP rho (\<tau> rho i + left I)"
          using VUntil_never i_etp_to_tau by blast
        from this k_def VUntil_never Until have "k \<notin> {lu i I .. j}"
          by (auto simp: r j_def)
        then have "j < k" using VUntil_never UntilBF k_def k_etp by auto
        from k_def r have "delta rho k i \<le> n" by auto
        then have "\<tau> rho k \<le> \<tau> rho i + n" by auto
        then have "k \<le> j"
          using tin0 VUntil_never UntilBF i_ltp_to_tau r k_def apply (auto simp: j_def)
          by blast
      }
      note aux = this
      show ?thesis
      proof (cases "right I")
        case (enat n)
        show ?thesis
          using VUntil_never Until aux
          unfolding enat
          apply (auto simp: i_etp_to_tau le_diff_conv2)
          by (metis Groups.ab_semigroup_add_class.add.commute add_le_imp_le_diff enat enat_ord_simps(1))
      next
        case infinity
        show ?thesis
          using VUntil_never Until
          by (auto simp: infinity i_etp_to_tau le_diff_conv2)
      qed
    qed
  }
  ultimately show ?case by auto
      (*
next
  case (MatchPBF r I)
  {
    assume SAT: "SAT i (MatchP I r)"
    then have "sat rho i (MatchP I r)" using MatchPBF Regex.soundness_SAT[of r SAT "sat rho" ]
      by cases auto
  }
  moreover
  {
    assume VIO: "VIO i (MatchP I r)"
    then have "\<not> sat rho i (MatchP I r)" using MatchPBF
    proof (cases)
      case (VMatchP_le)
      {
        fix j
        from \<tau>_mono have j0: "\<tau> rho 0 \<le> \<tau> rho j" by auto
        then have i_less: "\<tau> rho i < \<tau> rho j + left I" using VMatchP_le apply auto
          using j0 by linarith
        then have "delta rho i j < left I" using VMatchP_le j0 apply auto
          by (metis add.commute Nat.less_eq_nat.simps(1) i_less \<tau>_mono diff_is_0_eq less_diff_conv2 linorder_neqE_nat nat_le_linear not_less0)
        then have "\<not> mem (delta rho i j) I" by auto
      }
      then show ?thesis by auto
    next
      case (VMatchP k)
      from VMatchP MatchPBF have nmatch: "\<forall>j \<in> {k .. l i I}. \<not> Regex.match (sat rho) r j i"
        using Regex.soundness_VIO[of r VIO "sat rho"]
        by auto
      from VMatchP MatchPBF have "\<forall>j\<le>i. j \<notin> {k .. l i I} \<longrightarrow> \<not> mem (delta rho i j) I"
        apply (auto simp add: i_etp_to_tau split: enat.splits)
        subgoal premises prems for i' j
        proof -
          have f5: "j \<le> LTP rho (\<tau> rho i)"
            using prems(6) by (metis i_le_ltpi le_trans)
          have "\<tau> rho 0 \<le> \<tau> rho i"
            using prems(2)
            by auto
          then show False
            using f5 prems(7) prems(9)
            by (metis (no_types) add_diff_assoc i_le_ltpi_add i_ltp_to_tau le_add_diff_inverse)
        qed
        subgoal premises prems for j
        proof -
          from prems(6) have "\<tau> rho j \<le> \<tau> rho i"
            by auto
          then show False
            using prems(7,8)
            by (metis (no_types) add_diff_assoc i_le_ltpi_add le_add_diff_inverse)
        qed
        done
        then show ?thesis using nmatch
          by auto
      qed
  }
  ultimately show ?case by auto
next
  case (MatchFBF I r)
  {
    assume SAT: "SAT i (MatchF I r)"
    then have "sat rho i (MatchF I r)" using MatchFBF Regex.soundness_SAT[of r SAT "sat rho" ]
      by cases auto
  }
  moreover
  {
    assume VIO: "VIO i (MatchF I r)"
    then have "\<not> sat rho i (MatchF I r)" using MatchPBF
    proof (cases)
      case (VMatchF k)
      from MatchFBF(1) obtain n where n_def: "right I = enat n" by auto
      from VMatchF MatchFBF have nmatch: "\<forall>j \<in> {lu i I .. k}. \<not> Regex.match (sat rho) r i j"
        using n_def Regex.soundness_VIO[of r VIO "sat rho"]
        by auto
      from VMatchF MatchFBF have "\<forall>j\<ge>i. j \<notin> {lu i I .. k} \<longrightarrow> \<not> mem (delta rho j i) I"
        using n_def
        apply (auto simp: i_ltp_to_tau)
         apply (metis add.right_neutral add_diff_inverse i_etp_to_tau le_trans nat_add_left_cancel_le nat_diff_split)
        by (metis add.commute i_le_ltpi_add le_add_diff_inverse le_diff_conv)
      then show ?thesis using nmatch
        by auto
    qed
  }
  ultimately show ?case by auto
*)
qed (auto elim: SAT.cases VIO.cases)

end

(*
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

lift_definition nesingle :: "'a \<Rightarrow> 'a nelist" is "\<lambda>a. [a]" by simp
lift_definition necons :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a nelist" is Cons by simp

lemma nehd_nesingle: "nehd (nesingle a) = a"
  apply transfer
  by simp

lemma nehd_necons: "nehd (necons a as) = a"
  apply transfer
  by simp

lift_definition size_nelist :: "('a \<Rightarrow> nat) \<Rightarrow> 'a nelist \<Rightarrow> nat" is size_list .


instantiation nelist :: (size) size begin
definition size_nelist :: "'a nelist \<Rightarrow> nat" where
  size_nelist_overloaded_def: "size_nelist = MTL.size_nelist size"
instance proof qed
end

lemma size_nelist_o_map: "size_nelist g \<circ> nemap f = size_nelist (g \<circ> f)"
  unfolding nemap_def
  apply (auto simp: fun_eq_iff size_nelist_def)
  by (metis (mono_tags, lifting) Abs_nelist_inverse MTL.size_nelist.rep_eq List.list.map_disc_iff Rep_nelist mem_Collect_eq size_list_map)

setup \<open>
  BNF_LFP_Size.register_size_global \<^type_name>\<open>nelist\<close> \<^const_name>\<open>size_nelist\<close>
    @{thm size_nelist_overloaded_def}
    @{thms }
    @{thms size_nelist_o_map}
\<close>
*)

(*Added proofs for Prev and Next, as well as constraint violation proofs *)
datatype 'a sproof = STT nat | SAtm 'a nat | SNeg "'a vproof" | SDisjL "'a sproof" | SDisjR "'a sproof"
  | SConj "'a sproof" "'a sproof" | SImplR "'a sproof" | SImplL "'a vproof"
  | SIff_ss "'a sproof" "'a sproof" | SIff_vv "'a vproof" "'a vproof" | SOnce nat "'a sproof"
  | SSince "'a sproof" "'a sproof list" | SUntil "'a sproof list" "'a sproof" | SNext "'a sproof"
  | SPrev "'a sproof"
    (*| SMatchP "('a sproof) rsproof" | SMatchF "('a sproof) rsproof"*)
    and 'a vproof = VFF nat | VAtm 'a nat | VNeg "'a sproof" | VDisj "'a vproof" "'a vproof"
  | VConjL "'a vproof" | VConjR "'a vproof" | VImpl "'a sproof" "'a vproof"
  | VIff_sv "'a sproof" "'a vproof" | VIff_vs "'a vproof" "'a sproof" 
  | VOnce_le nat | VOnce_never nat nat "'a vproof list"
  | VSince nat "'a vproof" "'a vproof list" | VUntil nat "'a vproof list" "'a vproof"
  | VSince_never nat nat "'a vproof list" | VUntil_never nat nat "'a vproof list" | VSince_le nat
  | VNext "'a vproof" | VNext_ge nat | VNext_le nat | VPrev "'a vproof" | VPrev_ge nat | VPrev_le nat
  | VPrev_zero
    (*| VMatchP nat "('a vproof) rvproof list" | VMatchF nat "('a vproof) rvproof list"
    | VMatchP_le nat*)


context fixes compa :: "'a \<Rightarrow> 'b \<Rightarrow> order" begin
fun comparator_list' :: "'a list \<Rightarrow> 'b list \<Rightarrow> order" where
  "comparator_list' [] [] = Eq"
| "comparator_list' [] (y # ys) = Lt"
| "comparator_list' (x # xs) [] = Gt"
| "comparator_list' (x # xs) (y # ys) = (case compa x y of Eq \<Rightarrow> comparator_list' xs ys | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)"
end
  (*
thm comparator_sproof_simps[no_vars] comparator_vproof_simps[no_vars]
*)
instantiation sproof and vproof :: (ccompare) ccompare begin

primrec comparator_sproof :: "('a \<Rightarrow> 'b \<Rightarrow> order) \<Rightarrow> 'a sproof \<Rightarrow> 'b sproof \<Rightarrow> order"
  and comparator_vproof :: "('a \<Rightarrow> 'b \<Rightarrow> order) \<Rightarrow> 'a vproof \<Rightarrow> 'b vproof \<Rightarrow> order" where
  "comparator_sproof compa (STT i) rhs =
    (case rhs of
      STT j \<Rightarrow> comparator_of i j
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SAtm p i) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SAtm q j \<Rightarrow> (case compa p q of Eq \<Rightarrow> comparator_of i j | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SNeg vp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SAtm _ _ \<Rightarrow> Gt
    | SNeg vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SDisjL sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SAtm _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SDisjL sp' \<Rightarrow> comparator_sproof compa sp sp'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SDisjR sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SAtm _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SDisjL _ \<Rightarrow> Gt
    | SDisjR sp' \<Rightarrow> comparator_sproof compa sp sp'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SConj sp1 sp2) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SAtm _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SDisjL _ \<Rightarrow> Gt
    | SDisjR _ \<Rightarrow> Gt
    | SConj sp1' sp2' \<Rightarrow> (case comparator_sproof compa sp1 sp1' of Eq \<Rightarrow> comparator_sproof compa sp2 sp2' | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SImplR sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SAtm _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SDisjL _ \<Rightarrow> Gt
    | SDisjR _ \<Rightarrow> Gt
    | SConj _ _ \<Rightarrow> Gt
    | SImplR sp' \<Rightarrow> comparator_sproof compa sp sp'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SImplL vp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SAtm _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SDisjL _ \<Rightarrow> Gt
    | SDisjR _ \<Rightarrow> Gt
    | SConj _ _ \<Rightarrow> Gt
    | SImplR _ \<Rightarrow> Gt
    | SImplL vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SIff_ss sp1 sp2) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SAtm _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SDisjL _ \<Rightarrow> Gt
    | SDisjR _ \<Rightarrow> Gt
    | SConj _ _ \<Rightarrow> Gt
    | SImplR _ \<Rightarrow> Gt
    | SImplL _ \<Rightarrow> Gt
    | SIff_ss sp1' sp2' \<Rightarrow> (case comparator_sproof compa sp1 sp1' of Eq \<Rightarrow> comparator_sproof compa sp2 sp2' | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SIff_vv vp1 vp2) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SAtm _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SDisjL _ \<Rightarrow> Gt
    | SDisjR _ \<Rightarrow> Gt
    | SConj _ _ \<Rightarrow> Gt
    | SImplR _ \<Rightarrow> Gt
    | SImplL _ \<Rightarrow> Gt
    | SIff_ss _ _ \<Rightarrow> Gt
    | SIff_vv vp1' vp2' \<Rightarrow> (case comparator_vproof compa vp1 vp1' of Eq \<Rightarrow> comparator_vproof compa vp2 vp2' | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SOnce i sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SAtm _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SDisjL _ \<Rightarrow> Gt
    | SDisjR _ \<Rightarrow> Gt
    | SConj _ _ \<Rightarrow> Gt
    | SImplR _ \<Rightarrow> Gt
    | SImplL _ \<Rightarrow> Gt
    | SIff_ss _ _ \<Rightarrow> Gt
    | SIff_vv _ _ \<Rightarrow> Gt
    | SOnce i' sp' \<Rightarrow> (case comparator_of i i' of Eq \<Rightarrow> comparator_sproof compa sp sp' | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SSince sp2 sp1s) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SAtm _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SDisjL _ \<Rightarrow> Gt
    | SDisjR _ \<Rightarrow> Gt
    | SConj _ _ \<Rightarrow> Gt
    | SImplR _ \<Rightarrow> Gt
    | SImplL _ \<Rightarrow> Gt
    | SIff_ss _ _ \<Rightarrow> Gt
    | SIff_vv _ _ \<Rightarrow> Gt
    | SOnce _ _ \<Rightarrow> Gt
    | SSince sp2' sp1s' \<Rightarrow> (case comparator_sproof compa sp2 sp2' of 
                             Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_sproof compa) sp1s) sp1s'
                           | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SUntil sp1s sp2) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SAtm _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SDisjL _ \<Rightarrow> Gt
    | SDisjR _ \<Rightarrow> Gt
    | SConj _ _ \<Rightarrow> Gt
    | SImplR _ \<Rightarrow> Gt
    | SImplL _ \<Rightarrow> Gt
    | SIff_ss _ _ \<Rightarrow> Gt
    | SIff_vv _ _ \<Rightarrow> Gt
    | SOnce _ _ \<Rightarrow> Gt
    | SSince _ _ \<Rightarrow> Gt
    | SUntil sp1s' sp2' \<Rightarrow> (case comparator_sproof compa sp2 sp2' of 
                             Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_sproof compa) sp1s) sp1s'
                           | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SPrev sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SAtm _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SDisjL _ \<Rightarrow> Gt
    | SDisjR _ \<Rightarrow> Gt
    | SConj _ _ \<Rightarrow> Gt
    | SImplR _ \<Rightarrow> Gt
    | SImplL _ \<Rightarrow> Gt
    | SIff_ss _ _ \<Rightarrow> Gt
    | SIff_vv _ _ \<Rightarrow> Gt
    | SOnce _ _ \<Rightarrow> Gt
    | SSince _ _ \<Rightarrow> Gt
    | SUntil _ _  \<Rightarrow> Gt
    | SPrev sp' \<Rightarrow> comparator_sproof compa sp sp'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SNext sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SAtm _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SDisjL _ \<Rightarrow> Gt
    | SDisjR _ \<Rightarrow> Gt
    | SConj _ _ \<Rightarrow> Gt
    | SImplR _ \<Rightarrow> Gt
    | SImplL _ \<Rightarrow> Gt
    | SIff_ss _ _ \<Rightarrow> Gt
    | SIff_vv _ _ \<Rightarrow> Gt
    | SOnce _ _ \<Rightarrow> Gt
    | SSince _ _ \<Rightarrow> Gt
    | SUntil _ _  \<Rightarrow> Gt
    | SPrev _ \<Rightarrow> Gt
    | SNext sp' \<Rightarrow> comparator_sproof compa sp sp')"
| "comparator_vproof compa (VFF i) rhs =
    (case rhs of
      VFF j \<Rightarrow> comparator_of i j
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VAtm p i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm q j \<Rightarrow> (case compa p q of Eq \<Rightarrow> comparator_of i j | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VNeg sp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg sp' \<Rightarrow> comparator_sproof compa sp sp'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VDisj vp1 vp2) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj vp1' vp2' \<Rightarrow> (case comparator_vproof compa vp1 vp1' of Eq \<Rightarrow> comparator_vproof compa vp2 vp2' | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VConjL vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VConjR vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VImpl sp1 vp2) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR _ \<Rightarrow> Gt
    | VImpl sp1' vp2' \<Rightarrow> (case comparator_sproof compa sp1 sp1' of Eq \<Rightarrow> comparator_vproof compa vp2 vp2' | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VIff_sv sp1 vp2) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR _ \<Rightarrow> Gt
    | VImpl _ _ \<Rightarrow> Gt
    | VIff_sv sp1' vp2' \<Rightarrow> (case comparator_sproof compa sp1 sp1' of Eq \<Rightarrow> comparator_vproof compa vp2 vp2' | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VIff_vs vp1 sp2) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR _ \<Rightarrow> Gt
    | VImpl _ _ \<Rightarrow> Gt
    | VIff_sv _ _ \<Rightarrow> Gt
    | VIff_vs vp1' sp2' \<Rightarrow> (case comparator_vproof compa vp1 vp1' of Eq \<Rightarrow> comparator_sproof compa sp2 sp2' | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VOnce_le i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR _ \<Rightarrow> Gt
    | VImpl _ _ \<Rightarrow> Gt
    | VIff_sv _ _ \<Rightarrow> Gt
    | VIff_vs _ _ \<Rightarrow> Gt
    | VOnce_le i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VOnce_never i t vps) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR _ \<Rightarrow> Gt
    | VImpl _ _ \<Rightarrow> Gt
    | VIff_sv _ _ \<Rightarrow> Gt
    | VIff_vs _ _ \<Rightarrow> Gt
    | VOnce_le _ \<Rightarrow> Gt
    | VOnce_never i' t' vps' \<Rightarrow> (case comparator_of i i' of 
                                   Eq \<Rightarrow> (case comparator_of t t' of Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_vproof compa) vps) vps' | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
                                 | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VSince i vp1 vp2s) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR _ \<Rightarrow> Gt
    | VImpl _ _ \<Rightarrow> Gt
    | VIff_sv _ _ \<Rightarrow> Gt
    | VIff_vs _ _ \<Rightarrow> Gt
    | VOnce_le _ \<Rightarrow> Gt
    | VOnce_never _ _ _ \<Rightarrow> Gt
    | VSince i' vp1' vp2s' \<Rightarrow> (case comparator_of i i' of 
                                Eq \<Rightarrow> (case comparator_vproof compa vp1 vp1' of
                                        Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_vproof compa) vp2s) vp2s'
                                      | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
                              | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VUntil i vp2s vp1) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR _ \<Rightarrow> Gt
    | VImpl _ _ \<Rightarrow> Gt
    | VIff_sv _ _ \<Rightarrow> Gt
    | VIff_vs _ _ \<Rightarrow> Gt
    | VOnce_le _ \<Rightarrow> Gt
    | VOnce_never _ _ _ \<Rightarrow> Gt
    | VSince _ _ _ \<Rightarrow> Gt
    | VUntil i' vp2s' vp1' \<Rightarrow> (case comparator_of i i' of 
                                Eq \<Rightarrow> (case comparator_vproof compa vp1 vp1' of
                                        Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_vproof compa) vp2s) vp2s'
                                      | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
                              | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VSince_never i t vp2s) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR _ \<Rightarrow> Gt
    | VImpl _ _ \<Rightarrow> Gt
    | VIff_sv _ _ \<Rightarrow> Gt
    | VIff_vs _ _ \<Rightarrow> Gt
    | VOnce_le _ \<Rightarrow> Gt
    | VOnce_never _ _ _ \<Rightarrow> Gt
    | VSince _ _ _ \<Rightarrow> Gt
    | VUntil _ _ _ \<Rightarrow> Gt
    | VSince_never i' t' vp2s' \<Rightarrow> (case comparator_of i i' of 
                                   Eq \<Rightarrow> (case comparator_of t t' of Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_vproof compa) vp2s) vp2s' | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
                                  | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VUntil_never i t vp2s) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR _ \<Rightarrow> Gt
    | VImpl _ _ \<Rightarrow> Gt
    | VIff_sv _ _ \<Rightarrow> Gt
    | VIff_vs _ _ \<Rightarrow> Gt
    | VOnce_le _ \<Rightarrow> Gt
    | VOnce_never _ _ _ \<Rightarrow> Gt
    | VSince _ _ _ \<Rightarrow> Gt
    | VUntil _ _ _ \<Rightarrow> Gt
    | VSince_never _ _ _ \<Rightarrow> Gt
    | VUntil_never i' t' vp2s' \<Rightarrow> (case comparator_of i i' of 
                                   Eq \<Rightarrow> (case comparator_of t t' of Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_vproof compa) vp2s) vp2s' | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
                                 | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VSince_le i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR _ \<Rightarrow> Gt
    | VImpl _ _ \<Rightarrow> Gt
    | VIff_sv _ _ \<Rightarrow> Gt
    | VIff_vs _ _ \<Rightarrow> Gt
    | VOnce_le _ \<Rightarrow> Gt
    | VOnce_never _ _ _ \<Rightarrow> Gt
    | VSince _ _ _ \<Rightarrow> Gt
    | VUntil _ _ _ \<Rightarrow> Gt
    | VSince_never _ _ _ \<Rightarrow> Gt
    | VUntil_never _ _ _  \<Rightarrow> Gt
    | VSince_le i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VNext vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR _ \<Rightarrow> Gt
    | VImpl _ _ \<Rightarrow> Gt
    | VIff_sv _ _ \<Rightarrow> Gt
    | VIff_vs _ _ \<Rightarrow> Gt
    | VOnce_le _ \<Rightarrow> Gt
    | VOnce_never _ _ _ \<Rightarrow> Gt
    | VSince _ _ _ \<Rightarrow> Gt
    | VUntil _ _ _ \<Rightarrow> Gt
    | VSince_never _ _ _ \<Rightarrow> Gt
    | VUntil_never _ _ _  \<Rightarrow> Gt
    | VSince_le _ \<Rightarrow> Gt
    | VNext vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VNext_ge i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR _ \<Rightarrow> Gt
    | VImpl _ _ \<Rightarrow> Gt
    | VIff_sv _ _ \<Rightarrow> Gt
    | VIff_vs _ _ \<Rightarrow> Gt
    | VOnce_le _ \<Rightarrow> Gt
    | VOnce_never _ _ _ \<Rightarrow> Gt
    | VSince _ _ _ \<Rightarrow> Gt
    | VUntil _ _ _ \<Rightarrow> Gt
    | VSince_never _ _ _ \<Rightarrow> Gt
    | VUntil_never _ _ _  \<Rightarrow> Gt
    | VSince_le _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNext_ge i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VNext_le i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR _ \<Rightarrow> Gt
    | VImpl _ _ \<Rightarrow> Gt
    | VIff_sv _ _ \<Rightarrow> Gt
    | VIff_vs _ _ \<Rightarrow> Gt
    | VOnce_le _ \<Rightarrow> Gt
    | VOnce_never _ _ _ \<Rightarrow> Gt
    | VSince _ _ _ \<Rightarrow> Gt
    | VUntil _ _ _ \<Rightarrow> Gt
    | VSince_never _ _ _ \<Rightarrow> Gt
    | VUntil_never _ _ _  \<Rightarrow> Gt
    | VSince_le _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNext_ge _ \<Rightarrow> Gt
    | VNext_le i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VPrev vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR _ \<Rightarrow> Gt
    | VImpl _ _ \<Rightarrow> Gt
    | VIff_sv _ _ \<Rightarrow> Gt
    | VIff_vs _ _ \<Rightarrow> Gt
    | VOnce_le _ \<Rightarrow> Gt
    | VOnce_never _ _ _ \<Rightarrow> Gt
    | VSince _ _ _ \<Rightarrow> Gt
    | VUntil _ _ _ \<Rightarrow> Gt
    | VSince_never _ _ _ \<Rightarrow> Gt
    | VUntil_never _ _ _  \<Rightarrow> Gt
    | VSince_le _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNext_ge _ \<Rightarrow> Gt
    | VNext_le _ \<Rightarrow> Gt
    | VPrev vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VPrev_ge i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR _ \<Rightarrow> Gt
    | VImpl _ _ \<Rightarrow> Gt
    | VIff_sv _ _ \<Rightarrow> Gt
    | VIff_vs _ _ \<Rightarrow> Gt
    | VOnce_le _ \<Rightarrow> Gt
    | VOnce_never _ _ _ \<Rightarrow> Gt
    | VSince _ _ _ \<Rightarrow> Gt
    | VUntil _ _ _ \<Rightarrow> Gt
    | VSince_never _ _ _ \<Rightarrow> Gt
    | VUntil_never _ _ _  \<Rightarrow> Gt
    | VSince_le _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNext_ge _ \<Rightarrow> Gt
    | VNext_le _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrev_ge i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VPrev_le i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR _ \<Rightarrow> Gt
    | VImpl _ _ \<Rightarrow> Gt
    | VIff_sv _ _ \<Rightarrow> Gt
    | VIff_vs _ _ \<Rightarrow> Gt
    | VOnce_le _ \<Rightarrow> Gt
    | VOnce_never _ _ _ \<Rightarrow> Gt
    | VSince _ _ _ \<Rightarrow> Gt
    | VUntil _ _ _ \<Rightarrow> Gt
    | VSince_never _ _ _ \<Rightarrow> Gt
    | VUntil_never _ _ _  \<Rightarrow> Gt
    | VSince_le _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNext_ge _ \<Rightarrow> Gt
    | VNext_le _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrev_ge _ \<Rightarrow> Gt
    | VPrev_le i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa VPrev_zero rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VAtm _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VDisj _ _ \<Rightarrow> Gt
    | VConjL _ \<Rightarrow> Gt
    | VConjR _ \<Rightarrow> Gt
    | VImpl _ _ \<Rightarrow> Gt
    | VIff_sv _ _ \<Rightarrow> Gt
    | VIff_vs _ _ \<Rightarrow> Gt
    | VOnce_le _ \<Rightarrow> Gt
    | VOnce_never _ _ _ \<Rightarrow> Gt
    | VSince _ _ _ \<Rightarrow> Gt
    | VUntil _ _ _ \<Rightarrow> Gt
    | VSince_never _ _ _ \<Rightarrow> Gt
    | VUntil_never _ _ _  \<Rightarrow> Gt
    | VSince_le _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNext_ge _ \<Rightarrow> Gt
    | VNext_le _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrev_ge _ \<Rightarrow> Gt
    | VPrev_le _ \<Rightarrow> Gt
    | VPrev_zero \<Rightarrow> Eq)"

definition "ccompare_sproof = (case ID ccompare of None \<Rightarrow> None | Some comp_'a \<Rightarrow> Some (comparator_sproof comp_'a))"
definition "ccompare_vproof = (case ID ccompare of None \<Rightarrow> None | Some comp_'a \<Rightarrow> Some (comparator_vproof comp_'a))"

lemma comparator_list'_map[simp]: "comparator_list' (\<lambda>f x. f x) (map f xs) ys = comparator_list f xs ys"
  by (induct xs ys rule: comparator_list'.induct[where compa = f]) (auto split: order.splits)

lemma eq_Eq_comparator_proof:
  assumes "ID ccompare = Some compa"
  shows "comparator_sproof compa sp sp' = Eq \<longleftrightarrow> sp = sp'"
    "comparator_vproof compa vp vp' = Eq \<longleftrightarrow> vp = vp'"
   apply (induct sp and vp arbitrary: sp' and vp')
                      apply (simp_all add:  comparator_list_pointwise(1)[unfolded peq_comp_def, rule_format] comparator_of_def
      comparator.eq_Eq_conv[OF ID_ccompare'[OF assms]]
      comparator.Lt_lt_conv[OF ID_ccompare'[OF assms]]
      comparator.Gt_lt_conv[OF ID_ccompare'[OF assms]]
      split: sproof.splits vproof.splits order.splits if_splits)
              apply (meson ID_ccompare' anti_sym assms)
             apply (metis order.simps(2) order.simps(4))
            apply (metis order.simps(2) order.simps(4))
           apply (metis order.simps(2) order.simps(4))
          apply (metis order.simps(2) order.simps(4))
         apply (metis order.simps(2) order.simps(4))
        apply (meson ID_ccompare' anti_sym assms)
       apply (metis order.simps(2) order.simps(4))
      apply (metis order.simps(2) order.simps(4))
     apply (metis order.simps(2) order.simps(4))
    apply (metis order.simps(2) order.simps(4))
   apply (metis order.simps(2) order.simps(4))
  apply (metis order.simps(2) order.simps(4))
  done

lemma trans_order_equal[simp]:
  "trans_order Eq b b"
  "trans_order b Eq b"
  by (intro trans_orderI, auto)+

declare trans_order_different[simp]

lemma invert_order_comparator_proof:
  assumes "ID ccompare = Some compa"
  shows "invert_order (comparator_sproof compa sp sp') = comparator_sproof compa sp' sp"
    "invert_order (comparator_vproof compa vp vp') = comparator_vproof compa vp' vp"
   apply (induct sp and vp arbitrary: sp' and vp')
                      apply (simp_all add: comparator_of_def comparator_list_pointwise(2)[unfolded psym_comp_def, rule_format] split: sproof.splits vproof.splits order.splits)
              apply (metis comparator.eq_Eq_conv comparator.nGt_le_conv comparator.nLt_le_conv order.simps(6) ID_ccompare' assms)
             apply (metis invert_order.simps order.simps(6))
            apply (metis invert_order.simps order.simps(6))
           apply (metis invert_order.simps order.simps(6))
          apply (metis invert_order.simps order.simps(6))
         apply (metis invert_order.simps order.simps(6))
        apply (metis comparator.eq_Eq_conv comparator.nGt_le_conv comparator.nLt_le_conv order.simps(6) ID_ccompare' assms)
       apply (metis invert_order.simps order.simps(6))
      apply (metis invert_order.simps order.simps(6))
     apply (metis invert_order.simps order.simps(6))
    apply (metis invert_order.simps order.simps(6))
   apply (metis invert_order.simps order.simps(6))
  apply (metis invert_order.simps order.simps(6))
  done

lemma trans_comparator_proof:
  assumes "ID ccompare = Some compa"
  shows "trans_order (comparator_sproof compa sp sp') (comparator_sproof compa sp' sp'') (comparator_sproof compa sp sp'')"
    "trans_order (comparator_vproof compa vp vp') (comparator_vproof compa vp' vp'') (comparator_vproof compa vp vp'')"
proof (induct sp and vp arbitrary: sp' sp'' and vp' vp'')
  case (STT x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (SAtm x1 x2)
  then show ?case
    apply (simp add: comparator_of_def comparator.comp_same[OF ID_ccompare'[OF assms]]
        comparator.eq_Eq_conv[OF ID_ccompare'[OF assms]] split: sproof.splits vproof.splits order.splits if_splits)
    apply safe
                        apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
                        apply (metis order.distinct(5))
                        apply (metis order.distinct(5))
                        apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
                        apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
                        apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
                        apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
                        apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
                        apply (metis order.distinct(5))
                       apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
                      apply (metis order.distinct(5))
                     apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
                    apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
                   apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
                  apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
                 apply (metis order.distinct(5))
                apply (metis order.distinct(5))
               apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
              apply (metis order.distinct(5))
             apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
            apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
           apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
          apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
         apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
        apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
       apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
      apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
     apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
    apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
    done
next
  case (SNeg x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (SDisjL x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (SDisjR x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (SConj x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
    apply (smt (verit, del_insts) order.distinct(3) order.simps(2) trans_order_def)
    done
next
  case (SImplR x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (SImplL x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (SIff_ss x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
    apply (smt (verit, del_insts) order.distinct(3) order.simps(2) trans_order_def)
    done
next
  case (SIff_vv x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
    apply (smt (verit, del_insts) order.distinct(3) order.simps(2) trans_order_def)
    done
next
  case (SOnce x1 x2)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (SSince x1 x2)
  then show ?case
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_sproof compa"]
    apply (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
    apply (smt (verit, del_insts) order.simps(2) order.simps(4) trans_order_def)
    done
next
  case (SUntil x1 x2)
  then show ?case
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_sproof compa"]
    apply (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
    apply (smt (verit, del_insts) order.simps(2) order.simps(4) trans_order_def)
    done
next
  case (SNext x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (SPrev x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (VFF x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (VAtm x1 x2)
  then show ?case
    apply (simp add: comparator_of_def comparator.comp_same[OF ID_ccompare'[OF assms]]
        comparator.eq_Eq_conv[OF ID_ccompare'[OF assms]] split: sproof.splits vproof.splits order.splits if_splits)
    apply safe
                        apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
                        apply (metis order.distinct(5))
                        apply (metis order.distinct(5))
                        apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
                        apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
                        apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
                        apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
                        apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
                        apply (metis order.distinct(5))
                       apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
                      apply (metis order.distinct(5))
                     apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
                    apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
                   apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
                  apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
                 apply (metis order.distinct(5))
                apply (metis order.distinct(5))
               apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
              apply (metis order.distinct(5))
             apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
            apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
           apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
          apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
         apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
        apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
       apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
      apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
     apply (metis comparator.sym invert_order.simps(1) order.distinct(5) ID_ccompare' assms)
    apply (metis comparator.comp_trans order.distinct(5) ID_ccompare' assms)
    done
next
  case (VNeg x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (VDisj x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
    apply (smt (verit, del_insts) order.simps(2) order.simps(4) trans_order_def)
    done
next
  case (VConjL x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (VConjR x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (VImpl x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
    apply (smt (verit, del_insts) order.simps(2) order.simps(4) trans_order_def)
    done
next
  case (VIff_sv x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
    apply (smt (verit, del_insts) order.simps(2) order.simps(4) trans_order_def)
    done
next
  case (VIff_vs x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
    apply (smt (verit, del_insts) order.simps(2) order.simps(4) trans_order_def)
    done
next
  case (VOnce_le x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (VOnce_never x1 x2 x3)
  then show ?case
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (VSince x1 x2 x3)
  then show ?case
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_vproof compa"]
    apply (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
    apply (smt (verit, del_insts) order.simps(2) order.simps(4) trans_order_def)
    done
next
  case (VUntil x1 x2 x3)
  then show ?case
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_vproof compa"]
    apply (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
    apply (smt (verit, del_insts) order.simps(2) order.simps(4) trans_order_def)
    done
next
  case (VSince_never x1 x2 x3)
  then show ?case
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (VUntil_never x1 x2 x3)
  then show ?case
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (VSince_le x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (VNext x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (VNext_ge x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (VNext_le x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (VPrev x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (VPrev_ge x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case (VPrev_le x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
next
  case VPrev_zero
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits vproof.splits order.splits if_splits)
qed

instance
   apply standard
   apply (force simp add: ccompare_sproof_def ccompare_vproof_def comparator_def
      eq_Eq_comparator_proof invert_order_comparator_proof intro: trans_comparator_proof[THEN trans_orderD(2)] split: option.splits)+
  done

end

derive (eq) ceq sproof
derive (rbt) set_impl sproof
derive (eq) ceq vproof
derive (rbt) set_impl vproof

lemma neq_Nil_conv_snoc: "(xs \<noteq> []) = (\<exists>y ys. xs = ys @ [y])"
  by (induct xs) auto

lemma size_last_estimation[termination_simp]: "xs \<noteq> [] \<Longrightarrow> size (last xs) < size_list size xs"
  by (induct xs) auto
    (*
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
*)

(*Updated definitions for temporal operators; added constraint violations*)
fun s_at and v_at where
  "s_at (STT n) = n"
| "s_at (SAtm _ n) = n"
| "s_at (SNeg vphi) = v_at vphi"
| "s_at (SDisjL sphi) = s_at sphi"
| "s_at (SDisjR spsi) = s_at spsi"
| "s_at (SConj sphi spsi) = s_at sphi"
| "s_at (SImplL vphi) = v_at vphi"
| "s_at (SImplR spsi) = s_at spsi"
| "s_at (SIff_ss sphi spsi) = s_at sphi"
| "s_at (SIff_vv vphi vpsi) = v_at vphi"
| "s_at (SNext sphi) = s_at sphi - 1"
| "s_at (SPrev sphi) = s_at sphi + 1"
| "s_at (SOnce n sphi) = n"
| "s_at (SSince spsi sphis) = (case sphis of [] \<Rightarrow> s_at spsi | _ \<Rightarrow> s_at (last sphis))"
| "s_at (SUntil sphis spsi) = (case sphis of [] \<Rightarrow> s_at spsi | x # _ \<Rightarrow> s_at x)"
  (*
| "s_at (SMatchP p) = snd (rs_at s_at p)"
| "s_at (SMatchF p) = fst (rs_at s_at p)"
*)
| "v_at (VFF n) = n"
| "v_at (VAtm _ n) = n"
| "v_at (VNeg sphi) = s_at sphi"
| "v_at (VDisj vphi vpsi) = v_at vphi"
| "v_at (VConjL vphi) = v_at vphi"
| "v_at (VConjR vpsi) = v_at vpsi"
| "v_at (VImpl sphi vpsi) = s_at sphi"
| "v_at (VIff_sv sphi vpsi) = s_at sphi"
| "v_at (VIff_vs vphi spsi) = v_at vphi"
| "v_at (VNext vphi) = v_at vphi - 1"
| "v_at (VNext_ge n) = n"
| "v_at (VNext_le n) = n"
| "v_at (VPrev vphi) = v_at vphi + 1"
| "v_at (VPrev_ge n) = n"
| "v_at (VPrev_le n) = n"
| "v_at (VPrev_zero) = 0"
| "v_at (VOnce_le n) = n"
| "v_at (VOnce_never n li vphi) = n"
| "v_at (VSince n vpsi vphis) = n"
| "v_at (VSince_le n) = n"
| "v_at (VUntil n vphis vpsi) = n"
| "v_at (VSince_never n li vpsis) = n"
| "v_at (VUntil_never n hi vpsis) = n"
  (*
| "v_at (VMatchP n ps) = n"
| "v_at (VMatchP_le n) = n"
| "v_at (VMatchF n ps) = n"
*)
context fixes rho :: "'a trace"
begin

fun s_check and v_check where
  "s_check f p = (case (f, p) of
    (TT, STT i) \<Rightarrow> True
  | (Atom a, SAtm b i) \<Rightarrow> (a = b \<and> a \<in> (\<Gamma> rho i))
  | (Neg phi, SNeg sphi) \<Rightarrow> v_check phi sphi
  | (Disj phi psi, SDisjL sphi) \<Rightarrow> s_check phi sphi
  | (Disj phi psi, SDisjR spsi) \<Rightarrow> s_check psi spsi
  | (Conj phi psi, SConj sphi spsi) \<Rightarrow> s_check phi sphi \<and> s_check psi spsi \<and> s_at sphi = s_at spsi
  | (Impl phi psi, SImplL vphi) \<Rightarrow> v_check phi vphi
  | (Impl phi psi, SImplR spsi) \<Rightarrow> s_check psi spsi
  | (Iff phi psi, SIff_ss sphi spsi) \<Rightarrow> s_check phi sphi \<and> s_check psi spsi \<and> s_at sphi = s_at spsi
  | (Iff phi psi, SIff_vv vphi vpsi) \<Rightarrow> v_check phi vphi \<and> v_check psi vpsi \<and> v_at vphi = v_at vpsi
  | (Once I phi, SOnce i sphi) \<Rightarrow> 
    (let j = s_at sphi
    in j \<le> i \<and> mem (\<tau> rho i - \<tau> rho j) I \<and> s_check phi sphi)
  | (Since phi I psi, SSince spsi sphis) \<Rightarrow>
    (let i = s_at (SSince spsi sphis); j = s_at spsi
    in j \<le> i \<and> mem (\<tau> rho i - \<tau> rho j) I \<and> map s_at sphis = [Suc j ..< Suc i] \<and> s_check psi spsi
    \<and> (\<forall>sphi \<in> set sphis. s_check phi sphi))
  | (Until phi I psi, SUntil sphis spsi) \<Rightarrow>
    (let i = s_at (SUntil sphis spsi); j = s_at spsi
    in j \<ge> i \<and> mem (\<tau> rho j - \<tau> rho i) I \<and> map s_at sphis = [i ..< j] \<and> s_check psi spsi
    \<and> (\<forall>sphi \<in> set sphis. s_check phi sphi))
  | (Next I phi, SNext sphi) \<Rightarrow>
    (let j = s_at sphi; i = s_at (SNext sphi)
    in j = Suc i \<and> mem (\<Delta> rho j) I \<and> s_check phi sphi)
  | (Prev I phi, SPrev sphi) \<Rightarrow>
    (let j = s_at sphi; i = s_at (SPrev sphi)
    in i = Suc j \<and> mem (\<Delta> rho i) I \<and> s_check phi sphi)
  | (_, _) \<Rightarrow> False)"
  (*
| (MatchP I r, SMatchP sp) \<Rightarrow>
    (let rt = rs_at s_at sp
    in fst rt \<le> snd rt \<and> mem (delta rho (snd rt) (fst rt)) I \<and> rs_check s_check s_at r sp)
  | (MatchF I r, SMatchF sp) \<Rightarrow>
    (let rt = rs_at s_at sp
    in fst rt \<le> snd rt \<and> mem (delta rho (snd rt) (fst rt)) I \<and> rs_check s_check s_at r sp)
*)
| "v_check f p = (case (f, p) of
    (FF, VFF i) \<Rightarrow> True
  | (Atom a, VAtm b i) \<Rightarrow> (a = b \<and> a \<notin> (\<Gamma> rho i))
  | (Neg phi, VNeg sphi) \<Rightarrow> s_check phi sphi
  | (Disj phi psi, VDisj vphi vpsi) \<Rightarrow> v_check phi vphi \<and> v_check psi vpsi \<and> v_at vphi = v_at vpsi
  | (Conj phi psi, VConjL vphi) \<Rightarrow> v_check phi vphi
  | (Conj phi psi, VConjR vpsi) \<Rightarrow> v_check psi vpsi
  | (Impl phi psi, VImpl sphi vpsi) \<Rightarrow> s_check phi sphi \<and> v_check psi vpsi \<and> s_at sphi = v_at vpsi
  | (Iff phi psi, VIff_sv sphi vpsi) \<Rightarrow> s_check phi sphi \<and> v_check psi vpsi \<and> s_at sphi = v_at vpsi
  | (Iff phi psi, VIff_vs vphi spsi) \<Rightarrow> v_check phi vphi \<and> s_check psi spsi \<and> v_at vphi = s_at spsi
  | (Once I phi, VOnce_le i) \<Rightarrow> 
    \<tau> rho i < \<tau> rho 0 + left I
  | (Once I phi, VOnce_never i li vphis) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> ETP rho (\<tau> rho i - n))
    \<and> \<tau> rho 0 + left I \<le> \<tau> rho i
    \<and> map v_at vphis = [li ..< Suc (l rho i I)]
    \<and> (\<forall>vphi \<in> set vphis. v_check phi vphi))
  | (Since phi I psi, VSince_le i) \<Rightarrow>
    \<tau> rho i < \<tau> rho 0 + left I
  | (Since phi I psi, VSince i vphi vpsis) \<Rightarrow>
    (let j = v_at vphi
    in (case right I of \<infinity> \<Rightarrow> True | enat n \<Rightarrow> ETP rho (\<tau> rho i - n) \<le> j) \<and> j \<le> i
    \<and> \<tau> rho 0 + left I \<le> \<tau> rho i
    \<and> map v_at vpsis = [j ..< Suc (l rho i I)] \<and> v_check phi vphi
    \<and> (\<forall>vpsi \<in> set vpsis. v_check psi vpsi))
  | (Until phi I psi, VUntil i vpsis vphi) \<Rightarrow>
    (let j = v_at vphi
    in (case right I of \<infinity> \<Rightarrow> True | enat n \<Rightarrow> j \<le> LTP rho (\<tau> rho i + n)) \<and> i \<le> j
    \<and> map v_at vpsis = [(lu rho i I) ..< Suc j] \<and> v_check phi vphi
    \<and> (\<forall>vpsi \<in> set vpsis. v_check psi vpsi))
  | (Since phi I psi, VSince_never i li vpsis) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> ETP rho (\<tau> rho i - n))
    \<and> \<tau> rho 0 + left I \<le> \<tau> rho i
    \<and> map v_at vpsis = [li ..< Suc (l rho i I)]
    \<and> (\<forall>vpsi \<in> set vpsis. v_check psi vpsi))
  | (Until phi I psi, VUntil_never i hi vpsis) \<Rightarrow>
    (hi = (case right I of enat n \<Rightarrow> LTP rho (\<tau> rho i + n)) \<and> right I \<noteq> \<infinity>
    \<and> map v_at vpsis = [(lu rho i I) ..< Suc hi]
    \<and> (\<forall>vpsi \<in> set vpsis. v_check psi vpsi))
  | (Next I phi, VNext vphi) \<Rightarrow>
    (let j = v_at vphi; i = v_at (VNext vphi)
    in j = Suc i \<and> v_check phi vphi)
  | (Next I phi, VNext_ge i) \<Rightarrow>
    enat (\<Delta> rho (Suc i)) > right I
  | (Next I phi, VNext_le i) \<Rightarrow>
    \<Delta> rho (Suc i) < left I
  | (Prev I phi, VPrev vphi) \<Rightarrow>
    (let j = v_at vphi; i = v_at (VPrev vphi)
    in i = Suc j \<and> v_check phi vphi)
  | (Prev I phi, VPrev_ge i) \<Rightarrow>
    i > 0 \<and> enat (\<Delta> rho i) > right I
  | (Prev I phi, VPrev_le i) \<Rightarrow>
    i > 0 \<and> \<Delta> rho i < left I
  | (Prev I phi, VPrev_zero) \<Rightarrow>
    v_at (VPrev_zero :: 'a vproof) = 0
  | (_, _) \<Rightarrow> False)"
  (*
  | (MatchP I r, VMatchP_le i) \<Rightarrow>
    \<tau> rho i < \<tau> rho 0 + left I
  | (MatchP I r, VMatchP i vps) \<Rightarrow> 
    (let j = ETP rho (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> (\<tau> rho i - n))
    in \<tau> rho i \<ge> \<tau> rho 0 + left I \<and>  map (fst \<circ> rv_at v_at) vps = [j ..< Suc (l rho i I)]
    \<and> (\<forall>vp \<in> set vps. rv_check v_check v_at r vp \<and> snd (rv_at v_at vp) = i))
  | (MatchF I r, VMatchF i vps) \<Rightarrow> 
    (let j = LTP rho (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> (\<tau> rho i + n))
    in map (snd \<circ> rv_at v_at) vps = [(lu rho i I) ..< Suc j]
    \<and> (\<forall>vp \<in> set vps. rv_check v_check v_at r vp \<and> fst (rv_at v_at vp) = i))
*)

declare s_check.simps[simp del] v_check.simps[simp del]
simps_of_case s_check_simps[simp, code]: s_check.simps[unfolded prod.case] (splits: mtl.split sproof.split)
simps_of_case v_check_simps[simp, code]: v_check.simps[unfolded prod.case] (splits: mtl.split sproof.split)

lemma Cons_eq_upt_conv: "x # xs = [m ..< n] \<longleftrightarrow> m < n \<and> x = m \<and> xs = [Suc m ..< n]"
  by (induct n arbitrary: xs) (force simp: Cons_eq_append_conv)+

lemma map_setE[elim_format]: "map f xs = ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> \<exists>x\<in>set xs. f x = y"
  by (induct xs arbitrary: ys) auto

(*
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
*)

lemma check_sound:
  "s_check phi sphi \<Longrightarrow> SAT rho (s_at sphi) phi"
  "v_check phi vphi \<Longrightarrow> VIO rho (v_at vphi) phi"
proof (induction sphi and vphi arbitrary: phi and phi)
  case STT
  then show ?case by (cases phi) (auto intro: SAT_VIO.STT)
next
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
  case SImplR
  then show ?case by (cases phi) (auto intro: SAT_VIO.SImplR)
next
  case SImplL
  then show ?case by (cases phi) (auto intro: SAT_VIO.SImplL)
next
  case SIff_ss
  then show ?case by (cases phi) (auto intro: SAT_VIO.SIff_ss)
next
  case SIff_vv
  then show ?case by (cases phi) (auto intro: SAT_VIO.SIff_vv)
next
  case (SSince spsi sphis)
  then show ?case
  proof (cases phi)
    case (Since phi I psi)
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
  case (SOnce i sphi)
  then show ?case
  proof (cases phi)
    case (Once I phi)
    show ?thesis
      using SOnce
      unfolding Once
      apply (intro SAT_VIO.SOnce[of "s_at sphi"])
        apply (auto simp: Let_def le_Suc_eq Cons_eq_append_conv Cons_eq_upt_conv 
          split: if_splits list.splits)
      done
  qed auto
next
  case (SUntil sphis spsi)
  then show ?case
  proof (cases phi)
    case (Until phi I psi)
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
  case (SNext sphi)
  then show ?case by (cases phi) (auto simp add: Let_def SAT_VIO.SNext)
next
  case (SPrev sphi)
  then show ?case by (cases phi) (auto simp add: Let_def SAT_VIO.SPrev)
next
  case VFF
  then show ?case by (cases phi) (auto intro: SAT_VIO.VFF)
next
  case VAtm
  then show ?case by (cases phi) (auto intro: SAT_VIO.VP SAT_VIO.VPrev_zero)
next
  case VNeg
  then show ?case by (cases phi) (auto intro: SAT_VIO.VNeg SAT_VIO.VPrev_zero)
next
  case VDisj
  then show ?case by (cases phi) (auto intro: SAT_VIO.VDisj SAT_VIO.VPrev_zero)
next
  case VConjL
  then show ?case by (cases phi) (auto intro: SAT_VIO.VConjL)
next
  case VConjR
  then show ?case by (cases phi) (auto intro: SAT_VIO.VConjR)
next
  case VImpl
  then show ?case by (cases phi) (auto intro: SAT_VIO.VImpl)
next
  case VIff_sv
  then show ?case by (cases phi) (auto intro: SAT_VIO.VIff_sv)
next
  case VIff_vs
  then show ?case by (cases phi) (auto intro: SAT_VIO.VIff_vs)
next
  case VOnce_le
  then show ?case by (cases phi) (auto intro: SAT_VIO.VOnce_le)
next
  case (VOnce_never i li vphis)
  then show ?case
  proof (cases phi)
    case (Once I phi)
    {fix k
      define j where j_def: "j \<equiv> case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> ETP rho (\<tau> rho i - n)"
      assume k_def: "k \<ge> j \<and> k \<le> i \<and> k \<le> LTP rho (\<tau> rho i - left I)"
      from VOnce_never Once j_def have map: "set (map v_at vphis) = set [j ..< Suc (l rho i I)]"
        by (auto simp: Let_def)
      then have kset: "k \<in> set ([j ..< Suc (l rho i I)])" using j_def k_def by auto
      then obtain x where x: "x \<in> set vphis"  "v_at x = k" using k_def map
        apply auto
         apply (metis imageE insertI1)
        by (metis List.List.list.set_map imageE kset map)
      then have "VIO rho k phi" using VOnce_never unfolding Once
        by (auto simp: Let_def)
    } note * = this
    show ?thesis
      using VOnce_never
      unfolding Once
      apply (auto simp: Let_def intro!: SAT_VIO.VOnce_never)
      using VOnce_never.IH *  by (auto split: if_splits)
  qed (auto intro: SAT_VIO.intros)
next
  case VNext
  then show ?case by (cases phi) (auto intro: SAT_VIO.VNext)
next
  case VNext_ge
  then show ?case by (cases phi) (auto intro: SAT_VIO.VNext_ge)
next
  case VNext_le
  then show ?case by (cases phi) (auto intro: SAT_VIO.VNext_le)
next
  case VPrev
  then show ?case by (cases phi) (auto intro: SAT_VIO.VPrev)
next
  case VPrev_ge
  then show ?case by (cases phi) (auto intro: SAT_VIO.VPrev_ge)
next
  case VPrev_le
  then show ?case by (cases phi) (auto intro: SAT_VIO.VPrev_le)
next
  case VPrev_zero
  then show ?case by (cases phi) (auto intro: SAT_VIO.VPrev_zero)
next
  case VSince_le
  then show ?case by (cases phi) (auto intro: SAT_VIO.VSince_le)
next
  case (VSince i vphi vpsi)
  then show ?case
  proof (cases phi)
    case (Since phi I psi)
    {fix k
      assume k_def: "k \<ge> v_at vphi \<and> k \<le> i \<and> k \<le> LTP rho (\<tau> rho i - left I)"
      from VSince Since have map: "set (map v_at vpsi) = set ([(v_at vphi) ..< Suc (l rho i I)])"
        by (auto simp: Let_def)
      then have kset: "k \<in> set ([(v_at vphi) ..< Suc (l rho i I)])" using k_def by auto
      then obtain x where x: "x \<in> set vpsi" "v_at x = k" using k_def map kset
        apply auto
         apply (metis imageE insertI1)
        by (metis List.List.list.set_map imageE kset map)
      then have "VIO rho k psi" using VSince unfolding Since
        by (auto simp: Let_def)
    } note * = this
    show ?thesis
      using VSince
      unfolding Since
      apply (auto simp: Let_def split: enat.splits if_splits
          intro!: SAT_VIO.VSince[of _ i "v_at vphi"])
      using VSince.IH * by (auto split: if_splits)
  qed (auto intro: SAT_VIO.intros)
next
  case (VUntil i vpsis vphi)
  then show ?case
  proof (cases phi)
    case (Until phi I psi)
    {fix k
      assume k_def: "k \<le> v_at vphi \<and> k \<ge> i \<and> k \<ge> ETP rho (\<tau> rho i + left I)"
      from VUntil Until have map: "set (map v_at vpsis) = set [(lu rho i I) ..< Suc (v_at vphi)]"
        by (auto simp: Let_def)
      then have kset: "k \<in> set ([(lu rho i I) ..< Suc (v_at vphi)])" using k_def by auto
      then obtain x where x: "x \<in> set vpsis" "v_at x = k" using k_def map kset
        apply auto
         apply (metis imageE insertI1)
        by (metis List.List.list.set_map imageE kset map)
      then have "VIO rho k psi" using VUntil unfolding Until
        by (auto simp: Let_def)
    } note * = this
    then show ?thesis
      using VUntil
      unfolding Until
      by (auto simp: Let_def split: enat.splits if_splits
          intro!: SAT_VIO.VUntil)
  qed(auto intro: SAT_VIO.intros)
next
  case (VSince_never i li vpsis)
  then show ?case
  proof (cases phi)
    case (Since phi I psi)
    {fix k
      define j where j_def: "j \<equiv> case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> ETP rho (\<tau> rho i - n)"
      assume k_def: "k \<ge> j \<and> k \<le> i \<and> k \<le> LTP rho (\<tau> rho i - left I)"
      from VSince_never Since j_def have map: "set (map v_at vpsis) = set [j ..< Suc (l rho i I)]"
        by (auto simp: Let_def)
      then have kset: "k \<in> set ([j ..< Suc (l rho i I)])" using j_def k_def by auto
      then obtain x where x: "x \<in> set vpsis"  "v_at x = k" using k_def map
        apply auto
         apply (metis imageE insertI1)
        by (metis List.List.list.set_map imageE kset map)
      then have "VIO rho k psi" using VSince_never unfolding Since
        by (auto simp: Let_def)
    } note * = this
    show ?thesis
      using VSince_never
      unfolding Since
      apply (auto simp: Let_def intro!: SAT_VIO.VSince_never)
      using VSince_never.IH *  by (auto split: if_splits)
  qed (auto intro: SAT_VIO.intros)
next
  case (VUntil_never i hi vpsis)
  then show ?case
  proof (cases phi)
    case (Until phi I psi)
    obtain n where n_def: "right I = enat n"
      using VUntil_never
      by (auto simp: Until split: enat.splits)
    {fix k  
      define j where j_def: "j \<equiv> LTP rho (\<tau> rho i + n)"
      assume k_def: "k \<le> j \<and> k \<ge> i \<and> k \<ge> ETP rho (\<tau> rho i + left I)"
      from VUntil_never Until j_def have map: "set (map v_at vpsis) = set [(lu rho i I) ..< Suc j]"
        by (auto simp: Let_def n_def)
      then have kset: "k \<in> set ([(lu rho i I) ..< Suc j])" using k_def j_def by auto
      then obtain x where x: "x \<in> set vpsis" "v_at x = k" using k_def map
        apply auto
         apply (metis imageE insertI1)
        by (metis List.List.list.set_map imageE kset map)
      then have "VIO rho k psi" using VUntil_never unfolding Until
        by (auto simp: Let_def n_def)
    } note * = this
    then show ?thesis
      using VUntil_never
      unfolding Until
      by (auto simp: Let_def n_def intro: SAT_VIO.VUntil_never split: if_splits enat.splits)
  qed(auto intro: SAT_VIO.intros)
    (*
next
  case (SMatchP sp)
  then show ?case
  proof (cases phi)
    case (MatchP I r)
    then have "Regex.SAT (SAT rho) (fst (rs_at s_at sp)) (snd (rs_at s_at sp)) r"
      using rs_check_sound[of r sp s_check "SAT rho" s_at] SMatchP
      by (auto simp: Let_def)
    then show ?thesis using SMatchP MatchP
      by (auto simp: Let_def intro: SAT_VIO.SMatchP)
  qed(auto intro: SAT_VIO.intros)
next
  case (SMatchF sp)
  then show ?case
  proof (cases phi)
    case (MatchF I r)
    then have "Regex.SAT (SAT rho) (fst (rs_at s_at sp)) (snd (rs_at s_at sp)) r"
      using rs_check_sound[of r sp s_check "SAT rho" s_at] SMatchF MatchF
      by (auto simp: Let_def)
    then show ?thesis using SMatchF MatchF
      by (auto simp: Let_def intro: SAT_VIO.SMatchF)
  qed(auto intro: SAT_VIO.intros)
next
  case (VMatchP_le n)
  then show ?case
    by (cases phi) (auto intro: SAT_VIO.intros)
next
  case (VMatchP i vp)
  then show ?case
  proof (cases phi)
    case (MatchP I r)
    then have vio: "\<And>v. v \<in> set vp \<Longrightarrow> Regex.VIO (VIO rho) (fst (rv_at v_at v)) (snd (rv_at v_at v)) r"
      using rv_check_sound[of r _ v_check "VIO rho" v_at] VMatchP MatchP
      by (auto simp: Let_def)
    {fix k
      define j where j_def: "j \<equiv> ETP rho (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> (\<tau> rho i - n))"
      assume k_def: "k \<ge> j \<and> k \<le> i \<and> k \<le> LTP rho (\<tau> rho i - left I)"
      from VMatchP MatchP j_def have map: "set (map (fst \<circ> rv_at v_at) vp) = set [j ..< Suc (l rho i I)]"
        by (auto simp: Let_def)
      then have kset: "k \<in> set ([j ..< Suc (l rho i I)])" using k_def j_def by auto
      then obtain x where x: "x \<in> set vp" "fst (rv_at v_at x) = k"
        using k_def map
        apply auto
         apply (metis imageE insertI1)
        by (metis set_map[of "fst \<circ> rv_at v_at" vp] comp_apply[of fst "rv_at v_at"] imageE kset map)
      then have "Regex.VIO (VIO rho) k i r" using VMatchP MatchP vio[of x]
        by (auto simp: Let_def)
      } note * = this
    then show ?thesis using VMatchP MatchP
      by (auto simp: Let_def intro: SAT_VIO.VMatchP)
  qed(auto intro: SAT_VIO.intros)
next
  case (VMatchF i vp)
  then show ?case
  proof (cases phi)
    case (MatchF I r)
    then have vio: "\<And>v. v \<in> set vp \<Longrightarrow> Regex.VIO (VIO rho) (fst (rv_at v_at v)) (snd (rv_at v_at v)) r"
      using rv_check_sound[of r _ v_check "VIO rho" v_at] VMatchF MatchF
      by (auto simp: Let_def)
    {fix k
      define j where j_def: "j \<equiv> LTP rho (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> (\<tau> rho i + n))"
      assume k_def: "k \<le> j \<and> k \<ge> i \<and> k \<ge> ETP rho (\<tau> rho i + left I)"
      from VMatchF MatchF j_def have map: "set (map (snd \<circ> rv_at v_at) vp) = set [(lu rho i I) ..< Suc j]"
        by (auto simp: Let_def)
      then have kset: "k \<in> set ([(lu rho i I) ..< Suc j])" using k_def j_def by auto
      then obtain x where x: "x \<in> set vp" "snd (rv_at v_at x) = k" using k_def map
        apply auto
         apply (metis imageE insertI1)
        by (metis set_map[of "snd \<circ> rv_at v_at" vp] comp_apply[of snd "rv_at v_at"] imageE kset map)
      then have "Regex.VIO (VIO rho) i k r" using MatchF VMatchF vio[of x]
        by (auto simp: Let_def)
    } note * = this
    then show ?thesis
      using VMatchF MatchF
      by (auto simp: Let_def intro: SAT_VIO.VMatchF)
  qed(auto intro: SAT_VIO.intros)
*)
qed

lemma SAT_or_VIO: "SAT rho i \<phi> \<or> VIO rho i \<phi>"
  using completeness by blast

lemma set_map_list: "Suc j \<le> i \<and> (\<forall>k \<in> {Suc j ..< Suc i}. \<exists>sphi. s_at sphi = k \<and> s_check phi sphi)
\<Longrightarrow> \<exists>sphis. map (s_at) sphis = [Suc j ..< Suc i] \<and> (\<forall>sphi' \<in> set sphis. s_check phi sphi')"
proof(induction i)
  case 0
  then obtain sphi where sphi: "s_at sphi = i \<and> s_check phi sphi"
    using "local.0"  by auto
  define sphis where sphis: "sphis = [sphi]"
  then have "map s_at sphis = [i] \<and> (\<forall>sphi \<in> set sphis. s_check phi sphi)"
    using sphi by auto
  then show ?case
    by auto
next
  case (Suc x)
  then obtain sphis where sphis: "map (s_at) sphis = [Suc j ..< Suc x] \<and> (\<forall>sphi' \<in> set sphis. s_check phi sphi')"
    apply auto
    by (meson List.list.distinct(1) List.list.set_cases List.list.simps(8))
  from local.Suc.prems obtain sphi where sphi: "s_at sphi = Suc x \<and> s_check phi sphi"
    by fastforce
  then have "map s_at (sphis @ [sphi]) = [Suc j ..< Suc (Suc x)] \<and> (\<forall>sphi' \<in> set (sphis @ [sphi]). s_check phi sphi')"
    using sphis local.Suc by auto
  then show ?case by blast
qed

lemma check_complete:
  "bounded_future phi \<Longrightarrow> (SAT rho i phi \<longrightarrow> (\<exists>sphi. s_at sphi = i \<and> s_check phi sphi))
  \<and> (VIO rho i phi \<longrightarrow> (\<exists>vphi. v_at vphi = i \<and> v_check phi vphi))"
proof (induction phi arbitrary: i rule: bounded_future.induct)
  case TTBF
  then show ?case
    by (auto elim: VIO.cases intro: exI[of _ "STT i"])
next
  case FFBF
  then show ?case
    by (auto elim: SAT.cases intro: exI[of _ "VFF i"])
next
  case (AtomBF n)
  {assume "SAT rho i (Atom n)"
    then have "s_at (SAtm n i) = i \<and> s_check (Atom n) (SAtm n i)" by cases auto
  }
  moreover
  {assume "VIO rho i (Atom n)"
    then have "v_at (VAtm n i) = i \<and> v_check (Atom n) (VAtm n i)" by cases auto
  }
  ultimately show ?case by blast
next
  case (DisjBF phi psi)
  {assume "SAT rho i (Disj phi psi)"
    then have "\<exists>sphi. s_at sphi = i \<and> s_check (Disj phi psi) sphi"
    proof (cases)
      case (SDisjL)
      then obtain sphi where sphi: "s_at sphi = i \<and> s_check phi sphi" using DisjBF by auto
      then have "s_at (SDisjL sphi) = i \<and> s_check (Disj phi psi) (SDisjL sphi)"
        by auto
      then show ?thesis by blast
    next
      case (SDisjR)
      then obtain spsi where spsi: "s_at spsi = i \<and> s_check psi spsi" using DisjBF by auto
      then have "s_at (SDisjR spsi) = i \<and> s_check (Disj phi psi) (SDisjR spsi)"
        by auto
      then show ?thesis by blast
    qed
  }
  moreover
  {assume "VIO rho i (Disj phi psi)"
    then have "\<exists>vphi. v_at vphi = i \<and> v_check (Disj phi psi) vphi"
    proof (cases)
      case (VDisj)
      then obtain vphi and vpsi where sphi: "v_at vphi = i \<and> v_check phi vphi"
        and vpsi: "v_at vpsi = i \<and> v_check psi vpsi" using DisjBF by blast
      then have "v_at (VDisj vphi vpsi) = i \<and> v_check (Disj phi psi) (VDisj vphi vpsi)"
        by auto
      then show ?thesis by blast
    qed
  }
  ultimately show ?case by blast
next
  case (ConjBF phi psi)
  {assume "SAT rho i (Conj phi psi)"
    then have "\<exists>sphi. s_at sphi = i \<and> s_check (Conj phi psi) sphi"
    proof (cases)
      case (SConj)
      then obtain sphi and spsi where sphi: "s_at sphi = i \<and> s_check phi sphi"
        and spsi: "s_at spsi = i \<and> s_check psi spsi" using ConjBF by blast
      then have "s_at (SConj sphi spsi) = i \<and> s_check (Conj phi psi) (SConj sphi spsi)"
        by auto
      then show ?thesis by blast
    qed
  }
  moreover
  {assume "VIO rho i (Conj phi psi)"
    then have "\<exists>vphi. v_at vphi = i \<and> v_check (Conj phi psi) vphi"
    proof (cases)
      case (VConjL)
      then obtain vphi where vphi: "v_at vphi = i \<and> v_check phi vphi" using ConjBF by auto
      then have "v_at (VConjL vphi) = i \<and> v_check (Conj phi psi) (VConjL vphi)"
        by auto
      then show ?thesis by blast
    next
      case (VConjR)
      then obtain vpsi where vpsi: "v_at vpsi = i \<and> v_check psi vpsi" using ConjBF by auto
      then have "v_at (VConjR vpsi) = i \<and> v_check (Conj phi psi) (VConjR vpsi)"
        by auto
      then show ?thesis by blast
    qed
  }
  ultimately show ?case by blast
next
  case (NegBF phi)
  {assume "SAT rho i (Neg phi)"
    then have "\<exists>sphi. s_at sphi = i \<and> s_check (Neg phi) sphi"
    proof (cases)
      case (SNeg)
      then obtain vphi where vphi: "v_at vphi = i \<and> v_check phi vphi" using NegBF by auto
      then have "s_at (SNeg vphi) = i \<and> s_check (Neg phi) (SNeg vphi)"
        by auto
      then show ?thesis by blast
    qed
  }
  moreover
  {assume "VIO rho i (Neg phi)"
    then have "\<exists>vphi. v_at vphi = i \<and> v_check (Neg phi) vphi"
    proof (cases)
      case (VNeg)
      then obtain sphi where sphi: "s_at sphi = i \<and> s_check phi sphi" using NegBF by auto
      then have "v_at (VNeg sphi) = i \<and> v_check (Neg phi) (VNeg sphi)"
        by auto
      then show ?thesis by blast
    qed
  }
  ultimately show ?case by blast
next
  case (ImplBF phi psi)
  {assume "SAT rho i (Impl phi psi)"
    then have "\<exists>sp. s_at sp = i \<and> s_check (Impl phi psi) sp"
    proof (cases)
      case (SImplL)
      then obtain vphi where vphi: "v_at vphi = i \<and> v_check phi vphi"
        using ImplBF by blast
      then have "s_at (SImplL vphi) = i \<and> s_check (Impl phi psi) (SImplL vphi)"
        by auto
      then show ?thesis by blast
    next
      case (SImplR)
      then obtain spsi where spsi: "s_at spsi = i \<and> s_check psi spsi"
        using ImplBF by blast
      then have "s_at (SImplR spsi) = i \<and> s_check (Impl phi psi) (SImplR spsi)"
        by auto
      then show ?thesis by blast
    qed
  }
  moreover
  {assume "VIO rho i (Impl phi psi)"
    then have "\<exists>vp. v_at vp = i \<and> v_check (Impl phi psi) vp"
    proof (cases)
      case (VImpl)
      then obtain sphi and vpsi where sphi: "s_at sphi = i \<and> s_check phi sphi" 
        and vpsi: "v_at vpsi = i \<and> v_check psi vpsi"
        using ImplBF by blast
      then have "v_at (VImpl sphi vpsi) = i \<and> v_check (Impl phi psi) (VImpl sphi vpsi)"
        by auto
      then show ?thesis by blast
    qed
  }
  ultimately show ?case by blast
next
  case (IffBF phi psi)
  {assume "SAT rho i (Iff phi psi)"
    then have "\<exists>sp. s_at sp = i \<and> s_check (Iff phi psi) sp"
    proof (cases)
      case (SIff_ss)
      then obtain sphi and spsi where sphi: "s_at sphi = i \<and> s_check phi sphi" 
        and spsi: "s_at spsi = i \<and> s_check psi spsi"
        using IffBF by blast
      then have "s_at (SIff_ss sphi spsi) = i \<and> s_check (Iff phi psi) (SIff_ss sphi spsi)"
        by auto
      then show ?thesis by blast
    next
      case (SIff_vv)
      then obtain vphi and vpsi where sphi: "v_at vphi = i \<and> v_check phi vphi" 
        and vpsi: "v_at vpsi = i \<and> v_check psi vpsi"
        using IffBF by blast
      then have "s_at (SIff_vv vphi vpsi) = i \<and> s_check (Iff phi psi) (SIff_vv vphi vpsi)"
        by auto
      then show ?thesis by blast
    qed
  }
  moreover
  {assume "VIO rho i (Iff phi psi)"
    then have "\<exists>vp. v_at vp = i \<and> v_check (Iff phi psi) vp"
    proof (cases)
      case (VIff_sv)
      then obtain sphi and vpsi where sphi: "s_at sphi = i \<and> s_check phi sphi"
        and vpsi: "v_at vpsi = i \<and> v_check psi vpsi"
        using IffBF by blast
      then have "v_at (VIff_sv sphi vpsi) = i \<and> v_check (Iff phi psi) (VIff_sv sphi vpsi)"
        by auto
      then show ?thesis by blast
    next
      case (VIff_vs)
      then obtain vphi and spsi where sphi: "v_at vphi = i \<and> v_check phi vphi"
        and spsi: "s_at spsi = i \<and> s_check psi spsi"
        using IffBF by blast
      then have "v_at (VIff_vs vphi spsi) = i \<and> v_check (Iff phi psi) (VIff_vs vphi spsi)"
        by auto
      then show ?thesis by blast
    qed
  }
  ultimately show ?case by blast
next
  case (NextBF phi I)
  {assume "SAT rho i (Next I phi)"
    then have "\<exists>sphi. s_at sphi = i \<and> s_check (Next I phi) sphi"
    proof (cases)
      case (SNext)
      then obtain sphi where sphi: "s_at sphi = (Suc i) \<and> s_check phi sphi" using NextBF by auto
      then have "s_at (SNext sphi) = i \<and> s_check (Next I phi) (SNext sphi)"
        using SNext sphi by auto
      then show ?thesis by blast
    qed
  }
  moreover
  {assume "VIO rho i (Next I phi)"
    then have "\<exists>vphi. v_at vphi = i \<and> v_check (Next I phi) vphi"
    proof (cases)
      case (VNext)
      then obtain vphi where vphi: "v_at vphi = (Suc i) \<and> v_check phi vphi" using NextBF by auto
      then have "v_at (VNext vphi) = i \<and> v_check (Next I phi) (VNext vphi)"
        using VNext vphi by auto
      then show ?thesis by blast
    next
      case (VNext_le)
      then have "v_at (VNext_le i) = i \<and> v_check (Next I phi) (VNext_le i)" by auto
      then show ?thesis by blast
    next
      case (VNext_ge)
      then have "v_at (VNext_ge i) = i \<and> v_check (Next I phi) (VNext_ge i)" by auto
      then show ?thesis by blast
    qed
  }
  ultimately show ?case by blast
next
  case (PrevBF phi I)
  {assume "SAT rho i (Prev I phi)"
    then have "\<exists>sphi. s_at sphi = i \<and> s_check (Prev I phi) sphi"
    proof (cases)
      case (SPrev)
      then obtain sphi where sphi: "s_at sphi = i - 1 \<and> s_check phi sphi" using PrevBF by auto
      then have "s_at (SPrev sphi) = i \<and> s_check (Prev I phi) (SPrev sphi)"
        using SPrev sphi by auto
      then show ?thesis by blast
    qed
  }
  moreover
  {assume "VIO rho i (Prev I phi)"
    then have "\<exists>vphi. v_at vphi = i \<and> v_check (Prev I phi) vphi"
    proof (cases)
      case (VPrev)
      then obtain vphi where vphi: "v_at vphi = i - 1 \<and> v_check phi vphi" using PrevBF by auto
      then have "v_at (VPrev vphi) = i \<and> v_check (Prev I phi) (VPrev vphi)"
        using VPrev vphi by auto
      then show ?thesis by blast
    next
      case (VPrev_zero)
      then have "v_at (VPrev_zero) = i \<and> v_check (Prev I phi) (VPrev_zero)" by auto
      then show ?thesis by blast
    next
      case (VPrev_le)
      then have "v_at (VPrev_le i) = i \<and> v_check (Prev I phi) (VPrev_le i)" by auto
      then show ?thesis by blast
    next
      case (VPrev_ge)
      then have "v_at (VPrev_ge i) = i \<and> v_check (Prev I phi) (VPrev_ge i)" by auto
      then show ?thesis by blast
    qed
  }
  ultimately show ?case by blast
next
  case (SinceBF phi psi I)
  {assume "SAT rho i (Since phi I psi)"
    then have "\<exists>sphi. s_at sphi = i \<and> s_check (Since phi I psi) sphi"
    proof (cases)
      case (SSince j)
      then obtain spsi where spsi: "s_at spsi = j \<and> s_check psi spsi" using SinceBF by blast
      {assume "Suc j > i"
        then have "s_at (SSince spsi []) = i \<and> s_check (Since phi I psi) (SSince spsi [])"
          using spsi SSince by auto
        then have "\<exists>sphi. s_at sphi = i \<and> s_check (Since phi I psi) sphi" by blast
      }
      moreover
      {assume j_i: "Suc j \<le> i"
        from SinceBF SSince obtain f where f_def: "\<forall>k \<in> {Suc j..<Suc i}. s_at (f k) = k \<and> s_check phi (f k)"
          by atomize_elim (auto intro: bchoice)
        then obtain sphis where sphis: "map (s_at) sphis = [Suc j ..< Suc i]
        \<and> (\<forall>sphi \<in> set sphis. s_check phi sphi)"
          by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map f [Suc j..< Suc i]"])
        then have "sphis \<noteq> []" using j_i by auto
        then have "s_at (SSince spsi sphis) = i \<and> s_check (Since phi I psi) (SSince spsi sphis)"
          using spsi j_i sphis SSince
          apply (auto)
           apply (metis List.list.exhaust List.list.simps(5) last_map last_snoc)
          by (metis (full_types) List.list.exhaust List.list.simps(5) last_map last_snoc)
        then have "\<exists>sphi. s_at sphi = i \<and> s_check (Since phi I psi) sphi" by blast
      }
      ultimately show ?thesis
        using not_less by blast
    qed
  }
  moreover
  {assume "VIO rho i (Since phi I psi)"
    then have "\<exists>vphi. v_at vphi = i \<and> v_check (Since phi I psi) vphi"
    proof (cases)
      case (VSince_le)
      then have "v_at (VSince_le i) = i \<and> v_check (Since phi I psi) (VSince_le i)"
        by auto
      then show ?thesis by blast
    next
      case (VSince j)
      then obtain vphi where vphi: "v_at vphi = j \<and> v_check phi vphi" using SinceBF VSince by auto
      from SinceBF VSince obtain f where f_def: "\<forall>k \<in> {j .. l rho i I}. v_at (f k) = k \<and> v_check psi (f k)"
        by atomize_elim (auto intro: bchoice)
      then obtain vpsis where vpsis: "map (v_at) vpsis = [j ..< Suc (l rho i I)]
        \<and> (\<forall>vpsi \<in> set vpsis. v_check psi vpsi)"
        by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map f ([j ..< Suc (l rho i I)])"])
      then have "v_at (VSince i vphi vpsis) = i \<and> v_check (Since phi I psi) (VSince i vphi vpsis)"
        using vphi VSince by auto
      then show ?thesis by blast
    next
      case (VSince_never j)
      from SinceBF VSince_never obtain f where f_def: "\<forall>k \<in> {j .. l rho i I}. v_at (f k) = k \<and> v_check psi (f k)"
        by atomize_elim (auto intro: bchoice)
      then obtain vpsis where vpsis: "map (v_at) vpsis = [j ..< Suc (l rho i I)]
        \<and> (\<forall>vpsi \<in> set vpsis. v_check psi vpsi)"
        by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map f ([j ..< Suc (l rho i I)])"])
      then have "v_at (VSince_never i j vpsis) = i \<and> v_check (Since phi I psi) (VSince_never i j vpsis)"
        using VSince_never by auto
      then show ?thesis by blast
    qed
  }
  ultimately show ?case by blast
next
  case (OnceBF phi I)
  {assume "SAT rho i (Once I phi)"
    then have "\<exists>sphi. s_at sphi = i \<and> s_check (Once I phi) sphi"
    proof (cases)
      case (SOnce j)
      then obtain sphi where sphi: "s_at sphi = j \<and> s_check phi sphi" using OnceBF by blast
      {assume "Suc j > i"
        then have "s_at (SOnce i sphi) = i \<and> s_check (Once I phi) (SOnce i sphi)"
          using sphi SOnce by auto
        then have "\<exists>sphi. s_at sphi = i \<and> s_check (Once I phi) sphi" by blast
      }
      moreover
      {assume j_i: "Suc j \<le> i"
        have "s_at (SOnce i sphi) = i \<and> s_check (Once I phi) (SOnce i sphi)"
          using sphi j_i SOnce
          by (auto)
      }
      ultimately show ?thesis
        using not_less by blast
    qed
  }
  moreover
  {assume "VIO rho i (Once I phi)"
    then have "\<exists>vphi. v_at vphi = i \<and> v_check (Once I phi) vphi"
    proof (cases)
      case (VOnce_le)
      then have "v_at (VOnce_le i) = i \<and> v_check (Once I phi) (VOnce_le i)"
        by auto
      then show ?thesis by blast
    next
      case (VOnce_never j)
      from OnceBF VOnce_never obtain f where f_def: "\<forall>k \<in> {j .. l rho i I}. v_at (f k) = k \<and> v_check phi (f k)"
        by atomize_elim (auto intro: bchoice)
      then obtain vphis where vphis: "map (v_at) vphis = [j ..< Suc (l rho i I)]
          \<and> (\<forall>vphi \<in> set vphis. v_check phi vphi)"
        by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map f ([j ..< Suc (l rho i I)])"])
      then have "v_at (VOnce_never i j vphis) = i \<and> v_check (Once I phi) (VOnce_never i j vphis)"
        using VOnce_never by auto
      then show ?thesis by blast
    qed
  }
  ultimately show ?case by blast
next
  case (UntilBF I phi psi)
  {assume "SAT rho i (Until phi I psi)"
    then have "\<exists>sphi. s_at sphi = i \<and> s_check (Until phi I psi) sphi"
    proof (cases)
      case (SUntil j)
      then obtain spsi where spsi: "s_at spsi = j \<and> s_check psi spsi" using UntilBF SUntil by blast
      {assume "i \<ge> j"
        then have "s_at (SUntil [] spsi) = i \<and> s_check (Until phi I psi) (SUntil [] spsi)"
          using spsi SUntil by auto
        then have "\<exists>sphi. s_at sphi = i \<and> s_check (Until phi I psi) sphi" by blast
      }
      moreover
      { assume i_j: "i < j"
        from UntilBF SUntil obtain f where f_def: "\<forall>k \<in> {i ..< j}. s_at (f k) = k \<and> s_check phi (f k)"
          by atomize_elim (auto intro: bchoice)
        then obtain sphis where sphis: "map (s_at) sphis = [i ..< j]
          \<and> (\<forall>sphi \<in> set sphis. s_check phi sphi)"
          by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map f ([i ..< j])"])
        then have non_empt:"sphis \<noteq> []" using i_j apply auto
          by (metis gr_implies_not0 leD upt_eq_Nil_conv)
        then have "s_at (SUntil sphis spsi) = i \<and> s_check (Until phi I psi) (SUntil sphis spsi)"
          using spsi SUntil sphis apply (auto split: list.splits)
          using Cons_eq_upt_conv apply blast
          by (simp add: Cons_eq_upt_conv)
        then have "\<exists>sphi. s_at sphi = i \<and> s_check (Until phi I psi) sphi" by blast
      }
      ultimately show ?thesis using not_less by blast
    qed
  }
  moreover
  {assume "VIO rho i (Until phi I psi)"
    then have "\<exists>vphi. v_at vphi = i \<and> v_check (Until phi I psi) vphi"
    proof (cases)
      case (VUntil j)
      then obtain vphi where vphi: "v_at vphi = j \<and> v_check phi vphi" using UntilBF by auto
      from UntilBF VUntil obtain f where f_def: "\<forall>k \<in> {lu rho i I .. j}. v_at (f k) = k \<and> v_check psi (f k)"
        by atomize_elim (auto intro: bchoice)
      then obtain vpsis where vpsis: "map (v_at) vpsis = [lu rho i I ..< Suc j]
        \<and> (\<forall>vpsi \<in> set vpsis. v_check psi vpsi)"
        by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map f ([lu rho i I ..< Suc j])"])
      then have "v_at (VUntil i vpsis vphi) = i \<and> v_check (Until phi I psi) (VUntil i vpsis vphi)"
        using vphi UntilBF VUntil by auto
      then show ?thesis by blast
    next
      case (VUntil_never)
      obtain n where n_def: "right I = enat n"
        using UntilBF
        by (cases "right I") auto
      define j where "j = LTP rho (\<tau> rho i + n)"
      obtain f where f_def: "\<forall>k \<in> {lu rho i I .. j}. v_at (f k) = k \<and> v_check psi (f k)"
        using UntilBF VUntil_never by atomize_elim (auto simp: n_def j_def intro: bchoice)
      then obtain vpsis where vpsis: "map (v_at) vpsis = [lu rho i I ..< Suc j]
        \<and> (\<forall>vpsi \<in> set vpsis. v_check psi vpsi)"
        by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map f ([lu rho i I ..< Suc j])"])
      then have "v_at (VUntil_never i j vpsis) = i \<and> v_check (Until phi I psi) (VUntil_never i j vpsis)"
        using UntilBF VUntil_never by (auto simp: n_def j_def)
      then show ?thesis by blast
    qed
  }
  ultimately show ?case by blast
      (*
next
  case (MatchPBF r I)
  {
    assume sat: "SAT rho i (MatchP I r)"
    then have "\<exists>sp. s_at sp = i \<and> s_check (MatchP I r) sp"
    proof (cases)
      case (SMatchP j)
      then obtain rp where rp_def: "rs_check s_check s_at r rp \<and> rs_at s_at rp = (j, i)"
        using rs_check_complete[of r "SAT rho" s_at s_check j i] MatchPBF
        by auto
      define sp where sp_def: "sp \<equiv> SMatchP rp"
      then show ?thesis
        using SMatchP rp_def
        by (auto intro: exI[of _ sp])
    qed
  }
  moreover
  {
    assume vio: "VIO rho i (MatchP I r)"
    from vio have "\<exists>vp. v_at vp = i \<and> v_check (MatchP I r) vp"
    proof (cases)
      case (VMatchP_le)
      then show ?thesis
        by (auto intro: exI[of _ "VMatchP_le i"])
    next
      case (VMatchP j)
      then have "\<forall>k \<in> {j .. l rho i I}. \<exists>p'. fst (rv_at v_at p') = k \<and> rv_check v_check v_at r p' \<and> snd (rv_at v_at p') = i"
        using rv_check_complete[of r "VIO rho" v_at v_check _ i] MatchPBF
        apply auto
        by (metis fst_conv snd_conv)
      then obtain f where f_def: "\<forall>k \<in> {j .. l rho i I}. fst (rv_at v_at (f k)) = k \<and> rv_check v_check v_at r (f k) \<and> snd (rv_at v_at (f k)) = i"
        by atomize_elim (auto intro: bchoice)
      then obtain vps where vps: "map (fst \<circ> rv_at v_at) vps = [j ..< Suc (l rho i I)]
        \<and> (\<forall>vp \<in> set vps. rv_check v_check v_at r vp \<and> snd (rv_at v_at vp) = i)"
        by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map f ([j ..< Suc (l rho i I)])"])
      then have "v_at (VMatchP i vps) = i \<and> v_check (MatchP I r) (VMatchP i vps)"
        using VMatchP
        by auto
      then show ?thesis
        by blast
    qed
  }
  ultimately show ?case
    by auto
next
  case (MatchFBF I r)
  {
    assume sat: "SAT rho i (MatchF I r)"
    then have "\<exists>sp. s_at sp = i \<and> s_check (MatchF I r) sp"
    proof (cases)
      case (SMatchF j)
      then obtain rp where rp_def: "rs_check s_check s_at r rp \<and> rs_at s_at rp = (i, j)"
        using rs_check_complete[of r "SAT rho" s_at s_check i j] MatchFBF
        by auto
      define sp where sp_def: "sp \<equiv> SMatchF rp"
      then show ?thesis
        using SMatchF rp_def
        by (auto intro: exI[of _ sp])
    qed
  }
  moreover
  {
    assume vio: "VIO rho i (MatchF I r)"
    then have "\<exists>vp. v_at vp = i \<and> v_check (MatchF I r) vp"
    proof (cases)
      case (VMatchF j)
      then have "\<forall>k \<in> {lu rho i I .. j}. \<exists>p'. snd (rv_at v_at p') = k \<and> rv_check v_check v_at r p' \<and> fst (rv_at v_at p') = i"
        using rv_check_complete[of r "VIO rho" v_at v_check i _] MatchFBF
        by force
      then obtain f where f_def: "\<forall>k \<in> {lu rho i I .. j}. snd (rv_at v_at (f k)) = k \<and> rv_check v_check v_at r (f k)  \<and> fst (rv_at v_at (f k)) = i"
        by atomize_elim (auto intro: bchoice)
      then obtain vps where vps: "map (snd \<circ> rv_at v_at) vps = [lu rho i I ..< Suc j]
        \<and> (\<forall>vp \<in> set vps. rv_check v_check v_at r vp \<and> fst (rv_at v_at vp) = i)"
        by atomize_elim (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map f ([lu rho i I ..< Suc j])"])
      then have "v_at (VMatchF i vps) = i \<and> v_check (MatchF I r) (VMatchF i vps)"
        using VMatchF
        by auto
      then show ?thesis
        by blast
    qed
  }
  ultimately show ?case
    by auto
*)
qed

end

context
  fixes rho :: "'a trace" and phi :: "'a mtl"
begin

definition "p_check = (\<lambda>phi p. case_sum (s_check rho phi) (v_check rho phi) p)"

end

definition "p_at = (\<lambda>p. case_sum s_at v_at p)"

(* Optimal proof-finding algorithm *)

(* ++ operator from paper *)
definition proofApp :: "('a sproof + 'a vproof) \<Rightarrow> ('a sproof + 'a vproof)
\<Rightarrow> ('a sproof + 'a vproof)" (infixl "\<oplus>" 65) where
  "p \<oplus> r = (case (p, r) of
   (Inl (SSince p1 p2), Inl r) \<Rightarrow> Inl (SSince p1 (p2 @ [r]))
 | (Inl (SUntil p1 p2), Inl r) \<Rightarrow> Inl (SUntil (r # p1) p2)
 | (Inr (VSince i p1 p2), Inr r) \<Rightarrow> Inr (VSince (Suc i) p1 (p2 @ [r]))
 | (Inr (VOnce_never i li p1), Inr r) \<Rightarrow> Inr (VOnce_never (Suc i) li (p1 @ [r]))
 | (Inr (VSince_never i li p1), Inr r) \<Rightarrow> Inr (VSince_never (Suc i) li (p1 @ [r]))
 | (Inr (VUntil i p1 p2), Inr r) \<Rightarrow> Inr (VUntil (i-1) (r # p1) p2)
 | (Inr (VUntil_never i hi p1), Inr r) \<Rightarrow> Inr (VUntil_never (i-1) hi (r # p1)))"

definition proofIncr :: "('a sproof + 'a vproof) \<Rightarrow> ('a sproof + 'a vproof)" where
  "proofIncr p = (case p of
   Inr (VSince i p1 p2) \<Rightarrow> Inr (VSince (Suc i) p1 p2)
 | Inr (VOnce_never i li p1) \<Rightarrow> Inr (VSince_never (Suc i) li p1)
 | Inr (VSince_never i li p1) \<Rightarrow> Inr (VSince_never (Suc i) li p1)
 | Inr (VUntil i p1 p2) \<Rightarrow> Inr (VUntil (i-1) p1 p2)
 | Inr (VUntil_never i hi p1) \<Rightarrow> Inr (VUntil_never (i-1) hi (p1)))"

datatype 'a onetwo = One 'a | Two 'a 'a

term set_onetwo
thm onetwo.set

(* Minimum w.r.t. a wqo *)
fun min_onetwo where
  "min_onetwo r (One x) = x"
| "min_onetwo r (Two x y) = (if r x y then x else y)"

lemma min_onetwo_in: "min_onetwo r ot \<in> set_onetwo ot"
  by (cases ot) auto

lemma min_onetwo_le: "reflp r \<Longrightarrow> total_on r (set_onetwo ot) \<Longrightarrow> p \<in> set_onetwo ot \<Longrightarrow> r (min_onetwo r ot) p"
  by (cases ot) (auto simp add: reflp_def total_on_def)

definition min_list_wrt where
  "min_list_wrt r xs = hd [x \<leftarrow> xs. \<forall>y \<in> set xs. r x y]"

lemma refl_total_transp_imp_ex_min:
  "xs \<noteq> [] \<Longrightarrow> reflp r \<Longrightarrow> total_on r (set xs) \<Longrightarrow> transp r \<Longrightarrow> \<exists>x \<in> set xs. \<forall>y \<in> set xs. r x y"
proof(induction xs)
  case (Cons y' ys)
  then show ?case
  proof (cases ys)
    case Nil
    then show ?thesis
      using reflpD[OF Cons(3)] Cons(2)
      by simp
  next
    case cons_ys: (Cons a list)
    then have ys_nnil: "ys \<noteq> []"
      by auto
    from Cons(4) have total_ys: "total_on r (set ys)"
      by (simp add: total_on_def)
    from Cons(1)[OF ys_nnil Cons(3) total_ys Cons(5)]
    obtain x where x_def: "x \<in> set ys" "\<forall>y \<in> set ys. r x y"
      by auto
    then have "r x y' \<or> r y' x"
      using Cons(2,4)
      by (auto simp: total_on_def)
    moreover
    {
      assume r_xy: "r x y'"
      then have "\<exists>x \<in> set (y' # ys). \<forall>y \<in> set (y' # ys). r x y"
        using x_def
        by auto
    }
    moreover
    {
      assume r_yx: "r y' x"
      then have "\<forall>x \<in> set (y' # ys). r y' x"
        using x_def Cons(3,4) transpD[OF Cons(5), of y' x]
        by (auto simp: total_on_def reflp_def)
      then have "\<exists>y \<in> set (y' # ys). \<forall>x \<in> set (y' # ys). r y x"
        by auto
    }
    ultimately show ?thesis
      by auto
  qed
qed simp

lemma min_list_wrt_in:
  assumes nnil: "xs \<noteq> []" and total: "total_on r (set xs)"
    and refl: "reflp r" and transp: "transp r"
  shows "min_list_wrt r xs \<in> set xs"
proof -
  have "filter (\<lambda>x. \<forall>y \<in> set xs. r x y) xs \<noteq> []"
    using refl_total_transp_imp_ex_min[OF nnil refl total transp]
      filter_empty_conv[of "(\<lambda>x. \<forall>y \<in> set xs. r x y)" xs]
    by simp
  then show ?thesis
    using assms min_list_wrt_def[of r xs]
      filter_is_subset[of "(\<lambda>x. \<forall>y \<in> set xs. r x y)" xs] list.set_sel(1)
    by force
qed

lemma min_list_wrt_le:
  assumes total: "total_on r (set xs)" and refl: "reflp r" and transp: "transp r"
    and p_in: "p \<in> set xs"
  shows "r (min_list_wrt r xs) p"
proof -
  from p_in have nnil: "xs \<noteq> []"
    by auto
  have filter_nnil: "filter (\<lambda>x. \<forall>y \<in> set xs. r x y) xs \<noteq> []"
    using refl_total_transp_imp_ex_min[OF nnil refl total transp]
      filter_empty_conv[of "(\<lambda>x. \<forall>y \<in> set xs. r x y)" xs]
    by simp
  then show ?thesis
    using assms list.set_sel(1)[of "filter (\<lambda>x. \<forall>y \<in> set xs. r x y) xs"]
    by (auto simp: min_list_wrt_def)
qed

(* Helper functions for Cand *)
definition doDisj :: "('a sproof + 'a vproof) \<Rightarrow> ('a sproof + 'a vproof) \<Rightarrow>
('a sproof + 'a vproof) list" where
  "doDisj p1 p2 = (case (p1, p2) of
  (Inl p1, Inl p2) \<Rightarrow> [Inl (SDisjL p1), Inl (SDisjR p2)]
| (Inl p1, Inr p2) \<Rightarrow> [Inl (SDisjL p1)]
| (Inr p1, Inl p2) \<Rightarrow> [Inl (SDisjR p2)]
| (Inr p1, Inr p2) \<Rightarrow> [Inr (VDisj p1 p2)])"

definition doConj :: "('a sproof + 'a vproof) \<Rightarrow> ('a sproof + 'a vproof) \<Rightarrow>
('a sproof + 'a vproof) list" where
  "doConj p1 p2 = (case (p1, p2) of
  (Inl p1, Inl p2) \<Rightarrow> [Inl (SConj p1 p2)]
| (Inl p1, Inr p2) \<Rightarrow> [Inr (VConjR p2)]
| (Inr p1, Inl p2) \<Rightarrow> [Inr (VConjL p1)]
| (Inr p1, Inr p2) \<Rightarrow> [Inr (VConjL p1), Inr (VConjR p2)])"

definition doImpl :: "('a sproof + 'a vproof) \<Rightarrow> ('a sproof + 'a vproof) \<Rightarrow>
('a sproof + 'a vproof) list" where
  "doImpl p1 p2 = (case (p1, p2) of
  (Inl p1, Inl p2) \<Rightarrow> [Inl (SImplR p2)]
| (Inl p1, Inr p2) \<Rightarrow> [Inr (VImpl p1 p2)]
| (Inr p1, Inl p2) \<Rightarrow> [Inl (SImplL p1), Inl (SImplR p2)]
| (Inr p1, Inr p2) \<Rightarrow> [Inl (SImplL p1)])"

definition doIff :: "('a sproof + 'a vproof) \<Rightarrow> ('a sproof + 'a vproof) \<Rightarrow>
('a sproof + 'a vproof) list" where
  "doIff p1 p2 = (case (p1, p2) of
  (Inl p1, Inl p2) \<Rightarrow> [Inl (SIff_ss p1 p2)]
| (Inl p1, Inr p2) \<Rightarrow> [Inr (VIff_sv p1 p2)]
| (Inr p1, Inl p2) \<Rightarrow> [Inr (VIff_vs p1 p2)]
| (Inr p1, Inr p2) \<Rightarrow> [Inl (SIff_vv p1 p2)])"

definition doPrev :: "nat \<Rightarrow> \<I> \<Rightarrow> nat \<Rightarrow> ('a sproof + 'a vproof)
\<Rightarrow> ('a sproof + 'a vproof) list" where
  "doPrev i I tau p = (case (p, tau < left I) of
  (Inl p, True) \<Rightarrow> [Inr (VPrev_le i)]
| (Inl p, False) \<Rightarrow> (if mem tau I then [Inl (SPrev p)] else [Inr (VPrev_ge i)])
| (Inr p, True) \<Rightarrow> [Inr (VPrev p), Inr (VPrev_le i)]
| (Inr p, False) \<Rightarrow> (if mem tau I then [Inr (VPrev p)] else [Inr (VPrev p), Inr (VPrev_ge i)]))"

definition doNext :: "nat \<Rightarrow> \<I> \<Rightarrow> nat \<Rightarrow> ('a sproof + 'a vproof)
\<Rightarrow> ('a sproof + 'a vproof) list" where
  "doNext i I tau p = (case (p, tau < left I) of
  (Inl p, True) \<Rightarrow> [Inr (VNext_le i)]
| (Inl p, False) \<Rightarrow> (if mem tau I then [Inl (SNext p)] else [Inr (VNext_ge i)])
| (Inr p, True) \<Rightarrow> [Inr (VNext p), Inr (VNext_le i)]
| (Inr p, False) \<Rightarrow> (if mem tau I then [Inr (VNext p)] else [Inr (VNext p), Inr (VNext_ge i)]))"

definition doOnceBase :: "nat \<Rightarrow> nat \<Rightarrow> ('a sproof + 'a vproof)
\<Rightarrow> ('a sproof + 'a vproof) list" where
  "doOnceBase i a p = (case (p, a = 0) of
  (Inl p, True) \<Rightarrow> [Inl (SOnce i p)]
| (Inr p, True) \<Rightarrow> [Inr (VOnce_never i i [p])]
| (_, False) \<Rightarrow> [Inr (VOnce_never i i [])])"

definition doOnce :: "nat \<Rightarrow> nat \<Rightarrow> ('a sproof + 'a vproof) \<Rightarrow> ('a sproof + 'a vproof)
\<Rightarrow> ('a sproof + 'a vproof) list" where
  "doOnce i a p p' = (case (p, a = 0, p') of
(Inr p, True, Inl (SOnce j p'')) \<Rightarrow> [Inl (SOnce i p'')]
| (Inr p, True, Inr p') \<Rightarrow> [(Inr p') \<oplus> (Inr p)]
| (Inr p, False, Inl (SOnce j p'')) \<Rightarrow> [Inl (SOnce i p'')]
| (Inr p, False, Inr (VOnce_never j li q)) \<Rightarrow> [Inr (VOnce_never i li q)]
| (Inl p, True, Inr (VOnce_never j li q)) \<Rightarrow> [Inl (SOnce i p)]
| (Inl p, True, Inl (SOnce j p'')) \<Rightarrow> [Inl (SOnce i p)]
| (Inl p, False, Inl (SOnce j p'')) \<Rightarrow> [Inl (SOnce i p'')]
| (Inl p, False, Inr (VOnce_never j li q)) \<Rightarrow> [Inr (VOnce_never i li q)])"

definition doSinceBase :: "nat \<Rightarrow> nat \<Rightarrow> ('a sproof + 'a vproof)
\<Rightarrow> ('a sproof + 'a vproof) \<Rightarrow> ('a sproof + 'a vproof) list" where
  "doSinceBase i a p1 p2 = (case (p1, p2, a = 0) of
  (_, Inl p2, True) \<Rightarrow> [Inl (SSince p2 [])]
| (Inl p1, _, False) \<Rightarrow> [Inr (VSince_never i i [])]
| (Inl p1, Inr p2, True) \<Rightarrow> [Inr (VSince_never i i [p2])]
| (Inr p1, _, False) \<Rightarrow> [Inr (VSince i p1 []), Inr (VSince_never i i [])]
| (Inr p1, Inr p2, True) \<Rightarrow> [Inr (VSince i p1 [p2]), Inr (VSince_never i i [p2])])"

definition doSince :: "nat \<Rightarrow> nat \<Rightarrow> ('a sproof + 'a vproof) \<Rightarrow> ('a sproof + 'a vproof)
\<Rightarrow> ('a sproof + 'a vproof) \<Rightarrow> ('a sproof + 'a vproof) list" where
  "doSince i a p1 p2 p' = (case (p1, p2, a = 0, p') of
  (Inr p1, Inr p2, True, Inl p') \<Rightarrow> [Inr (VSince i p1 [p2])]
| (Inr p1, _, False, Inl p') \<Rightarrow> [Inr (VSince i p1 [])]
| (Inr p1, Inl p2, True, Inl p') \<Rightarrow> [Inl (SSince p2 [])]
| (Inl p1, Inr p2, True, Inl p') \<Rightarrow> [(Inl p') \<oplus> (Inl p1)]
| (Inl p1, _, False, Inl p') \<Rightarrow> [(Inl p') \<oplus> (Inl p1)]
| (Inl p1, Inl p2, True, Inl p') \<Rightarrow> [(Inl p') \<oplus> (Inl p1), Inl (SSince p2 [])]
| (Inr p1, Inr p2, True, Inr (VSince_never j li q)) \<Rightarrow> [Inr (VSince i p1 [p2]), p' \<oplus> (Inr p2)]
| (Inr p1, _, False, Inr (VSince_never j li q)) \<Rightarrow> [Inr (VSince i p1 []), Inr (VSince_never i li q)]
| (_, Inl p2, True, Inr (VSince_never j li q)) \<Rightarrow> [Inl (SSince p2 [])]
| (Inl p1, Inr p2, True, Inr (VSince_never j li q)) \<Rightarrow> [p' \<oplus> (Inr p2)]
| (Inl p1, _, False, Inr (VSince_never j li q)) \<Rightarrow> [Inr (VSince_never i li q)]
| (Inr p1, Inr p2, True, Inr (VSince j q1 q2)) \<Rightarrow> [Inr (VSince i p1 [p2]), p' \<oplus> (Inr p2)]
| (Inr p1, _, False, Inr (VSince j q1 q2)) \<Rightarrow> [Inr (VSince i p1 []), Inr (VSince i q1 q2)]
| (_, Inl p2, True, Inr (VSince j q1 q2)) \<Rightarrow> [Inl (SSince p2 [])]
| (Inl p1, Inr p2, True, Inr (VSince j q1 q2)) \<Rightarrow> [p' \<oplus> (Inr p2)]
| (Inl p1, _, False, Inr (VSince j q1 q2)) \<Rightarrow> [Inr (VSince i q1 q2)])"

definition doUntilBase :: "nat \<Rightarrow> nat \<Rightarrow> ('a sproof + 'a vproof) \<Rightarrow> ('a sproof + 'a vproof)
\<Rightarrow> ('a sproof + 'a vproof) list" where
  "doUntilBase i a p1 p2 = (case (p1, p2, a = 0) of
  (_, Inl p2, True) \<Rightarrow> [Inl (SUntil [] p2)]
| (Inl p1, _, False) \<Rightarrow> [Inr (VUntil_never i i [])]
| (Inl p1, Inr p2, True) \<Rightarrow> [Inr (VUntil_never i i [p2])]
| (Inr p1, _, False) \<Rightarrow> [Inr (VUntil i [] p1), Inr (VUntil_never i i [])]
| (Inr p1, Inr p2, True) \<Rightarrow> [Inr (VUntil i [p2] p1), Inr (VUntil_never i i [p2])])"

definition doUntil :: "nat \<Rightarrow> nat \<Rightarrow> ('a sproof + 'a vproof) \<Rightarrow> ('a sproof + 'a vproof)
\<Rightarrow> ('a sproof + 'a vproof) \<Rightarrow> ('a sproof + 'a vproof) list" where
  "doUntil i a p1 p2 p' = (case (p1, p2, a = 0, p') of
  (Inr p1, Inr p2, True, Inl (SUntil q1 q2)) \<Rightarrow> [Inr (VUntil i [p2] p1)]
| (Inr p1, _, False, Inl (SUntil q1 q2)) \<Rightarrow> [Inr (VUntil i [] p1)]
| (Inr p1, Inl p2, True, Inl (SUntil q1 q2)) \<Rightarrow> [Inl (SUntil [] p2)]
| (Inl p1, Inr p2, True, Inl (SUntil q1 q2)) \<Rightarrow> [p' \<oplus> (Inl p1)]
| (Inl p1, _, False, Inl (SUntil q1 q2)) \<Rightarrow> [p' \<oplus> (Inl p1)]
| (Inl p1, Inl p2, True, Inl (SUntil q1 q2)) \<Rightarrow> [p' \<oplus> (Inl p1), Inl (SUntil [] p2)]
| (Inr p1, Inr p2, True, Inr (VUntil_never j hi q)) \<Rightarrow> [Inr (VUntil i [p2] p1), p' \<oplus> (Inr p2)]
| (Inr p1, _, False, Inr (VUntil_never j hi q)) \<Rightarrow> [Inr (VUntil i [] p1), Inr (VUntil_never i hi q)]
| (_, Inl p2, True, Inr (VUntil_never j hi q)) \<Rightarrow> [Inl (SUntil [] p2)]
| (Inl p1, Inr p2, True, Inr (VUntil_never j hi q)) \<Rightarrow> [p' \<oplus> (Inr p2)]
| (Inl p1, _, False, Inr (VUntil_never j hi q)) \<Rightarrow> [Inr (VUntil_never i hi q)]
| (Inr p1, Inr p2, True, Inr (VUntil j q1 q2)) \<Rightarrow> [Inr (VUntil i [p2] p1), p' \<oplus> (Inr p2)]
| (Inr p1, _, False, Inr (VUntil j q1 q2)) \<Rightarrow> [Inr (VUntil i [] p1), Inr (VUntil i q1 q2)]
| (_, Inl p2, True, Inr (VUntil j q1 q2)) \<Rightarrow> [Inl (SUntil [] p2)]
| (Inl p1, Inr p2, True, Inr (VUntil j q1 q2)) \<Rightarrow> [p' \<oplus> (Inr p2)]
| (Inl p1, _, False, Inr (VUntil j q1 q2)) \<Rightarrow> [Inr (VUntil i q1 q2)])"

locale alg = fixes rho :: "'a trace" and
  wqo :: "('a sproof + 'a vproof) \<Rightarrow> ('a sproof + 'a vproof) \<Rightarrow> bool"
  (*and f :: "('a sproof rsproof + 'a vproof rvproof) \<Rightarrow> nat"*)
begin

(* O and C from paper *)
function (sequential) Cand :: "nat \<Rightarrow> 'a mtl \<Rightarrow> ('a sproof + 'a vproof) list"
  and Opt :: "nat \<Rightarrow> 'a mtl \<Rightarrow> ('a sproof + 'a vproof)" where
  "Cand i TT = [Inl (STT i)]"
| "Cand i FF = [Inr (VFF i)]"
| "Cand i (Atom n) = (case n \<in> \<Gamma> rho i of
  True \<Rightarrow> [Inl (SAtm n i)] | False \<Rightarrow> [Inr (VAtm n i)])"
| "Cand i (Disj phi psi) = doDisj (Opt i phi) (Opt i psi)"
| "Cand i (Conj phi psi) = doConj (Opt i phi) (Opt i psi)"
| "Cand i (Impl phi psi) = doImpl (Opt i phi) (Opt i psi)"
| "Cand i (Iff phi psi) = doIff (Opt i phi) (Opt i psi)"
| "Cand i (Neg phi) = (let p = Opt i phi
  in (if isl p then [Inr (VNeg (projl p))] else [Inl (SNeg (projr p))]))"
| "Cand i (Prev I phi) = (if i = 0 then [Inr VPrev_zero]
  else doPrev i I (\<Delta> rho i) (Opt (i-1) phi))"
| "Cand i (Next I phi) = doNext i I (\<Delta> rho (i+1)) (Opt (i+1) phi)"
| "Cand i (Since phi I psi) = (if \<tau> rho i < \<tau> rho 0 + left I then [Inr (VSince_le i)]
  else (let p1 = Opt i phi;
  p2 = Opt i psi
  in (if i = 0 then doSinceBase 0 0 p1 p2
  else if right I \<ge> enat (\<Delta> rho i)
  then doSince i (left I) p1 p2 (Opt (i-1) (Since phi (subtract (\<Delta> rho i) I) psi))
  else doSinceBase i (left I) p1 p2)))"
| "Cand i (Until phi I psi) = (let p1 = Opt i phi;
  p2 = Opt i psi
  in (if right I = \<infinity> then undefined else if right I \<ge> enat (\<Delta> rho (i+1)) then
  doUntil i (left I) p1 p2 (Opt (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi))
  else doUntilBase i (left I) p1 p2))"
| "Cand i (Once I phi) = (if \<tau> rho i < \<tau> rho 0 + left I then [Inr (VOnce_le i)]
  else (let p = Opt i phi in 
  (if i = 0 then doOnceBase 0 0 p
    else if right I \<ge> enat (\<Delta> rho i)
    then doOnce i (left I) p (Opt (i-1) (Once (subtract (\<Delta> rho i) I) phi))
    else doOnceBase i (left I) p)))"
  (*
| "Cand i (MatchP I r) = (if \<tau> rho i < \<tau> rho 0 + left I then [Inr (VMatchP_le i)]
  else (let k = ETP rho (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> \<tau> rho i - n);
  ps = map (\<lambda>x. Optr f Opt x i r) [k ..< Suc (l rho i I)]
  in (if (\<forall>x \<in> set ps. \<not> isl x) then [Inr (VMatchP i (map projr ps))] else
  [Inl (SMatchP (projl (hd (filter isl ps))))])))"
| "Cand i (MatchF I r) = (let k = LTP rho (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> \<tau> rho i + n);
  ps = map (\<lambda>x. Optr f Opt i x r) [lu rho i I ..< Suc k]
  in (if (\<forall>x \<in> set ps. \<not> isl x) then [Inr (VMatchF i (map projr ps))] else
  [Inl (SMatchF (projl (hd (filter isl ps))))]))"
*)
| "Opt i phi = min_list_wrt wqo (Cand i phi)"
  by pat_completeness auto

fun dist where
  "dist i (Since _ _ _) = i"
| "dist i (Once _ _) = i"
| "dist i (Until _ I _) =  LTP rho (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> (\<tau> rho i + n)) - i"
| "dist _ _ = undefined"

termination Cand
  apply (relation "measures
    [\<lambda>args. case args of Inl (_, \<phi>) \<Rightarrow> size \<phi> | Inr (_, \<phi>) \<Rightarrow> size \<phi>,
     \<lambda>args. case args of Inl (i, \<phi>) \<Rightarrow> dist i \<phi> | Inr (i, \<phi>) \<Rightarrow> dist i \<phi>,
     \<lambda>args. case args of Inl _ \<Rightarrow> 0 | Inr _ \<Rightarrow> 1]")
                      apply (auto simp: add.commute termination_simp)
  subgoal for i _ I _ x
  proof (induction i)
    case 0
    then show ?case
      by (simp add: Suc_le_lessD i_ltp_to_tau)
  next
    case (Suc j)
    then have ge0: "\<tau> rho (Suc j) + x \<ge> \<tau> rho 0"
      by (auto simp add: add_increasing add.commute)
    then have "\<tau> rho (Suc (Suc j)) \<le> \<tau> rho (Suc j) + x" using local.Suc by auto
    then have "Suc (Suc j) \<le> LTP rho (\<tau> rho (Suc j) + x)"
      using i_ltp_to_tau ge0 local.Suc by auto
    then show ?case by (simp add: add.commute)
  qed
  done
end

definition "valid rho i phi p = (case p of
    Inl p \<Rightarrow> s_check rho phi p \<and> s_at p = i
  | Inr p \<Rightarrow> v_check rho phi p \<and> v_at p = i)"

inductive checkApp :: "('a sproof + 'a vproof) \<Rightarrow> ('a sproof + 'a vproof) \<Rightarrow> bool" where
  "checkApp (Inl (SSince p1 p2)) (Inl r)"
| "checkApp (Inl (SUntil p1 p2)) (Inl r)"
| "p2 \<noteq> [] \<Longrightarrow> checkApp (Inr (VSince i p1 p2)) (Inr r)"
| "p1 \<noteq> [] \<Longrightarrow> checkApp (Inr (VSince_never i li p1)) (Inr r)"
| "p1 \<noteq> [] \<Longrightarrow> checkApp (Inr (VUntil i p1 p2)) (Inr r)"
| "p1 \<noteq> [] \<Longrightarrow> checkApp (Inr (VUntil_never i hi p1)) (Inr r)"

inductive checkIncr :: "('a sproof + 'a vproof) \<Rightarrow> bool" where
  "v_at p1 \<le> i \<Longrightarrow> (\<And>p. p \<in> set p2 \<Longrightarrow> v_at p \<le> i) \<Longrightarrow> checkIncr (Inr (VSince i p1 p2))"
| "(\<And>p. p \<in> set p1 \<Longrightarrow> v_at p \<le> i) \<Longrightarrow> checkIncr (Inr (VSince_never i li p1))"
| "(\<And>p. p \<in> set p1 \<Longrightarrow> i \<le> v_at p) \<Longrightarrow> i \<le> v_at p2 \<Longrightarrow> checkIncr (Inr (VUntil i p1 p2))"
| "(\<And>p. p \<in> set p1 \<Longrightarrow> i \<le> v_at p) \<Longrightarrow> checkIncr (Inr (VUntil_never i hi p1))"

locale cmonotone = fixes wqo :: "'a sproof + 'a vproof \<Rightarrow> 'a sproof + 'a vproof \<Rightarrow> bool"
  assumes
    SNeg: "\<And>p p'. wqo (Inr p) (Inr p') \<Longrightarrow> wqo (Inl (SNeg p)) (Inl (SNeg p'))"
    and VNeg: "\<And>p p'. wqo (Inl p) (Inl p') \<Longrightarrow> wqo (Inr (VNeg p)) (Inr (VNeg p'))"
    and SDisjL: "\<And>p p'. wqo (Inl p) (Inl p') \<Longrightarrow> wqo (Inl (SDisjL p)) (Inl (SDisjL p'))"
    and SDisjR: "\<And>p p'. wqo (Inl p) (Inl p') \<Longrightarrow> wqo (Inl (SDisjR p)) (Inl (SDisjR p'))"
    and VDisj: "\<And>p1 p1' p2 p2'. wqo (Inr p1) (Inr p1') \<Longrightarrow> wqo (Inr p2) (Inr p2' ) \<Longrightarrow>
  wqo (Inr (VDisj p1 p2)) (Inr (VDisj p1' p2'))"
    and SConj: "\<And>p1 p1' p2 p2'. wqo (Inl p1) (Inl p1') \<Longrightarrow> wqo (Inl p2) (Inl p2' ) \<Longrightarrow>
  wqo (Inl (SConj p1 p2)) (Inl (SConj p1' p2'))"
    and VConjL: "\<And>p p'. wqo (Inr p) (Inr p') \<Longrightarrow> wqo (Inr (VConjL p)) (Inr (VConjL p'))"
    and VConjR: "\<And>p p'. wqo (Inr p) (Inr p') \<Longrightarrow> wqo (Inr (VConjR p)) (Inr (VConjR p'))"
    and SImplR: "\<And>p p'. wqo (Inl p) (Inl p') \<Longrightarrow> wqo (Inl (SImplR p)) (Inl (SImplR p'))"
    and SImplL: "\<And>p p'. wqo (Inr p) (Inr p') \<Longrightarrow> wqo (Inl (SImplL p)) (Inl (SImplL p'))"
    and VImpl: "\<And>p1 p1' p2 p2'. wqo (Inl p1) (Inl p1') \<Longrightarrow> wqo (Inr p2) (Inr p2' ) \<Longrightarrow>
  wqo (Inr (VImpl p1 p2)) (Inr (VImpl p1' p2'))"
    and SIff_ss: "\<And>p1 p1' p2 p2'. wqo (Inl p1) (Inl p1') \<Longrightarrow> wqo (Inl p2) (Inl p2' ) \<Longrightarrow>
  wqo (Inl (SIff_ss p1 p2)) (Inl (SIff_ss p1' p2'))"
    and SIff_vv: "\<And>p1 p1' p2 p2'. wqo (Inr p1) (Inr p1') \<Longrightarrow> wqo (Inr p2) (Inr p2' ) \<Longrightarrow>
  wqo (Inl (SIff_vv p1 p2)) (Inl (SIff_vv p1' p2'))"
    and VIff_sv: "\<And>p1 p1' p2 p2'. wqo (Inl p1) (Inl p1') \<Longrightarrow> wqo (Inr p2) (Inr p2' ) \<Longrightarrow>
  wqo (Inr (VIff_sv p1 p2)) (Inr (VIff_sv p1' p2'))"
    and VIff_vs: "\<And>p1 p1' p2 p2'. wqo (Inr p1) (Inr p1') \<Longrightarrow> wqo (Inl p2) (Inl p2' ) \<Longrightarrow>
  wqo (Inr (VIff_vs p1 p2)) (Inr (VIff_vs p1' p2'))"
    and SOnce: "\<And>i p p'. wqo (Inl p) (Inl p') \<Longrightarrow> wqo (Inl (SOnce i p)) (Inl (SOnce i p'))"
    and VOnce_never: "\<And>i li q q'. wqo (Inr q) (Inr q') \<Longrightarrow>
  wqo (Inr (VOnce_never i li [q])) (Inr (VOnce_never i li [q']))"
    and SSince: "\<And>p p'. wqo (Inl p) (Inl p') \<Longrightarrow> wqo (Inl (SSince p [])) (Inl (SSince p' []))"
    and VSince_Nil: "\<And>i p p'. wqo (Inr p) (Inr p') \<Longrightarrow> wqo (Inr (VSince i p [])) (Inr (VSince i p' []))"
    and VSince: "\<And>i p p' q q'. wqo (Inr p) (Inr p') \<Longrightarrow> wqo (Inr q) (Inr q') \<Longrightarrow>
  wqo (Inr (VSince i p [q])) (Inr (VSince i p' [q']))"
    and VSince_never: "\<And>i li q q'. wqo (Inr q) (Inr q') \<Longrightarrow>
  wqo (Inr (VSince_never i li [q])) (Inr (VSince_never i li [q']))"
    and SUntil_Nil: "\<And>p p'. wqo (Inl p) (Inl p') \<Longrightarrow>
  wqo (Inl (SUntil [] p)) (Inl (SUntil [] p'))"
    and SUntil: "\<And>p p' q q'. wqo (Inl p) (Inl p') \<Longrightarrow> wqo (Inl q) (Inl q') \<Longrightarrow>
  wqo (Inl (SUntil [q] p)) (Inl (SUntil [q'] p'))"
    and VUntil_Nil: "\<And>i p p'. wqo (Inr p) (Inr p') \<Longrightarrow>
  wqo (Inr (VUntil i [] p)) (Inr (VUntil i [] p'))"
    and VUntil: "\<And>i p p' q q'. wqo (Inr p) (Inr p') \<Longrightarrow> wqo (Inr q) (Inr q') \<Longrightarrow>
  wqo (Inr (VUntil i [q] p)) (Inr (VUntil i [q'] p'))"
    and VUntil_never: "\<And>i hi q q'. wqo (Inr q) (Inr q') \<Longrightarrow>
  wqo (Inr (VUntil_never i hi [q])) (Inr (VUntil_never i hi [q']))"
    and SNext: "\<And>p p'. wqo (Inl p) (Inl p') \<Longrightarrow> wqo (Inl (SNext p)) (Inl (SNext p'))"
    and VNext: "\<And>p p'. wqo (Inr p) (Inr p') \<Longrightarrow> wqo (Inr (VNext p)) (Inr (VNext p'))"
    and SPrev: "\<And>p p'. wqo (Inl p) (Inl p') \<Longrightarrow> wqo (Inl (SPrev p)) (Inl (SPrev p'))"
    and VPrev: "\<And>p p'. wqo (Inr p) (Inr p') \<Longrightarrow> wqo (Inr (VPrev p)) (Inr (VPrev p'))"
    and proofApp_mono: "\<And>i phi p p' r r'. checkApp p r \<Longrightarrow> checkApp p' r' \<Longrightarrow> wqo p p' \<Longrightarrow> wqo r r' \<Longrightarrow>
  valid rho i phi (p \<oplus> r) \<Longrightarrow> valid rho i phi (p' \<oplus> r') \<Longrightarrow> wqo (p \<oplus> r) (p' \<oplus> r')"
    and proofIncr_mono: "\<And>i phi p p'. checkIncr p \<Longrightarrow> checkIncr p' \<Longrightarrow> wqo p p' \<Longrightarrow>
  valid rho i phi p \<Longrightarrow> valid rho i phi p' \<Longrightarrow> wqo (proofIncr p) (proofIncr p')"

(* Algorithm lemmas  *)
locale trans_wqo = cmonotone wqo + alg (*sp mc*) rho wqo (*f + algr sp mc f Opt "s_check rho" "v_check rho" s_at v_at*)
  for (*sp mc*) wqo rho (*f*) +
  assumes refl_wqo: "reflp wqo"
    and trans_wqo: "transp wqo"
    and pw_total: "\<And>i \<phi>. total_on wqo {p. valid rho i \<phi> p}"
begin

(*
lemma "valid rho i (Since phi I psi) p \<Longrightarrow> valid rho (i+1) phi r \<Longrightarrow> valid rho i (Since phi I psi) (p \<oplus> r)"
  apply (auto simp: valid_def proofApp_def split: sum.splits)
*)

lemma valid_SinceE: "valid rho i (Since phi I psi) p \<Longrightarrow>
  (\<And>spsi sphis. p = Inl (SSince spsi sphis) \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i vphi vpsis. p = Inr (VSince i vphi vpsis) \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i li vpsis. p = Inr (VSince_never i li vpsis) \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i. p = Inr (VSince_le i) \<Longrightarrow> P) \<Longrightarrow> P"
  apply (cases p)
  subgoal for x
    by (cases x) (auto simp: valid_def)
  subgoal for x
    by (cases x) (auto simp: valid_def)
  done

lemma valid_UntilE: "
  valid rho i (Until phi I psi) p \<Longrightarrow>
  (\<And>spsi sphis. p = Inl (SUntil spsi sphis) \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i vphi vpsis. p = Inr (VUntil i vphi vpsis) \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i hi vpsis. p = Inr (VUntil_never i hi vpsis) \<Longrightarrow> P) \<Longrightarrow> P"
  apply (cases p)
  subgoal for x
    by (cases x) (auto simp: valid_def)
  subgoal for x
    by (cases x) (auto simp: valid_def)
  done

simps_of_case proofApp_simps[simp]: proofApp_def

lemma not_wqo:
  "valid rho i phi p1 \<Longrightarrow> valid rho i phi p2 \<Longrightarrow> \<not> wqo p1 p2 \<Longrightarrow> wqo p2 p1"
  using pw_total trans_wqo refl_wqo
  by (metis mem_Collect_eq reflpD total_on_def)

definition "optimal i phi p = (valid rho i phi p \<and> (\<forall>q. valid rho i phi q \<longrightarrow> wqo p q))"

lemma check_consistent:
  assumes bf: "bounded_future phi"
  shows "s_check rho phi p \<Longrightarrow> s_at p = v_at q \<Longrightarrow> \<not> v_check rho phi q"
  by (auto simp only: s_at.simps list.case dest!: check_sound
      soundness[THEN conjunct1, THEN mp]
      soundness[THEN conjunct2, THEN mp])

lemma val_SAT_imp_l:
  assumes bf: "bounded_future phi" and
    val: " valid rho i phi p" and sat: "SAT rho i phi"
  shows "\<exists>a. p = Inl a"
  using check_consistent[OF bf] check_complete[OF bf] assms unfolding valid_def
  apply (cases p) apply auto
  by blast

lemma val_VIO_imp_r:
  assumes bf: "bounded_future phi" and
    val: "valid rho i phi p" and vio: "VIO rho i phi"
  shows "\<exists>a. p = Inr a"
  using check_consistent[OF bf] check_complete[OF bf] assms unfolding valid_def
  apply (cases p) apply auto
  by fastforce

(* Lemma 30 *)
lemma disj_sound:
  assumes p1_def: "optimal i phi p1" and p2_def: "optimal i psi p2"
    and p_def: "p \<in> set (doDisj p1 p2)"
  shows "valid rho i (Disj phi psi) p"
proof (cases p1)
  case (Inl a)
  then have p1s: "p1 = Inl a" by auto
  then show ?thesis
  proof (cases p2)
    case (Inl a2)
    then have sp: "p = Inl (SDisjL a) \<or> p = Inl (SDisjR a2)"
      using p_def p1s local.Inl unfolding doDisj_def valid_def by auto
    then show ?thesis using Inl p_def p1_def p2_def p1s
      unfolding optimal_def valid_def
      by auto
  next
    case (Inr b2)
    then have "p = Inl (SDisjL a)"
      using p_def local.Inl unfolding doDisj_def by simp
    then show ?thesis using p_def p1_def p2_def p1s Inr
      unfolding optimal_def valid_def by auto
  qed
next
  case (Inr b)
  then have p1v: "p1 = Inr b" by auto
  then show ?thesis
  proof (cases p2)
    case (Inl a2)
    then have "p = Inl (SDisjR a2)" using p_def Inr unfolding doDisj_def
      by auto
    then show ?thesis using p2_def Inl p1_def p_def
      unfolding optimal_def valid_def by auto
  next
    case (Inr b2)
    then have "p = Inr (VDisj b b2)" using p_def p1v unfolding doDisj_def
      by auto
    then show ?thesis using p_def p1_def p2_def local.Inr p1v
      unfolding optimal_def valid_def by auto
  qed
qed

lemma disj_optimal:
  assumes bf: "bounded_future (Disj phi psi)" and
    p1_def: "optimal i phi p1" and p2_def: "optimal i psi p2"
  shows "optimal i (Disj phi psi) (min_list_wrt wqo (doDisj p1 p2))"
proof (rule ccontr)
  have bf_phi: "bounded_future phi"
    using bf by auto
  have bf_psi: "bounded_future psi"
    using bf by auto
  from p1_def p2_def have nnil: "doDisj p1 p2 \<noteq> []"
    using doDisj_def[of p1 p2]
    by (cases p1; cases p2; auto)
  assume nopt: "\<not> optimal i (Disj phi psi) (min_list_wrt wqo (doDisj p1 p2))"
  from disj_sound[OF p1_def p2_def min_list_wrt_in[of "doDisj p1 p2" wqo]]
    refl_wqo trans_wqo pw_total nnil
  have vmin: "valid rho i (Disj phi psi) (min_list_wrt wqo (doDisj p1 p2))"
    apply auto
    by (metis disj_sound not_wqo p1_def p2_def total_onI)
  from this nopt obtain q where q_val: "valid rho i (Disj phi psi) q" and
    q_le: "\<not> wqo (min_list_wrt wqo (doDisj p1 p2)) q"
    unfolding optimal_def by auto
  then have "wqo (min_list_wrt wqo (doDisj p1 p2)) q"
  proof(cases q)
    case (Inl a)
    {fix p
      assume al: "a = SDisjL p"
      then have p_val: "valid rho i phi (Inl p)" using q_val Inl unfolding valid_def by auto
      obtain p1' where p1'_def: "p1 = Inl p1'"
        using p_val p1_def check_consistent[OF bf_phi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      have "wqo p1 (Inl p)" using p_val p1_def unfolding optimal_def by auto
      then have "wqo (Inl (SDisjL (projl p1))) q"
        using al Inl SDisjL p1'_def by auto
      moreover have "Inl (SDisjL (projl p1)) \<in> set (doDisj p1 p2)"
        using p1_def p2_def bf check_consistent[of phi] check_consistent[of psi] p_val
        by (auto simp add: doDisj_def optimal_def valid_def split: sum.splits)
      ultimately have "wqo (min_list_wrt wqo (doDisj p1 p2)) q"
        using min_list_wrt_le[OF _ refl_wqo]
          disj_sound[OF p1_def p2_def] pw_total[of i "Disj phi psi"] trans_wqo
        by (metis not_wqo total_on_def transpE)
    } note * = this
    {fix p
      assume ar: "a = SDisjR p"
      then have p_val: "valid rho i psi (Inl p)" using q_val Inl unfolding valid_def by auto
      obtain p2' where p2'_def: "p2 = Inl p2'"
        using p_val p2_def check_consistent[OF bf_psi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      have "wqo p2 (Inl p)" using p_val p2_def unfolding optimal_def by auto
      then have "wqo (Inl (SDisjR (projl p2))) q"
        using ar Inl SDisjR p2'_def by auto
      moreover have "Inl (SDisjR (projl p2)) \<in> set (doDisj p1 p2)"
        using p1_def p2_def bf check_consistent[of phi] check_consistent[of psi] p_val
        by (auto simp add: doDisj_def optimal_def valid_def split: sum.splits)
      ultimately have "wqo (min_list_wrt wqo (doDisj p1 p2)) q"
        using min_list_wrt_le[OF _ refl_wqo]
          disj_sound[OF p1_def p2_def] pw_total[of i "Disj phi psi"] trans_wqo
        by (metis not_wqo total_on_def transpE)
    } note ** = this
    then show ?thesis using * ** q_val Inl unfolding valid_def doDisj_def
      by (cases a) auto
  next
    case (Inr b)
    then obtain p and p' where formq: "b = VDisj p p'" using q_val
      unfolding valid_def by (cases b) auto
    then have p_val: "valid rho i phi (Inr p) \<and> valid rho i psi (Inr p')" using q_val Inr
      unfolding valid_def by auto
    then have sub: "wqo p1 (Inr p) \<and> wqo p2 (Inr p')" using p1_def p2_def formq
      unfolding optimal_def by auto
    obtain p1' where p1'_def: "p1 = Inr p1'"
      using p_val p1_def check_consistent[OF bf_phi]
      by (auto simp add: optimal_def valid_def split: sum.splits)
    obtain p2' where p2'_def: "p2 = Inr p2'"
      using p_val p2_def check_consistent[OF bf_psi]
      by (auto simp add: optimal_def valid_def split: sum.splits)
    have "wqo (Inr (VDisj (projr p1) (projr p2))) (Inr b)"
      using formq VDisj p1'_def p2'_def sub by auto
    moreover have "Inr (VDisj (projr p1) (projr p2)) \<in> set (doDisj p1 p2)"
      using p1_def p2_def bf check_consistent[of phi] check_consistent[of psi] p_val
      by (auto simp add: doDisj_def optimal_def valid_def split: sum.splits)
    ultimately show ?thesis
      using min_list_wrt_le[OF _ refl_wqo] disj_sound[OF p1_def p2_def]
        pw_total[of i "Disj phi psi"] trans_wqo Inr
      apply (auto simp add: total_on_def)
      by (metis transpD)
  qed
  then show False using q_le by auto
qed

(* Lemma ?? *)
lemma conj_sound:
  assumes p1_def: "optimal i phi p1" and p2_def: "optimal i psi p2"
    and p_def: "p \<in> set (doConj p1 p2)"
  shows "valid rho i (Conj phi psi) p"
proof (cases p1)
  case (Inr a)
  then have p1s: "p1 = Inr a" by auto
  then show ?thesis
  proof (cases p2)
    case (Inr a2)
    then have vp: "p = Inr (VConjL a) \<or> p = Inr (VConjR a2)"
      using p_def p1s local.Inr unfolding doConj_def valid_def by auto
    then show ?thesis using Inr p_def p1_def p2_def p1s
      unfolding optimal_def valid_def
      by auto
  next
    case (Inl b2)
    then have "p = Inr (VConjL a)"
      using p_def p1s local.Inl unfolding doConj_def by simp
    then show ?thesis using p_def p1_def p2_def p1s Inr
      unfolding optimal_def valid_def by auto
  qed
next
  case (Inl b)
  then have p1v: "p1 = Inl b" by auto
  then show ?thesis
  proof (cases p2)
    case (Inr a2)
    then have "p = Inr (VConjR a2)" using p_def Inl unfolding doConj_def
      by auto
    then show ?thesis using p2_def Inr p1_def p_def
      unfolding optimal_def valid_def by auto
  next
    case (Inl b2)
    then have "p = Inl (SConj b b2)" using p_def p1v unfolding doConj_def
      by auto
    then show ?thesis using p_def p1_def p2_def local.Inl p1v
      unfolding optimal_def valid_def by auto
  qed
qed

lemma conj_optimal:
  assumes bf: "bounded_future (Conj phi psi)" and
    p1_def: "optimal i phi p1" and p2_def: "optimal i psi p2"
  shows "optimal i (Conj phi psi) (min_list_wrt wqo (doConj p1 p2))"
proof (rule ccontr)
  have bf_phi: "bounded_future phi"
    using bf by auto
  have bf_psi: "bounded_future psi"
    using bf by auto
  from p1_def p2_def have nnil: "doConj p1 p2 \<noteq> []"
    using doConj_def[of p1 p2]
    by (cases p1; cases p2; auto)
  assume nopt: "\<not> optimal i (Conj phi psi) (min_list_wrt wqo (doConj p1 p2))"
  from conj_sound[OF p1_def p2_def min_list_wrt_in[of "doConj p1 p2" wqo]]
    refl_wqo trans_wqo pw_total nnil
  have vmin: "valid rho i (Conj phi psi) (min_list_wrt wqo (doConj p1 p2))"
    apply auto
    by (metis conj_sound not_wqo p1_def p2_def total_onI)
  from this nopt obtain q where q_val: "valid rho i (Conj phi psi) q" and
    q_le: "\<not> wqo (min_list_wrt wqo (doConj p1 p2)) q"
    unfolding optimal_def by auto
  then have "wqo (min_list_wrt wqo (doConj p1 p2)) q"
  proof(cases q)
    case (Inr a)
    {fix p
      assume al: "a = VConjL p"
      then have p_val: "valid rho i phi (Inr p)" using q_val Inr unfolding valid_def by auto
      obtain p1' where p1'_def: "p1 = Inr p1'"
        using p_val p1_def check_consistent[OF bf_phi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      have "wqo p1 (Inr p)" using p_val p1_def unfolding optimal_def by auto
      then have "wqo (Inr (VConjL (projr p1))) q"
        using al Inr VConjL p1'_def by auto
      moreover have "Inr (VConjL (projr p1)) \<in> set (doConj p1 p2)"
        using p1_def p2_def bf check_consistent[of phi] check_consistent[of psi] p_val
        by (auto simp add: doConj_def optimal_def valid_def split: sum.splits)
      ultimately have "wqo (min_list_wrt wqo (doConj p1 p2)) q"
        using min_list_wrt_le[OF _ refl_wqo]
          conj_sound[OF p1_def p2_def] pw_total[of i "Conj phi psi"] trans_wqo
        by (metis not_wqo total_on_def transpE)
    } note * = this
    {fix p
      assume ar: "a = VConjR p"
      then have p_val: "valid rho i psi (Inr p)" using q_val Inr unfolding valid_def by auto
      obtain p2' where p2'_def: "p2 = Inr p2'"
        using p_val p2_def check_consistent[OF bf_psi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      have "wqo p2 (Inr p)" using p_val p2_def unfolding optimal_def by auto
      then have "wqo (Inr (VConjR (projr p2))) q"
        using ar Inr VConjR p2'_def by auto
      moreover have "Inr (VConjR (projr p2)) \<in> set (doConj p1 p2)"
        using p1_def p2_def bf check_consistent[of phi] check_consistent[of psi] p_val
        by (auto simp add: doConj_def optimal_def valid_def split: sum.splits)
      ultimately have "wqo (min_list_wrt wqo (doConj p1 p2)) q"
        using min_list_wrt_le[OF _ refl_wqo]
          conj_sound[OF p1_def p2_def] pw_total[of i "Conj phi psi"] trans_wqo
        by (metis not_wqo total_on_def transpE)
    } note ** = this
    then show ?thesis using * ** q_val Inr unfolding valid_def doConj_def
      by (cases a) auto
  next
    case (Inl b)
    then obtain p and p' where formq: "b = SConj p p'" using q_val
      unfolding valid_def by (cases b) auto
    then have p_val: "valid rho i phi (Inl p) \<and> valid rho i psi (Inl p')" using q_val Inl
      unfolding valid_def by auto
    then have sub: "wqo p1 (Inl p) \<and> wqo p2 (Inl p')" using p1_def p2_def formq
      unfolding optimal_def by auto
    obtain p1' where p1'_def: "p1 = Inl p1'"
      using p_val p1_def check_consistent[OF bf_phi]
      by (auto simp add: optimal_def valid_def split: sum.splits)
    obtain p2' where p2'_def: "p2 = Inl p2'"
      using p_val p2_def check_consistent[OF bf_psi]
      by (auto simp add: optimal_def valid_def split: sum.splits)
    have "wqo (Inl (SConj (projl p1) (projl p2))) (Inl b)"
      using formq SConj p1'_def p2'_def sub by auto
    moreover have "Inl (SConj (projl p1) (projl p2)) \<in> set (doConj p1 p2)"
      using p1_def p2_def bf check_consistent[of phi] check_consistent[of psi] p_val
      by (auto simp add: doConj_def optimal_def valid_def split: sum.splits)
    ultimately show ?thesis
      using min_list_wrt_le[OF _ refl_wqo] conj_sound[OF p1_def p2_def]
        pw_total[of i "Conj phi psi"] trans_wqo Inl
      apply (auto simp add: total_on_def)
      by (metis transpD)
  qed
  then show False using q_le by auto
qed

lemma impl_sound:
  assumes p1_def: "optimal i phi p1" and p2_def: "optimal i psi p2"
    and p_def: "p \<in> set (doImpl p1 p2)"
  shows "valid rho i (Impl phi psi) p"
proof (cases p1)
  case (Inr va)
  then have vp1: "p1 = Inr va" 
    by simp
  then show ?thesis
  proof (cases p2)
    case (Inr vb)
    then have sp: "p = Inl (SImplL va)"
      using p_def vp1 Inr unfolding doImpl_def valid_def 
      by simp
    then show ?thesis using Inr p_def p1_def p2_def vp1
      unfolding optimal_def valid_def
      by simp
  next
    case (Inl sb)
    then have sp: "p = Inl (SImplL va) \<or> p = Inl (SImplR sb)"
      using p_def vp1 Inl unfolding doImpl_def valid_def
      by simp
    then show ?thesis using Inl p_def p1_def p2_def vp1
      unfolding optimal_def valid_def 
      by auto
  qed
next
  case (Inl sa)
  then have sp1: "p1 = Inl sa" 
    by simp
  then show ?thesis
  proof (cases p2)
    case (Inr vb)
    then have vp: "p = Inr (VImpl sa vb)" 
      using p_def Inl unfolding doImpl_def 
      by simp
    then show ?thesis using Inr p_def p1_def p2_def sp1
      unfolding optimal_def valid_def 
      by simp
  next
    case (Inl sb)
    then have sp: "p = Inl (SImplR sb)"
      using p_def Inl sp1 unfolding doImpl_def
      by simp
    then show ?thesis using Inl p_def p1_def p2_def sp1
      unfolding optimal_def valid_def 
      by simp
  qed
qed

lemma impl_optimal:
  assumes bf: "bounded_future (Impl phi psi)" and
    p1_def: "optimal i phi p1" and p2_def: "optimal i psi p2"
  shows "optimal i (Impl phi psi) (min_list_wrt wqo (doImpl p1 p2))"
proof(rule ccontr)
  have bf_phi: "bounded_future phi"
    using bf by auto
  have bf_psi: "bounded_future psi"
    using bf by auto
  from p1_def p2_def have nnil: "doImpl p1 p2 \<noteq> []"
    using doImpl_def[of p1 p2]
    by (cases p1; cases p2; auto)
  assume nopt: "\<not> optimal i (Impl phi psi) (min_list_wrt wqo (doImpl p1 p2))"
  from impl_sound[OF p1_def p2_def min_list_wrt_in[of "doImpl p1 p2" wqo]]
    refl_wqo trans_wqo pw_total nnil
  have vmin: "valid rho i (Impl phi psi) (min_list_wrt wqo (doImpl p1 p2))"
    apply auto
    by (metis impl_sound not_wqo p1_def p2_def total_onI)
  from this nopt 
  obtain q where q_val: "valid rho i (Impl phi psi) q" and
    q_le: "\<not> wqo (min_list_wrt wqo (doImpl p1 p2)) q"
    unfolding optimal_def 
    by auto
  then have "wqo (min_list_wrt wqo (doImpl p1 p2)) q"
  proof(cases q)
    case (Inr a)
    then obtain p and p' where formq: "a = VImpl p p'" using q_val
      unfolding valid_def by (cases a) auto
    then have p_val: "valid rho i phi (Inl p) \<and> valid rho i psi (Inr p')" using q_val Inr
      unfolding valid_def by auto
    then have sub: "wqo p1 (Inl p) \<and> wqo p2 (Inr p')" using p1_def p2_def formq
      unfolding optimal_def by auto
    obtain p1' where p1'_def: "p1 = Inl p1'"
      using p_val p1_def check_consistent[OF bf_phi]
      by (auto simp add: optimal_def valid_def split: sum.splits)
    obtain p2' where p2'_def: "p2 = Inr p2'"
      using p_val p2_def check_consistent[OF bf_psi]
      by (auto simp add: optimal_def valid_def split: sum.splits)
    have "wqo (Inr (VImpl (projl p1) (projr p2))) (Inr a)"
      using formq VImpl p1'_def p2'_def sub by auto
    moreover have "Inr (VImpl (projl p1) (projr p2)) \<in> set (doImpl p1 p2)"
      using p1_def p2_def bf check_consistent[of phi] check_consistent[of psi] p_val
      by (auto simp add: doImpl_def optimal_def valid_def split: sum.splits)
    ultimately show ?thesis
      using min_list_wrt_le[OF _ refl_wqo] impl_sound[OF p1_def p2_def]
        pw_total[of i "Impl phi psi"] trans_wqo Inr
      apply (auto simp add: total_on_def)
      by (metis transpD)
  next
    case (Inl b)
    {fix p
      assume al: "b = SImplL p"
      then have p_val: "valid rho i phi (Inr p)" using q_val Inl unfolding valid_def 
        by auto
      obtain p1' where p1'_def: "p1 = Inr p1'"
        using p_val p1_def check_consistent[OF bf_phi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      have "wqo p1 (Inr p)" using p_val p1_def unfolding optimal_def by auto
      then have "wqo (Inl (SImplL (projr p1))) q"
        using al Inl SImplL p1'_def by auto
      moreover have "Inl (SImplL (projr p1)) \<in> set (doImpl p1 p2)"
        using p1_def p2_def bf check_consistent[of phi] check_consistent[of psi] p_val
        by (auto simp add: doImpl_def optimal_def valid_def split: sum.splits)
      ultimately have "wqo (min_list_wrt wqo (doImpl p1 p2)) q"
        using min_list_wrt_le[OF _ refl_wqo]
          impl_sound[OF p1_def p2_def] pw_total[of i "Impl phi psi"] trans_wqo
        by (metis not_wqo total_on_def transpE)
    } note * = this
    {fix p
      assume ar: "b = SImplR p"
      then have p_val: "valid rho i psi (Inl p)" using q_val Inl unfolding valid_def by auto
      obtain p2' where p2'_def: "p2 = Inl p2'"
        using p_val p2_def check_consistent[OF bf_psi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      have "wqo p2 (Inl p)" using p_val p2_def unfolding optimal_def by auto
      then have "wqo (Inl (SImplR (projl p2))) q"
        using ar Inl SImplR p2'_def by auto
      moreover have "Inl (SImplR (projl p2)) \<in> set (doImpl p1 p2)"
        using p1_def p2_def bf check_consistent[of phi] check_consistent[of psi] p_val
        by (auto simp add: doImpl_def optimal_def valid_def split: sum.splits)
      ultimately have "wqo (min_list_wrt wqo (doImpl p1 p2)) q"
        using min_list_wrt_le[OF _ refl_wqo]
          impl_sound[OF p1_def p2_def] pw_total[of i "Impl phi psi"] trans_wqo
        by (metis not_wqo total_on_def transpE)
    } note ** = this
    then show ?thesis using * ** q_val Inl unfolding valid_def doImpl_def
      by (cases b) auto
  qed
  then show False using q_le by auto
qed

lemma iff_sound:
  assumes p1_def: "optimal i phi p1" and p2_def: "optimal i psi p2"
    and p_def: "p \<in> set (doIff p1 p2)"
  shows "valid rho i (Iff phi psi) p"
proof (cases p1)
  case (Inr va)
  then have vp1: "p1 = Inr va" 
    by simp
  then show ?thesis
  proof (cases p2)
    case (Inr vb)
    then have sp: "p = Inl (SIff_vv va vb)"
      using p_def vp1 unfolding doIff_def valid_def 
      by simp
    then show ?thesis using Inr p_def p1_def p2_def vp1
      unfolding optimal_def valid_def
      by simp
  next
    case (Inl sb)
    then have vp: "p = Inr (VIff_vs va sb)"
      using p_def vp1 Inl unfolding doIff_def valid_def
      by simp
    then show ?thesis using Inl p_def p1_def p2_def vp1
      unfolding optimal_def valid_def 
      by simp
  qed
next
  case (Inl sa)
  then have sp1: "p1 = Inl sa" 
    by simp
  then show ?thesis
  proof (cases p2)
    case (Inr vb)
    then have vp: "p = Inr (VIff_sv sa vb)" 
      using p_def Inl unfolding doIff_def 
      by simp
    then show ?thesis using Inr p_def p1_def p2_def sp1
      unfolding optimal_def valid_def 
      by simp
  next
    case (Inl sb)
    then have sp: "p = Inl (SIff_ss sa sb)"
      using p_def Inl sp1 unfolding doIff_def
      by simp
    then show ?thesis using Inl p_def p1_def p2_def sp1
      unfolding optimal_def valid_def 
      by simp
  qed
qed

lemma iff_optimal:
  assumes bf: "bounded_future (Iff phi psi)" and
    p1_def: "optimal i phi p1" and p2_def: "optimal i psi p2"
  shows "optimal i (Iff phi psi) (min_list_wrt wqo (doIff p1 p2))"
proof(rule ccontr)
  have bf_phi: "bounded_future phi"
    using bf by auto
  have bf_psi: "bounded_future psi"
    using bf by auto
  from p1_def p2_def have nnil: "doIff p1 p2 \<noteq> []"
    using doIff_def[of p1 p2]
    by (cases p1; cases p2; auto)
  assume nopt: "\<not> optimal i (Iff phi psi) (min_list_wrt wqo (doIff p1 p2))"
  from iff_sound[OF p1_def p2_def min_list_wrt_in[of "doIff p1 p2" wqo]]
    refl_wqo trans_wqo pw_total nnil
  have vmin: "valid rho i (Iff phi psi) (min_list_wrt wqo (doIff p1 p2))"
    apply auto
    by (metis iff_sound not_wqo p1_def p2_def total_onI)
  from this nopt
  obtain q where q_val: "valid rho i (Iff phi psi) q" and
    q_le: "\<not> wqo (min_list_wrt wqo (doIff p1 p2)) q"
    unfolding optimal_def 
    by auto
  then have "wqo (min_list_wrt wqo (doIff p1 p2)) q"
  proof(cases q)
    case (Inr a)
    {fix p p'
      assume formq: "a = VIff_sv p p'"
      then have p_val: "valid rho i phi (Inl p) \<and> valid rho i psi (Inr p')" using q_val Inr
        unfolding valid_def by auto
      then have sub: "wqo p1 (Inl p) \<and> wqo p2 (Inr p')" using p1_def p2_def formq
        unfolding optimal_def by auto
      obtain p1' where p1'_def: "p1 = Inl p1'"
        using p_val p1_def check_consistent[OF bf_phi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      obtain p2' where p2'_def: "p2 = Inr p2'"
        using p_val p2_def check_consistent[OF bf_psi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      have "wqo (Inr (VIff_sv (projl p1) (projr p2))) (Inr a)"
        using formq VIff_sv p1'_def p2'_def sub by auto
      moreover have "Inr (VIff_sv (projl p1) (projr p2)) \<in> set (doIff p1 p2)"
        using p1_def p2_def bf check_consistent[of phi] check_consistent[of psi] p_val
        by (auto simp add: doIff_def optimal_def valid_def split: sum.splits)
      ultimately have "wqo (min_list_wrt wqo (doIff p1 p2)) q"
        using min_list_wrt_le[OF _ refl_wqo] iff_sound[OF p1_def p2_def]
          pw_total[of i "Iff phi psi"] trans_wqo Inr
        by (metis not_wqo total_on_def transpE)
    } note * = this
    {fix p p'
      assume formq: "a = VIff_vs p p'"
      then have p_val: "valid rho i phi (Inr p) \<and> valid rho i psi (Inl p')" using q_val Inr
        unfolding valid_def by auto
      then have sub: "wqo p1 (Inr p) \<and> wqo p2 (Inl p')" using p1_def p2_def formq
        unfolding optimal_def by auto
      obtain p1' where p1'_def: "p1 = Inr p1'"
        using p_val p1_def check_consistent[OF bf_phi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      obtain p2' where p2'_def: "p2 = Inl p2'"
        using p_val p2_def check_consistent[OF bf_psi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      have "wqo (Inr (VIff_vs (projr p1) (projl p2))) (Inr a)"
        using formq VIff_vs p1'_def p2'_def sub by auto
      moreover have "Inr (VIff_vs (projr p1) (projl p2)) \<in> set (doIff p1 p2)"
        using p1_def p2_def bf check_consistent[of phi] check_consistent[of psi] p_val
        by (auto simp add: doIff_def optimal_def valid_def split: sum.splits)
      ultimately have "wqo (min_list_wrt wqo (doIff p1 p2)) q"
        using min_list_wrt_le[OF _ refl_wqo] iff_sound[OF p1_def p2_def]
          pw_total[of i "Iff phi psi"] trans_wqo Inr
        by (metis not_wqo total_on_def transpE)
    } note ** = this
    then show ?thesis using * ** q_val Inr unfolding valid_def doIff_def
      by (cases a) auto
  next
    case (Inl b)
    {fix p p'
      assume formq: "b = SIff_ss p p'"
      then have p_val: "valid rho i phi (Inl p) \<and> valid rho i psi (Inl p')" using q_val Inl
        unfolding valid_def by auto
      then have sub: "wqo p1 (Inl p) \<and> wqo p2 (Inl p')" using p1_def p2_def formq
        unfolding optimal_def by auto
      obtain p1' where p1'_def: "p1 = Inl p1'"
        using p_val p1_def check_consistent[OF bf_phi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      obtain p2' where p2'_def: "p2 = Inl p2'"
        using p_val p2_def check_consistent[OF bf_psi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      have "wqo (Inl (SIff_ss (projl p1) (projl p2))) (Inl b)"
        using formq SIff_ss p1'_def p2'_def sub by auto
      moreover have "Inl (SIff_ss (projl p1) (projl p2)) \<in> set (doIff p1 p2)"
        using p1_def p2_def bf check_consistent[of phi] check_consistent[of psi] p_val
        by (auto simp add: doIff_def optimal_def valid_def split: sum.splits)
      ultimately have "wqo (min_list_wrt wqo (doIff p1 p2)) q"
        using min_list_wrt_le[OF _ refl_wqo] iff_sound[OF p1_def p2_def]
          pw_total[of i "Iff phi psi"] trans_wqo Inl
        by (metis not_wqo total_on_def transpE)
    } note * = this
    {fix p p'
      assume formq: "b = SIff_vv p p'"
      then have p_val: "valid rho i phi (Inr p) \<and> valid rho i psi (Inr p')" using q_val Inl
        unfolding valid_def by auto
      then have sub: "wqo p1 (Inr p) \<and> wqo p2 (Inr p')" using p1_def p2_def formq
        unfolding optimal_def by auto
      obtain p1' where p1'_def: "p1 = Inr p1'"
        using p_val p1_def check_consistent[OF bf_phi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      obtain p2' where p2'_def: "p2 = Inr p2'"
        using p_val p2_def check_consistent[OF bf_psi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      have "wqo (Inl (SIff_vv (projr p1) (projr p2))) (Inl b)"
        using formq SIff_vv p1'_def p2'_def sub by auto
      moreover have "Inl(SIff_vv (projr p1) (projr p2)) \<in> set (doIff p1 p2)"
        using p1_def p2_def bf check_consistent[of phi] check_consistent[of psi] p_val
        by (auto simp add: doIff_def optimal_def valid_def split: sum.splits)
      ultimately have "wqo (min_list_wrt wqo (doIff p1 p2)) q"
        using min_list_wrt_le[OF _ refl_wqo] iff_sound[OF p1_def p2_def]
          pw_total[of i "Iff phi psi"] trans_wqo Inl
        by (metis not_wqo total_on_def transpE)
    } note ** = this
    then show ?thesis using * ** q_val Inl unfolding valid_def doIff_def
      by (cases b) auto
  qed
  then show False using q_le by auto
qed

lemma onceBase0_sound:
  assumes p1_def: "optimal i phi p1" and
    i_props: "i = 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I" and
    p_def: "p \<in> set (doOnceBase 0 0 p1)"
  shows "valid rho i (Once I phi) p"
  using assms unfolding optimal_def valid_def
  apply (auto simp: i_etp_to_tau doOnceBase_def zero_enat_def[symmetric] split: sum.splits enat.splits)
  apply (meson Orderings.order_class.order.not_eq_order_implies_strict diff_le_self i_etp_to_tau less_nat_zero_code)
  done

lemma onceBase0_optimal:
  assumes bf: "bounded_future (Once I phi)" and
    p1_def: "optimal i phi p1" and
    i_props: "i = 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I"
  shows
    "optimal i (Once I phi) (min_list_wrt wqo (doOnceBase 0 0 p1))"
proof (rule ccontr)
  have bf_phi: "bounded_future phi"
    using bf by auto
  from doOnceBase_def[of 0 0 p1]
  have nnil: "doOnceBase 0 0 p1 \<noteq> []"
    by (cases p1; auto)
  assume nopt: "\<not> optimal i (Once I phi) (min_list_wrt wqo (doOnceBase 0 0 p1))"
  from onceBase0_sound[OF p1_def i_props min_list_wrt_in[of _ wqo]]
    refl_wqo pw_total trans_wqo nnil
  have vmin: "valid rho i (Once I phi) (min_list_wrt wqo (doOnceBase 0 0 p1))"
    apply auto
    by (metis i_props not_wqo p1_def onceBase0_sound total_onI)
  then obtain q where q_val: "valid rho i (Once I phi) q" and
    q_le: "\<not> wqo (min_list_wrt wqo (doOnceBase 0 0 p1)) q" using nopt
    unfolding optimal_def by auto
  then have "wqo (min_list_wrt wqo (doOnceBase 0 0 p1)) q"
  proof (cases q)
    case (Inl a)
    then obtain sphiq where sq: "a = SOnce i sphiq"
      using q_val unfolding valid_def
      by (cases a) auto
    then have p_val: "valid rho i phi (Inl sphiq)" using Inl q_val i_props
      unfolding valid_def
      by (auto simp: Let_def)
    then have p_le: "wqo p1 (Inl sphiq)" using p1_def unfolding optimal_def
      by auto
    obtain p1' where p1'_def: "p1 = Inl p1'"
      using p_val p1_def check_consistent[OF bf_phi]
      by (auto simp add: optimal_def valid_def split: sum.splits)
    have "wqo (Inl (SOnce i p1')) q"
      using SOnce[OF p_le[unfolded p1'_def]] sq Inl
      by (fastforce simp add: p1'_def map_idI)
    moreover have "Inl (SOnce i (projl p1)) \<in> set (doOnceBase 0 0 p1)"
      using i_props p1_def bf check_consistent[of phi] p_val
      unfolding doOnceBase_def optimal_def valid_def
      by (auto split: sum.splits)
    ultimately show ?thesis using min_list_wrt_le[OF _ refl_wqo]
        onceBase0_sound[OF p1_def i_props] pw_total[of i "Once I phi"]
        trans_wqo Inl
      apply (auto simp add: total_on_def p1'_def)
      by (metis transpD)
  next
    case (Inr b)
    {fix vphi li
      assume vb: "b = VOnce_never i li [vphi]"
      then have b_val: "valid rho i phi (Inr vphi)" using Inr q_val i_props
        unfolding valid_def by (auto simp: Let_def split: if_splits)
      then have lcomp: "wqo p1 (Inr vphi)"
        using p1_def unfolding optimal_def
        by auto
      have li_def: "li = (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> ETP rho (\<tau> rho i - n))"
        using q_val
        by (auto simp: Inr vb valid_def)
      obtain p1' where p1'_def: "p1 = Inr p1'"
        using b_val p1_def check_consistent[OF bf_phi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      have etp_0: "ETP rho (\<tau> rho 0 - n) = 0" for n
        by (meson Nat.bot_nat_0.extremum_uniqueI diff_le_self i_etp_to_tau)
      have "wqo (Inr (VOnce_never i li [p1'])) q"
        using vb Inr VOnce_never lcomp
        by (auto simp add: p1'_def)
      moreover have "Inr (VOnce_never i li [p1']) \<in> set (doOnceBase 0 0 p1)"
        using i_props p1_def bf check_consistent b_val
        unfolding doOnceBase_def optimal_def valid_def
        by (auto split: sum.splits enat.splits simp: p1'_def li_def etp_0)
      ultimately have "wqo (min_list_wrt wqo (doOnceBase 0 0 p1)) q"
        using min_list_wrt_le[OF _ refl_wqo]
          onceBase0_sound[OF p1_def i_props] pw_total[of i "Once I phi"]
          trans_wqo Inr
        apply (auto simp add: total_on_def)
        by (metis transpD)
    }
    then show ?thesis using Inr q_val assms unfolding valid_def
      apply (cases b)
                          apply (auto simp: Let_def split: if_splits enat.splits)
       apply (metis order.asym diff_le_self i_etp_to_tau i_props le_0_eq)
      apply (metis diff_le_self i_etp_to_tau i_le_ltpi le_zero_eq)
      done
  qed
  then show False using q_le by auto
qed

lemma sinceBase0_sound:
  assumes p1_def: "optimal i phi p1" and p2_def: "optimal i psi p2" and
    i_props: "i = 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I" and
    p_def: "p \<in> set (doSinceBase 0 0 p1 p2)"
  shows "valid rho i (Since phi I psi) p"
  using assms unfolding optimal_def valid_def
  apply (auto simp: i_etp_to_tau doSinceBase_def zero_enat_def[symmetric] split: sum.splits enat.splits)
   apply (meson Orderings.order_class.order.not_eq_order_implies_strict diff_le_self i_etp_to_tau less_nat_zero_code)
  apply (metis add_cancel_right_left add_diff_cancel_left' diff_is_0_eq diff_less i_etp_to_tau le_0_eq le_iff_add nat_le_linear nat_less_le)
  done

lemma sinceBase0_optimal:
  assumes bf: "bounded_future (Since phi I psi)" and
    p1_def: "optimal i phi p1" and p2_def: "optimal i psi p2" and
    i_props: "i = 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I"
  shows
    "optimal i (Since phi I psi) (min_list_wrt wqo (doSinceBase 0 0 p1 p2))"
proof (rule ccontr)
  have bf_phi: "bounded_future phi"
    using bf by auto
  have bf_psi: "bounded_future psi"
    using bf by auto
  from doSinceBase_def[of 0 0 p1 p2]
  have nnil: "doSinceBase 0 0 p1 p2 \<noteq> []"
    by (cases p1; cases p2; auto)
  assume nopt: "\<not> optimal i (Since phi I psi) (min_list_wrt wqo (doSinceBase 0 0 p1 p2))"
  from sinceBase0_sound[OF p1_def p2_def i_props min_list_wrt_in[of _ wqo]]
    refl_wqo pw_total trans_wqo nnil
  have vmin: "valid rho i (Since phi I psi) (min_list_wrt wqo (doSinceBase 0 0 p1 p2))"
    apply auto
    by (metis i_props not_wqo p1_def p2_def sinceBase0_sound total_onI)
  then obtain q  where q_val: "valid rho i (Since phi I psi) q" and
    q_le: "\<not> wqo (min_list_wrt wqo (doSinceBase 0 0 p1 p2)) q" using nopt
    unfolding optimal_def by auto
  then have "wqo (min_list_wrt wqo (doSinceBase 0 0 p1 p2)) q"
  proof (cases q)
    case (Inl a)
    then obtain spsiq sphisq where sq: "a = SSince spsiq sphisq"
      using q_val unfolding valid_def
      by (cases a) auto
    then have p_val: "valid rho i psi (Inl spsiq)" using Inl q_val i_props
      unfolding valid_def
      by (auto simp: Let_def)
    then have p2_le: "wqo p2 (Inl spsiq)" using p2_def unfolding optimal_def
      by auto
    obtain p2' where p2'_def: "p2 = Inl p2'"
      using p_val p2_def check_consistent[OF bf_psi]
      by (auto simp add: optimal_def valid_def split: sum.splits)
    have sphisq_Nil: "sphisq = []"
      using q_val i_props
      by (auto simp: Inl sq valid_def Let_def split: list.splits if_splits)
    have "wqo (Inl (SSince p2' [])) q"
      using SSince[OF p2_le[unfolded p2'_def]] sq Inl
      by (fastforce simp add: p2'_def map_idI sphisq_Nil)
    moreover have "Inl (SSince (projl p2) []) \<in> set (doSinceBase 0 0 p1 p2)"
      using i_props p1_def p2_def bf check_consistent[of psi] p_val
      unfolding doSinceBase_def optimal_def valid_def
      by (auto split: sum.splits)
    ultimately show ?thesis using min_list_wrt_le[OF _ refl_wqo]
        sinceBase0_sound[OF p1_def p2_def i_props] pw_total[of i "Since phi I psi"]
        trans_wqo Inl
      apply (auto simp add: total_on_def p2'_def)
      by (metis transpD)
  next
    case (Inr b)
    {fix vphi vpsi
      assume vs: "b = VSince i vphi [vpsi]"
      then have b_val: "valid rho i phi (Inr vphi)
      \<and> valid rho i psi (Inr vpsi)"
        using q_val Inr i_props unfolding valid_def
        by (auto simp: Let_def)
      then have p1_le: "wqo p1 (Inr vphi)"
        using p1_def
        unfolding optimal_def by auto
      obtain p1' where p1'_def: "p1 = Inr p1'"
        using b_val p1_def check_consistent[OF bf_phi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      obtain p2' where p2'_def: "p2 = Inr p2'"
        using b_val p2_def check_consistent[OF bf_psi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      have lcomp: "wqo (Inr p2') (Inr vpsi)" using b_val p2_def
        unfolding optimal_def
        by (auto simp: p2'_def)
      have "wqo (Inr (VSince i p1' [p2'])) q"
        using VSince[OF p1_le[unfolded p1'_def] lcomp] Inr vs
        by (auto simp add: p1'_def p2'_def)
      moreover have "Inr (VSince i p1' [p2']) \<in> set (doSinceBase 0 0 p1 p2)"
        using i_props p1_def p2_def bf check_consistent b_val
        unfolding doSinceBase_def optimal_def valid_def
        by (auto split: sum.splits simp: p1'_def p2'_def)
      ultimately have "wqo (min_list_wrt wqo (doSinceBase 0 0 p1 p2)) q"
        using min_list_wrt_le[OF _ refl_wqo]
          sinceBase0_sound[OF p1_def p2_def i_props] pw_total[of i "Since phi I psi"]
          trans_wqo Inr
        apply (auto simp add: total_on_def)
        by (metis transpD)
    } note * = this
    {fix vpsi li
      assume vb: "b = VSince_never i li [vpsi]"
      then have b_val: "valid rho i psi (Inr vpsi)" using Inr q_val i_props
        unfolding valid_def by (auto simp: Let_def split: if_splits)
      then have lcomp: "wqo p2 (Inr vpsi)"
        using p2_def unfolding optimal_def
        by auto
      have li_def: "li = (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> ETP rho (\<tau> rho i - n))"
        using q_val
        by (auto simp: Inr vb valid_def)
      obtain p2' where p2'_def: "p2 = Inr p2'"
        using b_val p2_def check_consistent[OF bf_psi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      have etp_0: "ETP rho (\<tau> rho 0 - n) = 0" for n
        by (meson Nat.bot_nat_0.extremum_uniqueI diff_le_self i_etp_to_tau)
      have "wqo (Inr (VSince_never i li [p2'])) q"
        using vb Inr VSince_never lcomp
        by (auto simp add: p2'_def)
      moreover have "Inr (VSince_never i li [p2']) \<in> set (doSinceBase 0 0 p1 p2)"
        using i_props p1_def p2_def bf check_consistent b_val
        unfolding doSinceBase_def optimal_def valid_def
        by (auto split: sum.splits enat.splits simp: p2'_def li_def etp_0)
      ultimately have "wqo (min_list_wrt wqo (doSinceBase 0 0 p1 p2)) q"
        using min_list_wrt_le[OF _ refl_wqo]
          sinceBase0_sound[OF p1_def p2_def i_props] pw_total[of i "Since phi I psi"]
          trans_wqo Inr
        apply (auto simp add: total_on_def)
        by (metis transpD)
    }
    then show ?thesis using * Inr q_val assms unfolding valid_def doSinceBase_def
      apply (cases b)
                          apply (auto simp: Let_def split: if_splits enat.splits)
       apply (metis order.asym diff_le_self i_etp_to_tau i_props le_0_eq)
      apply (metis diff_le_self i_etp_to_tau i_le_ltpi le_zero_eq)
      done
  qed
  then show False using q_le by auto
qed

lemma r_less_Delta_imp_less:
  assumes "(i > 0 \<and> right I < enat (\<Delta> rho i))"
  shows "(\<forall>j < i. \<not> mem (delta rho i j) I)"
proof -
  from \<tau>_mono have j_le: "\<forall>j < i. \<tau> rho j \<le> \<tau> rho (i-1)" by auto
  then show ?thesis using assms
    apply (cases "right I") apply auto
    by (smt One_nat_def Suc_leI diff_le_mono2 j_le le_trans not_less_eq_eq)
qed

lemma sinceBase_constrs:
  assumes i_props: "i > 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I
  \<and> right I < enat (\<Delta> rho i)" and
    n_def: "right I = enat n" and j_def: "j \<le> (i-1)"
  shows "j < ETP rho (\<tau> rho i - n)"
proof -
  from \<tau>_mono j_def have tjs: "\<tau> rho j \<le> \<tau> rho (i-1)" by auto
  from i_props have "n < \<tau> rho i - \<tau> rho (i-1)" using n_def by auto
  then have "n < \<tau> rho i - \<tau> rho j" using tjs \<tau>_mono
    by (metis add_less_le_mono diff_add diff_le_self less_diff_conv)
  then have "\<tau> rho j < \<tau> rho i - n" by auto
  then show ?thesis using less_\<tau>D i_etp_to_tau leD leI
    by blast
qed

lemma ETP_lt_delta: "n < delta rho i (i - 1) \<Longrightarrow> i = ETP rho (\<tau> rho i - n)" for n
  apply (cases i)
   apply auto
  by (smt (verit, ccfv_threshold) add_diff_cancel_left' diff_is_0_eq' i_etp_to_tau leD le_add_diff_inverse2 le_diff_iff' le_trans less_or_eq_imp_le nat_le_linear not_less_eq not_less_eq_eq)

lemma onceBaseNZ_sound:
  assumes i_props: "i > 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I
  \<and> right I < enat (\<Delta> rho i)" and
    p1_def: "optimal i phi p1"
    and p_def: "p \<in> set (doOnceBase i (left I) p1)"
  shows "valid rho i (Once I phi) p"
proof (cases "left I")
  {fix i::nat
    assume i_ge: "i > 0"
    then have "\<tau> rho i \<le> \<tau> rho i \<and> \<tau> rho i \<ge> \<tau> rho 0" by auto
    then have "i \<le> LTP rho (\<tau> rho i)" using i_ge
      by (auto simp add: i_ltp_to_tau)
    then have "i \<le> min i (LTP rho (\<tau> rho i))" by auto
  } note ** = this
  case 0
  then show ?thesis
  proof (cases p1)
    case (Inl a)
    then have p1s: "p1 = Inl a" by auto
    then have "p = Inl (SOnce i a)" using p_def p1s "local.0"
      unfolding doOnceBase_def by simp
    then show ?thesis using p1_def "local.0" Inl zero_enat_def
      unfolding optimal_def valid_def by auto
  next
    case (Inr b)
    then have p1v: "p1 = Inr b" by auto
    then have "p = Inr (VOnce_never i i [b])" using p_def p1v "local.0"
      unfolding doOnceBase_def by simp
    then show ?thesis using p_def p1_def i_props Inr p1v "local.0"
        sinceBase_constrs[OF i_props] ** ETP_lt_delta enat_iless
      unfolding optimal_def valid_def
      by (auto simp: Let_def i_etp_to_tau split: enat.splits sum.splits)
  qed
next
  case (Suc n)
  then show ?thesis
  proof (cases p1)
    case (Inl a)
    then have "p = Inr (VOnce_never i i [])" using p_def Suc p1_def
      unfolding doOnceBase_def by auto
    then show ?thesis using Inl p_def p1_def Suc i_props sinceBase_constrs[OF i_props] ETP_lt_delta enat_iless
      unfolding valid_def
      by (auto simp: Let_def split: enat.splits)
        (metis add_Suc_right i_le_ltpi_minus leD not_less_eq_eq zero_less_Suc)
  next
    case (Inr b)
    then have "p = Inr (VOnce_never i i [])"
      using p_def p1_def Suc unfolding doOnceBase_def by auto
    then show ?thesis using Inr p1_def i_props Suc sinceBase_constrs[OF i_props] ETP_lt_delta enat_iless
      unfolding optimal_def valid_def
      by (auto simp: Let_def split: enat.splits)
        (metis i_le_ltpi_minus i_props leD zero_less_Suc)+
  qed
qed

lemma onceBaseNZ_optimal:
  assumes i_props: "i > 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I
  \<and> right I < enat (\<Delta> rho i)" and
    p1_def: "optimal i phi p1"
    and bf: "bounded_future (Once I phi)"
  shows "optimal i (Once I phi) (min_list_wrt wqo (doOnceBase i (left I) p1))"
proof (rule ccontr)
  have bf_phi: "bounded_future phi"
    using bf by auto
  from doOnceBase_def[of i "left I" p1]
  have nnil: "doOnceBase i (left I) p1 \<noteq> []"
    by (cases p1; cases "left I"; auto)
  from pw_total[of i "Once I phi"] have total_set: "total_on wqo (set (doOnceBase i (left I) p1))"
    using onceBaseNZ_sound[OF i_props p1_def]
    by (metis not_wqo total_onI)
  have filter_nnil: "filter (\<lambda>x. \<forall>y \<in> set (doOnceBase i (left I) p1). wqo x y) (doOnceBase i (left I) p1) \<noteq> []"
    using refl_total_transp_imp_ex_min[OF nnil refl_wqo total_set trans_wqo]
      filter_empty_conv[of "(\<lambda>x. \<forall>y \<in> set (doOnceBase i (left I) p1). wqo x y)" "(doOnceBase i (left I) p1)"]
    by simp
  assume nopt: "\<not> optimal i (Once I phi) (min_list_wrt wqo (doOnceBase i (left I) p1))"
  define minp where minp: "minp \<equiv> (min_list_wrt wqo (doOnceBase i (left I) p1))"
  {
    assume l_ge: "left I > 0"
    then have "right I > 0" using left_right[of I] zero_enat_def
      apply auto
      using enat_0_iff(2) by auto
    then have "\<not> mem (delta rho i i) I" using l_ge by auto
    then have "\<forall>j \<le> i. \<not> mem (delta rho i j) I"
      using i_props r_less_Delta_imp_less l_ge le_neq_implies_less
      by blast
    then have "\<not> sat rho i (Once I phi)" by auto
    then have "VIO rho i (Once I phi)" using completeness
      by blast
  } note * = this
  from onceBaseNZ_sound[OF i_props p1_def min_list_wrt_in[of _ wqo]]
    minp trans_wqo refl_wqo pw_total nnil
  have vmin: "valid rho i (Once I phi) minp"
    apply auto
    by (metis i_props not_wqo p1_def onceBaseNZ_sound total_onI)
  then obtain q where q_val: "valid rho i (Once I phi) q" and
    q_le: "\<not> wqo minp q" using nopt minp unfolding optimal_def
    by auto
  then have "wqo minp q" using minp
  proof (cases q)
    case (Inl a)
    then obtain sphiq where sq: "a = SOnce i sphiq"
      using q_val unfolding valid_def
      by (cases a) auto
    then have p_val: "valid rho i phi (Inl sphiq)" using Inl q_val i_props
      unfolding valid_def
      apply (auto simp: Let_def split: list.splits)
      by (metis One_nat_def le_neq_implies_less r_less_Delta_imp_less)
    then have p1_le: "wqo p1 (Inl sphiq)" using p1_def unfolding optimal_def
      by simp
    from q_val have sats: "SAT rho i (Once I phi)" using check_sound Inl
      unfolding valid_def by auto
    obtain p1' where p1'_def: "p1 = Inl p1'"
      using p_val p1_def check_consistent[OF bf_phi]
      by (auto simp add: optimal_def valid_def split: sum.splits)
    have "wqo (Inl (SOnce i (projl p1))) q"
      using SOnce[OF p1_le[unfolded p1'_def]] sq Inl
      by (fastforce simp add: p1'_def map_idI)
    moreover have "Inl (SOnce i (projl p1)) \<in> set (doOnceBase i (left I) p1)"
      using i_props p1_def bf check_consistent p_val * sats
      unfolding doOnceBase_def optimal_def valid_def
      apply (cases "left I"; auto split: sum.splits nat.splits)
      by (metis bf check_complete)+
    ultimately show ?thesis
      using min_list_wrt_le[OF _ refl_wqo]
        onceBaseNZ_sound[OF i_props p1_def] pw_total[of i " Once I phi"]
        trans_wqo Inl minp
      apply (auto simp add: total_on_def)
      by (metis transpD)
  next
    case (Inr b)
    {fix n j
      assume j_def: "right I = enat n \<and> j \<le> LTP rho (\<tau> rho i)
       \<and> ETP rho (\<tau> rho i - n) \<le> j \<and> j \<le> i"
      then have jin: "\<tau> rho j \<ge> \<tau> rho i - n" using i_etp_to_tau by auto
      from \<tau>_mono have j_lei: "\<forall>j < i. \<tau> rho j \<le> \<tau> rho (i-1)" by auto
      from this i_props j_def have "\<forall>j < i. \<tau> rho j \<le> \<tau> rho i - n"
        apply auto
        by (metis One_nat_def j_lei add_diff_inverse_nat add_le_imp_le_diff add_le_mono less_imp_le_nat less_nat_zero_code nat_diff_split_asm)
      then have "j = i" using j_def jin apply auto
        by (metis add.commute order.not_eq_order_implies_strict diff_diff_left enat_ord_simps(2) i_props j_lei less_le_not_le zero_less_diff)
    } note ** = this
    then show ?thesis
    proof (cases "left I")
      case 0
      {fix vphi
        assume bv: "b = VOnce_never i i [vphi]"
        then have b_val: "valid rho i phi (Inr vphi)"
          using q_val Inr min.absorb_iff1 i_props "0" i_le_ltpi
          unfolding valid_def
          by (auto simp: Let_def split: if_splits enat.splits)
        then have p1_wqo: "wqo p1 (Inr vphi)"
          using b_val p1_def unfolding optimal_def
          by auto
        obtain p1' where p1'_def: "p1 = Inr p1'"
          using b_val p1_def check_consistent[OF bf_phi]
          by (auto simp add: optimal_def valid_def split: sum.splits)
        have "wqo (Inr (VOnce_never i i [p1'])) q"
          using bv Inr VOnce_never p1_wqo
          by (auto simp add: p1'_def)
        moreover have "Inr (VOnce_never i i [p1']) \<in> set (doOnceBase i (left I) p1)"
          using i_props bf check_consistent b_val "0"
          unfolding doOnceBase_def optimal_def valid_def
          by (auto split: sum.splits nat.splits simp: p1'_def)
        ultimately have "wqo minp q" using min_list_wrt_le[OF _ refl_wqo]
            onceBaseNZ_sound[OF i_props p1_def] pw_total[of i "Once I phi"]
            trans_wqo bv Inr minp
          apply (auto simp add: total_on_def)
          by (metis transpD)
      }
      moreover
      have "\<exists>vphi. b = VOnce_never i i [vphi]"
        using q_val "0" Inr assms(1) ** 
        unfolding valid_def doOnceBase_def
      proof (cases b)
        case (VOnce_never i j vphis)
        then show ?thesis
          using VOnce_never q_val "0" Inr assms(1) ** 
          unfolding valid_def doOnceBase_def
          by (cases vphis; cases "tl vphis")
            (auto simp: Let_def min_def i_etp_to_tau i_le_ltpi dest: ETP_lt_delta[simplified] split: if_splits enat.splits)
      next
        case (VOnce_le i)
        then show ?thesis
          using q_val "0" Inr assms(1) ** 
          unfolding valid_def doOnceBase_def
          by (auto simp: Let_def leD split: if_splits enat.splits)
      qed (auto simp: Let_def split: if_splits enat.splits)
      ultimately show ?thesis by blast
    next
      case (Suc nat)
      from q_val Inr have "VIO rho i (Once I phi)"
        using check_sound(2)[of rho "Once I phi" b]
        unfolding valid_def by auto
      {fix li vphis
        assume bv: "b = VOnce_never i li vphis"
        have vphis_Nil: "vphis = []"
          using q_val i_props
          by (auto simp: Inr bv valid_def Let_def split: if_splits enat.splits)
            (smt (z3) "**" Lattices.linorder_class.min.cobounded1 Suc i_le_ltpi i_le_ltpi_minus leD le_trans min_def zero_less_Suc)
        have li_def: "li = i"
          using q_val
          apply (auto simp: Inr bv vphis_Nil valid_def split: enat.splits if_splits)
          using diff_le_self i_etp_to_tau apply blast
          using ETP_lt_delta enat_ord_simps(2) i_props by presburger
        have "wqo (Inr (VOnce_never i i [])) q"
          using q_val bv Inr not_wqo
          by (fastforce simp add: map_idI vphis_Nil li_def)
        moreover have "Inr (VOnce_never i i []) \<in> set (doOnceBase i (left I) p1)"
          using i_props p1_def bf check_consistent Suc
          unfolding doOnceBase_def optimal_def valid_def
          by (auto split: sum.splits nat.splits)
        ultimately have "wqo minp q" using min_list_wrt_le[OF _ refl_wqo]
            onceBaseNZ_sound[OF i_props p1_def] pw_total[of i "Once I phi"]
            trans_wqo bv Inr minp
          apply (auto simp add: total_on_def)
          by (metis transpD)
      }
      then show ?thesis
        using minp Suc Inr q_val assms
        unfolding doOnceBase_def valid_def optimal_def
        by (cases b) (auto)
    qed
  qed
  then show False using q_le by auto
qed

lemma sinceBaseNZ_sound:
  assumes i_props: "i > 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I
  \<and> right I < enat (\<Delta> rho i)" and
    p1_def: "optimal i phi p1"and p2_def: "optimal i psi p2"
    and p_def: "p \<in> set (doSinceBase i (left I) p1 p2)"
  shows "valid rho i (Since phi I psi) p"
proof (cases "left I")
  {fix i::nat
    assume i_ge: "i > 0"
    then have "\<tau> rho i \<le> \<tau> rho i \<and> \<tau> rho i \<ge> \<tau> rho 0" by auto
    then have "i \<le> LTP rho (\<tau> rho i)" using i_ge
      by (auto simp add: i_ltp_to_tau)
    then have "i \<le> min i (LTP rho (\<tau> rho i))" by auto
  }note ** = this
  case 0
  then show ?thesis
  proof (cases p1)
    case (Inl a)
    then have p1s: "p1 = Inl a" by auto
    then show ?thesis
    proof (cases p2)
      case (Inl a1)
      then have "p = Inl (SSince a1 [])" using p_def p1s "local.0"
        unfolding doSinceBase_def by auto
      then show ?thesis using p2_def "local.0" Inl zero_enat_def
        unfolding optimal_def valid_def by auto
    next
      case (Inr b1)
      from Inr have "p = Inr (VSince_never i i [b1])" using p_def p1s "local.0"
        unfolding doSinceBase_def by auto
      then show ?thesis
        using p2_def "local.0" Inr i_props i_etp_to_tau
          sinceBase_constrs[OF i_props] ** ETP_lt_delta enat_iless
        unfolding optimal_def valid_def
        by (auto split: sum.splits enat.splits)
    qed
  next
    case (Inr b)
    then have p1v: "p1 = Inr b" by auto
    then show ?thesis
    proof (cases p2)
      case (Inl a1)
      then have "p = Inl (SSince a1 [])" using p_def "local.0" p1v
        unfolding doSinceBase_def by auto
      then show ?thesis using p_def p2_def "local.0" zero_enat_def Inl
        unfolding optimal_def valid_def by auto
    next
      case (Inr b1)
      then have "p = Inr (VSince i b [b1]) \<or> p = Inr (VSince_never i i [b1])"
        using p_def "local.0" p1v unfolding doSinceBase_def by auto
      then show ?thesis using p_def p1_def p2_def i_props Inr p1v "local.0"
          sinceBase_constrs[OF i_props] ** ETP_lt_delta enat_iless
        unfolding optimal_def valid_def
        by (auto simp: Let_def i_etp_to_tau split: enat.splits sum.splits)
    qed
  qed
next
  case (Suc n)
  then show ?thesis
  proof (cases p1)
    case (Inl a)
    then have "p = Inr (VSince_never i i [])" using p_def Suc p1_def
      unfolding doSinceBase_def
      by (cases p2; auto)
    then show ?thesis using Inl p_def p1_def Suc i_props sinceBase_constrs[OF i_props] ETP_lt_delta enat_iless
      unfolding valid_def
      by (auto simp: Let_def split: enat.splits)
        (metis add_Suc_right i_le_ltpi_minus leD not_less_eq_eq zero_less_Suc)
  next
    case (Inr b)
    then have "p = Inr (VSince i b []) \<or> p = Inr (VSince_never i i [])"
      using p_def p1_def Suc unfolding doSinceBase_def
      by (cases p2; auto)
    then show ?thesis using Inr p1_def i_props Suc sinceBase_constrs[OF i_props] ETP_lt_delta enat_iless
      unfolding optimal_def valid_def
      by (auto simp: Let_def split: enat.splits)
        (metis i_le_ltpi_minus i_props leD zero_less_Suc)+
  qed
qed

lemma sinceBaseNZ_optimal:
  assumes i_props: "i > 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I
  \<and> right I < enat (\<Delta> rho i)" and
    p1_def: "optimal i phi p1" and p2_def: "optimal i psi p2"
    and bf: "bounded_future (Since phi I psi)"
  shows "optimal i (Since phi I psi) (min_list_wrt wqo (doSinceBase i (left I) p1 p2))"
proof (rule ccontr)
  have bf_phi: "bounded_future phi"
    using bf by auto
  have bf_psi: "bounded_future psi"
    using bf by auto
  from doSinceBase_def[of i "left I" p1 p2]
  have nnil: "doSinceBase i (left I) p1 p2 \<noteq> []"
    by (cases p1; cases p2; cases "left I"; auto)
  from pw_total[of i "Since phi I psi"] have total_set: "total_on wqo (set (doSinceBase i (left I) p1 p2))"
    using sinceBaseNZ_sound[OF i_props p1_def p2_def]
    by (metis not_wqo total_onI)
  have filter_nnil: "filter (\<lambda>x. \<forall>y \<in> set (doSinceBase i (left I) p1 p2). wqo x y) (doSinceBase i (left I) p1 p2) \<noteq> []"
    using refl_total_transp_imp_ex_min[OF nnil refl_wqo total_set trans_wqo]
      filter_empty_conv[of "(\<lambda>x. \<forall>y \<in> set (doSinceBase i (left I) p1 p2). wqo x y)" "(doSinceBase i (left I) p1 p2)"]
    by simp
  assume nopt: "\<not> optimal i (Since phi I psi) (min_list_wrt wqo (doSinceBase i (left I) p1 p2))"
  define minp where minp: "minp \<equiv> (min_list_wrt wqo (doSinceBase i (left I) p1 p2))"
  {
    assume l_ge: "left I > 0"
    then have "right I > 0" using left_right[of I] zero_enat_def
      apply auto
      using enat_0_iff(2) by auto
    then have "\<not> mem (delta rho i i) I" using l_ge by auto
    then have "\<forall>j \<le> i. \<not> mem (delta rho i j) I"
      using i_props r_less_Delta_imp_less l_ge le_neq_implies_less
      by blast
    then have "\<not> sat rho i (Since phi I psi)" by auto
    then have "VIO rho i (Since phi I psi)" using completeness
      by blast
  } note * = this
  from sinceBaseNZ_sound[OF i_props p1_def p2_def min_list_wrt_in[of _ wqo]]
    minp trans_wqo refl_wqo pw_total nnil
  have vmin: "valid rho i (Since phi I psi) minp"
    apply auto
    by (metis i_props not_wqo p1_def p2_def sinceBaseNZ_sound total_onI)
  then obtain q where q_val: "valid rho i (Since phi I psi) q" and
    q_le: "\<not> wqo minp q" using nopt minp unfolding optimal_def
    by auto
  then have "wqo minp q" using minp
  proof (cases q)
    case (Inl a)
    then obtain spsiq sphisq where sq: "a = SSince spsiq sphisq"
      using q_val unfolding valid_def
      by (cases a) auto
    then have p_val: "valid rho i psi (Inl spsiq)" using Inl q_val i_props
      unfolding valid_def
      apply (auto simp: Let_def split: list.splits)
       apply (metis One_nat_def le_neq_implies_less r_less_Delta_imp_less)
      by (metis One_nat_def le_neq_implies_less r_less_Delta_imp_less)
    then have p2_le: "wqo p2 (Inl spsiq)" using p2_def unfolding optimal_def
      by auto
    from q_val have sats: "SAT rho i (Since phi I psi)" using check_sound Inl
      unfolding valid_def by auto
    have sphisq_Nil: "sphisq = []"
      using q_val Suc_le_lessD i_props r_less_Delta_imp_less
      by (auto simp: Inl sq valid_def Let_def split: list.splits if_splits)
    obtain p2' where p2'_def: "p2 = Inl p2'"
      using p_val p2_def check_consistent[OF bf_psi]
      by (auto simp add: optimal_def valid_def split: sum.splits)
    have "wqo (Inl (SSince (projl p2) [])) q"
      using SSince[OF p2_le[unfolded p2'_def]] sq Inl
      by (fastforce simp add: p2'_def map_idI sphisq_Nil)
    moreover have "Inl (SSince (projl p2) []) \<in> set (doSinceBase i (left I) p1 p2)"
      using i_props p1_def p2_def bf check_consistent p_val * sats
      unfolding doSinceBase_def optimal_def valid_def
      apply (cases "left I"; auto split: sum.splits nat.splits)
      by (metis bf check_complete)+
    ultimately show ?thesis
      using min_list_wrt_le[OF _ refl_wqo]
        sinceBaseNZ_sound[OF i_props p1_def p2_def] pw_total[of i "Since phi I psi"]
        trans_wqo Inl minp
      apply (auto simp add: total_on_def)
      by (metis transpD)
  next
    case (Inr b)
    {fix n j
      assume j_def: "right I = enat n \<and> j \<le> LTP rho (\<tau> rho i)
       \<and> ETP rho (\<tau> rho i - n) \<le> j \<and> j \<le> i"
      then have jin: "\<tau> rho j \<ge> \<tau> rho i - n" using i_etp_to_tau by auto
      from \<tau>_mono have j_lei: "\<forall>j < i. \<tau> rho j \<le> \<tau> rho (i-1)" by auto
      from this i_props j_def have "\<forall>j < i. \<tau> rho j \<le> \<tau> rho i - n"
        apply auto
        by (metis One_nat_def j_lei add_diff_inverse_nat add_le_imp_le_diff add_le_mono less_imp_le_nat less_nat_zero_code nat_diff_split_asm)
      then have "j = i" using j_def jin apply auto
        by (metis add.commute order.not_eq_order_implies_strict diff_diff_left enat_ord_simps(2) i_props j_lei less_le_not_le zero_less_diff)
    } note ** = this
    then show ?thesis
    proof (cases "left I")
      case 0
      {fix vphi vpsi
        assume bv: "b = VSince i vphi [vpsi]"
        then have b_val: "valid rho i phi (Inr vphi)
            \<and> valid rho i psi (Inr vpsi)" using q_val Inr i_props i_etp_to_tau
          "local.0" ** i_le_ltpi
          unfolding valid_def
          by (auto simp: Let_def split: enat.splits if_splits)
        then have p1_wqo: "wqo p1 (Inr vphi)" using p1_def
          unfolding optimal_def by auto
        have p2_wqo: "wqo p2 (Inr vpsi)"
          using b_val p2_def unfolding optimal_def
          by auto
        obtain p1' where p1'_def: "p1 = Inr p1'"
          using b_val p1_def check_consistent[OF bf_phi]
          by (auto simp add: optimal_def valid_def split: sum.splits)
        obtain p2' where p2'_def: "p2 = Inr p2'"
          using b_val p2_def check_consistent[OF bf_psi]
          by (auto simp add: optimal_def valid_def split: sum.splits)
        have "wqo (Inr (VSince i p1' [p2'])) q"
          using bv Inr VSince[OF p1_wqo[unfolded p1'_def]] p2_wqo
          by (auto simp add: p1'_def p2'_def)
        moreover have "Inr (VSince i (p1') [p2']) \<in> set (doSinceBase i (left I) p1 p2)"
          using i_props p1_def p2_def bf check_consistent b_val "0"
          unfolding doSinceBase_def optimal_def valid_def
          by (auto split: sum.splits nat.splits simp: p1'_def p2'_def)
        ultimately have "wqo minp q" using min_list_wrt_le[OF _ refl_wqo]
            sinceBaseNZ_sound[OF i_props p1_def p2_def] pw_total[of i "Since phi I psi"]
            trans_wqo bv Inr minp
          apply (auto simp add: total_on_def)
          by (metis transpD)
      }
      moreover
      {fix vpsi
        assume bv: "b = VSince_never i i [vpsi]"
        then have b_val: "valid rho i psi (Inr vpsi)"
          using q_val Inr min.absorb_iff1 i_props "0" i_le_ltpi
          unfolding valid_def
          by (auto simp: Let_def split: if_splits enat.splits)
        then have p2_wqo: "wqo p2 (Inr vpsi)"
          using b_val p2_def unfolding optimal_def
          by auto
        obtain p2' where p2'_def: "p2 = Inr p2'"
          using b_val p2_def check_consistent[OF bf_psi]
          by (auto simp add: optimal_def valid_def split: sum.splits)
        have "wqo (Inr (VSince_never i i [p2'])) q"
          using bv Inr VSince_never p2_wqo
          by (auto simp add: p2'_def)
        moreover have "Inr (VSince_never i i [p2']) \<in> set (doSinceBase i (left I) p1 p2)"
          using i_props p2_def bf check_consistent b_val "0"
          unfolding doSinceBase_def optimal_def valid_def
          by (auto split: sum.splits nat.splits simp: p2'_def)
        ultimately have "wqo minp q" using min_list_wrt_le[OF _ refl_wqo]
            sinceBaseNZ_sound[OF i_props p1_def p2_def] pw_total[of i "Since phi I psi"]
            trans_wqo bv Inr minp
          apply (auto simp add: total_on_def)
          by (metis transpD)
      }
      ultimately show ?thesis using q_val "0" Inr minp assms **
        unfolding valid_def doSinceBase_def
        apply (cases b)
                            apply (auto simp: Let_def split: if_splits enat.splits)
             apply (metis (no_types, lifting) list.map_disc_iff append_eq_append_conv2 map_eq_Cons_conv min_less_iff_conj nat_less_le self_append_conv upt_rec)
            apply (meson i_le_ltpi le_trans)
           apply (metis (no_types, lifting) list.map_disc_iff append_eq_append_conv2 eq_imp_le map_eq_Cons_conv min_less_iff_conj nat_less_le self_append_conv upt_rec)
          apply (meson diff_le_self i_etp_to_tau)
         apply (metis diff_diff_cancel diff_is_0_eq i_etp_to_tau i_le_ltpi le_trans nat_le_linear)
        using i_props by auto
    next
      case (Suc nat)
      from q_val Inr have "VIO rho i (Since phi I psi)"
        using check_sound(2)[of rho "Since phi I psi" b]
        unfolding valid_def by auto
          (*
      have minp_def: "minp = Inr (VSince i (projr p1) []) \<or> minp = Inr (VSince_never i i [])"
        using minp vmin Suc nnil doSinceBase_def[of i "left I" p1 p2]
          trans_wqo pw_total filter_nnil
        unfolding valid_def
        by (cases p1; cases p2; auto simp: min_list_wrt_def refl_wqo reflpD)
*)
      {fix vphi vpsis
        assume bv: "b = VSince i vphi vpsis"
        then have b_val: "valid rho i phi (Inr vphi)"
          using q_val Inr i_props Suc ** i_le_ltpi
          unfolding valid_def
          apply (auto simp: Let_def split: enat.splits if_splits)
          using le_trans apply blast
          using le_trans by blast
        then have p1_wqo: "wqo p1 (Inr vphi)" using p1_def
          unfolding optimal_def by auto
        have vpsis_Nil: "vpsis = []"
          using q_val
          apply (auto simp: Inr bv valid_def Let_def split: if_splits enat.splits)
           apply (metis "**" Suc i_le_ltpi i_le_ltpi_minus i_props leD le_trans zero_less_Suc)
          by (metis enat_ord_simps(3) i_props leD)
        obtain p1' where p1'_def: "p1 = Inr p1'"
          using b_val p1_def check_consistent[OF bf_phi]
          by (auto simp add: optimal_def valid_def split: sum.splits)
        have "wqo (Inr (VSince i (projr p1) [])) q"
          using bv Inr VSince_Nil[OF p1_wqo[unfolded p1'_def]]
          by (fastforce simp add: p1'_def map_idI vpsis_Nil)
        moreover have "Inr (VSince i (projr p1) []) \<in> set (doSinceBase i (left I) p1 p2)"
          using i_props p1_def p2_def bf check_consistent b_val Suc
          unfolding doSinceBase_def optimal_def valid_def
          by (auto split: sum.splits nat.splits)
        ultimately have "wqo minp q" using min_list_wrt_le[OF _ refl_wqo]
            sinceBaseNZ_sound[OF i_props p1_def p2_def] pw_total[of i "Since phi I psi"]
            trans_wqo bv Inr minp
          apply (auto simp add: total_on_def)
          by (metis transpD)
      }
      moreover
      {fix li vpsis
        assume bv: "b = VSince_never i li vpsis"
        have vpsis_Nil: "vpsis = []"
          using q_val i_props
          by (auto simp: Inr bv valid_def Let_def split: if_splits enat.splits)
            (smt (z3) "**" Lattices.linorder_class.min.cobounded1 Suc i_le_ltpi i_le_ltpi_minus leD le_trans min_def zero_less_Suc)
        have li_def: "li = i"
          using q_val
          apply (auto simp: Inr bv vpsis_Nil valid_def split: enat.splits if_splits)
          using diff_le_self i_etp_to_tau apply blast
          using ETP_lt_delta enat_ord_simps(2) i_props by presburger
        have "wqo (Inr (VSince_never i i [])) q"
          using q_val bv Inr not_wqo
          by (fastforce simp add: map_idI vpsis_Nil li_def)
        moreover have "Inr (VSince_never i i []) \<in> set (doSinceBase i (left I) p1 p2)"
          using i_props p2_def bf check_consistent Suc
          unfolding doSinceBase_def optimal_def valid_def
          by (auto split: sum.splits nat.splits)
        ultimately have "wqo minp q" using min_list_wrt_le[OF _ refl_wqo]
            sinceBaseNZ_sound[OF i_props p1_def p2_def] pw_total[of i "Since phi I psi"]
            trans_wqo bv Inr minp
          apply (auto simp add: total_on_def)
          by (metis transpD)
      }
      ultimately show ?thesis
        using minp Suc Inr q_val assms
        unfolding doSinceBase_def valid_def optimal_def
        by (cases b) (auto)
    qed
  qed
  then show False using q_le by auto
qed

lemma untilBase_constrs:
  assumes n_def: "right I = enat n" and j_def: "j \<ge> (i+1)"
    and i_props: "right I < enat (\<Delta> rho (i+1))"
  shows "LTP rho (\<tau> rho i + n) < j"
proof -
  from assms have tjs: "\<tau> rho (i+1) \<le> \<tau> rho j" by auto
  from i_props have "n < \<tau> rho (i+1) - \<tau> rho i" using n_def by auto
  then have "\<tau> rho i + n < \<tau> rho (i+1)" by auto
  then have "\<tau> rho i + n < \<tau> rho j" using j_def tjs less_le_trans
    by blast
  then show ?thesis using less_\<tau>D i_ltp_to_tau leD leI
    by (metis add_lessD1 add_less_same_cancel1 not_add_less1)
qed

lemma LTP_lt_delta: "n < delta rho (Suc i) i \<Longrightarrow> i = LTP rho (\<tau> rho i + n)"
  using i_le_ltpi_add[of i rho n] i_ltp_to_tau[where ?i="Suc i" and ?rho=rho and ?n="\<tau> rho i + n"]
  using less_diff_conv trans_le_add1 by force

lemma untilBase_sound:
  assumes i_props: "right I < enat (\<Delta> rho (i+1))" and
    p1_def: "optimal i phi p1" and p2_def: "optimal i psi p2" and
    p_def: "p \<in> set (doUntilBase i (left I) p1 p2)"
  shows "valid rho i (Until phi I psi) p"
proof(cases "left I")
  case 0
  then show ?thesis
  proof (cases p2)
    case (Inl a)
    then have "p = Inl (SUntil [] (projl p2))" using assms "0"
      unfolding doUntilBase_def
      by (cases p1) auto
    then show ?thesis using "0" i_props p2_def zero_enat_def Inl
      unfolding optimal_def valid_def by auto
  next
    case (Inr b)
    then have p2v: "p2 = Inr b" by auto
    then show ?thesis
    proof(cases p1)
      case (Inl a)
      then have "p = Inr (VUntil_never i i [projr p2])" using assms "0" Inr
        unfolding doUntilBase_def
        by auto
      then show ?thesis using "0" i_props p2_def Inr i_ge_etpi[of rho i]
          i_ltp_to_tau untilBase_constrs LTP_lt_delta enat_iless
        unfolding optimal_def valid_def
        by (auto simp: Let_def split: enat.splits)
    next
      case (Inr b1)
      then have "p = Inr (VUntil i [projr p2] (projr p1))
      \<or> p = Inr (VUntil_never i i [projr p2])" using assms "0" p2v
        unfolding doUntilBase_def
        by auto
      then show ?thesis using untilBase_constrs assms "0" Inr
          p2v i_ge_etpi[of rho i] i_le_ltpi_add[of i rho] LTP_lt_delta enat_iless
        unfolding optimal_def valid_def
        by (auto simp: Let_def split: enat.splits)
    qed
  qed
next
  case (Suc n)
  then show ?thesis
  proof (cases p1)
    case (Inl a)
    then have "p = Inr (VUntil_never i i [])" using assms Suc
      unfolding doUntilBase_def
      by (cases p2) auto
    then show ?thesis using Inl Suc assms untilBase_constrs LTP_lt_delta enat_iless
      unfolding valid_def
      apply (auto simp: Let_def split: enat.splits)
      by (metis Suc_le_lessD i_etp_to_tau not_add_less1)
  next
    case (Inr b)
    then have "p = Inr (VUntil i [] (projr p1)) \<or> p = Inr (VUntil_never i i [])"
      using Suc assms unfolding doUntilBase_def
      by (cases p2) auto
    then show ?thesis using Inr Suc assms untilBase_constrs i_ge_etpi[of rho i] LTP_lt_delta enat_iless
      unfolding optimal_def valid_def
      apply (auto simp: Let_def split: enat.splits)
       apply (simp add: i_etp_to_tau)
      by (metis (no_types, lifting) Suc_le_lessD i_etp_to_tau not_add_less1)
  qed
qed

lemma r_less_imp_nphi:
  assumes "right I < enat (\<Delta> rho (i+1))"
  shows "\<forall>j > i. \<not> mem (delta rho j i) I"
proof -
  from \<tau>_mono have j_to_tau: "\<forall>j \<ge> i. \<tau> rho i \<le> \<tau> rho j" by auto
  then show ?thesis using assms
    apply (cases "right I") apply auto
    by (smt add.commute add_diff_cancel_right' diff_le_self j_to_tau le_less_trans less_\<tau>D less_diff_iff less_imp_le_nat not_less_eq plus_1_eq_Suc)
qed

lemma untilBase_optimal:
  assumes bf: "bounded_future (Until phi I psi)" and
    i_props: "right I < enat (\<Delta> rho (i+1))" and
    p1_def: "optimal i phi p1" and p2_def: "optimal i psi p2"
  shows "optimal i (Until phi I psi) (min_list_wrt wqo (doUntilBase i (left I) p1 p2))"
proof (rule ccontr)
  have bf_phi: "bounded_future phi"
    using bf by auto
  have bf_psi: "bounded_future psi"
    using bf by auto
  from doUntilBase_def[of i "left I" p1 p2]
  have nnil: "doUntilBase i (left I) p1 p2 \<noteq> []"
    by (cases p1; cases p2; cases "left I"; auto)
  from pw_total[of i "Until phi I psi"] have total_set: "total_on wqo (set (doUntilBase i (left I) p1 p2))"
    using untilBase_sound[OF i_props p1_def p2_def]
    by (metis not_wqo total_onI)
  have filter_nnil: "filter (\<lambda>x. \<forall>y \<in> set (doUntilBase i (left I) p1 p2). wqo x y) (doUntilBase i (left I) p1 p2) \<noteq> []"
    using refl_total_transp_imp_ex_min[OF nnil refl_wqo total_set trans_wqo]
      filter_empty_conv[of "(\<lambda>x. \<forall>y \<in> set (doUntilBase i (left I) p1 p2). wqo x y)" "(doUntilBase i (left I) p1 p2)"]
    by simp
  {assume sat: "SAT rho i (Until phi I psi)"
    then have satu: "sat rho i (Until phi I psi)" using soundness
      by blast
    then have "sat rho i psi" using i_props r_less_imp_nphi
      apply auto
      using nat_less_le by blast
    then have "left I = 0" using satu sat_Until_rec[of rho i phi I psi] i_props
      by auto
  } note * = this
  define minp where minp: "minp \<equiv> (min_list_wrt wqo (doUntilBase i (left I) p1 p2))"
  assume nopt: "\<not> optimal i (Until phi I psi) minp"
  from untilBase_sound[OF i_props p1_def p2_def min_list_wrt_in[of _ wqo]]
    refl_wqo trans_wqo pw_total minp nnil
  have vmin: "valid rho i (Until phi I psi) minp"
    apply auto
    by (metis i_props not_wqo p1_def p2_def untilBase_sound total_onI)
  then obtain q where q_val: "valid rho i (Until phi I psi) q" and
    q_le: "\<not> wqo minp q" using nopt unfolding optimal_def by auto
  then have "wqo minp q" using minp
  proof (cases q)
    case (Inl a)
    then obtain spsi sphis where a_def: "a = SUntil sphis spsi" using q_val
      unfolding valid_def by (cases a) auto
    from q_val have satu: "SAT rho i (Until phi I psi)" using check_sound Inl
      unfolding valid_def by auto
    from a_def have p_val: "valid rho i psi (Inl spsi)" using q_val Inl i_props
      unfolding valid_def apply (auto simp: Let_def split: list.splits)
      by (metis Suc_eq_plus1 diff_add_inverse2 le_neq_implies_less r_less_imp_nphi)
    then have p2_le: "wqo p2 (Inl spsi)" using p2_def unfolding optimal_def
      by auto
    have sphis_Nil: "sphis = []"
      using q_val i_props
      by (auto simp: Inl a_def valid_def Let_def split: list.splits)
        (metis (no_types, lifting) Cons_eq_upt_conv Suc_eq_plus1 diff_add_inverse2 r_less_imp_nphi)
    obtain p2' where p2'_def: "p2 = Inl p2'"
      using p_val p2_def check_consistent[OF bf_psi]
      by (auto simp add: optimal_def valid_def split: sum.splits)
    have "wqo (Inl (SUntil [] (projl p2))) q"
      using Inl a_def SUntil_Nil[OF p2_le[unfolded p2'_def]]
      by (fastforce simp add: p2'_def map_idI sphis_Nil)
    moreover have "Inl (SUntil [] (projl p2)) \<in> set (doUntilBase i (left I) p1 p2)"
      using assms check_consistent[of psi] satu * p_val
      unfolding doUntilBase_def optimal_def valid_def
      by (auto split: sum.splits)
    ultimately show ?thesis using min_list_wrt_le[OF _ refl_wqo]
        untilBase_sound[OF i_props p1_def p2_def] pw_total[of i "Until phi I psi"]
        trans_wqo Inl minp
      apply (auto simp add: total_on_def)
      by (metis transpD)
  next
    case (Inr b)
    then show ?thesis
    proof (cases "left I")
      {fix n j
        assume j_def: "right I = enat n \<and> ETP rho (\<tau> rho i) \<le> j
       \<and> j \<le> LTP rho (\<tau> rho i + n) \<and> j \<ge> i"
        from \<tau>_mono have "\<tau> rho i + n \<ge> \<tau> rho 0"  by (auto simp add: trans_le_add1)
        then have jin: "\<tau> rho j \<le> \<tau> rho i + n" using j_def i_ltp_to_tau by auto
        from \<tau>_mono have j_gei: "\<forall>j > i. \<tau> rho j \<ge> \<tau> rho (i+1)" by auto
        from this i_props j_def have "\<forall>j > i. \<tau> rho j \<ge> \<tau> rho i + n"
          apply auto
          by (smt Suc_eq_plus1 diff_is_0_eq' j_gei le_add_diff_inverse le_trans less_imp_le_nat less_nat_zero_code nat_add_left_cancel_le nat_le_linear)
        then have "j = i" using j_def jin apply auto
          by (metis dual_order.strict_implies_not_eq add_diff_cancel_left' add_diff_cancel_right' i_props j_gei le_antisym le_neq_implies_less less_add_one)
      } note ** = this
      case 0
      {fix vpsi vphi
        assume bv: "b = VUntil i [vpsi] vphi"
        then have p_val: "valid rho i phi (Inr vphi) \<and> valid rho i psi (Inr vpsi)"
          using bf q_val Inr "0" unfolding valid_def
          apply (auto simp: Let_def split: if_splits enat.splits)
          by (metis max.order_iff i_ge_etpi le0 le_antisym upt_eq_Nil_conv)
        then have wqo_p1: "wqo p1 (Inr vphi)" using p1_def unfolding optimal_def
          by auto
        obtain p1' where p1'_def: "p1 = Inr p1'"
          using p_val p1_def check_consistent[OF bf_phi]
          by (auto simp add: optimal_def valid_def split: sum.splits)
        obtain p2' where p2'_def: "p2 = Inr p2'"
          using p_val p2_def check_consistent[OF bf_psi]
          by (auto simp add: optimal_def valid_def split: sum.splits)
        from p_val have wqo_p2: "wqo p2 (Inr vpsi)" using p2_def unfolding optimal_def
          by auto
        then have lcomp: "wqo (Inr p2') (Inr vpsi)"
          by (auto simp: p2'_def)
        have "wqo (Inr (VUntil i [p2'] (p1'))) q"
          using wqo_p1 Inr bv VUntil[OF wqo_p1[unfolded p1'_def] lcomp]
          by (auto simp add: p1'_def p2'_def)
        moreover have "Inr (VUntil i [projr p2] (projr p1)) \<in> set (doUntilBase i (left I) p1 p2)"
          using assms check_consistent * p_val "0"
          unfolding doUntilBase_def optimal_def valid_def
          by (auto split: sum.splits)
        ultimately have "wqo minp q" using min_list_wrt_le[OF _ refl_wqo]
            untilBase_sound[OF i_props p1_def p2_def] pw_total[of i "Until phi I psi"]
            trans_wqo Inr minp
          apply (auto simp add: total_on_def p1'_def p2'_def)
          by (metis transpD)
      }
      moreover
      {fix vpsi
        assume bv: "b = VUntil_never i i [vpsi]"
        then have p_val: "valid rho i psi (Inr vpsi)" using Inr q_val bf "0"
          unfolding valid_def by (auto simp: Let_def split: enat.splits if_splits)
        then have wqo_p2: "wqo p2 (Inr vpsi)" using p2_def unfolding optimal_def
          by auto
        then have lcomp: "wqo p2 (Inr vpsi)"
          by auto
        obtain p2' where p2'_def: "p2 = Inr p2'"
          using p_val p2_def check_consistent[OF bf_psi]
          by (auto simp add: optimal_def valid_def split: sum.splits)
        have "wqo (Inr (VUntil_never i i [p2'])) q"
          using bv Inr VUntil_never lcomp
          by (auto simp add: p2'_def)
        moreover have "Inr (VUntil_never i i [p2']) \<in> set (doUntilBase i (left I) p1 p2)"
          using assms check_consistent * p_val "0"
          unfolding doUntilBase_def optimal_def valid_def
          by (auto split: sum.splits simp: p2'_def)
        ultimately have "wqo minp q" using min_list_wrt_le[OF _ refl_wqo]
            untilBase_sound[OF i_props p1_def p2_def] pw_total[of i "Until phi I psi"]
            trans_wqo Inr minp
          apply (auto simp add: total_on_def p2'_def)
          by (metis transpD)
      }
      ultimately show ?thesis using minp Inr "0" q_val assms **
        unfolding doUntilBase_def valid_def
        apply (cases b)
                            apply (auto simp: Let_def split: if_splits)
            apply fastforce
        using i_ge_etpi le_trans apply blast
          apply fastforce
         apply (simp add: i_le_ltpi_add)
        using i_ge_etpi i_le_ltpi_add le_trans by blast
    next
      {fix n j
        assume j_def: "right I = enat n \<and> ETP rho (\<tau> rho i) \<le> j
       \<and> j \<le> LTP rho (\<tau> rho i + n) \<and> j \<ge> i"
        from \<tau>_mono have "\<tau> rho i + n \<ge> \<tau> rho 0"  by (auto simp add: trans_le_add1)
        then have jin: "\<tau> rho j \<le> \<tau> rho i + n" using j_def i_ltp_to_tau by auto
        from \<tau>_mono have j_gei: "\<forall>j > i. \<tau> rho j \<ge> \<tau> rho (i+1)" by auto
        from this i_props j_def have "\<forall>j > i. \<tau> rho j \<ge> \<tau> rho i + n"
          apply auto
          by (smt Suc_eq_plus1 diff_is_0_eq' j_gei le_add_diff_inverse le_trans less_imp_le_nat less_nat_zero_code nat_add_left_cancel_le nat_le_linear)
        then have "j = i" using j_def jin apply auto
          by (metis dual_order.strict_implies_not_eq add_diff_cancel_left' add_diff_cancel_right' i_props j_gei le_antisym le_neq_implies_less less_add_one)
      } note ** = this
      case (Suc nat)
      then have "minp = Inr (VUntil_never i i []) \<or> minp = Inr (VUntil i [] (projr p1))"
        using minp assms q_val Inr filter_nnil
        unfolding doUntilBase_def valid_def
        by (cases p1; cases p2; auto simp: min_list_wrt_def)
      moreover
      {fix hi vpsis
        assume bv: "b = VUntil_never i hi vpsis"
        have vpsis_Nil: "vpsis = []"
          using q_val
          by (auto simp: Inr bv valid_def Let_def split: enat.splits if_splits)
            (smt (z3) "**" Lattices.linorder_class.max.cobounded2 Suc Suc_n_not_le_n add_Suc_shift i_etp_to_tau le_add1 le_trans max_def)
        have hi_def: "hi = i"
          using q_val
          using i_le_ltpi_add
          apply (auto simp: Inr bv valid_def vpsis_Nil split: if_splits)
           apply blast
          by (metis Groups.ab_semigroup_add_class.add.commute LTP_lt_delta diff_add_inverse2 enat_ord_simps(2) i_props plus_1_eq_Suc)
        have "wqo (Inr (VUntil_never i hi [])) q"
          using not_wqo q_val
          by (auto simp: Inr bv vpsis_Nil)
        moreover have "Inr (VUntil_never i i []) \<in> set (doUntilBase i (left I) p1 p2)"
          using assms check_consistent Suc
          unfolding doUntilBase_def optimal_def valid_def
          by (auto split: sum.splits)
        ultimately have "wqo minp q" using min_list_wrt_le[OF _ refl_wqo]
            untilBase_sound[OF i_props p1_def p2_def] pw_total[of i "Until phi I psi"]
            trans_wqo Inr minp
          apply (auto simp add: total_on_def hi_def)
          by (metis transpD)
      }
      moreover
      {fix vphi vpsis
        assume bv: "b = VUntil i vpsis vphi"
        then have p_val: "valid rho i phi (Inr vphi)"
          using Inr q_val i_props Suc ** i_ge_etpi unfolding valid_def
          apply (auto simp: Let_def split: enat.splits if_splits)
          using le_trans apply blast
          using le_trans by blast
        then have p1_wqo: "wqo p1 (Inr vphi)" using p1_def unfolding optimal_def
          by auto
        have vpsis_Nil: "vpsis = []"
          using q_val i_props
          by (auto simp: Inr bv valid_def Let_def split: if_splits enat.splits)
            (metis "**" Suc Zero_not_Suc add_diff_cancel_left' diff_is_0_eq' i_etp_to_tau i_ge_etpi le_trans)
        obtain p1' where p1'_def: "p1 = Inr p1'"
          using p_val p1_def check_consistent[OF bf_phi]
          by (auto simp add: optimal_def valid_def split: sum.splits)
        have "wqo (Inr (VUntil i [] (projr p1))) q"
          using Inr bv VUntil_Nil[OF p1_wqo[unfolded p1'_def]]
          by (fastforce simp add: p1'_def map_idI vpsis_Nil)
        moreover have "Inr (VUntil i [] (projr p1)) \<in> set (doUntilBase i (left I) p1 p2)"
          using assms check_consistent Suc p_val
          unfolding doUntilBase_def optimal_def valid_def
          by (auto split: sum.splits)
        ultimately have "wqo minp q" using min_list_wrt_le[OF _ refl_wqo]
            untilBase_sound[OF i_props p1_def p2_def] pw_total[of i "Until phi I psi"]
            trans_wqo Inr minp
          apply (auto simp add: total_on_def)
          by (metis transpD)
      }
      ultimately show ?thesis using assms minp q_val Inr Suc
        unfolding doUntilBase_def valid_def
        by (cases b) auto
    qed
  qed
  then show False using q_le by auto
qed

lemma prev_sound:
  assumes i_props: "i > 0" and
    p1_def: "optimal (i-1) phi p1" and
    p_def: "p \<in> set (doPrev i I (\<Delta> rho i) p1)"
  shows "valid rho i (Prev I phi) p"
proof (cases p1)
  define \<tau> where \<tau>_def: "\<tau> \<equiv> \<Delta> rho i"
  case (Inl a)
  {assume \<tau>_ge: "enat \<tau> > right I"
    then have "\<tau> > left I" using i_props left_right[of I] \<tau>_def  apply auto
      by (metis (no_types, lifting) One_nat_def diff_less enat_ord_simps(1) enat_trans less_enatE nat_less_le r_less_Delta_imp_less zero_less_one)
    then have "p = Inr (VPrev_ge i)" using i_props \<tau>_def Inl p_def \<tau>_ge
      unfolding doPrev_def
      by (auto split: if_splits)
    then have "valid rho i (Prev I phi) p" using \<tau>_def \<tau>_ge i_props unfolding valid_def
      by auto
  }
  moreover
  {assume \<tau>_le: "\<tau> < left I"
    then have "p = Inr (VPrev_le i)" using i_props \<tau>_def Inl p_def
      unfolding doPrev_def by auto
    then have "valid rho i (Prev I phi) p" using \<tau>_def \<tau>_le i_props unfolding valid_def
      by auto
  }
  moreover
  {assume \<tau>_in: "mem \<tau> I"
    then have "p = Inl (SPrev (projl p1))" using Inl \<tau>_def p_def unfolding doPrev_def
      by auto
    then have "valid rho i (Prev I phi) p" using p1_def Inl \<tau>_def \<tau>_in i_props
      unfolding optimal_def valid_def by auto
  }
  ultimately show ?thesis using Inl assms \<tau>_def
    unfolding doPrev_def optimal_def valid_def
    by (auto split: sum.splits if_splits)
next
  define \<tau> where \<tau>_def: "\<tau> \<equiv> \<Delta> rho i"
  case (Inr b)
  {assume \<tau>_ge: "enat \<tau> > right I"
    then have "\<tau> > left I" using i_props left_right[of I] \<tau>_def  apply auto
      by (metis (no_types, lifting) One_nat_def diff_less enat_ord_simps(1) enat_trans less_enatE nat_less_le r_less_Delta_imp_less zero_less_one)
    then have "p = Inr (VPrev_ge i) \<or> p = Inr (VPrev (projr p1))" using i_props \<tau>_def Inr p_def \<tau>_ge
      unfolding doPrev_def
      by (auto split: if_splits)
    then have "valid rho i (Prev I phi) p" using p1_def \<tau>_def \<tau>_ge i_props Inr
      unfolding valid_def optimal_def
      by auto
  }
  moreover
  {assume \<tau>_le: "\<tau> < left I"
    then have "p = Inr (VPrev_le i) \<or> p = Inr (VPrev (projr p1))"
      using i_props \<tau>_def Inr p_def
      unfolding doPrev_def by auto
    then have "valid rho i (Prev I phi) p" using p1_def \<tau>_def \<tau>_le i_props Inr
      unfolding valid_def optimal_def
      by auto
  }
  moreover
  {assume \<tau>_in: "mem \<tau> I"
    then have "p = Inr (VPrev (projr p1))" using Inr \<tau>_def p_def unfolding doPrev_def
      by auto
    then have "valid rho i (Prev I phi) p" using p1_def Inr \<tau>_def \<tau>_in i_props
      unfolding optimal_def valid_def by auto
  }
  ultimately show ?thesis using assms Inr \<tau>_def
    unfolding doPrev_def optimal_def valid_def
    by (auto split: sum.splits if_splits)
qed

lemma prev_optimal:
  assumes i_props: "i > 0" and
    p1_def: "optimal (i-1) phi p1" and bf: "bounded_future (Prev I phi)"
  shows "optimal i (Prev I phi) (min_list_wrt wqo (doPrev i I (\<Delta> rho i) p1))"
proof (rule ccontr)
  have bf_phi: "bounded_future phi"
    using bf by auto
  from doPrev_def[of i I "\<Delta> rho i" p1]
  have nnil: "doPrev i I (\<Delta> rho i) p1 \<noteq> []"
    by (cases p1; cases "left I"; cases "\<Delta> rho i < left I"; auto)
  from pw_total[of i "Prev I phi"] have total_set: "total_on wqo (set (doPrev i I (\<Delta> rho i) p1))"
    using prev_sound[OF i_props p1_def]
    by (metis not_wqo total_onI)
  have filter_nnil: "filter (\<lambda>x. \<forall>y \<in> set (doPrev i I (\<Delta> rho i) p1). wqo x y) (doPrev i I (\<Delta> rho i) p1) \<noteq> []"
    using refl_total_transp_imp_ex_min[OF nnil refl_wqo total_set trans_wqo]
      filter_empty_conv[of "(\<lambda>x. \<forall>y \<in> set (doPrev i I (\<Delta> rho i) p1). wqo x y)" "(doPrev i I (\<Delta> rho i) p1)"]
    by simp
  define minp where minp: "minp \<equiv> min_list_wrt wqo (doPrev i I (\<Delta> rho i) p1)"
  assume nopt: "\<not> optimal i (Prev I phi) minp"
  from prev_sound[OF i_props p1_def min_list_wrt_in[OF nnil total_set refl_wqo trans_wqo]]
    minp
  have vmin: "valid rho i (Prev I phi) minp" 
    by auto
  then obtain q where q_val: "valid rho i (Prev I phi) q" and
    q_le: "\<not> wqo minp q" using minp nopt unfolding optimal_def by auto
  then have "wqo minp q" using minp
  proof(cases q)
    case (Inl a)
    then have SATp: "SAT rho i (Prev I phi)" using q_val check_sound(1)
      unfolding valid_def
      by auto
    then have satp: "sat rho i (Prev I phi)" using soundness
      by blast
    then have sat_phi: "sat rho (i-1) phi \<and> mem (\<Delta> rho i) I"
      using sat.simps(9)[of rho i I phi] i_props
      by (auto split: nat.splits)
    then have SAT_phi: "SAT rho (i-1) phi" using completeness[of rho _ phi] i_props bf
      by auto
    then have sp1: "\<exists>p1'. p1 = Inl p1'" using p1_def unfolding optimal_def valid_def
      apply (cases p1) apply auto
      by (metis check_sound(2) soundness)
    then have mins: "minp = Inl (SPrev (projl p1))"
      using minp sat_phi refl_wqo SPrev optimal_def p1_def
      unfolding doPrev_def
      by (auto simp: min_list_wrt_def)
    from Inl obtain sphi where a_def: "a = SPrev sphi"
      using q_val unfolding valid_def
      by (cases a) auto
    then have p_val: "valid rho (i-1) phi (Inl sphi)" using Inl q_val i_props
      unfolding valid_def
      by (auto simp: Let_def)
    then have p1_wqo: "wqo p1 (Inl sphi)" using p1_def unfolding optimal_def
      by auto
    obtain p1' where p1'_def: "p1 = Inl p1'"
      using p_val p1_def check_consistent[OF bf_phi]
      by (auto simp add: optimal_def valid_def split: sum.splits)
    have "wqo (Inl (SPrev (projl p1))) q"
      using Inl a_def SPrev[OF p1_wqo[unfolded p1'_def]]
      by (auto simp add: p1'_def)
    then show ?thesis using mins minp by auto
  next
    case (Inr b)
    then have "VIO rho i (Prev I phi)"
      using q_val
      unfolding valid_def
      by (cases b) (auto simp add: MTL.SAT_VIO.intros check_sound(2))
    then obtain b' where b'_def: "minp = Inr b'"
      using val_VIO_imp_r[OF bf] vmin
      unfolding valid_def
      by auto
    then have "(\<exists>a. b' = VPrev a) \<or> b' = VPrev_le i
    \<or> b' = VPrev_ge i"
      using vmin i_props
      unfolding valid_def
      by (cases b') auto
    moreover
    {assume bv: "b = VPrev_le i"
      then have d_le: "\<Delta> rho i < left I" using q_val Inr unfolding valid_def
        by auto
      then have "q \<in> set (doPrev i I (\<Delta> rho i) p1)" using Inr bv
        unfolding doPrev_def
        by (cases p1) auto
      then have "wqo minp q" using d_le Inr bv minp filter_nnil
        unfolding doPrev_def
        by (cases p1) (auto simp add: min_list_wrt_def refl_wqo reflpD)
    }
    moreover
    {assume bv: "b = VPrev_ge i"
      then have d_ge: "enat (\<Delta> rho i) > right I" using q_val Inr unfolding valid_def
        by auto
      then have d_gel: "\<Delta> rho i > left I" using left_right[of I] i_props apply auto
        by (smt One_nat_def diff_less enat_ord_simps(1) enat_trans less_enatE nat_less_le r_less_Delta_imp_less zero_less_one)
      then have "q \<in> set (doPrev i I (\<Delta> rho i) p1)" using Inr bv d_ge
        unfolding doPrev_def
        by (cases p1) auto
      then have "wqo minp q" using d_ge Inr bv minp d_gel filter_nnil
        unfolding doPrev_def
        by (cases p1) (auto simp add: min_list_wrt_def refl_wqo reflpD)
    }
    moreover
    {fix vphi
      assume bv: "b = VPrev vphi"
      then have p_val: "valid rho (i-1) phi (Inr vphi)" using Inr q_val
        unfolding valid_def by auto
      then have p1_wqo: "wqo p1 (Inr vphi)" using p1_def unfolding optimal_def
        by auto
      obtain p1' where p1'_def: "p1 = Inr p1'"
        using p_val p1_def check_consistent[OF bf_phi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      have "wqo (Inr (VPrev (projr p1))) q"
        using bv Inr VPrev[OF p1_wqo[unfolded p1'_def]] by (auto simp add: p1'_def)
      moreover have "Inr (VPrev (projr p1)) \<in> set (doPrev i I (\<Delta> rho i) p1)"
        using assms p_val check_consistent unfolding doPrev_def optimal_def valid_def
        by (cases p1; cases "\<Delta> rho i < left I") auto
      ultimately have "wqo minp q" using minp bv min_list_wrt_le[OF _ refl_wqo]
          prev_sound[OF i_props p1_def] pw_total[of i "Prev I phi"]
          trans_wqo Inr
        apply (auto simp add: total_on_def)
        by (metis transpD)
    }
    ultimately show ?thesis using q_val Inr assms unfolding doPrev_def valid_def
      by (cases b) auto
  qed
  then show False using q_le by auto
qed

lemma next_sound:
  assumes p1_def: "optimal (i+1) phi p1" and
    p_def: "p \<in> set (doNext i I (\<Delta> rho (i+1)) p1)"
  shows "valid rho i (Next I phi) p"
proof (cases p1)
  define \<tau> where \<tau>_def: "\<tau> \<equiv> \<Delta> rho (i+1)"
  case (Inl a)
  {assume \<tau>_le: "\<tau> < left I"
    then have "p = Inr (VNext_le i)" using \<tau>_def p_def Inl unfolding doNext_def
      by auto
    then have "valid rho i (Next I phi) p" using \<tau>_le \<tau>_def
      unfolding valid_def by auto
  }
  moreover
  {assume \<tau>_ge: "enat \<tau> > right I"
    then have n_\<tau>_ler:"\<not> enat \<tau> \<le> right I" by auto
    from \<tau>_ge have \<tau>_gel: "\<tau> > left I" using left_right
      by (meson enat_ord_simps(2) less_le_trans not_le)
    then have "p = Inr (VNext_ge i)" using n_\<tau>_ler \<tau>_ge \<tau>_def p_def Inl
      unfolding doNext_def by auto
    then have "valid rho i (Next I phi) p" using n_\<tau>_ler \<tau>_ge \<tau>_def p_def Inl \<tau>_gel
      unfolding valid_def doNext_def by auto
  }
  moreover
  {assume \<tau>_in: "mem \<tau> I"
    then have "p = Inl (SNext (projl p1))" using \<tau>_def Inl p_def unfolding doNext_def
      by auto
    then have "valid rho i (Next I phi) p" using p1_def \<tau>_def \<tau>_in Inl p_def
      unfolding doNext_def valid_def optimal_def
      by (auto simp: Let_def)
  }
  ultimately show ?thesis using \<tau>_def Inl assms
    unfolding doNext_def optimal_def valid_def
    by (auto split: sum.splits if_splits)
next
  define \<tau> where \<tau>_def: "\<tau> \<equiv> \<Delta> rho (i+1)"
  case (Inr b)
  {assume \<tau>_le: "\<tau> < left I"
    then have "p = Inr (VNext_le i) \<or> p = Inr (VNext (projr p1))"
      using \<tau>_def p_def Inr unfolding doNext_def
      by auto
    then have "valid rho i (Next I phi) p" using \<tau>_le \<tau>_def p1_def p_def
      unfolding valid_def optimal_def doNext_def by (cases p1) auto
  }
  moreover
  {assume \<tau>_ge: "enat \<tau> > right I"
    then have n_\<tau>_ler:"\<not> enat \<tau> \<le> right I" by auto
    from \<tau>_ge have \<tau>_gel: "\<tau> > left I" using left_right
      by (meson enat_ord_simps(2) less_le_trans not_le)
    then have "p = Inr (VNext_ge i) \<or> p = Inr (VNext (projr p1))"
      using n_\<tau>_ler \<tau>_ge \<tau>_def p_def Inr
      unfolding doNext_def by auto
    then have "valid rho i (Next I phi) p" using \<tau>_ge \<tau>_gel n_\<tau>_ler \<tau>_def p1_def p_def
      unfolding valid_def optimal_def doNext_def by (cases p1) auto
  }
  moreover
  {assume \<tau>_in: "mem \<tau> I"
    then have "p = Inr (VNext (projr p1))" using \<tau>_def Inr p_def unfolding doNext_def
      by auto
    then have "valid rho i (Next I phi) p" using p1_def \<tau>_def \<tau>_in Inr p_def
      unfolding doNext_def valid_def optimal_def
      by (auto simp: Let_def)
  }
  ultimately show ?thesis using \<tau>_def Inr assms
    unfolding doNext_def optimal_def valid_def
    by (auto split: sum.splits if_splits)
qed

lemma next_optimal:
  assumes p1_def: "optimal (i+1) phi p1" and
    bf: "bounded_future (Next I phi)"
  shows "optimal i (Next I phi) (min_list_wrt wqo (doNext i I (\<Delta> rho (i+1)) p1))"
proof (rule ccontr)
  have bf_phi: "bounded_future phi"
    using bf by auto
  from doNext_def[of i I "\<Delta> rho (i+1)" p1]
  have nnil: "doNext i I (\<Delta> rho (i+1)) p1 \<noteq> []"
    by (cases p1; cases "left I"; cases "\<Delta> rho (i+1) < left I"; auto)
  from pw_total[of i "Next I phi"] have total_set: "total_on wqo (set (doNext i I (\<Delta> rho (i+1)) p1))"
    using next_sound[OF p1_def]
    by (metis not_wqo total_onI)
  have filter_nnil: "filter (\<lambda>x. \<forall>y \<in> set (doNext i I (\<Delta> rho (i+1)) p1). wqo x y) (doNext i I (\<Delta> rho (i+1)) p1) \<noteq> []"
    using refl_total_transp_imp_ex_min[OF nnil refl_wqo total_set trans_wqo]
      filter_empty_conv[of "(\<lambda>x. \<forall>y \<in> set (doNext i I (\<Delta> rho (i+1)) p1). wqo x y)" "(doNext i I (\<Delta> rho (i+1)) p1)"]
    by simp
  define minp where minp: "minp \<equiv> min_list_wrt wqo (doNext i I (\<Delta> rho (i+1)) p1)"
  assume nopt: "\<not> optimal i (Next I phi) minp"
  from next_sound[OF p1_def min_list_wrt_in] total_set refl_wqo trans_wqo nnil minp
  have vmin: "valid rho i (Next I phi) minp"
    by auto
  then obtain q where q_val: "valid rho i (Next I phi) q" and
    q_le: "\<not> wqo minp q" using minp nopt unfolding optimal_def by auto
  then have "wqo minp q" using minp
  proof(cases q)
    case (Inl a)
    then have SATn: "SAT rho i (Next I phi)" using q_val check_sound(1)
      unfolding valid_def
      by auto
    then have satn: "sat rho i (Next I phi)" using soundness
      by blast
    then have sat_phi: "sat rho (i+1) phi \<and> mem (\<Delta> rho (i+1)) I"
      using sat.simps(9)[of rho i I phi]
      by (auto split: nat.splits)
    then have SAT_phi: "SAT rho (i+1) phi" using completeness[of rho _ phi] bf
      by auto
    then have sp1: "\<exists>p1'. p1 = Inl p1'" using p1_def unfolding optimal_def valid_def
      apply (cases p1) apply auto
      using bf check_sound(2) soundness by fastforce
    then have mins: "minp = Inl (SNext (projl p1))"
      using minp sat_phi filter_nnil
      unfolding doNext_def
      by (auto simp: min_list_wrt_def)
    from Inl obtain sphi where a_def: "a = SNext sphi"
      using q_val unfolding valid_def
      by (cases a) auto
    then have p_val: "valid rho (i+1) phi (Inl sphi)" using Inl q_val
      unfolding valid_def
      by (auto simp: Let_def)
    then have p1_wqo: "wqo p1 (Inl sphi)" using p1_def unfolding optimal_def
      by auto
    obtain p1' where p1'_def: "p1 = Inl p1'"
      using p_val p1_def check_consistent[OF bf_phi]
      by (auto simp add: optimal_def valid_def split: sum.splits)
    have "wqo (Inl (SNext (projl p1))) q"
      using Inl a_def SNext[OF p1_wqo[unfolded p1'_def]] by (auto simp add: p1'_def)
    then show ?thesis using mins minp by auto
  next
    case (Inr b)
    then have "VIO rho i (Next I phi)"
      using q_val
      unfolding valid_def
      by (cases b) (auto simp add: MTL.SAT_VIO.intros check_sound(2))
    then obtain b' where b'_def: "minp = Inr b'"
      using val_VIO_imp_r[OF bf] vmin
      unfolding valid_def
      by auto
    then have "(\<exists>a. b' = VNext a) \<or> b' = VNext_le i
    \<or> b' = VNext_ge i"
      using vmin
      unfolding valid_def
      by (cases b') auto
    moreover
    {assume bv: "b = VNext_le i"
      then have d_le: "\<Delta> rho (i+1) < left I" using q_val Inr unfolding valid_def
        by auto
      then have "q \<in> set (doNext i I (\<Delta> rho (i+1)) p1)" using Inr bv
        unfolding doNext_def
        by (cases p1) auto
      then have "wqo minp q"
        using d_le Inr bv minp filter_nnil
        unfolding doNext_def
        by (cases p1) (auto simp: refl_wqo reflpD min_list_wrt_def)
    }
    moreover
    {assume bv: "b = VNext_ge i"
      then have d_ge: "enat (\<Delta> rho (i+1)) > right I" using q_val Inr unfolding valid_def
        by auto
      then have d_gel: "\<Delta> rho (i+1) > left I" using left_right[of I]
        apply auto
        using enat_ord_simps(2) le_less_trans by blast
      then have "q \<in> set (doNext i I (\<Delta> rho (i+1)) p1)" using Inr bv d_ge
        unfolding doNext_def
        by (cases p1) auto
      then have "wqo minp q"
        using d_ge Inr bv minp d_gel filter_nnil
        unfolding doNext_def
        by (cases p1) (auto simp add: refl_wqo reflpD min_list_wrt_def)
    }
    moreover
    {fix vphi
      assume bv: "b = VNext vphi"
      then have p_val: "valid rho (i+1) phi (Inr vphi)" using Inr q_val
        unfolding valid_def by auto
      then have p1_wqo: "wqo p1 (Inr vphi)" using p1_def unfolding optimal_def
        by auto
      obtain p1' where p1'_def: "p1 = Inr p1'"
        using p_val p1_def check_consistent[OF bf_phi]
        by (auto simp add: optimal_def valid_def split: sum.splits)
      have "wqo (Inr (VNext (projr p1))) q"
        using bv Inr VNext[OF p1_wqo[unfolded p1'_def]] by (auto simp add: p1'_def)
      moreover have "Inr (VNext (projr p1)) \<in> set (doNext i I (\<Delta> rho (i+1)) p1)"
        using assms p_val check_consistent unfolding doNext_def optimal_def valid_def
        by (cases p1; cases "\<Delta> rho (i+1) < left I") auto
      ultimately have "wqo minp q"
        using minp bv min_list_wrt_le[OF _ refl_wqo]
          next_sound[OF p1_def] pw_total[of i "Next I phi"]
          trans_wqo Inr
        apply (auto simp add: total_on_def)
        by (metis transpD)
    }
    ultimately show ?thesis using q_val Inr assms unfolding valid_def
      by (cases b) auto
  qed
  then show False using q_le by auto
qed

lemma diff_cancel_middle:
  fixes a b c :: nat
  shows "b + a \<ge> c \<Longrightarrow> a - (b + a - c) = c - b"
  by simp

lemma since_sound:
  assumes i_props: "i > 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I
  \<and> right I \<ge> enat (\<Delta> rho i)" and
    p1_def: "optimal i phi p1" and p2_def: "optimal i psi p2" and
    p'_def: "optimal (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) p'"
    and p_def: "p \<in> set (doSince i (left I) p1 p2 p')"
    and bf: "bounded_future (Since phi I psi)"
    and bf': "bounded_future (Since phi (subtract (\<Delta> rho i) I) psi)"
  shows "valid rho i (Since phi I psi) p"
proof (cases p')
  case (Inl a)
  then have p'l: "p' = Inl a" by auto
  then have satp': "sat rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi)"
    using soundness p'_def check_sound(1)[of rho "Since phi (subtract (\<Delta> rho i) I) psi" a]
    unfolding optimal_def valid_def by fastforce
  then obtain q qs where a_def: "a = SSince q qs" using Inl p'_def
    unfolding optimal_def valid_def by (cases a) auto
  then have a_val: "s_check rho (Since phi (subtract (\<Delta> rho i) I) psi) a"
    using Inl p'_def unfolding optimal_def valid_def by (auto simp: Let_def)
  then have mem: "mem (delta rho (i-1) (s_at q)) (subtract (\<Delta> rho i) I)"
    using a_def Inl p'_def s_check.simps unfolding optimal_def valid_def
    by (auto simp: Let_def)
  then have "left I - \<Delta> rho i \<le> delta rho (i-1) (s_at q)" by auto
  then have tmp: "left I \<le> \<tau> rho i - \<tau> rho (i-1) + (\<tau> rho (i-1) - \<tau> rho (s_at q))"
    by auto
  from a_val have qi: "(s_at q) \<le> (i-1)" using a_def p'l p'_def
    unfolding optimal_def valid_def
    by (auto simp: Let_def)
  then have liq: "left I \<le> delta rho i (s_at q)" using diff_add_assoc tmp
    by auto
  show ?thesis
  proof (cases "right I")
    case n_def: (enat n)
    from mem n_def have "enat (delta rho (i-1) (s_at q)) \<le> enat n - enat (\<Delta> rho i)"
      by auto
    then have "delta rho (i-1) (s_at q) + \<Delta> rho i \<le> n"
      apply auto
      by (metis One_nat_def enat_ord_simps(1) i_props le_diff_conv le_diff_conv2 n_def)
    then have riq: "enat (delta rho i (s_at q)) \<le> right I" using n_def by auto
    then show ?thesis
    proof (cases "left I = 0")
      case True
      then show ?thesis
      proof (cases p1)
        case (Inl a1)
        then have p1l: "p1 = Inl a1" by auto
        then show ?thesis
        proof (cases p2)
          case (Inl a2)
          then have por: "p = p' \<oplus> p1 \<or> p = Inl (SSince (projl p2) [])"
            using a_def p'l p1l True p_def unfolding doSince_def by auto
          moreover
          {
            assume pplus: "p = p' \<oplus> p1"
            then have "p = Inl (SSince q (qs @ [projl p1]))" using a_def p'l p1l
                p'_def p1_def unfolding proofApp_def by auto
            then have "valid rho i (Since phi I psi) p"
              using a_def True p'_def p1_def p'l p1l i_props liq riq
              unfolding optimal_def valid_def
              apply (auto simp: Let_def split: list.splits)
              by (metis Suc_pred i_props upt_Suc_append)
          }
          ultimately show ?thesis
            using Inl p1l True assms n_def unfolding optimal_def valid_def
            by auto
        next
          case (Inr b2)
          then have pplus: "p = p' \<oplus> p1" using p1l p_def True p'l
            unfolding doSince_def by auto
          then have "p = Inl (SSince q (qs @ [projl p1]))" using a_def p'l p1l
              p'_def p1_def unfolding proofApp_def by auto
          then show ?thesis
            using a_def True p'_def p1_def p'l p1l i_props liq riq n_def
            unfolding optimal_def valid_def
            apply (auto simp: Let_def split: list.splits)
            by (metis Suc_pred i_props upt_Suc_append)
        qed
      next
        case (Inr b1)
        then have p1r: "p1 = Inr b1" by auto
        then show ?thesis
        proof (cases p2)
          case (Inl a2)
          then have "p = Inl (SSince (projl p2) [])" using p_def Inr True p'l
            unfolding doSince_def by auto
          then show ?thesis using p2_def True Inl Inr p'l i_props zero_enat_def
            unfolding optimal_def valid_def by auto
        next
          case (Inr b2)
          then have "p = Inr (VSince i (projr p1) [projr p2])" using p1r True p'l p_def
            unfolding doSince_def by auto
          then show ?thesis using i_props p1_def p2_def True p1r Inr bf n_def
            unfolding optimal_def valid_def
            apply (auto split: enat.splits)
            using diff_le_self i_etp_to_tau apply blast
            using i_le_ltpi by blast
        qed
      qed
    next
      case False
      then show ?thesis
      proof (cases p1)
        case (Inl a1)
        then have pplus: "p = p' \<oplus> p1" using p_def False p'l
          unfolding doSince_def by (cases p2) auto
        then have pl: "p = Inl (SSince q (qs @ [projl p1]))" using a_def p'l Inl
          unfolding proofApp_def by auto thm s_check.simps
        from p'_def p'l a_def Inl i_props liq riq have p'_props:
          "map s_at qs = [Suc (s_at q) ..< i] \<and> (\<forall>q' \<in> set qs. s_check rho phi q')"
          unfolding optimal_def valid_def
          apply (auto simp: Let_def split: list.splits if_splits)
           apply (metis One_nat_def Suc_diff_1 Suc_leI diff_Suc_less le_add_diff_inverse2 upt_eq_Cons_conv upt_eq_Nil_conv)
          by (metis One_nat_def Suc_diff_1 upt_Suc_append)
        then have map_eq: "map s_at (qs @ [projl p1]) = [Suc (s_at q) ..< Suc i]
            \<and> (\<forall>q' \<in> set (qs @ [projl p1]). s_check rho phi q')"
          using Inl p1_def i_props qi
          by (auto simp: optimal_def valid_def)
        from pl p1_def Inl have at_p1: "s_at (last (qs @ [projl p1])) = s_at a1"
          by (auto simp: optimal_def valid_def)
        from a_def p'_def p'l have "s_check rho psi q \<and> mem (delta rho i (s_at q)) I"
          using liq riq
          by (auto simp: Let_def optimal_def valid_def)
        then show ?thesis
          using False pl Inl p1_def i_props liq riq map_eq at_p1
          unfolding optimal_def valid_def
          apply (auto simp: Let_def n_def at_p1 split: if_splits list.splits)
          by (metis last_ConsR last_snoc)+
      next
        case (Inr b1)
        then have "p = Inr (VSince i (projr p1) [])" using Inr False p'l p_def
          unfolding doSince_def by (cases p2) auto
        then show ?thesis using p1_def i_props Inr False bf
          unfolding optimal_def valid_def
          by (auto simp add: i_etp_to_tau Let_def False i_ltp_to_tau le_diff_conv2
              split: enat.splits)
      qed
    qed
  next
    case infinity
    then have riq: "enat (delta rho i (s_at q)) \<le> right I" by auto
    then show ?thesis
    proof (cases "left I = 0")
      case True
      then show ?thesis
      proof (cases p1)
        case (Inl a1)
        then have p1l: "p1 = Inl a1" by auto
        then show ?thesis
        proof (cases p2)
          case (Inl a2)
          then have por: "p = p' \<oplus> p1 \<or> p = Inl (SSince (projl p2) [])"
            using a_def p'l p1l True p_def unfolding doSince_def by auto
          moreover
          {
            assume pplus: "p = p' \<oplus> p1"
            then have "p = Inl (SSince q (qs @ [projl p1]))" using a_def p'l p1l
                p'_def p1_def unfolding proofApp_def by auto
            then have "valid rho i (Since phi I psi) p"
              using a_def True p'_def p1_def p'l p1l i_props liq riq
              unfolding optimal_def valid_def
              apply (auto simp: Let_def split: list.splits)
              by (metis Suc_pred i_props upt_Suc_append)
          }
          ultimately show ?thesis
            using Inl p1l True assms infinity unfolding optimal_def valid_def
            by auto
        next
          case (Inr b2)
          then have pplus: "p = p' \<oplus> p1" using p1l p_def True p'l
            unfolding doSince_def by auto
          then have "p = Inl (SSince q (qs @ [projl p1]))" using a_def p'l p1l
              p'_def p1_def unfolding proofApp_def by auto
          then show ?thesis
            using a_def True p'_def p1_def p'l p1l i_props liq riq infinity
            unfolding optimal_def valid_def
            apply (auto simp: Let_def split: list.splits)
            by (metis Suc_pred i_props upt_Suc_append)
        qed
      next
        case (Inr b1)
        then have p1r: "p1 = Inr b1" by auto
        then show ?thesis
        proof (cases p2)
          case (Inl a2)
          then have "p = Inl (SSince (projl p2) [])" using p_def Inr True p'l
            unfolding doSince_def by auto
          then show ?thesis using p2_def True Inl Inr p'l i_props zero_enat_def
            unfolding optimal_def valid_def by auto
        next
          case (Inr b2)
          then have "p = Inr (VSince i (projr p1) [projr p2])" using p1r True p'l p_def
            unfolding doSince_def by auto
          then show ?thesis using i_props p1_def p2_def True p1r Inr bf infinity
            unfolding optimal_def valid_def
            apply (auto split: enat.splits)
            using i_le_ltpi by blast
        qed
      qed
    next
      case False
      then show ?thesis
      proof (cases p1)
        case (Inl a1)
        then have pplus: "p = p' \<oplus> p1" using p_def False p'l
          unfolding doSince_def by (cases p2) auto
        then have pl: "p = Inl (SSince q (qs @ [projl p1]))" using a_def p'l Inl
          unfolding proofApp_def by auto
        then show ?thesis
          using False p1_def p'_def Inl i_props liq riq a_def p'l infinity
          unfolding optimal_def valid_def
          apply (auto simp: Let_def split: list.splits if_splits)
           apply (simp_all add: Cons_eq_upt_conv)
          apply (metis One_nat_def Suc_diff_1 i_props upt_Suc_append)
          done
      next
        case (Inr b1)
        then have "p = Inr (VSince i (projr p1) [])" using Inr False p'l p_def
          unfolding doSince_def by (cases p2) auto
        then show ?thesis using p1_def i_props Inr False bf
          unfolding optimal_def valid_def
          by (auto simp add: i_etp_to_tau Let_def False i_ltp_to_tau le_diff_conv2
              split: enat.splits)
      qed
    qed
  qed
next
  case (Inr b)
  then have p'r: "p' = Inr b" by auto
  then show ?thesis
  proof (cases b)
    case VFF
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VAtm x11 x12)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VNeg x2)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VDisj x31 x32)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VConjL x31)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VConjR x31)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VImpl x71 x72)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VIff_sv x71 x72)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VIff_vs x71 x72)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VOnce_le x8)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VOnce_never x71 x72)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VUntil x51 x52 x53)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VUntil_never x71 x72)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VSince_le x8)
    then have c: "\<tau> rho (i-1) < \<tau> rho 0 + (left I - \<Delta> rho i)" using p'r p'_def
      unfolding optimal_def valid_def by auto
    then have "\<tau> rho (i-1) - \<tau> rho 0 < left I - \<Delta> rho i" using i_props
      by (simp add: less_diff_conv2)
    then have "\<tau> rho i - \<tau> rho 0 < left I" by linarith
    then show ?thesis using i_props by auto
  next
    case (VNext x9)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VNext_ge x10)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VNext_le x11a)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VPrev x12a)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VPrev_ge x13)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VPrev_le x14)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case VPrev_zero
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VSince j q qs)
    then have j_def: "j = i-1" using p'r p'_def unfolding optimal_def valid_def
      by auto
    then show ?thesis
    proof (cases "left I = 0")
      case True
      then show ?thesis
      proof (cases p2)
        case (Inl a2)
        then have "p = Inl (SSince (projl p2) [])" using p_def p'r VSince True
          unfolding doSince_def by (cases p1) auto
        then show ?thesis using Inl p2_def True i_props zero_enat_def
          unfolding optimal_def valid_def by auto
      next
        case (Inr b2)
        then have p2r: "p2 = Inr b2" by auto
        {
          from i_props have b2_ge: "v_at b2 > 0" using p2r p2_def
            unfolding optimal_def valid_def by auto
          then have nl_def: "v_at q \<le> v_at b2 -1" using VSince p'r p'_def p2_def p2r
            unfolding optimal_def valid_def by (auto simp: Let_def)
          define l where l_def: "l \<equiv> [v_at q ..< min (v_at b2 -1) (LTP rho (\<tau> rho (v_at b2 -1)))]"
          then have "l = [v_at q ..< v_at b2 -1]"
            by (auto simp add: i_le_ltpi min_def)
          then have "l @ [min (v_at b2 -1) (LTP rho (\<tau> rho (v_at b2 -1)))] = l @ [v_at b2 -1]"
            by (auto simp add: i_le_ltpi min_def)
          then have "l @ [min (v_at b2 -1) (LTP rho (\<tau> rho (v_at b2 -1)))] = [v_at q ..< min (v_at b2 ) (LTP rho (\<tau> rho (v_at b2)))]"
            using nl_def l_def b2_ge
            apply (auto simp add: i_le_ltpi min_def)
            by (metis Suc_pred upt_Suc_append)
        } note * = this
        then show ?thesis
        proof (cases p1)
          case (Inl a1)
          from Inl have "p = p' \<oplus> p2" using p2r VSince p'r p_def True
            unfolding doSince_def by auto
          then have "p = Inr (VSince i q (qs @ [projr p2]))" using VSince p'r
              p2_def p2r i_props unfolding optimal_def valid_def proofApp_def j_def
            by auto
          then show ?thesis using p'_def p2_def i_props True Inl p2r VSince p'r bf'
              j_def i_le_ltpi
            unfolding optimal_def valid_def
            apply (auto simp: Let_def)
                   apply (auto split: if_splits enat.splits)
            using * apply auto
            using min.order_iff apply blast
            using min.order_iff apply blast
                   apply (meson diff_le_self le_trans)
                  apply (meson diff_le_self le_trans)
            using le_trans apply blast
            using le_trans apply blast
            using le_trans apply blast
            using le_trans apply blast
            using le_trans apply blast
            using le_trans by blast
        next
          case (Inr b1)
          then have "p = Inr (VSince i (projr p1) [projr p2]) \<or> p = p' \<oplus> p2"
            using p2r p'r VSince True p_def unfolding doSince_def by auto
          moreover
          {
            assume pplus: "p = p' \<oplus> p2"
            then have "p = Inr (VSince i q (qs @ [projr p2]))" using VSince p'r
                p2_def p2r i_props unfolding optimal_def valid_def proofApp_def j_def
              by auto
            then have "valid rho i (Since phi I psi) p" using p'_def p2_def i_props True Inr p2r VSince p'r bf'
                j_def i_le_ltpi
              unfolding optimal_def valid_def
              apply (auto simp: Let_def)
                     apply (auto split: if_splits enat.splits)
              using * apply auto
              using Lattices.linorder_class.min.order_iff apply blast
              using Lattices.linorder_class.min.order_iff apply blast
                     apply (meson diff_le_self le_trans)
                    apply (meson diff_le_self le_trans)
              using le_trans apply blast
              using le_trans apply blast
              using le_trans apply blast
              using le_trans apply blast
              using le_trans apply blast
              using le_trans by blast
          }
          moreover
          {
            assume p: "p = Inr (VSince i (projr p1) [projr p2])"
            then have "valid rho i (Since phi I psi) p"
              using p1_def p2_def Inr p2r bf True i_le_ltpi i_props
              unfolding optimal_def valid_def
              by (auto simp add: i_etp_to_tau split: enat.splits)
          }
          ultimately show ?thesis by auto
        qed
      qed
    next
      case False
      {fix n
        assume n_def: "right I = enat n"
        from i_props n_def have r: "n \<ge> \<Delta> rho i" by auto
        then have "ETP rho (\<tau> rho (i-1) - (n - \<Delta> rho i)) \<le> v_at q"
          using p'_def VSince p'r n_def unfolding optimal_def valid_def
          by (auto simp: Let_def)
        then have "ETP rho (\<tau> rho i - n) \<le> v_at q"
          using r diff_diff_right[of "\<Delta> rho i" n "\<tau> rho (i-1)"] by auto
      }note ** = this
      then show ?thesis
      proof (cases p1)
        case (Inl a1)
        from Inl have formp: "p = Inr (VSince i q qs)" using VSince p'r False p_def
          unfolding doSince_def by (cases p2) auto
        from p'_def have v_at_qs: "map v_at qs = [v_at q ..< Suc (l rho (i - 1) (subtract (\<Delta> rho i) I))]"
          unfolding optimal_def valid_def VSince p'r
          by (auto simp: Let_def)
        have l_subtract: "l rho (i - 1) (subtract (\<Delta> rho i) I) = l rho i I"
          using False i_props
          apply (auto simp: min_def)
             apply (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
          subgoal
            apply (rule antisym)
            subgoal apply (subst i_ltp_to_tau)
               apply  (auto simp: gr0_conv_Suc not_le)
              by (smt order.trans add_Suc diff_cancel_middle diff_diff_left diff_is_0_eq i_ltp_to_tau i_props le_add2 le_diff_conv2 nat_le_linear)
            subgoal
              by (auto simp: gr0_conv_Suc)
            done
          subgoal
            by (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
          subgoal
            by (metis diff_cancel_middle diff_zero i_le_ltpi less_le neq0_conv zero_less_diff)
          done
        from p'_def have vq: "v_check rho phi q \<and> (\<forall>q \<in> set qs. v_check rho psi q)"
          unfolding optimal_def valid_def VSince p'r
          by (auto simp: Let_def)
        from p'_def i_props have "v_at q \<le> i" using VSince p'r
          unfolding optimal_def valid_def
          by (auto simp: Let_def)
        then show ?thesis using False i_props VSince p'r bf' formp ** vq
            v_at_qs[unfolded l_subtract]
          unfolding valid_def
          by (auto simp: Let_def i_etp_to_tau split: enat.splits)
      next
        case (Inr b1)
        then have "p = Inr (VSince i (projr p1) []) \<or> p = Inr (VSince i q qs)"
          using False p_def p'r VSince unfolding doSince_def
          by (cases p2) auto
        moreover
        {
          assume formp: "p = Inr (VSince i (projr p1) [])"
          then have "valid rho i (Since phi I psi) p"
            using False Inr p1_def i_props bf
            unfolding optimal_def valid_def
            apply auto
             apply (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
            using diff_le_self i_etp_to_tau
            apply (auto split: enat.splits)
            using diff_le_self by blast
        }
        moreover
        {
          assume formp: "p = Inr (VSince i q qs)"
          from p'_def have v_at_qs: "map v_at qs = [v_at q ..< Suc (l rho (i - 1) (subtract (\<Delta> rho i) I))]"
            unfolding optimal_def valid_def VSince p'r
            by (auto simp: Let_def)
          have l_subtract: "l rho (i - 1) (subtract (\<Delta> rho i) I) = l rho i I"
            using False i_props
            apply (auto simp: min_def)
               apply (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
            subgoal
              apply (rule antisym)
              subgoal apply (subst i_ltp_to_tau)
                 apply  (auto simp: gr0_conv_Suc not_le)
                by (smt order.trans add_Suc diff_cancel_middle diff_diff_left diff_is_0_eq i_ltp_to_tau i_props le_add2 le_diff_conv2 nat_le_linear)
              subgoal
                by (auto simp: gr0_conv_Suc)
              done
            subgoal
              by (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
            subgoal
              by (metis diff_cancel_middle diff_zero i_le_ltpi less_le neq0_conv zero_less_diff)
            done
          from p'_def have vq: "v_check rho phi q \<and> (\<forall>q \<in> set qs. v_check rho psi q)"
            unfolding optimal_def valid_def VSince p'r
            by (auto simp: Let_def)
          from p'_def i_props have "v_at q \<le> i" using VSince p'r
            unfolding optimal_def valid_def
            by (auto simp: Let_def)
          then have "valid rho i (Since phi I psi) p" using False i_props VSince p'r
              bf' formp ** vq v_at_qs[unfolded l_subtract]
            unfolding valid_def
            by (auto simp: Let_def i_etp_to_tau split: enat.splits)
        }
        ultimately show ?thesis by auto
      qed
    qed
  next
    case (VSince_never j li qs)
    have li_def: "li = (case right I - enat (delta rho i (i - Suc 0)) of enat n \<Rightarrow>
      ETP rho (\<tau> rho (i - Suc 0) - n) | \<infinity> \<Rightarrow> 0)"
      using p'_def
      by (auto simp: Inr VSince_never optimal_def valid_def)
    have li: "li = (case right I of enat n \<Rightarrow> ETP rho (\<tau> rho i - n) | \<infinity> \<Rightarrow> 0)"
      using i_props
      by (auto simp: li_def split: enat.splits)
    have j_def: "j = i-1" using p'r p'_def VSince_never unfolding optimal_def valid_def
      by auto
    then show ?thesis
    proof (cases "left I = 0")
      case True
      then show ?thesis
      proof (cases "right I")
        case n_def: (enat n)
        then show ?thesis
        proof (cases p2)
          case (Inl a2)
          then have "p = Inl (SSince (projl p2) [])"
            using p'r VSince_never True p_def unfolding doSince_def
            by (cases p1) auto
          then show ?thesis using p2_def i_props Inl True zero_enat_def
            unfolding optimal_def valid_def by auto
        next
          case (Inr b2)
          then have p2r: "p2 = Inr b2" by auto
          {
            from i_props n_def have r: "n \<ge> \<Delta> rho i" by auto
            then have "ETP rho (\<tau> rho (i-1) - (n - \<Delta> rho i)) \<le> i-1"
              using p'_def VSince_never p'r n_def unfolding optimal_def valid_def
              by (auto simp add: i_etp_to_tau le_diff_conv Let_def split: if_splits)
            then have "ETP rho (\<tau> rho i - n) \<le> i-1"
              using r diff_diff_right[of "\<Delta> rho i" n "\<tau> rho (i-1)"] by auto
          }note * = this
          {
            from i_props have b2_ge: "v_at b2 > 0" using p2r p2_def
              unfolding optimal_def valid_def by auto
            then have nl_def: "ETP rho (\<tau> rho i - n) \<le> v_at b2 - 1" using * VSince_never p'r p'_def p2_def p2r
              unfolding optimal_def valid_def by (auto simp: Let_def)
            define l where l_def: "l \<equiv> [ETP rho (\<tau> rho i - n) ..< min (v_at b2 -1) (LTP rho (\<tau> rho (v_at b2 -1)))]"
            then have "l = [ETP rho (\<tau> rho i - n) ..< v_at b2 -1]"
              by (auto simp add: i_le_ltpi min_def)
            then have "l @ [min (v_at b2 -1) (LTP rho (\<tau> rho (v_at b2 -1)))] = l @ [v_at b2 -1]"
              by (auto simp add: i_le_ltpi min_def)
            then have "l @ [min (v_at b2 -1) (LTP rho (\<tau> rho (v_at b2 -1)))] = [ETP rho (\<tau> rho i - n) ..< min (v_at b2 ) (LTP rho (\<tau> rho (v_at b2)))]"
              using nl_def l_def b2_ge
              apply (auto simp add: i_le_ltpi min_def)
              by (metis Suc_pred upt_Suc_append)
          }note ** = this
          then show ?thesis
          proof (cases p1)
            case (Inl a1)
            then have "p = p' \<oplus> p2" using p2r p'r VSince_never True p_def
              unfolding doSince_def by auto
            then have "p = Inr (VSince_never i li (qs @ [projr p2]))"
              using VSince_never p'r p2_def p2r i_props
              unfolding optimal_def valid_def proofApp_def j_def
              by auto
            then show ?thesis using * ** n_def p'_def p2_def p2r p'r VSince_never
                True i_props i_le_ltpi
              unfolding optimal_def valid_def
              using [[linarith_split_limit=20]]
              apply (auto 0 0 simp: Let_def split: if_splits)
              using min.orderE apply blast
                   apply (metis One_nat_def Suc_diff_1 le_SucI)
                  apply (metis Suc_pred le_trans nat_le_linear not_less_eq_eq)
              using le_trans by blast+
          next
            case (Inr b1)
            then have "p = Inr (VSince i (projr p1) [projr p2]) \<or> p = p' \<oplus> p2"
              using p2r True p'r VSince_never p_def unfolding doSince_def
              by auto
            moreover
            {
              assume "p = p' \<oplus> p2"
              then have "p = Inr (VSince_never i li (qs @ [projr p2]))"
                using VSince_never p'r p2_def p2r i_props
                unfolding optimal_def valid_def proofApp_def j_def
                by auto
              then have "valid rho i (Since phi I psi) p" using * ** n_def p'_def p2_def p2r p'r VSince_never
                  True i_props i_le_ltpi
                unfolding optimal_def valid_def
                using [[linarith_split_limit=20]]
                apply (auto 0 0 simp: Let_def split: if_splits)
                using min.orderE apply blast
                     apply (metis One_nat_def Suc_diff_1 le_SucI)
                    apply (metis Suc_pred le_trans nat_le_linear not_less_eq_eq)
                using le_trans by blast+
            }
            moreover
            {
              assume "p = Inr (VSince i (projr p1) [projr p2])"
              then have "valid rho i (Since phi I psi) p"
                using Inr p2r p1_def p2_def True i_props n_def
                unfolding optimal_def valid_def
                apply (auto simp add: i_etp_to_tau)
                using i_le_ltpi by blast
            }
            ultimately show ?thesis by auto
          qed
        qed
      next
        case infinity
        then show ?thesis        proof (cases p2)
          case (Inl a2)
          then have "p = Inl (SSince (projl p2) [])"
            using p'r VSince_never True p_def unfolding doSince_def
            by (cases p1) auto
          then show ?thesis using p2_def i_props Inl True zero_enat_def
            unfolding optimal_def valid_def by auto
        next
          case (Inr b2)
          then have p2r: "p2 = Inr b2" by auto
          {
            from i_props have b2_ge: "v_at b2 > 0" using p2r p2_def
              unfolding optimal_def valid_def by auto
            then have nl_def: "ETP rho 0 \<le> v_at b2 - 1" using VSince_never p'r p'_def p2_def p2r
              unfolding optimal_def valid_def by (auto simp: Let_def i_etp_to_tau)
            define l where l_def: "l \<equiv> [ETP rho 0 ..< min (v_at b2 -1) (LTP rho (\<tau> rho (v_at b2 -1)))]"
            then have "l = [ETP rho 0 ..< v_at b2 -1]"
              by (auto simp add: i_le_ltpi min_def)
            then have "l @ [min (v_at b2 -1) (LTP rho (\<tau> rho (v_at b2 -1)))] = l @ [v_at b2 -1]"
              by (auto simp add: i_le_ltpi min_def)
            then have "l @ [min (v_at b2 -1) (LTP rho (\<tau> rho (v_at b2 -1)))] = [ETP rho 0 ..< min (v_at b2 ) (LTP rho (\<tau> rho (v_at b2)))]"
              using nl_def l_def b2_ge
              apply (auto simp add: i_le_ltpi min_def)
              by (metis Suc_pred diff_0_eq_0 diff_is_0_eq upt_Suc)
          }note ** = this
          then show ?thesis
          proof (cases p1)
            case (Inl a1)
            then have "p = p' \<oplus> p2" using p2r p'r VSince_never True p_def
              unfolding doSince_def by auto
            then have "p = Inr (VSince_never i li (qs @ [projr p2]))"
              using VSince_never p'r p2_def p2r i_props
              unfolding optimal_def valid_def proofApp_def j_def
              by auto
            then show ?thesis using infinity p'_def p2_def p2r p'r VSince_never
                True i_props i_le_ltpi **
              unfolding optimal_def valid_def
              by (auto simp: Let_def i_etp_to_tau i_le_ltpi split: if_splits)
          next
            case (Inr b1)
            then have "p = Inr (VSince i (projr p1) [projr p2]) \<or> p = p' \<oplus> p2"
              using p2r True p'r VSince_never p_def unfolding doSince_def
              by auto
            moreover
            {
              assume "p = p' \<oplus> p2"
              then have "p = Inr (VSince_never i li (qs @ [projr p2]))"
                using VSince_never p'r p2_def p2r i_props
                unfolding optimal_def valid_def proofApp_def j_def
                by auto
              then have "valid rho i (Since phi I psi) p" using ** infinity p'_def p2_def p2r p'r VSince_never
                  True i_props i_le_ltpi
                unfolding optimal_def valid_def
                by (auto simp: Let_def  i_etp_to_tau i_le_ltpi split: if_splits)
            }
            moreover
            {
              assume "p = Inr (VSince i (projr p1) [projr p2])"
              then have "valid rho i (Since phi I psi) p"
                using Inr p2r p1_def p2_def True i_props infinity
                unfolding optimal_def valid_def
                apply (auto simp add: i_etp_to_tau)
                using i_le_ltpi by blast
            }
            ultimately show ?thesis by auto
          qed
        qed
      qed
    next
      case False
      then show ?thesis
      proof (cases p1)
        { fix n assume n_def: "right I = enat n"
          case (Inl a1)
          then have formp: "p = Inr (VSince_never i li qs)"
            using False p_def p'r VSince_never
            unfolding doSince_def by (cases p2) auto
          from p'_def have v_at_qs: "map v_at qs = [ETP rho (\<tau> rho (i-1) - (n - \<Delta> rho i)) ..< Suc (l rho (i - 1) (subtract (\<Delta> rho i) I))]"
            using n_def unfolding optimal_def valid_def VSince_never p'r
            by (auto simp: Let_def)
          have l_subtract: "l rho (i - 1) (subtract (\<Delta> rho i) I) = l rho i I"
            using False i_props
            apply (auto simp: min_def)
               apply (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
            subgoal
              apply (rule antisym)
              subgoal apply (subst i_ltp_to_tau)
                 apply  (auto simp: gr0_conv_Suc not_le)
                by (smt order.trans add_Suc diff_cancel_middle diff_diff_left diff_is_0_eq i_ltp_to_tau i_props le_add2 le_diff_conv2 nat_le_linear)
              subgoal
                by (auto simp: gr0_conv_Suc)
              done
            subgoal
              by (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
            subgoal
              by (metis diff_cancel_middle diff_zero i_le_ltpi less_le neq0_conv zero_less_diff)
            done
          from p'_def have vq: "\<forall>q \<in> set qs. v_check rho psi q"
            unfolding optimal_def valid_def VSince_never p'r
            by (auto simp: Let_def)
          from n_def i_props have "ETP rho (\<tau> rho (i-1) - (n - \<Delta> rho i)) = ETP rho (\<tau> rho i - n)"
            by auto
          then have "map v_at qs = [ETP rho (\<tau> rho i - n) ..< Suc (l rho i I)]"
            using v_at_qs[unfolded l_subtract] by auto
          then have ?thesis using False i_props VSince_never p'r bf' bf formp vq
              n_def unfolding valid_def
            by (auto simp: Let_def li)
        }
        moreover
        { assume infinity: "right I = \<infinity>"
          case (Inl a1)
          then have formp: "p = Inr (VSince_never i li qs)"
            using False p_def p'r VSince_never
            unfolding doSince_def by (cases p2) auto
          from p'_def have v_at_qs: "map v_at qs = [ETP rho 0 ..< Suc (l rho (i - 1) (subtract (\<Delta> rho i) I))]"
            using infinity unfolding optimal_def valid_def VSince_never p'r
            by (auto simp: Let_def)
          have l_subtract: "l rho (i - 1) (subtract (\<Delta> rho i) I) = l rho i I"
            using False i_props
            apply (auto simp: min_def)
               apply (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
            subgoal
              apply (rule antisym)
              subgoal apply (subst i_ltp_to_tau)
                 apply  (auto simp: gr0_conv_Suc not_le)
                by (smt order.trans add_Suc diff_cancel_middle diff_diff_left diff_is_0_eq i_ltp_to_tau i_props le_add2 le_diff_conv2 nat_le_linear)
              subgoal
                by (auto simp: gr0_conv_Suc)
              done
            subgoal
              by (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
            subgoal
              by (metis diff_cancel_middle diff_zero i_le_ltpi less_le neq0_conv zero_less_diff)
            done
          from p'_def have vq: "\<forall>q \<in> set qs. v_check rho psi q"
            unfolding optimal_def valid_def VSince_never p'r
            by (auto simp: Let_def)
          then have "map v_at qs = [ETP rho 0 ..< Suc (l rho i I)]"
            using v_at_qs[unfolded l_subtract] by auto
          then have ?thesis using False i_props VSince_never p'r bf' bf formp vq
              infinity unfolding valid_def
            by (auto simp: Let_def li)
        }
        moreover case Inl
        ultimately show ?thesis by (cases "right I"; blast)
      next
        { fix n assume n_def: "right I = enat n"
          case (Inr b1)
          then have "p = Inr (VSince i (projr p1) []) \<or> p = Inr (VSince_never i li qs)"
            using p'r VSince_never False p_def unfolding doSince_def
            by (cases p2) auto
          moreover
          {
            assume formp: "p = Inr (VSince_never i li qs)"
            from p'_def have v_at_qs: "map v_at qs = [ETP rho (\<tau> rho (i-1) - (n - \<Delta> rho i)) ..< Suc (l rho (i - 1) (subtract (\<Delta> rho i) I))]"
              using n_def unfolding optimal_def valid_def VSince_never p'r
              by (auto simp: Let_def)
            have l_subtract: "l rho (i - 1) (subtract (\<Delta> rho i) I) = l rho i I"
              using False i_props
              apply (auto simp: min_def)
                 apply (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
              subgoal
                apply (rule antisym)
                subgoal apply (subst i_ltp_to_tau)
                   apply  (auto simp: gr0_conv_Suc not_le)
                  by (smt order.trans add_Suc diff_cancel_middle diff_diff_left diff_is_0_eq i_ltp_to_tau i_props le_add2 le_diff_conv2 nat_le_linear)
                subgoal
                  by (auto simp: gr0_conv_Suc)
                done
              subgoal
                by (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
              subgoal
                by (metis diff_cancel_middle diff_zero i_le_ltpi less_le neq0_conv zero_less_diff)
              done
            from p'_def have vq: "\<forall>q \<in> set qs. v_check rho psi q"
              unfolding optimal_def valid_def VSince_never p'r
              by (auto simp: Let_def)
            from n_def i_props have "ETP rho (\<tau> rho (i-1) - (n - \<Delta> rho i)) = ETP rho (\<tau> rho i - n)"
              by auto
            then have "map v_at qs = [ETP rho (\<tau> rho i - n) ..< Suc (l rho i I)]"
              using v_at_qs[unfolded l_subtract] by auto
            then have "valid rho i (Since phi I psi) p"
              using False i_props VSince_never p'r bf' bf formp vq n_def
              unfolding valid_def
              by (auto simp: Let_def li)
          }
          moreover
          {
            assume formp: "p = Inr (VSince i (projr p1) [])"
            then have "valid rho i (Since phi I psi) p"
              using p1_def i_props Inr n_def False
              unfolding optimal_def valid_def
              apply (auto simp add: i_etp_to_tau)
              by (metis i_le_ltpi_minus le_antisym less_irrefl_nat less_or_eq_imp_le)
          }
          ultimately have ?thesis by auto
        }
        moreover
        { assume infinity: "right I = infinity"
          case (Inr b1)
          then have "p = Inr (VSince i (projr p1) []) \<or> p = Inr (VSince_never i li qs)"
            using p'r VSince_never False p_def unfolding doSince_def
            by (cases p2) auto
          moreover
          {
            assume formp: "p = Inr (VSince_never i li qs)"
            from p'_def have v_at_qs: "map v_at qs = [ETP rho 0 ..< Suc (l rho (i - 1) (subtract (\<Delta> rho i) I))]"
              using infinity unfolding optimal_def valid_def VSince_never p'r
              by (auto simp: Let_def)
            have l_subtract: "l rho (i - 1) (subtract (\<Delta> rho i) I) = l rho i I"
              using False i_props
              apply (auto simp: min_def)
                 apply (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
              subgoal
                apply (rule antisym)
                subgoal apply (subst i_ltp_to_tau)
                   apply  (auto simp: gr0_conv_Suc not_le)
                  by (smt order.trans add_Suc diff_cancel_middle diff_diff_left diff_is_0_eq i_ltp_to_tau i_props le_add2 le_diff_conv2 nat_le_linear)
                subgoal
                  by (auto simp: gr0_conv_Suc)
                done
              subgoal
                by (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
              subgoal
                by (metis diff_cancel_middle diff_zero i_le_ltpi less_le neq0_conv zero_less_diff)
              done
            from p'_def have vq: "\<forall>q \<in> set qs. v_check rho psi q"
              unfolding optimal_def valid_def VSince_never p'r
              by (auto simp: Let_def)
            then have "map v_at qs = [ETP rho 0 ..< Suc (l rho i I)]"
              using v_at_qs[unfolded l_subtract] by auto
            then have "valid rho i (Since phi I psi) p"
              using False i_props VSince_never p'r bf' bf formp vq infinity
              unfolding valid_def
              by (auto simp: Let_def li)
          }
          moreover
          {
            assume formp: "p = Inr (VSince i (projr p1) [])"
            then have "valid rho i (Since phi I psi) p"
              using p1_def i_props Inr False infinity
              unfolding optimal_def valid_def
              apply (auto simp add: i_etp_to_tau)
              by (metis i_le_ltpi_minus le_antisym less_irrefl_nat less_or_eq_imp_le)
          }
          ultimately have ?thesis by auto
        }
        thm calculation this
        moreover case Inr
        ultimately show ?thesis by (cases "right I"; blast)
      qed
    qed
      (*
 next
    case (VMatchP x12a)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VMatchF x13)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VMatchP_le x14)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
*)
  qed
qed

lemma once_sound:
  assumes i_props: "i > 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I
  \<and> right I \<ge> enat (\<Delta> rho i)" and
    p1_def: "optimal i phi p1" and
    p'_def: "optimal (i-1) (Once (subtract (\<Delta> rho i) I) phi) p'"
    and p_def: "p \<in> set (doOnce i (left I) p1 p')"
    and bf: "bounded_future (Once I phi)"
    and bf': "bounded_future (Once (subtract (\<Delta> rho i) I) phi)"
  shows "valid rho i (Once I phi) p"
proof (cases p')
  case (Inl a)
  then have p'l: "p' = Inl a" by auto
  then have satp': "sat rho (i-1) (Once (subtract (\<Delta> rho i) I) phi)"
    using soundness p'_def check_sound(1)[of rho "Once (subtract (\<Delta> rho i) I) phi" a]
    unfolding optimal_def valid_def by fastforce
  then obtain q where a_def: "a = SOnce (i-1) q" using Inl p'_def
    unfolding optimal_def valid_def p'l
    apply(cases a)
    by auto
  then have a_val: "s_check rho (Once (subtract (\<Delta> rho i) I) phi) a"
    using Inl p'_def unfolding optimal_def valid_def by (auto simp: Let_def)
  then have mem: "mem (delta rho (i-1) (s_at q)) (subtract (\<Delta> rho i) I)"
    using a_def Inl p'_def s_check.simps unfolding optimal_def valid_def
    by (auto simp: Let_def)
  then have "left I - \<Delta> rho i \<le> delta rho (i-1) (s_at q)" by auto
  then have tmp: "left I \<le> \<tau> rho i - \<tau> rho (i-1) + (\<tau> rho (i-1) - \<tau> rho (s_at q))"
    by auto
  from a_val have qi: "(s_at q) \<le> (i-1)" using a_def p'l p'_def
    unfolding optimal_def valid_def
    by (auto simp: Let_def)
  then have liq: "left I \<le> delta rho i (s_at q)" using diff_add_assoc tmp
    by auto
  show ?thesis
  proof (cases "right I")
    case n_def: (enat n)
    from mem n_def have "enat (delta rho (i-1) (s_at q)) \<le> enat n - enat (\<Delta> rho i)"
      by auto
    then have "delta rho (i-1) (s_at q) + \<Delta> rho i \<le> n"
      apply auto
      by (metis One_nat_def enat_ord_simps(1) i_props le_diff_conv le_diff_conv2 n_def)
    then have riq: "enat (delta rho i (s_at q)) \<le> right I" using n_def by auto
    then show ?thesis
    proof (cases "left I = 0")
      case True
      then show ?thesis
      proof (cases p1)
        case (Inl a1)
        then have p1l: "p1 = Inl a1" by auto
        then have sp: "p = Inl (SOnce i (projl p1))"
          using a_def p'l p1l True p_def unfolding doOnce_def by auto
        then show ?thesis
          using Inl True assms n_def unfolding optimal_def valid_def
          by auto
      next
        case (Inr b2)
        then have p1r: "p1 = Inr b2" by simp
        then have sp: "p = Inl (SOnce i q)"
          using p1r p_def True p'l a_def unfolding doOnce_def by auto
        then show ?thesis
          using Inr Inl True assms n_def a_def unfolding optimal_def valid_def
          by (auto simp: Let_def)
      qed
    next
      case False
      then show ?thesis
      proof (cases p1)
        case (Inl a1)
        then have p1l: "p1 = Inl a1" by simp
        then have sp: "p = Inl (SOnce i q)"
          using p1l p_def False p'l a_def unfolding doOnce_def by auto
        then show ?thesis
          using Inl False assms n_def a_def bf qi liq riq a_val unfolding optimal_def valid_def
          by (auto simp: Let_def)
      next
        case (Inr b2)
        then have p1r: "p1 = Inr b2" by simp
        then have sp: "p = Inl (SOnce i q)"
          using p1r p_def False p'l a_def unfolding doOnce_def by auto
        then show ?thesis
          using Inr False assms n_def a_def bf qi liq riq a_val unfolding optimal_def valid_def
          by (auto simp: Let_def)
      qed
    qed
  next
    case infinity
    then have riq: "enat (delta rho i (s_at q)) \<le> right I" by auto
    then show ?thesis
    proof (cases "left I = 0")
      case True
      then show ?thesis
      proof (cases p1)
        case (Inl a1)
        then have p1l: "p1 = Inl a1" by auto
        then have sp: "p = Inl (SOnce i (projl p1))"
          using a_def p'l p1l True p_def unfolding doOnce_def by auto
        then show ?thesis
          using a_def True p'_def p1_def p'l p1l i_props zero_enat_def
          unfolding optimal_def valid_def
          by auto
      next
        case (Inr b2)
        then have p1r: "p1 = Inr b2" by simp
        then have sp: "p = Inl (SOnce i q)"
          using p1r p_def True p'l a_def unfolding doOnce_def by auto
        then show ?thesis
          using Inr True assms zero_enat_def i_props a_def qi riq a_val
          unfolding optimal_def valid_def
          by (auto simp: Let_def)
      qed
    next
      case False
      then show ?thesis
      proof (cases p1)
        case (Inl a1)
        then have p1l: "p1 = Inl a1" by simp
        then have sp: "p = Inl (SOnce i q)"
          using p1l p_def False p'l a_def unfolding doOnce_def by auto
        then show ?thesis
          using Inl False assms zero_enat_def a_def bf qi liq riq a_val 
          unfolding optimal_def valid_def
          by (auto simp: Let_def)
      next
        case (Inr b2)
        then have p1r: "p1 = Inr b2" by simp
        then have sp: "p = Inl (SOnce i q)"
          using p1r p_def False p'l a_def unfolding doOnce_def by auto
        then show ?thesis
          using Inr False assms zero_enat_def a_def bf qi liq riq a_val
          unfolding optimal_def valid_def
          by (auto simp: Let_def)
      qed
    qed
  qed
next
  case (Inr b)
  then have p'r: "p' = Inr b" by auto
  then show ?thesis
  proof (cases b)
    case VFF
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VAtm x11 x12)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VNeg x2)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VDisj x31 x32)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VConjL x31)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VConjR x31)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VImpl x71 x72)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VIff_sv x71 x72)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VIff_vs x71 x72)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VOnce_le x8)
    then have c: "\<tau> rho (i-1) < \<tau> rho 0 + (left I - \<Delta> rho i)" using p'r p'_def
      unfolding optimal_def valid_def by auto
    then have "\<tau> rho (i-1) - \<tau> rho 0 < left I - \<Delta> rho i" using i_props
      by (simp add: less_diff_conv2)
    then have "\<tau> rho i - \<tau> rho 0 < left I" by linarith
    then show ?thesis using i_props by auto
  next
    case (VOnce_never j li qs)
    have li_def: "li = (case right I - enat (delta rho i (i - Suc 0)) of enat n \<Rightarrow>
      ETP rho (\<tau> rho (i - Suc 0) - n) | \<infinity> \<Rightarrow> 0)"
      using p'_def
      by (auto simp: Inr VOnce_never optimal_def valid_def)
    have li: "li = (case right I of enat n \<Rightarrow> ETP rho (\<tau> rho i - n) | \<infinity> \<Rightarrow> 0)"
      using i_props
      by (auto simp: li_def split: enat.splits)
    have j_def: "j = i-1" using p'r p'_def VOnce_never unfolding optimal_def valid_def
      by auto
    then show ?thesis 
    proof (cases "left I = 0")
      case True
      then show ?thesis
      proof (cases "right I")
        case n_def: (enat n)
        then show ?thesis
        proof (cases p1)
          case (Inl a1)
          then have "p = Inl (SOnce i (projl p1))"
            using p'r VOnce_never True p_def unfolding doOnce_def
            by auto
          then show ?thesis using p1_def i_props Inl True zero_enat_def
            unfolding optimal_def valid_def by auto
        next
          case (Inr b1)
          then have p1r: "p1 = Inr b1" by auto
          {
            from i_props n_def have r: "n \<ge> \<Delta> rho i" by auto
            then have "ETP rho (\<tau> rho (i-1) - (n - \<Delta> rho i)) \<le> i-1"
              using p'_def VOnce_never p'r n_def unfolding optimal_def valid_def
              by (auto simp add: i_etp_to_tau le_diff_conv Let_def split: if_splits)
            then have "ETP rho (\<tau> rho i - n) \<le> i-1"
              using r diff_diff_right[of "\<Delta> rho i" n "\<tau> rho (i-1)"] by auto
          } note * = this
          {
            from i_props have b1_ge: "v_at b1 > 0" using p1r p1_def
              unfolding optimal_def valid_def by auto
            then have nl_def: "ETP rho (\<tau> rho i - n) \<le> v_at b1 - 1" using * VOnce_never p'r p'_def p1_def p1r
              unfolding optimal_def valid_def by (auto simp: Let_def)
            define l where l_def: "l \<equiv> [ETP rho (\<tau> rho i - n) ..< min (v_at b1-1) (LTP rho (\<tau> rho (v_at b1-1)))]"
            then have "l = [ETP rho (\<tau> rho i - n) ..< v_at b1 -1]"
              by (auto simp add: i_le_ltpi min_def)
            then have "l @ [min (v_at b1-1) (LTP rho (\<tau> rho (v_at b1 -1)))] = l @ [v_at b1 -1]"
              by (auto simp add: i_le_ltpi min_def)
            then have "l @ [min (v_at b1-1) (LTP rho (\<tau> rho (v_at b1 -1)))] = [ETP rho (\<tau> rho i - n) ..< min (v_at b1) (LTP rho (\<tau> rho (v_at b1)))]"
              using nl_def l_def b1_ge
              apply (auto simp add: i_le_ltpi min_def)
              by (metis Suc_pred upt_Suc_append)
          } note ** = this
          then have "p = p' \<oplus> p1" using p1r p'r VOnce_never True p_def
            unfolding doOnce_def by auto
          then have "p = Inr (VOnce_never i li (qs @ [projr p1]))"
            using VOnce_never p'r p1_def p1r i_props
            unfolding optimal_def valid_def proofApp_def j_def
            by auto
          then show ?thesis
            using * ** n_def p'_def p1_def p1r p'r VOnce_never
              True i_props i_le_ltpi
            unfolding optimal_def valid_def
            using [[linarith_split_limit=20]]
            apply (auto 0 0 simp: Let_def split: if_splits)
            using min.orderE apply blast
                 apply (metis One_nat_def Suc_diff_1 le_SucI)
                apply (metis Suc_pred le_trans nat_le_linear not_less_eq_eq)
            using le_trans by blast+
        qed
      next
        case infinity
        then show ?thesis
        proof (cases p1)
          case (Inl a1)
          then have "p = Inl (SOnce i (projl p1))"
            using p'r VOnce_never True p_def unfolding doOnce_def
            by auto
          then show ?thesis using p1_def i_props Inl True zero_enat_def
            unfolding optimal_def valid_def by auto
        next
          case (Inr b1)
          then have p1r: "p1 = Inr b1" by auto
          {
            from i_props have b1_ge: "v_at b1 > 0" using p1r p1_def
              unfolding optimal_def valid_def by auto
            then have nl_def: "ETP rho 0 \<le> v_at b1 - 1" using VOnce_never p'r p'_def p1_def p1r
              unfolding optimal_def valid_def by (auto simp: Let_def i_etp_to_tau)
            define l where l_def: "l \<equiv> [ETP rho 0 ..< min (v_at b1 -1) (LTP rho (\<tau> rho (v_at b1 -1)))]"
            then have "l = [ETP rho 0 ..< v_at b1 -1]"
              by (auto simp add: i_le_ltpi min_def)
            then have "l @ [min (v_at b1 -1) (LTP rho (\<tau> rho (v_at b1 -1)))] = l @ [v_at b1 -1]"
              by (auto simp add: i_le_ltpi min_def)
            then have "l @ [min (v_at b1 -1) (LTP rho (\<tau> rho (v_at b1 -1)))] = [ETP rho 0 ..< min (v_at b1) (LTP rho (\<tau> rho (v_at b1)))]"
              using nl_def l_def b1_ge
              apply (auto simp add: i_le_ltpi min_def)
              by (metis Suc_pred diff_0_eq_0 diff_is_0_eq upt_Suc)
          } note ** = this
          then have "p = p' \<oplus> p1" using p1r p'r VOnce_never True p_def
            unfolding doOnce_def by auto
          then have "p = Inr (VOnce_never i li (qs @ [projr p1]))"
            using VOnce_never p'r p1_def p1r i_props
            unfolding optimal_def valid_def proofApp_def j_def
            by auto
          then show ?thesis
            using infinity p'_def p1_def p1r p'r VOnce_never
              True i_props i_le_ltpi **
            unfolding optimal_def valid_def
            by (auto simp: Let_def i_etp_to_tau i_le_ltpi split: if_splits)
        qed
      qed
    next
      case False
      then show ?thesis
      proof (cases p1)
        { fix n assume n_def: "right I = enat n"
          case (Inl a1)
          then have formp: "p = Inr (VOnce_never i li qs)"
            using False p_def p'r VOnce_never
            unfolding doOnce_def by (simp add: Inl) 
          from p'_def have v_at_qs: "map v_at qs = [ETP rho (\<tau> rho (i-1) - (n - \<Delta> rho i)) ..< Suc (l rho (i - 1) (subtract (\<Delta> rho i) I))]"
            using n_def unfolding optimal_def valid_def VOnce_never p'r
            by (auto simp: Let_def)
          have l_subtract: "l rho (i - 1) (subtract (\<Delta> rho i) I) = l rho i I"
            using False i_props
            apply (auto simp: min_def)
               apply (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
            subgoal
              apply (rule antisym)
              subgoal apply (subst i_ltp_to_tau)
                 apply  (auto simp: gr0_conv_Suc not_le)
                by (smt order.trans add_Suc diff_cancel_middle diff_diff_left diff_is_0_eq i_ltp_to_tau i_props le_add2 le_diff_conv2 nat_le_linear)
              subgoal
                by (auto simp: gr0_conv_Suc)
              done
            subgoal
              by (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
            subgoal
              by (metis diff_cancel_middle diff_zero i_le_ltpi less_le neq0_conv zero_less_diff)
            done
          from p'_def have vq: "\<forall>q \<in> set qs. v_check rho phi q"
            unfolding optimal_def valid_def VOnce_never p'r
            by (auto simp: Let_def)
          from n_def i_props have "ETP rho (\<tau> rho (i-1) - (n - \<Delta> rho i)) = ETP rho (\<tau> rho i - n)"
            by auto
          then have "map v_at qs = [ETP rho (\<tau> rho i - n) ..< Suc (l rho i I)]"
            using v_at_qs[unfolded l_subtract] by auto
          then have ?thesis using False i_props VOnce_never p'r bf' bf formp vq n_def 
            unfolding valid_def
            by (auto simp: Let_def li)
        }
        moreover
        { assume infinity: "right I = \<infinity>"
          case (Inl a1)
          then have formp: "p = Inr (VOnce_never i li qs)"
            using False p_def p'r VOnce_never
            unfolding doOnce_def by auto
          from p'_def have v_at_qs: "map v_at qs = [ETP rho 0 ..< Suc (l rho (i - 1) (subtract (\<Delta> rho i) I))]"
            using infinity unfolding optimal_def valid_def VOnce_never p'r
            by (auto simp: Let_def)
          have l_subtract: "l rho (i - 1) (subtract (\<Delta> rho i) I) = l rho i I"
            using False i_props
            apply (auto simp: min_def)
               apply (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
            subgoal
              apply (rule antisym)
              subgoal apply (subst i_ltp_to_tau)
                 apply  (auto simp: gr0_conv_Suc not_le)
                by (smt order.trans add_Suc diff_cancel_middle diff_diff_left diff_is_0_eq i_ltp_to_tau i_props le_add2 le_diff_conv2 nat_le_linear)
              subgoal
                by (auto simp: gr0_conv_Suc)
              done
            subgoal
              by (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
            subgoal
              by (metis diff_cancel_middle diff_zero i_le_ltpi less_le neq0_conv zero_less_diff)
            done
          from p'_def have vq: "\<forall>q \<in> set qs. v_check rho phi q"
            unfolding optimal_def valid_def VOnce_never p'r
            by (auto simp: Let_def)
          then have "map v_at qs = [ETP rho 0 ..< Suc (l rho i I)]"
            using v_at_qs[unfolded l_subtract] by auto
          then have ?thesis using False i_props VOnce_never p'r bf' bf formp vq infinity
            unfolding valid_def
            by (auto simp: Let_def li)
        }
        moreover case Inl
        ultimately show ?thesis 
          by (cases "right I"; auto)
      next
        { fix n 
          assume n_def: "right I = enat n"
          case (Inr b1)
          then have "p = Inr (VOnce_never i li qs)"
            using p'r VOnce_never False p_def unfolding doOnce_def
            by (simp add: Inr)
          moreover
          {
            assume formp: "p = Inr (VOnce_never i li qs)"
            from p'_def have v_at_qs: "map v_at qs = [ETP rho (\<tau> rho (i-1) - (n - \<Delta> rho i)) ..< Suc (l rho (i - 1) (subtract (\<Delta> rho i) I))]"
              using n_def unfolding optimal_def valid_def VOnce_never p'r
              by (auto simp: Let_def)
            have l_subtract: "l rho (i - 1) (subtract (\<Delta> rho i) I) = l rho i I"
              using False i_props
              apply (auto simp: min_def)
                 apply (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
              subgoal
                apply (rule antisym)
                subgoal apply (subst i_ltp_to_tau)
                   apply  (auto simp: gr0_conv_Suc not_le)
                  by (smt order.trans add_Suc diff_cancel_middle diff_diff_left diff_is_0_eq i_ltp_to_tau i_props le_add2 le_diff_conv2 nat_le_linear)
                subgoal
                  by (auto simp: gr0_conv_Suc)
                done
              subgoal
                by (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
              subgoal
                by (metis diff_cancel_middle diff_zero i_le_ltpi less_le neq0_conv zero_less_diff)
              done
            from p'_def have vq: "\<forall>q \<in> set qs. v_check rho phi q"
              unfolding optimal_def valid_def VOnce_never p'r
              by (auto simp: Let_def)
            from n_def i_props have "ETP rho (\<tau> rho (i-1) - (n - \<Delta> rho i)) = ETP rho (\<tau> rho i - n)"
              by auto
            then have "map v_at qs = [ETP rho (\<tau> rho i - n) ..< Suc (l rho i I)]"
              using v_at_qs[unfolded l_subtract] by auto
            then have "valid rho i (Once I phi) p"
              using False i_props VOnce_never p'r bf' bf formp vq n_def
              unfolding valid_def
              by (auto simp: Let_def li)
          }
          ultimately have ?thesis by auto
        }
        moreover
        { assume infinity: "right I = infinity"
          case (Inr b1)
          then have "p = Inr (VOnce_never i li qs)"
            using p'r VOnce_never False p_def unfolding doOnce_def
            by (simp add: Inr)
          moreover
          {
            assume formp: "p = Inr (VOnce_never i li qs)"
            from p'_def have v_at_qs: "map v_at qs = [ETP rho 0 ..< Suc (l rho (i - 1) (subtract (\<Delta> rho i) I))]"
              using infinity unfolding optimal_def valid_def VOnce_never p'r
              by (auto simp: Let_def)
            have l_subtract: "l rho (i - 1) (subtract (\<Delta> rho i) I) = l rho i I"
              using False i_props
              apply (auto simp: min_def)
                 apply (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
              subgoal
                apply (rule antisym)
                subgoal apply (subst i_ltp_to_tau)
                   apply  (auto simp: gr0_conv_Suc not_le)
                  by (smt order.trans add_Suc diff_cancel_middle diff_diff_left diff_is_0_eq i_ltp_to_tau i_props le_add2 le_diff_conv2 nat_le_linear)
                subgoal
                  by (auto simp: gr0_conv_Suc)
                done
              subgoal
                by (smt False add_leD2 diff_diff_cancel diff_is_0_eq' i_ltp_to_tau le_diff_conv2)
              subgoal
                by (metis diff_cancel_middle diff_zero i_le_ltpi less_le neq0_conv zero_less_diff)
              done
            from p'_def have vq: "\<forall>q \<in> set qs. v_check rho phi q"
              unfolding optimal_def valid_def VOnce_never p'r
              by (auto simp: Let_def)
            then have "map v_at qs = [ETP rho 0 ..< Suc (l rho i I)]"
              using v_at_qs[unfolded l_subtract] by auto
            then have "valid rho i (Once I phi) p"
              using False i_props VSince_never p'r bf' bf formp vq infinity
              unfolding valid_def
              by (auto simp: Let_def li)
          }
          ultimately have ?thesis by auto
        }
        moreover case Inr
        ultimately show ?thesis by (cases "right I"; auto)
      qed
    qed
  next
    case (VUntil x51 x52 x53)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VUntil_never x71 x72)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VSince_le x8)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VNext x9)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VNext_ge x10)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VNext_le x11a)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VPrev x12a)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VPrev_ge x13)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VPrev_le x14)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case VPrev_zero
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VSince x51 x52 x53)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VSince_never x51 x52 x53)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
        (*
 next
    case (VMatchP x12a)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VMatchF x13)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VMatchP_le x14)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
*)
  qed
qed

lemma map_set_in_imp_set_in:
  "\<forall>p \<in> set qs. v_check rho phi p
  \<Longrightarrow> \<forall>j \<in> set (map v_at qs). \<exists>p \<in> set qs. v_at p = j \<and> v_check rho phi p"
  and
  "\<forall>p \<in> set ps. s_check rho phi p
  \<Longrightarrow> \<forall>j \<in> set (map s_at ps). \<exists>p \<in> set ps. s_at p = j \<and> s_check rho phi p"
  by auto

lemma mem_imp_ge_etp:
  assumes mem: "mem (delta rho (i-1) j) (subtract (\<Delta> rho i) I)"
    and j_le_i: "j \<le> i-1" and
    i_props: "i > 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I \<and> right I \<ge> enat (\<Delta> rho i)"
  shows "ETP rho (case right I of enat n \<Rightarrow> \<tau> rho i - n | _ \<Rightarrow> 0) \<le> j"
proof (cases "right I")
  case (enat n)
  from mem have "delta rho (i-1) j \<le> n + \<tau> rho (i-1) - \<tau> rho i"
    using i_props enat by auto
  then have "delta rho (i-1) j + \<tau> rho i \<le> n + \<tau> rho (i-1)"
    apply auto
    by (metis One_nat_def enat_ord_simps(1) i_props le_diff_conv le_diff_conv2 enat)
  then show ?thesis by (auto simp add: i_etp_to_tau enat split: enat.splits)
qed (auto simp add: i_etp_to_tau)

lemma mem_imp_le_ltp:
  assumes mem: "mem (delta rho (i-1) j) (subtract (\<Delta> rho i) I)"
    and j_le_i: "j \<le> i-1" and
    i_props: "i > 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I \<and> right I \<ge> enat (\<Delta> rho i)"
  shows "j \<le> LTP rho (\<tau> rho i - left I)"
proof -
  from mem have "left I + \<tau> rho (i-1) - \<tau> rho i \<le> delta rho (i-1) j" by auto
  then have "left I + \<tau> rho (i-1) - \<tau> rho i + \<tau> rho j \<le> \<tau> rho (i-1)"
    using j_le_i add_le_mono1[of "left I + \<tau> rho (i-1) - \<tau> rho i" "delta rho (i-1) j" "\<tau> rho j"]
    by auto
  then have "\<tau> rho j \<le> \<tau> rho i - left I" by auto
  then show ?thesis using i_props by (auto simp add: i_ltp_to_tau)
qed

lemma i_props_imp_not_le:
  assumes i_props: "i > 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I
   \<and> right I \<ge> enat (\<Delta> rho i)" and
    p'_def: "optimal (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) p'"
  shows "p' \<noteq> Inr (VSince_le (i-1))"
proof (rule ccontr)
  assume p'_le: "\<not> p' \<noteq> Inr (VSince_le (i-1))"
  then have "\<tau> rho (i-1) < \<tau> rho 0 + (left I - \<Delta> rho i)" using p'_def
    unfolding optimal_def valid_def by auto
  then have "\<tau> rho (i-1) - \<tau> rho 0 < left I - \<Delta> rho i" using i_props
    by (simp add: less_diff_conv2)
  then have i_le: "\<tau> rho i < \<tau> rho 0 + left I" by linarith
  then show False using i_props by auto
qed

lemma case_snoc: "(case xs @ [x] of [] \<Rightarrow> a | x # xs \<Rightarrow> b) = b"
  by (cases xs; auto)

lemma sval_to_sval':
  assumes val: "valid rho i (Since phi I psi) (Inl (SSince spsi (ys @ [y])))" and
    i_props: "0 < i \<and> \<tau> rho 0 + left I \<le> \<tau> rho i \<and> enat (\<Delta> rho i) \<le> right I"
  shows "valid rho (i - 1) (Since phi (subtract (\<Delta> rho i) I) psi)
     (Inl (SSince spsi ys))"
proof -
  from val have spsi_i: "s_at spsi \<le> s_at y" unfolding valid_def
    by (auto simp: Let_def case_snoc)
  from val have y_i: "s_at y = i" unfolding valid_def
    by (auto simp: Let_def case_snoc)
  then have map_ys: "map s_at ys = [Suc (s_at spsi) ..< i]" using val
    unfolding valid_def by (auto simp: Let_def case_snoc split: if_splits)
  from val have "left I - (\<Delta> rho i) \<le> \<tau> rho (i-1) - \<tau> rho (s_at spsi)"
    unfolding valid_def
    apply (auto simp: Let_def case_snoc split: if_splits)
    subgoal premises prems
    proof -
      from y_i prems(2) spsi_i have "left I + \<tau> rho (s_at spsi) \<le> \<tau> rho i"
        by (auto simp add: le_diff_conv2)
      then show ?thesis using y_i by auto
    qed
    done
  moreover have "\<And>n. right I = enat n \<Longrightarrow> \<tau> rho (i-1) - \<tau> rho (s_at spsi) \<le> n - (\<Delta> rho i)"
    using val unfolding valid_def
    by (auto simp: Let_def case_snoc split: if_splits)
  ultimately have mem': "mem (delta rho (i-1) (s_at spsi)) (subtract (\<Delta> rho i) I)"
    by (cases "right I") auto
  then show ?thesis
  proof (cases ys rule: rev_cases)
    case Nil
    then show ?thesis using assms y_i zero_enat_def unfolding valid_def
      by (auto simp add: Let_def le_diff_conv2 split: if_splits)
  next
    case (snoc as a)
    then have "s_at a = i - 1" using map_ys
      apply auto
      by (metis Nil_is_append_conv Suc_pred append1_eq_conv not_Cons_self2 not_gr_zero upt_Suc upt_eq_Nil_conv)
    then show ?thesis using mem' snoc assms y_i map_ys unfolding valid_def
      apply (auto simp: Let_def case_snoc)
      by (metis Suc_pred upt_Suc_append)
  qed
qed

lemma etpi_imp_etp_suci:
  assumes rI: "n \<ge> \<Delta> rho i"
    and etpj: "i > 0 \<and> ETP rho (\<tau> rho i - n) \<le> j"
  shows "ETP rho (\<tau> rho (i-1) - (n - (\<Delta> rho i))) \<le> j"
proof -
  have "\<tau> rho (i-1) - (n - (\<Delta> rho i)) = \<tau> rho i - n"
    using assms diff_diff_right[of "\<tau> rho (i-1)" "\<tau> rho i" n] by auto
  then show ?thesis using etpj by (auto simp add: i_etp_to_tau)
qed

lemma val_ge_zero:
  assumes pr: "p = Inr p'" and form_p': "p' = VSince (i-1) p1 p2"
    and val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) p"
  shows "\<tau> rho 0 \<le> \<tau> rho (i-1) - (left I - (\<Delta> rho i))"
  using assms unfolding valid_def by (auto simp: Let_def)

lemma val_ge_zero_never:
  assumes pr: "p = Inr p'" and form_p': "p' = VSince_never (i-1) li p1"
    and val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) p"
  shows "\<tau> rho 0 \<le> \<tau> rho (i-1) - (left I - (\<Delta> rho i))"
  using assms unfolding valid_def
  by (auto simp: Let_def split: enat.splits)

lemma i_to_predi_props:
  assumes "i > 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I \<and> right I \<ge> enat (\<Delta> rho i)"
  shows "\<tau> rho 0 + (left I + \<tau> rho (i - Suc 0) - \<tau> rho i) \<le> \<tau> rho (i - Suc 0)"
proof -
  from assms have "(left I + \<tau> rho (i-1) - \<tau> rho i) \<le> \<tau> rho (i-1) - \<tau> rho 0"
    by auto
  then show ?thesis using le_diff_conv2 by auto
qed

lemma predi_eq_ltp:
  assumes i_props: "i > 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I
   \<and> right I \<ge> enat (\<Delta> rho i)" and "\<tau> rho (i-1) \<le> \<tau> rho (i-1) - (left I + \<tau> rho (i-1) - \<tau> rho i)"
    and i_g_ltp: "i > LTP rho (\<tau> rho i - left I)"
  shows "(i-1) = LTP rho (\<tau> rho i - left I)"
proof -
  from assms have "\<tau> rho (i-1) \<le> \<tau> rho i - left I" by auto
  then show ?thesis using i_g_ltp i_props apply (auto simp add: i_ltp_to_tau)
    by (metis Suc_pred add_le_imp_le_diff i_ltp_to_tau i_props le_less_Suc_eq)
qed

lemma predi_val_props:
  assumes i_props: "i > 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I
   \<and> right I \<ge> enat (\<Delta> rho i)" and j_le: "\<tau> rho j \<le> \<tau> rho i - left I"
    and j_le_predi: "j \<le> i-1"
  shows "\<tau> rho j \<le> \<tau> rho (i-1) - (left I + \<tau> rho (i-1) - \<tau> rho i)"
proof -
  from assms have "\<tau> rho j - \<tau> rho (i-1) \<le> \<tau> rho i - left I - \<tau> rho (i-1) "
    by auto
  then have "\<tau> rho j + left I + \<tau> rho (i-1) - \<tau> rho i \<le> \<tau> rho (i-1)"
    apply auto
    by (metis (no_types, lifting) add.commute le_diff_conv2 add_leD2 add_le_cancel_left i_props j_le le_diff_conv)
  then have "(left I + \<tau> rho (i-1) - \<tau> rho i) \<le> \<tau> rho (i-1) - \<tau> rho j"
    by auto
  then have "\<tau> rho j + (left I + \<tau> rho (i-1) - \<tau> rho i) \<le> \<tau> rho (i-1)" using j_le_predi
    by (auto simp add: le_diff_conv2)
  then show ?thesis using assms by auto
qed

lemma valid_checkApp_VSince: "valid rho j (Since phi I psi) (Inr (VSince j vphi' vpsis')) \<Longrightarrow>
  left I = 0 \<or> v_at vphi' \<le> LTP rho (\<tau> rho j - left I) \<Longrightarrow> checkApp (Inr (VSince j vphi' vpsis')) (Inr p2')"
  apply (auto simp: valid_def Let_def split: if_splits enat.splits intro!: checkApp.intros)
  using i_le_ltpi le_trans
  apply blast+
  done

lemma valid_checkApp_VSince_never: "valid rho j (Since phi I psi) (Inr (VSince_never j li vpsis')) \<Longrightarrow>
  left I = 0 \<or> (case right I of \<infinity> \<Rightarrow> True | enat n \<Rightarrow> ETP rho (\<tau> rho j - n) \<le> LTP rho (\<tau> rho j - left I)) \<Longrightarrow>
  checkApp (Inr (VSince_never j li vpsis')) (Inr p2')"
  apply (auto simp: valid_def Let_def split: if_splits enat.splits intro!: checkApp.intros)
  apply (meson diff_le_self i_etp_to_tau)
  apply (meson diff_le_self i_etp_to_tau i_le_ltpi leD le_less_trans not_le_imp_less)
  by (meson diff_le_self i_etp_to_tau)

lemma valid_checkIncr_VSince: "valid rho j phi (Inr (VSince j vphi' vpsis')) \<Longrightarrow>
  checkIncr (Inr (VSince j vphi' vpsis'))"
  apply (cases phi)
  apply (auto simp: valid_def Let_def split: if_splits enat.splits dest!: arg_cong[where ?x="map _ _" and ?f=set] intro!: checkIncr.intros)
  apply (drule imageI[where ?A="set vpsis'" and ?f=v_at])
  apply auto[1]
  apply (drule imageI[where ?A="set vpsis'" and ?f=v_at])
  apply auto[1]
  done

lemma valid_checkIncr_VSince_never: "valid rho j phi (Inr (VSince_never j li vpsis')) \<Longrightarrow>
  checkIncr (Inr (VSince_never j li vpsis'))"
  apply (cases phi)
  apply (auto simp: valid_def Let_def split: if_splits enat.splits dest!: arg_cong[where ?x="map _ _" and ?f=set] intro!: checkIncr.intros)
  apply (drule imageI[where ?A="set vpsis'" and ?f=v_at])
  apply auto[1]
  apply (drule imageI[where ?A="set vpsis'" and ?f=v_at])
  apply auto[1]
  done

lemma valid_shift_VSince:
  assumes i_props: "i > 0" "right I \<ge> enat (\<Delta> rho i)"
    and valid: "valid rho i (Since phi I psi) (Inr (VSince i p ys))"
    and v_at_p: "v_at p \<le> i - Suc 0"
  shows "valid rho (i - 1) (Since phi (subtract (delta rho i (i - 1)) I) psi) (Inr (VSince (i - 1) p (if left I = 0 then butlast ys else ys)))"
proof (cases "left I = 0")
  case True
  obtain z zs where ys_def: "ys = zs @ [z]"
    using valid True
    apply (cases ys rule: rev_cases)
    apply (auto simp: valid_def Let_def split: if_splits enat.splits)
    apply (meson i_le_ltpi le_trans)+
    done
  show ?thesis
    using assms etpi_imp_etp_suci i_props True
    unfolding optimal_def valid_def
    apply (auto simp add: Let_def i_ltp_to_tau ys_def split: if_splits)
    using i_le_ltpi apply (auto simp: min_def split: enat.splits)
    done
next
  case False
  have b: "\<tau> rho i \<ge> \<tau> rho 0 + left I"
    using valid
    by (auto simp: valid_def Let_def)
  have rw: "\<tau> rho (i - Suc 0) - (left I + \<tau> rho (i - Suc 0) - \<tau> rho i) =
    (if left I + \<tau> rho (i - Suc 0) \<ge> \<tau> rho i then \<tau> rho i - left I else \<tau> rho (i - Suc 0))"
    by auto
  have e: "right I = enat n \<Longrightarrow> right (subtract (delta rho i (i - 1)) I) = enat n' \<Longrightarrow>
    ETP rho (\<tau> rho i - n) = ETP rho (\<tau> rho (i - 1) - n')" for n n'
    apply (auto)
    by (metis One_nat_def diff_cancel_middle enat_ord_simps(1) i_props(2) le_diff_conv)
  have l: "l rho i I = min (i - Suc 0) (LTP rho (\<tau> rho i - left I))"
    using False b
    apply (auto simp: min_def)
    by (meson i_le_ltpi_minus i_props leD)
  have t: "\<tau> rho (i - 1) - left (subtract (delta rho i (i - 1)) I) =
  (if left I + \<tau> rho (i - Suc 0) \<ge> \<tau> rho i then \<tau> rho i - left I else \<tau> rho (i - Suc 0))"
    using i_props
    by auto
  have F1: "\<tau> rho (i - Suc 0) \<ge> \<tau> rho 0 + left (subtract (delta rho i (i - 1)) I)"
    using i_props b
    apply (auto)
    using i_props i_to_predi_props by blast
  have F2: "v_at p \<le> min (i - Suc 0) (LTP rho (\<tau> rho i - left I))" if "ys \<noteq> []"
    using valid v_at_p that
    by (auto simp: valid_def Let_def split: if_splits enat.splits)
  have F3: "\<not> \<tau> rho i \<le> left I + \<tau> rho (i - Suc 0) \<Longrightarrow>
    LTP rho (\<tau> rho i - left I) = LTP rho (\<tau> rho (i - 1))"
    using False i_props LTP_lt_delta b
    apply (auto)
    by (smt (z3) One_nat_def Suc_pred diff_is_0_eq i_le_ltpi_minus le_add_diff_inverse2 nat_le_linear neq0_conv predi_eq_ltp rw trans_le_add2)
  show ?thesis
    using False F1 F2 valid e v_at_p
    apply (cases ys rule: rev_cases)
    by (auto simp: valid_def Let_def rw t l F3) (auto split: enat.splits)
qed

lemma valid_shift_VSince_never:
  assumes i_props: "i > 0" "right I \<ge> enat (\<Delta> rho i)"
    and valid: "valid rho i (Since phi I psi) (Inr (VSince_never i li ys))"
  shows "valid rho (i - 1) (Since phi (subtract (delta rho i (i - 1)) I) psi) (Inr (VSince_never (i - 1) li (if left I = 0 then butlast ys else ys)))"
proof (cases "left I = 0")
  case True
  obtain z zs where ys_def: "ys = zs @ [z]"
    using valid True
    apply (cases ys rule: rev_cases)
    apply (auto simp: valid_def Let_def split: if_splits enat.splits)
    apply (meson diff_le_self i_etp_to_tau)
    by (meson \<tau>_mono diff_le_self i_etp_to_tau i_ltp_to_tau i_props(1) less_or_eq_imp_le)
  show ?thesis
    using assms etpi_imp_etp_suci i_props True
    unfolding optimal_def valid_def
    apply (auto simp add: Let_def i_ltp_to_tau ys_def split: if_splits)
    using i_le_ltpi apply (auto simp: min_def split: enat.splits)
    done
next
  case False
  have b: "\<tau> rho i \<ge> \<tau> rho 0 + left I"
    using valid
    by (auto simp: valid_def Let_def)
  have rw: "\<tau> rho (i - Suc 0) - (left I + \<tau> rho (i - Suc 0) - \<tau> rho i) =
    (if left I + \<tau> rho (i - Suc 0) \<ge> \<tau> rho i then \<tau> rho i - left I else \<tau> rho (i - Suc 0))"
    by auto
  have e: "right I = enat n \<Longrightarrow> right (subtract (delta rho i (i - 1)) I) = enat n' \<Longrightarrow>
    ETP rho (\<tau> rho i - n) = ETP rho (\<tau> rho (i - 1) - n')" for n n'
    apply (auto)
    by (metis One_nat_def diff_cancel_middle enat_ord_simps(1) i_props(2) le_diff_conv)
  have l: "l rho i I = min (i - Suc 0) (LTP rho (\<tau> rho i - left I))"
    using False b
    apply (auto simp: min_def)
    by (meson i_le_ltpi_minus i_props leD)
  have t: "\<tau> rho (i - 1) - left (subtract (delta rho i (i - 1)) I) =
  (if left I + \<tau> rho (i - Suc 0) \<ge> \<tau> rho i then \<tau> rho i - left I else \<tau> rho (i - Suc 0))"
    using i_props
    by auto
  have F1: "\<tau> rho (i - Suc 0) \<ge> \<tau> rho 0 + left (subtract (delta rho i (i - 1)) I)"
    using i_props b
    apply (auto)
    using i_props i_to_predi_props by blast
  have F3: "\<not> \<tau> rho i \<le> left I + \<tau> rho (i - Suc 0) \<Longrightarrow>
    LTP rho (\<tau> rho i - left I) = LTP rho (\<tau> rho (i - 1))"
    using False i_props LTP_lt_delta b
    apply (auto)
    by (smt (z3) One_nat_def Suc_pred diff_is_0_eq i_le_ltpi_minus le_add_diff_inverse2 nat_le_linear neq0_conv predi_eq_ltp rw trans_le_add2)
  show ?thesis
    using False F1 valid e
    by (auto simp: valid_def Let_def rw t l F3) (auto split: enat.splits)
qed

lemma since_optimal:
  assumes i_props: "i > 0 \<and> \<tau> rho i \<ge> \<tau> rho 0 + left I
   \<and> right I \<ge> enat (\<Delta> rho i)" and
    p1_def: "optimal i phi p1" and p2_def: "optimal i psi p2" and
    p'_def: "optimal (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) p'"
    and bf: "bounded_future (Since phi I psi)"
    and bf': "bounded_future (Since phi (subtract (\<Delta> rho i) I) psi)"
  shows "optimal i (Since phi I psi) (min_list_wrt wqo (doSince i (left I) p1 p2 p'))"
proof (rule ccontr)
  define minp where minp: "minp \<equiv> min_list_wrt wqo (doSince i (left I) p1 p2 p')"
  from bf have bfpsi: "bounded_future psi" by auto
  from bf have bfphi: "bounded_future phi" by auto
      (*  from bf obtain n where n_def: "right I = enat n" by auto*)
  from pw_total[of i "Since phi I psi"] have total_set: "total_on wqo (set (doSince i (left I) p1 p2 p'))"
    using since_sound[OF i_props p1_def p2_def p'_def _ bf bf']
    by (metis not_wqo total_onI)
  define li where "li = (case right I - enat (delta rho i (i - Suc 0)) of enat n \<Rightarrow>
      ETP rho (\<tau> rho (i - Suc 0) - n) | \<infinity> \<Rightarrow> 0)"
  have li: "li = (case right I of enat n \<Rightarrow> ETP rho (\<tau> rho i - n) | \<infinity> \<Rightarrow> 0)"
    using i_props
    by (auto simp: li_def split: enat.splits)
  from p'_def have p'_form: "(\<exists>p p''. p' = Inl (SSince p p'')) \<or> (\<exists>p p''. p' = Inr (VSince (i-1) p p''))
  \<or> (\<exists>p. p' = Inr (VSince_never (i-1) li p))"
  proof(cases "SAT rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi)")
    case True
    then show ?thesis
      using val_SAT_imp_l[OF bf'] p'_def
        valid_SinceE[of "i-1" phi "subtract (\<Delta> rho i) I" psi p']
      unfolding optimal_def
      apply auto
      by blast
  next
    case False
    then have VIO: "VIO rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi)"
      using SAT_or_VIO
      by auto
    then obtain b' where b'_def: "p' = Inr b'"
      using val_VIO_imp_r[OF bf'] p'_def
      unfolding optimal_def
      by force
    then show ?thesis
      using p'_def i_props_imp_not_le[OF i_props p'_def]
      unfolding optimal_def valid_def
      by (cases b') (auto simp: li_def)
  qed
  from doSince_def[of i "left I" p1 p2 p'] p'_form
  have nnil: "doSince i (left I) p1 p2 p' \<noteq> []"
    by (cases p1; cases p2; cases "left I"; cases p'; auto)
  have filter_nnil: "filter (\<lambda>x. \<forall>y \<in> set (doSince i (left I) p1 p2 p'). wqo x y) (doSince i (left I) p1 p2 p') \<noteq> []"
    using refl_total_transp_imp_ex_min[OF nnil refl_wqo total_set trans_wqo]
      filter_empty_conv[of "(\<lambda>x. \<forall>y \<in> set (doSince i (left I) p1 p2 p'). wqo x y)" "(doSince i (left I) p1 p2 p')"]
    by simp
  assume nopt: "\<not> optimal i (Since phi I psi) minp"
  from since_sound[OF i_props p1_def p2_def p'_def min_list_wrt_in bf bf']
    total_set trans_wqo refl_wqo nnil minp
  have vmin: "valid rho i (Since phi I psi) minp"
    by auto
  then obtain q where q_val: "valid rho i (Since phi I psi) q" and
    q_le: "\<not> wqo minp q" using minp nopt unfolding optimal_def by auto
  then have "wqo minp q" using minp
  proof (cases q)
    case (Inl a)
    then have q_s: "q = Inl a" by auto
    then have SATs: "SAT rho i (Since phi I psi)" using q_val check_sound(1)
      unfolding valid_def by auto
    then have sats: "sat rho i (Since phi I psi)" using soundness
      by blast
    from Inl obtain spsi sphis where a_def: "a = SSince spsi sphis"
      using q_val unfolding valid_def by (cases a) auto
    then have valpsi: "valid rho (s_at spsi) psi (Inl spsi)" using q_val Inl
      unfolding valid_def by (auto simp: Let_def)
    from q_val Inl a_def
    have spsi_bounds: "s_at spsi \<ge> ETP rho (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> \<tau> rho i - n) \<and> s_at spsi \<le> i"
      unfolding valid_def
      by (auto simp: Let_def i_etp_to_tau split: list.splits if_splits enat.splits)
    from valpsi val_SAT_imp_l[OF bf] SATs have check_spsi: "s_check rho psi spsi"
      unfolding valid_def by auto
    then show ?thesis
    proof (cases p')
      case (Inl a')
      then have p'l: "p' = Inl a'" by auto
      then obtain spsi' sphis' where a'_def: "a' = SSince spsi' sphis'"
        using p'_def unfolding optimal_def valid_def
        by (cases a') auto
      from SATs vmin have minl: "\<exists>a. minp = Inl a" using minp val_SAT_imp_l[OF bf]
        by auto
      then show ?thesis
      proof (cases p1)
        case (Inl a1)
        then have p1l: "p1 = Inl a1" by auto
        then show ?thesis
        proof (cases "left I = 0")
          case True
          then show ?thesis
          proof (cases p2)
            case (Inl a2)
            then have form: "doSince i (left I) p1 p2 p' = [(p' \<oplus> p1), Inl (SSince a2 [])]"
              using p1l p'l True a'_def unfolding doSince_def by auto
            then show ?thesis
            proof (cases sphis rule: rev_cases)
              case Nil
              then have "wqo (Inl (SSince a2 [])) q"
                using Inl q_val p2_def SSince[of a2 spsi]
                by (auto simp: optimal_def valid_def q_s a_def)
              moreover have "Inl (SSince a2 []) \<in> set (doSince i (left I) p1 p2 p')"
                using form by auto
              ultimately show ?thesis using minp min_list_wrt_le[OF _ refl_wqo]
                  since_sound[OF i_props p1_def p2_def p'_def _ bf bf']
                  pw_total[of i "Since phi I psi"] q_val
                  trans_wqo q_s
                apply (auto simp add: total_on_def)
                by (metis transpD)
            next
              case (snoc ys y)
              from p'l p1l a'_def have check_p: "checkApp p' p1"
                by (auto intro: checkApp.intros)
              from form since_sound[OF i_props p1_def p2_def p'_def _ bf bf']
              have p_val: "valid rho i (Since phi I psi) (p' \<oplus> p1)"
                by auto
              from a_def snoc have y_val: "valid rho i phi (Inl y)"
                using q_s q_val True i_props unfolding valid_def
                by (auto simp: Let_def case_snoc split: if_splits)
              with q_val have q'_val:
                "valid rho (i - 1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inl (SSince spsi ys))"
                using y_val snoc i_props sval_to_sval'[of i phi I psi spsi ys y]
                unfolding q_s a_def
                by (auto simp: Let_def valid_def case_snoc)
              then have q_eq: "q = (Inl (SSince spsi ys)) \<oplus> (Inl y)"
                using q_s a_def snoc by auto
              then have q_val2: "valid rho i (Since phi I psi) ((Inl (SSince spsi ys)) \<oplus> (Inl y))"
                using q_val by auto
              then have check_q: "checkApp (Inl (SSince spsi ys)) (Inl y)"
                using checkApp.intros(1) by auto
              then have wqo_p': "wqo p' (Inl (SSince spsi ys))" using q'_val p'_def
                unfolding optimal_def by auto
              moreover have wqo_p1: "wqo p1 (Inl y)" using i_props p1_def y_val
                unfolding optimal_def by auto
              ultimately have "wqo (p' \<oplus> p1) q"
                using snoc q_s a_def
                  proofApp_mono[OF check_p check_q wqo_p' wqo_p1 p_val q_val2]
                by auto
              moreover have "(p' \<oplus> p1) \<in> set (doSince i (left I) p1 p2 p')"
                using form by auto
              ultimately show ?thesis using minp min_list_wrt_le[OF _ refl_wqo] snoc
                  since_sound[OF i_props p1_def p2_def p'_def _ bf bf']
                  pw_total[of i "Since phi I psi"] p'l trans_wqo q_s p1l a'_def
                unfolding proofApp_def
                apply (auto simp add: total_on_def)
                by (metis transpD)
            qed
          next
            case (Inr b2)
            then have form: "minp = p' \<oplus> p1"
              using Inr p1l p'l a'_def True minp filter_nnil
              unfolding doSince_def
              by (auto simp: min_list_wrt_def)
            from p2_def Inr have psi_VIO: "VIO rho i psi"
              using check_consistent[OF bfpsi]
              unfolding optimal_def valid_def
              by (auto simp add: check_sound(2))
            then have spsi_less: "s_at spsi < i"
              using a_def q_s q_val zero_enat_def unfolding valid_def
              apply (auto simp: Let_def split: list.splits if_splits)
              using bfpsi check_sound(1) soundness by blast
            then have sphis_not_nil: "sphis \<noteq> []" using a_def q_s q_val
              unfolding valid_def by auto
            then obtain y and ys where snoc_q: "sphis = ys @ [y]"
              using a_def q_s q_val spsi_less unfolding valid_def
              apply (auto simp: Let_def split: if_splits)
              by (metis neq_Nil_conv_snoc sphis_not_nil)
            from p'l p1l a'_def have check_p: "checkApp p' p1"
              by (auto intro: checkApp.intros)
            from form vmin have p_val: "valid rho i (Since phi I psi) (p' \<oplus> p1)"
              using minp by auto
            from a_def snoc_q have y_val: "valid rho i phi (Inl y)"
              using q_s q_val True i_props unfolding valid_def
              by (auto simp: Let_def case_snoc split: if_splits)
            with q_val have q'_val:
              "valid rho (i - 1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inl (SSince spsi ys))"
              using y_val snoc_q i_props sval_to_sval'[of i phi I psi spsi ys y]
              unfolding q_s a_def
              by (auto simp: Let_def valid_def case_snoc)
            then have q_eq: "q = (Inl (SSince spsi ys)) \<oplus> (Inl y)"
              using q_s a_def snoc_q by auto
            then have q_val2: "valid rho i (Since phi I psi) ((Inl (SSince spsi ys)) \<oplus> (Inl y))"
              using q_val by auto
            then have check_q: "checkApp (Inl (SSince spsi ys)) (Inl y)"
              using checkApp.intros(1) by auto
            then have wqo_p': "wqo p' (Inl (SSince spsi ys))" using q'_val p'_def
              unfolding optimal_def by auto
            moreover have wqo_p1: "wqo p1 (Inl y)" using i_props p1_def y_val
              unfolding optimal_def by auto
            ultimately show ?thesis
              using snoc_q q_s a_def form
                proofApp_mono[OF check_p check_q wqo_p' wqo_p1 p_val q_val2]
              by auto
          qed
        next
          case False
          then have form: "minp = p' \<oplus> p1"
            using p1l p'l a'_def minp filter_nnil
            unfolding doSince_def
            by (cases p2; auto simp: min_list_wrt_def)
          from False have spsi_less: "s_at spsi < i" using q_val a_def q_s
            unfolding valid_def
            by (auto simp: Let_def split: if_splits)
          then have sphis_not_nil: "sphis \<noteq> []" using a_def q_s q_val
            unfolding valid_def by auto
          then obtain y and ys where snoc_q: "sphis = ys @ [y]"
            using a_def q_s q_val spsi_less unfolding valid_def
            apply (auto simp: Let_def split: if_splits)
            by (metis neq_Nil_conv_snoc sphis_not_nil)
          from p'l p1l a'_def have check_p: "checkApp p' p1"
            by (auto intro: checkApp.intros)
          from form vmin have p_val: "valid rho i (Since phi I psi) (p' \<oplus> p1)"
            using minp by auto
          from a_def snoc_q have y_val: "valid rho i phi (Inl y)"
            using q_s q_val i_props unfolding valid_def
            by (auto simp: Let_def case_snoc split: if_splits)
          with q_val have q'_val:
            "valid rho (i - 1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inl (SSince spsi ys))"
            using y_val snoc_q i_props sval_to_sval'[of i phi I psi spsi ys y]
            unfolding q_s a_def
            by (auto simp: Let_def valid_def case_snoc)
          then have q_eq: "q = (Inl (SSince spsi ys)) \<oplus> (Inl y)"
            using q_s a_def snoc_q by auto
          then have q_val2: "valid rho i (Since phi I psi) ((Inl (SSince spsi ys)) \<oplus> (Inl y))"
            using q_val by auto
          then have check_q: "checkApp (Inl (SSince spsi ys)) (Inl y)"
            using checkApp.intros(1) by auto
          then have wqo_p': "wqo p' (Inl (SSince spsi ys))" using q'_val p'_def
            unfolding optimal_def by auto
          moreover have wqo_p1: "wqo p1 (Inl y)" using i_props p1_def y_val
            unfolding optimal_def by auto
          ultimately show ?thesis
            using snoc_q q_s a_def form
              proofApp_mono[OF check_p check_q wqo_p' wqo_p1 p_val q_val2]
            by auto
        qed
      next
        case (Inr b1)
        then have phivio: "VIO rho i phi" using p1_def check_sound(2)
          unfolding optimal_def valid_def
          by auto
        from Inr have form_min: "minp = Inl (SSince (projl p2) [])"
          using p'l minp minl filter_nnil unfolding doSince_def
          by (cases p2; cases "left I = 0"; auto simp: min_list_wrt_def)
        then have sphis_nil: "sphis = []" using phivio q_val a_def i_props q_s
          unfolding valid_def
          apply (auto simp: Let_def split: if_splits list.splits)
          using bfphi check_sound(1) soundness apply blast
          using bfphi check_sound(1) last_in_set soundness by blast
        then have sc: "s_at spsi = i" using a_def q_s q_val unfolding valid_def
          by auto
        then obtain a2 where a2_def: "p2 = Inl a2"
          using bfpsi check_sound(1) check_spsi optimal_def p2_def val_SAT_imp_l
          by blast
        moreover have "wqo p2 (Inl spsi)" using valpsi sc p2_def
          unfolding optimal_def by auto
        ultimately show ?thesis using form_min q_s a_def sphis_nil a2_def
            SSince[of a2 spsi] by auto
      qed
    next
      case (Inr b)
      then have formb: "(\<exists>q qs. b = VSince (i-1) q qs) \<or> (\<exists>qs. b = VSince_never (i-1) li qs)"
        using i_props_imp_not_le[OF i_props p'_def] p'_def i_props Inr
        unfolding optimal_def valid_def
        by (cases b) (auto simp: li_def)
      then have viosp: "\<not> sat rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi)"
        using p'_def Inr check_sound(2)[of rho "Since phi (subtract (\<Delta> rho i) I) psi" b]
          soundness[of rho _ "Since phi (subtract (delta rho i (i - 1)) I) psi"]
        unfolding optimal_def valid_def
        by (auto simp: Let_def)
      then have satc: "mem 0 I \<and> sat rho i psi" using i_props sats sat_Since_rec
        apply auto
        apply (metis MTL.sat.simps(11) le_zero_eq sat_Since_rec viosp)
        apply (metis enat_0_iff(2) zero_le)
        by (metis MTL.sat.simps(11) sat_Since_rec viosp)
      from vmin SATs val_SAT_imp_l obtain ap where ap_def: "minp = Inl ap"
        using minp unfolding valid_def apply auto
        using bf by blast
      then have aps: "ap = SSince (projl p2) []" using minp formb Inr satc
          filter_nnil
        unfolding doSince_def proofApp_def
        by (cases p1; cases p2) (auto simp: min_list_wrt_def split: if_splits)
      then obtain a2 where a2_def: "p2 = Inl a2"
        using ap_def minp satc formb Inr filter_nnil
        unfolding doSince_def proofApp_def
        by (cases p1; cases p2) (auto simp: min_list_wrt_def split: if_splits)
      then have min: "min (i-1) (LTP rho (\<tau> rho (i-1) - (left (subtract (\<Delta> rho i) I)))) = i-1"
        using satc apply auto
        by (metis min.orderE i_le_ltpi)
      {fix qs
        assume bv: "b = VSince_never (i-1) li qs"
        then have tc: "map v_at qs = [(case right I of enat n \<Rightarrow> ETP rho (\<tau> rho i - n) | _ \<Rightarrow> 0) ..< i]"
          using min satc Inr p'_def i_props unfolding optimal_def valid_def
          by (auto split: enat.splits)
        then have qs_check: "\<forall>p \<in> set qs. v_check rho psi p"
          using bv min satc Inr p'_def i_props
          unfolding optimal_def valid_def by auto
        then have jc: "\<forall>j \<in> set (map v_at qs). \<exists>p. v_at p = j \<and> v_check rho psi p"
          using map_set_in_imp_set_in qs_check by auto
        then have "s_at spsi = i"
          using spsi_bounds check_spsi jc tc check_consistent[OF bfpsi]
          apply (auto split: enat.splits)
          apply force
          by (metis Nat.add_0_right add_diff_inverse_nat atLeastLessThan_iff diff_is_0_eq le0)
      }
      moreover
      {fix qa qs
        assume bv: "b = VSince (i-1) qa qs"
        then have tc: "map v_at qs = [v_at qa ..< i]"
          using min Inr p'_def i_props
          unfolding optimal_def valid_def by (auto simp: Let_def)
        then have qs_check: "\<forall>p \<in> set qs. v_check rho psi p"
          using bv min Inr p'_def i_props
          unfolding optimal_def valid_def by (auto simp: Let_def)
        then have jc: "\<forall>j \<in> set (map v_at qs). \<exists>p. v_at p = j \<and> v_check rho psi p"
          using map_set_in_imp_set_in by auto
        from bv Inr p'_def have qa_le_i: "v_at qa \<le> i"
          unfolding optimal_def valid_def by (auto simp: Let_def)
        from bv Inr p'_def have qa_check: "v_check rho phi qa"
          unfolding optimal_def valid_def by (auto simp: Let_def)
        {
          assume spsi_le: "s_at spsi < v_at qa"
          from a_def Inl q_val
          have tc_q: "map s_at sphis = [Suc (s_at spsi) ..< Suc i]"
            unfolding valid_def by (auto simp: Let_def)
          then have qa_in: "v_at qa \<in> set (map s_at sphis)" using spsi_le qa_le_i
            by (auto split: if_splits)
          from a_def Inl q_val have phis_check: "\<forall>p \<in> set sphis. s_check rho phi p"
            unfolding valid_def by (auto simp: Let_def)
          then have "\<forall>j \<in> set (map s_at sphis). \<exists>p. s_at p = j \<and> s_check rho phi p"
            using map_set_in_imp_set_in by auto
          then have spsi_ge: "s_at spsi \<ge> v_at qa" using qa_in qa_check spsi_le
              check_consistent[OF bfphi]
            by auto
          then have False using spsi_le by auto
        }
        then have spsi_ge: "s_at spsi \<ge> v_at qa" using not_le_imp_less by blast
        from bf have bfpsi: "bounded_future psi" by auto
        then have "s_at spsi = i" using tc jc check_spsi check_consistent[OF bfpsi]
            spsi_bounds spsi_ge
          by force
      }
      ultimately have "wqo p2 (Inl spsi)" and s_at_spsi: "s_at spsi = i" using formb p2_def valpsi
        unfolding optimal_def by auto
      moreover have "sphis = []"
        using q_val s_at_spsi
        by (auto simp: Inl a_def valid_def Let_def split: list.splits if_splits)
      ultimately show ?thesis using a_def Inl ap_def aps a2_def SSince[of a2 spsi]
        by (auto simp: map_idI)
    qed
  next
    case (Inr b)
    then have qr: "q = Inr b" by auto
    then have VIO: "VIO rho i (Since phi I psi)"
      using q_val check_sound(2)[of rho "Since phi I psi" b]
      unfolding valid_def by auto
    then have formb: "(\<exists>p ps. b = VSince i p ps) \<or> (\<exists>ps. b = VSince_never i li ps)"
      using Inr q_val i_props unfolding valid_def by (cases b) (auto simp: li)
    moreover
    {fix p ps
      assume bv: "b = VSince i p ps"
      from bv have vp: "valid rho (v_at p) phi (Inr p)" using q_val qr
        unfolding valid_def by (auto simp: Let_def)
      then have p_bounds: "ETP rho (case right I of enat n \<Rightarrow> (\<tau> rho i - n) | \<infinity> \<Rightarrow> 0) \<le> v_at p \<and> v_at p \<le> i"
        using bv qr q_val unfolding valid_def by (auto simp: Let_def split: enat.splits)
      then have "wqo minp q"
      proof (cases p')
        case (Inl a')
        then obtain p1' ps' where a's: "a' = SSince p1' ps'" using p'_def
          unfolding optimal_def valid_def
          by (cases a') auto
        from a's Inl have ps'c: "map s_at ps' = [Suc (s_at p1') ..< i]"
          using p'_def unfolding optimal_def valid_def
          apply (auto simp: Let_def)
          by (metis Suc_pred i_props upt_Suc_append)
        from a's Inl have ps'_check: "\<forall>p \<in> set ps'. s_check rho phi p"
          using p'_def unfolding optimal_def valid_def
          by (auto simp: Let_def)
        then have jc: "\<forall>j \<in> set (map s_at ps'). \<exists>p. s_at p = j \<and> s_check rho phi p"
          using map_set_in_imp_set_in by auto
        from a's Inl have sp1'_le_ltp: "s_at p1' \<le> LTP rho (\<tau> rho i - left I)"
          using p'_def i_props mem_imp_le_ltp unfolding optimal_def valid_def
          by (auto simp: Let_def)
        from a's Inl have sp1'_bounds: "ETP rho (case right I of enat n \<Rightarrow> (\<tau> rho i - n) | \<infinity> \<Rightarrow> 0) \<le> s_at p1'
        \<and> s_at p1' < i" using p'_def i_props mem_imp_ge_etp[of i I "s_at p1'"]
          unfolding optimal_def valid_def
          by (auto simp: Let_def)
        from a's Inl have sp1': "s_check rho psi p1'" using p'_def
          unfolding optimal_def valid_def by (auto simp: Let_def)
        from jc have "v_at p \<notin> set (map s_at ps')" using vp bfphi check_consistent
          unfolding valid_def by auto
        then have "v_at p \<le> s_at p1' \<or> v_at p = i" using sp1'_bounds ps'c p_bounds
          by (auto split: enat.splits)
        moreover
        {
          assume p_le_p1': "v_at p \<le> s_at p1'"
          from bv qr q_val
          have tc_q: "map v_at ps = [v_at p ..< Suc (l rho i I)]"
            unfolding valid_def by (auto simp: Let_def)
          then have qa_in: "s_at p1' \<in> set (map v_at ps)"
            using p_le_p1' sp1'_bounds sp1'_le_ltp
            by (auto split: if_splits)
          from bv qr q_val have phis_check: "\<forall>p \<in> set ps. v_check rho psi p"
            unfolding valid_def by (auto simp: Let_def)
          then have "\<forall>j \<in> set (map v_at ps). \<exists>p. v_at p = j \<and> v_check rho psi p"
            using map_set_in_imp_set_in by auto
          then have spsi_ge: "v_at p > s_at p1'" using qa_in sp1' p_le_p1'
              check_consistent[OF bfpsi]
            by auto
          then have False using p_le_p1' by auto
        }
        ultimately have p_eq_i: "v_at p = i" by auto
        from Inl have form_minp: "minp = Inr (VSince i (projr p1) [projr p2])
        \<or> minp = Inr (VSince i (projr p1) [])"
          using vmin val_VIO_imp_r[OF bf vmin VIO] minp a's filter_nnil
          unfolding doSince_def proofApp_def
          by (cases p1; cases p2; cases "left I = 0") (auto simp: min_list_wrt_def split: if_splits)
        moreover
        {
          assume pv: "minp = Inr (VSince i (projr p1) [projr p2])"
          then have l0: "left I = 0" using minp Inl a's filter_nnil
            unfolding doSince_def proofApp_def
            by (cases p1; cases p2; cases "left I = 0") (auto simp: min_list_wrt_def split: if_splits)
          then obtain pps where pps: "ps = [pps] \<and> valid rho i psi (Inr pps)"
            using p_eq_i p_bounds qr bv q_val unfolding valid_def
            by (auto simp add: i_le_ltpi min_def split: if_splits)
          from pv l0 obtain a1 where a1_def: "p1 = Inr a1"
            using form_minp minp a's Inl filter_nnil
            unfolding doSince_def proofApp_def
            by (cases p1; cases p2; cases "left I = 0") (auto simp: min_list_wrt_def split: if_splits)
          obtain a2 where a2_def: "p2 = Inr a2"
            using pps p2_def check_consistent[OF bfpsi]
            by (auto simp add: optimal_def valid_def split: sum.splits)
          from vp p_eq_i p1_def have "wqo p1 (Inr p)" unfolding optimal_def
            by auto
          moreover have lcomp: "wqo (Inr a2) (Inr pps)" using p2_def pps
            unfolding optimal_def by (auto simp: a2_def)
          ultimately have "wqo minp q"
            using a2_def bv qr pv a1_def VSince[of a1 p] pps
            by auto
        }
        moreover
        {
          assume pv: "minp = Inr (VSince i (projr p1) [])"
          then obtain a1 where a1_def: "p1 = Inr a1"
            using vmin val_VIO_imp_r[OF bf vmin VIO] minp a's Inl filter_nnil
            unfolding doSince_def proofApp_def
            by (cases p1; cases p2; cases "left I = 0") (auto simp: min_list_wrt_def split: if_splits)
          have wqo_p: "wqo p1 (Inr p)" using p1_def p_eq_i vp
            unfolding optimal_def by auto
          have "wqo minp q"
          proof (cases "left I")
            case 0
            then show ?thesis
              using vmin
              by (auto simp: pv valid_def Let_def i_ltp_to_tau split: enat.splits if_splits)
          next
            case (Suc nat)
            have ps_Nil: "ps = []"
              using q_val p_eq_i
              apply (auto simp: Inr bv Suc valid_def Let_def split: enat.splits if_splits)
              apply (metis add_Suc_right i_le_ltpi_minus i_props leD zero_less_Suc)
              by (metis add_Suc_right i_le_ltpi_minus i_props leD zero_less_Suc)
            show ?thesis
              using VSince_Nil[of a1 p] wqo_p pv bv qr a1_def
              by (auto simp: map_idI ps_Nil)
          qed
        }
        ultimately show ?thesis by auto
      next
        case (Inr b')
        then have p'b': "p' = Inr b'" by auto
        then have formb': "(\<exists>p ps. b' = VSince (i-1)  p ps)
        \<or> (\<exists>ps. b' = VSince_never (i-1) li ps)"
          using Inr p'_def i_props i_props_imp_not_le[OF i_props p'_def]
          unfolding optimal_def valid_def by (cases b') (auto simp: Let_def li_def)
        moreover
        {fix vphi' vpsis'
          assume b'v: "b' = VSince (i-1) vphi' vpsis'"
          then have "wqo minp q"
          proof (cases p1)
            case (Inl a1)
            then show ?thesis
            proof (cases "left I = 0")
              case True
              then have form_min: "minp = p' \<oplus> p2" using b'v Inl minp Inr filter_nnil
                  val_VIO_imp_r[OF bf vmin VIO]
                unfolding doSince_def by (cases p2) (auto simp: min_list_wrt_def)
              then obtain p2' where p2r: "p2 = Inr p2'"
                using True b'v Inl minp Inr val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doSince_def apply (cases p2; auto simp: min_list_wrt_def)
                by (metis (mono_tags) Inl_Inr_False List.filter.simps(1) List.list.sel(1))
              then show ?thesis
                using form_min qr bv Inl p1_def q_val unfolding optimal_def valid_def
                apply (cases ps rule: rev_cases)
                apply (auto simp add: Let_def True i_ltp_to_tau split: if_splits enat.splits)[1]
                subgoal premises prems for ys y
                proof -
                  from vmin form_min p2r have p_val: "valid rho i (Since phi I psi) (p' \<oplus> (Inr p2'))"
                    by auto
                  have check_p: "checkApp p' (Inr p2')"
                    using p'_def True
                    unfolding p2r b'v p'b'
                    by (auto simp: optimal_def intro!: valid_checkApp_VSince)
                  from prems have y_val: "valid rho i psi (Inr y)"
                    using q_val True i_le_ltpi i_props unfolding valid_def
                    by (auto simp: Let_def min_def split: if_splits)
                  have "v_at p \<le> i - Suc 0"
                    using q_val p'_def p1_def
                    apply (auto simp: qr bv Inl optimal_def valid_def Let_def)
                    by (metis MTL.trans_wqo.check_consistent Suc_pred bfphi i_props le_antisym not_less_eq_eq trans_wqo_axioms)
                  then have val_q': "valid rho (i - 1) (Since phi (subtract (delta rho i (i - 1)) I) psi) (Inr (VSince (i - 1) p ys))"
                    using valid_shift_VSince[of i I phi psi p ps]
                    using i_props True q_val
                    by (auto simp: qr bv prems(8))
                  then have q_val2: "valid rho i (Since phi I psi) ((Inr (VSince (i-1) p ys)) \<oplus> (Inr y))"
                    using q_val prems i_props by auto
                  have check_q: "checkApp (Inr (VSince (i-1) p ys)) (Inr y)"
                    using val_q' True
                    unfolding p2r b'v p'b'
                    by (auto simp: optimal_def intro!: valid_checkApp_VSince)
                  from p'_def have wqo_p': "wqo p' (Inr (VSince (i - 1) p ys))"
                    using val_q' unfolding optimal_def by simp
                  moreover have wqo_p2: "wqo p2 (Inr y)" using i_props p2_def y_val
                    unfolding optimal_def by auto
                  ultimately show ?thesis
                    unfolding prems using p'b' b'v p2_def q_val prems p2r unfolding valid_def optimal_def
                    using proofApp_mono[OF check_p check_q wqo_p' wqo_p2[unfolded p2r] p_val q_val2]
                    apply auto
                    by (metis One_nat_def Suc_diff_1 bv i_props prems(8) q_le qr)
                qed
                done
            next
              case False
              then have form: "minp = Inr (VSince i vphi' vpsis')"
                using b'v Inl minp Inr filter_nnil unfolding doSince_def
                by (cases p2) (auto simp: min_list_wrt_def)
              then show ?thesis using qr bv q_val Inl p1_def i_props
                unfolding optimal_def valid_def
                apply (cases ps rule: rev_cases)
                apply (auto simp add: Let_def False i_ltp_to_tau split: if_splits)[1]
                subgoal premises prems
                proof -
                  from p'_def have p'_val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) p'"
                    unfolding optimal_def by auto
                  from p1_def Inl have p_ni: "\<not> v_at p = s_at a1"
                    using check_consistent[OF bfphi] prems(13-15)
                    unfolding optimal_def valid_def
                    by auto
                  then have p_le_predi: "v_at p \<le> s_at a1 - 1"
                    using p_bounds prems by auto
                  then have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince (i-1) p ps))"
                    using valid_shift_VSince[of i I phi psi p ps]
                    using i_props q_val False prems(12)
                    by (auto simp: qr bv prems(8))
                  then have "wqo p' (Inr (VSince (i-1) p ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr (Inr (VSince (i - 1) vphi' vpsis'))"
                    using p'_val
                    by (auto simp: p'b' b'v intro!: valid_checkIncr_VSince)
                  moreover have "checkIncr (Inr (VSince (s_at a1 - Suc 0) p []))"
                    using p_le_predi
                    by (auto intro!: checkIncr.intros)
                  ultimately show ?thesis
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince (i-1) p ps)"]
                      valid_q_before i_props prems(3,13)
                    unfolding p'b' b'v
                    apply (auto simp add: proofIncr_def intro: checkIncr.intros split: enat.splits)
                    using bv prems(4) qr apply blast+
                    done
                qed
                subgoal premises prems for ys y
                proof -
                  {fix i j
                  }
                  from p1_def have a1_i: "s_at a1 = i" using Inl
                    unfolding optimal_def valid_def by auto
                  from p'_def have p'_val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) p'"
                    unfolding optimal_def by auto
                  from p1_def have p_ni: "\<not> v_at p = s_at a1"
                    using check_consistent[OF bfphi] prems
                    unfolding optimal_def valid_def
                    by auto
                  then have p_le_predi: "v_at p \<le> s_at a1 - 1"
                    using p_bounds prems thm i_le_ltpi_minus
                    by (auto simp: Let_def)
                      (*
                  with a1_i prems(2-4, 7-8) False i_props p_bounds have "map v_at ps = [v_at p ..< Suc (l rho (i-1) (subtract (\<Delta> rho i) I))]"
                    apply (auto simp: Let_def split: enat.splits)
                         apply (simp add: min_def split: if_splits)
                          apply (metis a1_i diff_is_0_eq i_le_ltpi_minus i_props neq0_conv zero_less_diff)
                         apply (smt add.commute Nat.add_0_right Nat.minus_nat.diff_0 One_nat_def diff_cancel_middle diff_is_0_eq' i_le_ltpi_minus i_ltp_to_tau i_props i_to_predi_props nat_le_linear neq0_conv predi_eq_ltp zero_less_diff)
                        apply (simp add: min_def split: if_splits)
                         apply (metis a1_i diff_is_0_eq i_le_ltpi_minus i_props neq0_conv zero_less_diff)
                        apply (smt add.commute Nat.add_0_right Nat.minus_nat.diff_0 One_nat_def diff_cancel_middle diff_is_0_eq' i_le_ltpi_minus i_ltp_to_tau i_props i_to_predi_props nat_le_linear neq0_conv predi_eq_ltp zero_less_diff)
                       apply (metis Nat.minus_nat.diff_0 diff_cancel_middle diff_is_0_eq' i_le_ltpi le_trans nat_le_linear)
                      apply (simp add: min_def split: if_splits)
                       apply (metis a1_i diff_is_0_eq i_le_ltpi_minus i_props neq0_conv zero_less_diff)
                      apply (smt add.commute Nat.add_0_right Nat.minus_nat.diff_0 One_nat_def diff_cancel_middle diff_is_0_eq' i_le_ltpi_minus i_ltp_to_tau i_props i_to_predi_props nat_le_linear neq0_conv predi_eq_ltp zero_less_diff)
                     apply (simp add: min_def split: if_splits)
                      apply (metis a1_i diff_is_0_eq i_le_ltpi_minus i_props neq0_conv zero_less_diff)
                     apply (smt add.commute Nat.add_0_right Nat.minus_nat.diff_0 One_nat_def diff_cancel_middle diff_is_0_eq' i_le_ltpi_minus i_ltp_to_tau i_props i_to_predi_props nat_le_linear neq0_conv predi_eq_ltp zero_less_diff)
                    by (metis Nat.minus_nat.diff_0 diff_cancel_middle diff_is_0_eq' i_le_ltpi le_trans nat_le_linear)
*)
                  then have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince (i-1) p ps))"
                    using valid_shift_VSince[of i I phi psi p ps]
                    using prems val_ge_zero[OF p'b' b'v p'_val] False i_props p_le_predi
                    unfolding valid_def
                    by (auto simp: Let_def)
                  then have "wqo p' (Inr (VSince (i-1) p ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VSince)
                  moreover have "checkIncr (Inr (VSince (i - 1) p ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VSince)
                  ultimately show ?thesis
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince (i-1) p ps)"]
                      valid_q_before i_props prems(3) form qr
                    unfolding p'b' b'v a1_i[symmetric]
                    by (auto simp add: proofIncr_def intro: checkIncr.intros)
                qed
                done
            qed
          next
            case (Inr b1)
            then show ?thesis
            proof (cases "left I = 0")
              case True
              then have form: "minp = Inr (VSince i b1 [projr p2]) \<or> minp = (p' \<oplus> p2)"
                using Inr p'b' b'v minp val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doSince_def by (cases p2) (auto simp: min_list_wrt_def)
              then obtain p2' where p2r: "p2 = Inr p2'"
                using p'b' b'v Inr True minp val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doSince_def
                by (cases p2; auto simp: min_list_wrt_def split: if_splits)
              then have res: "doSince i (left I) p1 p2 p' = [Inr (VSince i b1 [projr p2]), (p' \<oplus> p2)]"
                using True Inr p'b' b'v unfolding doSince_def by auto
              from True q_val qr bv have ps_not_nil: "ps \<noteq> []"
                unfolding valid_def
                apply (auto simp: Let_def split: if_splits)
                using i_le_ltpi le_trans by blast
              then obtain y and ys where snoc_q: "ps = ys @ [y]"
                using qr bv
                by (cases ps rule: rev_cases; auto)
              then have y_val: "valid rho i psi (Inr y)"
                using q_val qr bv True unfolding valid_def
                by (auto simp: Let_def min_def i_le_ltpi split: if_splits)
              then have wqo_p2: "wqo (Inr p2') (Inr y)" using p2r p2_def
                unfolding optimal_def by auto
              then show ?thesis
              proof (cases ys)
                case Nil
                then have p_eq_i: "v_at p = i" using True bv qr q_val i_props
                  unfolding valid_def
                  apply (auto simp: Let_def min_def i_le_ltpi split: if_splits)
                  by (metis List.list.simps(8) List.list.simps(9) append1_eq_conv le_antisym map_append neq0_conv snoc_q upt_eq_Nil_conv)
                then have p_val: "valid rho i phi (Inr p)" using vp
                  by auto
                from wqo_p2 have lcomp: "wqo (Inr p2') (Inr y)"
                  by auto
                moreover have wqo_p1: "wqo (Inr b1) (Inr p)"
                  using Inr p1_def p_val unfolding optimal_def by auto
                ultimately have "wqo (Inr (VSince i b1 [p2'])) q"
                  using qr bv snoc_q VSince[OF wqo_p1 lcomp] Nil p2r
                  by auto
                moreover have "(Inr (VSince i b1 [p2'])) \<in> set (doSince i (left I) p1 p2 p')"
                  using form minp Inr p2r Inr True b'v p'b'
                  unfolding doSince_def by auto
                ultimately show ?thesis using minp min_list_wrt_le[OF _ refl_wqo]
                    since_sound[OF i_props p1_def p2_def p'_def _ bf bf'] form
                    pw_total[of i "Since phi I psi"] p'b' trans_wqo Inr b'v p2r
                  unfolding proofApp_def
                  apply (auto simp add: total_on_def)
                  by (metis transpD)
              next
                case (Cons a as)
                then have p_less_i: "v_at p \<le> i - 1"
                  using True bv qr q_val i_props snoc_q Cons_eq_upt_conv
                  unfolding valid_def
                  by (auto simp: Let_def min_def i_le_ltpi split: if_splits)
                then have q'_val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince (i-1) p ys))"
                  using q_val snoc_q True qr bv etpi_imp_etp_suci i_props
                  unfolding valid_def
                  by (auto simp: Let_def min_def i_ltp_to_tau split: if_splits enat.splits)
                then have wqo_p': "wqo p' (Inr (VSince (i-1) p ys))"
                  using p'_def unfolding optimal_def by auto
                have check_q: "checkApp (Inr (VSince (i-1) p ys)) (Inr y)"
                  using q'_val True
                  by (auto intro!: valid_checkApp_VSince)
                have check_min: "checkApp p' (Inr p2')" using p2r p'b' b'v
                  using p'_def True
                  by (auto simp: optimal_def intro!: valid_checkApp_VSince)
                from res have val_min: "valid rho i (Since phi I psi) (p' \<oplus> (Inr p2'))"
                  using b'v p'b' p2r
                    since_sound[OF i_props p1_def p2_def p'_def _ bf bf']
                  by auto
                from q_val have q_val2: "valid rho i (Since phi I psi) ((Inr (VSince (i-1) p ys)) \<oplus> (Inr y))"
                  using qr bv snoc_q i_props unfolding proofApp_def by auto
                then have "wqo (p' \<oplus> (Inr p2')) q"
                  using qr bv snoc_q p'b' b'v i_props
                    proofApp_mono[OF check_min check_q wqo_p' wqo_p2 val_min q_val2]
                  by auto
                moreover have "(p' \<oplus> (Inr p2')) \<in> set (doSince i (left I) p1 p2 p')"
                  using form minp Inr p2r Inr True b'v p'b'
                  unfolding doSince_def by auto
                ultimately show ?thesis using minp min_list_wrt_le[OF _ refl_wqo]
                    since_sound[OF i_props p1_def p2_def p'_def _ bf bf'] form
                    pw_total[of i "Since phi I psi"] p'b' trans_wqo Inr b'v p2r
                  unfolding proofApp_def
                  apply (auto simp add: total_on_def)
                  by (metis transpD)
              qed
            next
              case False
              then have lI: "left I \<noteq> 0" by auto
              then have form: "minp = Inr (VSince i b1 [])
                \<or> minp = Inr (VSince i vphi' vpsis')" using Inr p'b' b'v minp
                val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doSince_def by (cases p2) (auto simp: min_list_wrt_def)
              from p1_def Inr have b1i: "v_at b1 = i"
                unfolding optimal_def valid_def by auto
              from False Inr p'b' b'v have
                res: "doSince i (left I) p1 p2 p' = [Inr (VSince i b1 []), Inr (VSince i vphi' vpsis')]"
                unfolding doSince_def by (cases p2; auto)
              then show ?thesis
              proof (cases "v_at p = i")
                case True
                then have ps_nil: "ps = []" using qr bv q_val False
                  unfolding valid_def
                  apply (auto simp: Let_def min_def split: if_splits)
                  using i_le_ltpi_minus by force
                from True vp have wqo_p1: "wqo (Inr b1) (Inr p)" using p1_def Inr
                  unfolding optimal_def by auto
                then have "wqo (Inr (VSince i b1 [])) q"
                  using qr bv ps_nil VSince_Nil[OF wqo_p1] by auto
                moreover have "(Inr (VSince i b1 [])) \<in> set (doSince i (left I) p1 p2 p')"
                  using Inr b'v p'b' res by auto
                ultimately show ?thesis using minp min_list_wrt_le[OF _ refl_wqo]
                    since_sound[OF i_props p1_def p2_def p'_def _ bf bf'] form
                    pw_total[of i "Since phi I psi"] p'b' trans_wqo Inr b'v
                  apply (auto simp add: total_on_def)
                  by (metis transpD)
              next
                case False
                then have p_le_predi: "v_at p \<le> i - 1" using p_bounds
                  apply (cases "right I")
                  apply fastforce
                  by linarith
                from p'_def have p'_val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) p'"
                  unfolding optimal_def by auto
                then show ?thesis using qr bv q_val Inr p1_def i_props
                  unfolding optimal_def valid_def
                  apply (cases ps rule: rev_cases)
                  apply (auto simp add: Let_def False i_ltp_to_tau split: if_splits)[1]
                  subgoal premises prems
                  proof -
                    from p'_def have p'_val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) p'"
                      unfolding optimal_def by auto
                    then have p_le_predi: "v_at p \<le> i - 1" using False p_bounds
                      by auto
                    then have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince (i-1) p ps))"
                      using prems val_ge_zero[OF p'b' b'v p'_val]
                      unfolding valid_def
                      apply (auto simp add: le_diff_conv Let_def i_ltp_to_tau split: enat.splits)
                      using One_nat_def i_to_predi_props prems(11) apply presburger+
                      done
                    then have "wqo p' (Inr (VSince (i-1) p ps))" using p'_def
                      unfolding optimal_def by auto
                    moreover have "checkIncr p'"
                      using p'_def
                      unfolding p'b' b'v
                      by (auto simp: optimal_def intro!: valid_checkIncr_VSince)
                    moreover have "checkIncr (Inr (VSince (i - 1) p ps))"
                      using valid_q_before
                      by (auto intro!: valid_checkIncr_VSince)
                    ultimately have wqo_p: "wqo (Inr (VSince i vphi' vpsis')) q"
                      using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince (i-1) p ps)"]
                        valid_q_before i_props prems(3) qr bv
                      unfolding p'b' b'v
                      by (auto simp add: proofIncr_def)
                    moreover have comp_in: "(Inr (VSince i vphi' vpsis')) \<in> set (doSince i (left I) p1 p2 p')"
                      using Inr b'v p'b' res by auto
                    ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo trans_wqo]
                        since_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                        pw_total[of i "Since phi I psi"] p'b' trans_wqo b'v wqo_p prems res
                        prems(13)
                      apply (auto simp add: total_on_def)
                      by (metis transpD)
                  qed
                  subgoal premises prems for ys y
                  proof -
                    from False have p_le_predi: "v_at p \<le> i - 1"
                      using p_bounds
                      by auto
                        (*
                    with prems(2-4, 7-8) False i_props p_bounds have "map v_at ps = [v_at p ..< Suc (l rho (i-1) (subtract (\<Delta> rho i) I))]"
                    apply (auto simp: Let_def split: enat.splits)
                         apply (simp add: min_def split: if_splits)
                      apply (metis add_leD2 add_le_imp_le_diff diff_diff_cancel diff_is_0_eq i_ltp_to_tau lI)
                         apply (smt add.commute Nat.add_0_right Nat.minus_nat.diff_0 One_nat_def diff_cancel_middle diff_is_0_eq' i_le_ltpi_minus i_ltp_to_tau i_props i_to_predi_props nat_le_linear neq0_conv predi_eq_ltp zero_less_diff)
                        apply (simp add: min_def split: if_splits)
                         apply (metis add_leD2 add_le_imp_le_diff diff_diff_cancel diff_is_0_eq i_ltp_to_tau lI)
                        apply (smt add.commute Nat.add_0_right Nat.minus_nat.diff_0 One_nat_def diff_cancel_middle diff_is_0_eq' i_le_ltpi_minus i_ltp_to_tau i_props i_to_predi_props nat_le_linear neq0_conv predi_eq_ltp zero_less_diff)
                       apply (metis Nat.minus_nat.diff_0 diff_cancel_middle diff_is_0_eq' i_le_ltpi le_trans nat_le_linear)
                      apply (simp add: min_def split: if_splits)
                       apply (metis add_leD2 add_le_imp_le_diff diff_diff_cancel diff_is_0_eq i_ltp_to_tau lI)
                      apply (smt add.commute Nat.add_0_right Nat.minus_nat.diff_0 One_nat_def diff_cancel_middle diff_is_0_eq' i_le_ltpi_minus i_ltp_to_tau i_props i_to_predi_props nat_le_linear neq0_conv predi_eq_ltp zero_less_diff)
                     apply (simp add: min_def split: if_splits)
                      apply (metis add_leD2 add_le_imp_le_diff diff_diff_cancel diff_is_0_eq i_ltp_to_tau lI)
                     apply (smt add.commute Nat.add_0_right Nat.minus_nat.diff_0 One_nat_def diff_cancel_middle diff_is_0_eq' i_le_ltpi_minus i_ltp_to_tau i_props i_to_predi_props nat_le_linear neq0_conv predi_eq_ltp zero_less_diff)
                    by (metis Nat.minus_nat.diff_0 diff_cancel_middle diff_is_0_eq' i_le_ltpi le_trans nat_le_linear)
*)
                    have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince (i-1) p ps))"
                      using valid_shift_VSince[of i I phi psi p ps]
                      using prems val_ge_zero[OF p'b' b'v p'_val] lI i_props p_le_predi
                      unfolding valid_def
                      by (auto simp: Let_def)
                    then have "wqo p' (Inr (VSince (i-1) p ps))" using p'_def
                      unfolding optimal_def by auto
                    moreover have "checkIncr p'"
                      using p'_def
                      unfolding p'b' b'v
                      by (auto simp: optimal_def intro!: valid_checkIncr_VSince)
                    moreover have "checkIncr (Inr (VSince (i - 1) p ps))"
                      using valid_q_before
                      by (auto intro!: valid_checkIncr_VSince)
                    ultimately have wqo_p: "wqo (Inr (VSince i vphi' vpsis')) q"
                      using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince (i-1) p ps)"]
                        valid_q_before i_props qr bv
                      unfolding p'b' b'v
                      by (auto simp add: proofIncr_def intro: checkIncr.intros)
                    moreover have comp_in: "(Inr (VSince i vphi' vpsis')) \<in> set (doSince i (left I) p1 p2 p')"
                      using Inr b'v p'b' res by auto
                    ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo trans_wqo]
                        since_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                        pw_total[of i "Since phi I psi"] p'b' trans_wqo b'v wqo_p prems res
                      apply (auto simp add: total_on_def)
                      by (metis transpD)
                  qed
                  done
              qed
            qed
          qed
        }
        moreover
        {fix li' vpsis'
          assume b'v: "b' = VSince_never (i-1) li' vpsis'"
          have li'_def: "li' = li"
            using p'_def
            by (auto simp: Inr b'v optimal_def valid_def li_def)
          have "wqo minp q"
            using b'v
          proof (cases p1)
            case (Inl a1)
            from p1_def have a1_i: "s_at a1 = i" using Inl
              unfolding optimal_def valid_def by auto
            show ?thesis
              using Inl
            proof (cases "left I = 0")
              case True
              then have form_min: "minp = p' \<oplus> p2" using Inl b'v p'b' minp
                  val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doSince_def by (cases p2) (auto simp: min_list_wrt_def)
              then obtain p2' where p2r: "p2 = Inr p2'"
                using True b'v Inl minp Inr val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doSince_def
                apply (cases p2; auto simp: min_list_wrt_def split: if_splits)
                by (metis Inl_Inr_False)
              then show ?thesis
                using form_min qr bv Inl p1_def q_val unfolding optimal_def valid_def
                apply (cases ps rule: rev_cases)
                apply (auto simp add: Let_def True i_ltp_to_tau split: if_splits enat.splits)[1]
                subgoal premises prems for ys y
                proof -
                  from vmin form_min p2r have p_val: "valid rho i (Since phi I psi) (p' \<oplus> (Inr p2'))"
                    by auto
                  have check_p: "checkApp p' (Inr p2')"
                    using p'_def True
                    unfolding p2r b'v p'b'
                    by (auto simp: optimal_def intro!: valid_checkApp_VSince_never)
                  from prems have y_val: "valid rho i psi (Inr y)"
                    using q_val True i_le_ltpi i_props unfolding valid_def
                    by (auto simp: Let_def min_def split: if_splits)
                  have "v_at p \<le> s_at a1 - Suc 0"
                    using p1_def q_val
                    apply (auto simp: Inl optimal_def valid_def qr bv Let_def)
                    by (metis MTL.trans_wqo.check_consistent Suc_pred bfphi i_props le_antisym not_less_eq_eq trans_wqo_axioms)
                  then have val_q': "valid rho (i - 1) (Since phi (subtract (delta rho i (i - 1)) I) psi) (Inr (VSince (i - 1) p ys))"
                    using valid_shift_VSince[of i I phi psi p ps]
                    using qr bv Inl p1_def q_val etpi_imp_etp_suci i_props prems
                    unfolding optimal_def valid_def
                    by (auto simp add: Let_def True)
                  then have q_val2: "valid rho i (Since phi I psi) ((Inr (VSince (i-1) p ys)) \<oplus> (Inr y))"
                    using q_val prems i_props by auto
                  have check_q: "checkApp (Inr (VSince (i-1) p ys)) (Inr y)"
                    using val_q' True
                    by (auto intro!: valid_checkApp_VSince)
                  from p'_def have wqo_p': "wqo p' (Inr (VSince (i - 1) p ys))"
                    using val_q' unfolding optimal_def by simp
                  moreover have wqo_p2: "wqo p2 (Inr y)" using i_props p2_def y_val
                    unfolding optimal_def by auto
                  ultimately show ?thesis
                    unfolding prems using p'b' b'v p2_def q_val prems p2r unfolding valid_def optimal_def
                    using proofApp_mono[OF check_p check_q wqo_p' wqo_p2[unfolded p2r] p_val q_val2]
                    apply auto
                    by (metis One_nat_def Suc_diff_1 bv i_props prems(8) q_le qr)
                qed
                done
            next
              case False
              then have form: "minp = Inr (VSince_never i li' vpsis')"
                using minp p'b' b'v Inl filter_nnil unfolding doSince_def
                by (cases p2) (auto simp: min_list_wrt_def)
              then show ?thesis using qr bv q_val Inl p1_def i_props
                unfolding optimal_def valid_def
                apply (cases ps rule: rev_cases)
                apply (auto simp add: Let_def False i_ltp_to_tau split: if_splits)[1]
                subgoal premises prems
                proof -
                  from p'_def have p'_val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) p'"
                    unfolding optimal_def by auto
                  from p1_def Inl have p_ni: "\<not> v_at p = s_at a1"
                    using check_consistent[OF bfphi] prems
                    unfolding optimal_def valid_def
                    by auto
                  then have p_le_predi: "v_at p \<le> s_at a1 - 1"
                    using p_bounds prems
                    by auto
                  then have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince (i-1) p ps))"
                    using valid_shift_VSince[of i I phi psi p ps] i_props q_val False
                    by (auto simp: qr bv a1_i)
                  then have "wqo p' (Inr (VSince (i-1) p ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VSince_never)
                  moreover have "checkIncr (Inr (VSince (i - 1) p ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VSince)
                  ultimately show ?thesis
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince (i-1) p ps)"]
                      valid_q_before i_props prems
                    unfolding p'b' b'v
                    by (auto simp add: proofIncr_def li'_def intro: checkIncr.intros)
                qed
                subgoal premises prems for ys y
                proof -
                  thm Inl
                  from p'_def have p'_val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) p'"
                    unfolding optimal_def by auto
                  from p1_def have p_ni: "\<not> v_at p = s_at a1"
                    using check_consistent[OF bfphi] prems
                    unfolding optimal_def valid_def
                    by auto
                  then have p_le_predi: "v_at p \<le> s_at a1 - 1"
                    using p_bounds prems
                    by auto
                      (*
                   with a1_i prems(2-4, 8) False i_props p_bounds have "map v_at ps = [v_at p ..< Suc (l rho (i-1) (subtract (\<Delta> rho i) I))]"
                    apply (auto simp: Let_def split: enat.splits)
                         apply (simp add: min_def split: if_splits)
                          apply (metis a1_i diff_is_0_eq i_le_ltpi_minus i_props neq0_conv zero_less_diff)
                         apply (smt add.commute Nat.add_0_right Nat.minus_nat.diff_0 One_nat_def diff_cancel_middle diff_is_0_eq' i_le_ltpi_minus i_ltp_to_tau i_props i_to_predi_props nat_le_linear neq0_conv predi_eq_ltp zero_less_diff)
                        apply (simp add: min_def split: if_splits)
                         apply (metis a1_i diff_is_0_eq i_le_ltpi_minus i_props neq0_conv zero_less_diff)
                        apply (smt add.commute Nat.add_0_right Nat.minus_nat.diff_0 One_nat_def diff_cancel_middle diff_is_0_eq' i_le_ltpi_minus i_ltp_to_tau i_props i_to_predi_props nat_le_linear neq0_conv predi_eq_ltp zero_less_diff)
                       apply (metis Nat.minus_nat.diff_0 diff_cancel_middle diff_is_0_eq' i_le_ltpi le_trans nat_le_linear)
                      apply (simp add: min_def split: if_splits)
                       apply (metis a1_i diff_is_0_eq i_le_ltpi_minus i_props neq0_conv zero_less_diff)
                      apply (smt add.commute Nat.add_0_right Nat.minus_nat.diff_0 One_nat_def diff_cancel_middle diff_is_0_eq' i_le_ltpi_minus i_ltp_to_tau i_props i_to_predi_props nat_le_linear neq0_conv predi_eq_ltp zero_less_diff)
                     apply (simp add: min_def split: if_splits)
                      apply (metis a1_i diff_is_0_eq i_le_ltpi_minus i_props neq0_conv zero_less_diff)
                     apply (smt add.commute Nat.add_0_right Nat.minus_nat.diff_0 One_nat_def diff_cancel_middle diff_is_0_eq' i_le_ltpi_minus i_ltp_to_tau i_props i_to_predi_props nat_le_linear neq0_conv predi_eq_ltp zero_less_diff)
                    by (metis Nat.minus_nat.diff_0 diff_cancel_middle diff_is_0_eq' i_le_ltpi le_trans nat_le_linear)
*)
                  then have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince (i-1) p ps))"
                    using valid_shift_VSince[of i I phi psi p ps] False q_val i_props
                    by (auto simp: qr bv a1_i)
                  then have "wqo p' (Inr (VSince (i-1) p ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VSince_never)
                  moreover have "checkIncr (Inr (VSince (i - 1) p ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VSince)
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VSince_never)
                  moreover have "checkIncr (Inr (VSince (i - 1) p ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VSince)
                  ultimately show ?thesis
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince (i-1) p ps)"]
                      valid_q_before i_props prems form qr
                    unfolding p'b' b'v a1_i[symmetric]
                    by (auto simp add: proofIncr_def li'_def intro: checkIncr.intros)
                qed
                done
            qed
          next
            case (Inr b1)
            then show ?thesis
            proof (cases "left I = 0")
              case True
              then have form: "minp = Inr (VSince i b1 [projr p2]) \<or> minp = p' \<oplus> p2"
                using Inr p'b' b'v minp val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doSince_def by (cases p2) (auto simp: min_list_wrt_def)
              then obtain p2' where p2r: "p2 = Inr p2'"
                using p'b' b'v Inr True minp val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doSince_def
                by (cases p2; auto simp: min_list_wrt_def split: if_splits)
              then have res: "doSince i (left I) p1 p2 p' = [Inr (VSince i b1 [projr p2]), (p' \<oplus> p2)]"
                using True Inr p'b' b'v unfolding doSince_def by auto
              from True q_val qr bv have ps_not_nil: "ps \<noteq> []"
                unfolding valid_def
                apply (auto simp: Let_def split: if_splits)
                using i_le_ltpi le_trans by blast
              then obtain y and ys where snoc_q: "ps = ys @ [y]"
                using qr bv
                by (cases ps rule: rev_cases; auto)
              then have y_val: "valid rho i psi (Inr y)"
                using q_val qr bv True unfolding valid_def
                by (auto simp: Let_def min_def i_le_ltpi split: if_splits)
              then have wqo_p2: "wqo (Inr p2') (Inr y)" using p2r p2_def
                unfolding optimal_def by auto
              then show ?thesis
              proof (cases ys)
                case Nil
                then have p_eq_i: "v_at p = i" using True bv qr q_val i_props
                  unfolding valid_def
                  apply (auto simp: Let_def min_def i_le_ltpi split: if_splits)
                  by (metis List.list.simps(8) List.list.simps(9) append1_eq_conv le_antisym map_append neq0_conv snoc_q upt_eq_Nil_conv)
                then have p_val: "valid rho i phi (Inr p)" using vp
                  by auto
                from wqo_p2 have lcomp: "wqo (Inr p2') (Inr y)"
                  by auto
                moreover have wqo_p1: "wqo (Inr b1) (Inr p)"
                  using Inr p1_def p_val unfolding optimal_def by auto
                ultimately have "wqo (Inr (VSince i b1 [p2'])) q"
                  using qr bv snoc_q VSince[OF wqo_p1 lcomp] Nil p2r
                  by auto
                moreover have "(Inr (VSince i b1 [p2'])) \<in> set (doSince i (left I) p1 p2 p')"
                  using form minp Inr p2r Inr True b'v p'b'
                  unfolding doSince_def by auto
                ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                    since_sound[OF i_props p1_def p2_def p'_def _ bf bf'] form
                    pw_total[of i "Since phi I psi"] p'b' trans_wqo Inr b'v p2r
                  unfolding proofApp_def
                  apply (auto simp add: total_on_def)
                  by (metis transpD)
              next
                case (Cons a as)
                then have p_less_i: "v_at p \<le> i - 1"
                  using True bv qr q_val i_props snoc_q Cons_eq_upt_conv
                  unfolding valid_def
                  by (auto simp: Let_def min_def i_le_ltpi split: if_splits)
                then have q'_val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince (i-1) p ys))"
                  using q_val snoc_q True qr bv etpi_imp_etp_suci i_props
                  unfolding valid_def
                  by (auto simp: Let_def min_def i_ltp_to_tau split: if_splits enat.splits)
                then have wqo_p': "wqo p' (Inr (VSince (i-1) p ys))"
                  using p'_def unfolding optimal_def by auto
                have check_q: "checkApp (Inr (VSince (i-1) p ys)) (Inr y)"
                  using q'_val True
                  by (auto intro!: valid_checkApp_VSince)
                have check_min: "checkApp p' (Inr p2')" using p2r p'b' b'v
                  using p'_def True
                  unfolding p2r b'v p'b'
                  by (auto simp: optimal_def intro!: valid_checkApp_VSince_never)
                from res have val_min: "valid rho i (Since phi I psi) (p' \<oplus> (Inr p2'))"
                  using b'v p'b' p2r
                    since_sound[OF i_props p1_def p2_def p'_def _ bf bf']
                  by auto
                from q_val have q_val2: "valid rho i (Since phi I psi) ((Inr (VSince (i-1) p ys)) \<oplus> (Inr y))"
                  using qr bv snoc_q i_props unfolding proofApp_def by auto
                then have "wqo (p' \<oplus> (Inr p2')) q"
                  using qr bv snoc_q p'b' b'v i_props
                    proofApp_mono[OF check_min check_q wqo_p' wqo_p2 val_min q_val2]
                  by auto
                moreover have "(p' \<oplus> (Inr p2')) \<in> set (doSince i (left I) p1 p2 p')"
                  using form minp Inr p2r Inr True b'v p'b'
                  unfolding doSince_def by auto
                ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                    since_sound[OF i_props p1_def p2_def p'_def _ bf bf'] form
                    pw_total[of i "Since phi I psi"] p'b' trans_wqo Inr b'v p2r
                  unfolding proofApp_def
                  apply (auto simp add: total_on_def)
                  by (metis transpD)
              qed
            next
              case False
              then have lI: "left I \<noteq> 0" by auto
              then have form: "minp = Inr (VSince i b1 [])
              \<or> minp = Inr (VSince_never i li' vpsis')" using Inr p'b' b'v minp filter_nnil
                unfolding doSince_def by (cases p2) (auto simp: min_list_wrt_def)
              from p1_def Inr have b1i: "v_at b1 = i"
                unfolding optimal_def valid_def by auto
              from False Inr p'b' b'v have
                res: "doSince i (left I) p1 p2 p' = [Inr (VSince i b1 []), Inr (VSince_never i li' vpsis')]"
                unfolding doSince_def by (cases p2; auto)
              then show ?thesis
              proof (cases "v_at p = i")
                case True
                then have ps_nil: "ps = []" using qr bv q_val False
                  unfolding valid_def
                  apply (auto simp: Let_def min_def split: if_splits)
                  using i_le_ltpi_minus by force
                from True vp have wqo_p1: "wqo (Inr b1) (Inr p)" using p1_def Inr
                  unfolding optimal_def by auto
                then have "wqo (Inr (VSince i b1 [])) q"
                  using qr bv ps_nil VSince_Nil[OF wqo_p1] by auto
                moreover have "(Inr (VSince i b1 [])) \<in> set (doSince i (left I) p1 p2 p')"
                  using Inr b'v p'b' res by auto
                ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                    since_sound[OF i_props p1_def p2_def p'_def _ bf bf'] form
                    pw_total[of i "Since phi I psi"] p'b' trans_wqo Inr b'v
                  apply (auto simp add: total_on_def)
                  by (metis transpD)
              next
                case False
                then have p_le_predi: "v_at p \<le> i - 1" using p_bounds
                  by auto
                from p'_def have p'_val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) p'"
                  unfolding optimal_def by auto
                then show ?thesis using qr bv q_val Inr p1_def i_props
                  unfolding optimal_def valid_def
                  apply (cases ps rule: rev_cases)
                  apply (auto simp add: Let_def False i_ltp_to_tau split: if_splits)[1]
                  subgoal premises prems
                  proof -
                    from p'_def have p'_val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) p'"
                      unfolding optimal_def by auto
                    then have p_le_predi: "v_at p \<le> i - 1" using False p_bounds
                      by auto
                    then have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince (i-1) p ps))"
                      using prems val_ge_zero_never[OF p'b' b'v p'_val]
                      unfolding valid_def
                      apply (auto simp add: le_diff_conv Let_def i_ltp_to_tau split: enat.splits)
                      using i_props i_to_predi_props apply blast+
                      done
                    then have "wqo p' (Inr (VSince (i-1) p ps))" using p'_def
                      unfolding optimal_def by auto
                    moreover have "checkIncr p'"
                      using p'_def
                      unfolding p'b' b'v
                      by (auto simp: optimal_def intro!: valid_checkIncr_VSince_never)
                    moreover have "checkIncr (Inr (VSince (i - 1) p ps))"
                      using valid_q_before
                      by (auto intro!: valid_checkIncr_VSince)
                    ultimately have wqo_p: "wqo (Inr (VSince_never i li' vpsis')) q"
                      using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince (i-1) p ps)"]
                        valid_q_before i_props prems(3) qr bv
                      unfolding p'b' b'v prems(13)
                      by (auto simp add: proofIncr_def intro: checkIncr.intros)
                    moreover have comp_in: "(Inr (VSince_never i li' vpsis')) \<in> set (doSince i (left I) p1 p2 p')"
                      using Inr b'v p'b' res by auto
                    ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo trans_wqo]
                        since_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                        pw_total[of i "Since phi I psi"] p'b' trans_wqo b'v wqo_p prems res
                      apply (auto simp add: total_on_def li)
                      by (metis transpD)
                  qed
                  subgoal premises prems for ys y
                  proof -
                    from False have p_le_predi: "v_at p \<le> i - 1"
                      using p_bounds by auto
                        (*
                    with prems(2-4, 8) False i_props p_bounds have "map v_at ps = [v_at p ..< Suc (l rho (i-1) (subtract (\<Delta> rho i) I))]"
                    apply (auto simp: Let_def split: enat.splits)
                         apply (simp add: min_def split: if_splits)
                      apply (metis add_leD2 add_le_imp_le_diff diff_diff_cancel diff_is_0_eq i_ltp_to_tau lI)
                         apply (smt add.commute Nat.add_0_right Nat.minus_nat.diff_0 One_nat_def diff_cancel_middle diff_is_0_eq' i_le_ltpi_minus i_ltp_to_tau i_props i_to_predi_props nat_le_linear neq0_conv predi_eq_ltp zero_less_diff)
                        apply (simp add: min_def split: if_splits)
                         apply (metis add_leD2 add_le_imp_le_diff diff_diff_cancel diff_is_0_eq i_ltp_to_tau lI)
                        apply (smt add.commute Nat.add_0_right Nat.minus_nat.diff_0 One_nat_def diff_cancel_middle diff_is_0_eq' i_le_ltpi_minus i_ltp_to_tau i_props i_to_predi_props nat_le_linear neq0_conv predi_eq_ltp zero_less_diff)
                       apply (metis Nat.minus_nat.diff_0 diff_cancel_middle diff_is_0_eq' i_le_ltpi le_trans nat_le_linear)
                      apply (simp add: min_def split: if_splits)
                       apply (metis add_leD2 add_le_imp_le_diff diff_diff_cancel diff_is_0_eq i_ltp_to_tau lI)
                      apply (smt add.commute Nat.add_0_right Nat.minus_nat.diff_0 One_nat_def diff_cancel_middle diff_is_0_eq' i_le_ltpi_minus i_ltp_to_tau i_props i_to_predi_props nat_le_linear neq0_conv predi_eq_ltp zero_less_diff)
                     apply (simp add: min_def split: if_splits)
                      apply (metis add_leD2 add_le_imp_le_diff diff_diff_cancel diff_is_0_eq i_ltp_to_tau lI)
                     apply (smt add.commute Nat.add_0_right Nat.minus_nat.diff_0 One_nat_def diff_cancel_middle diff_is_0_eq' i_le_ltpi_minus i_ltp_to_tau i_props i_to_predi_props nat_le_linear neq0_conv predi_eq_ltp zero_less_diff)
                    by (metis Nat.minus_nat.diff_0 diff_cancel_middle diff_is_0_eq' i_le_ltpi le_trans nat_le_linear)
*)
                    have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince (i-1) p ps))"
                      using valid_shift_VSince[of i I phi psi p ps] i_props lI q_val p_le_predi
                      by (auto simp: qr bv)
                    then have "wqo p' (Inr (VSince (i-1) p ps))" using p'_def
                      unfolding optimal_def by auto
                    moreover have "checkIncr p'"
                      using p'_def
                      unfolding p'b' b'v
                      by (auto simp: optimal_def intro!: valid_checkIncr_VSince_never)
                    moreover have "checkIncr (Inr (VSince (i - 1) p ps))"
                      using valid_q_before
                      by (auto intro!: valid_checkIncr_VSince)
                    ultimately have wqo_p: "wqo (Inr (VSince_never i li' vpsis')) q"
                      using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince (i-1) p ps)"]
                        valid_q_before i_props qr bv
                      unfolding p'b' b'v
                      by (auto simp add: proofIncr_def intro: checkIncr.intros)
                    moreover have comp_in: "(Inr (VSince_never i li' vpsis')) \<in> set (doSince i (left I) p1 p2 p')"
                      using Inr b'v p'b' res by auto
                    ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo trans_wqo]
                        since_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                        pw_total[of i "Since phi I psi"] p'b' trans_wqo b'v wqo_p prems res
                      apply (auto simp add: total_on_def)
                      by (metis transpD)
                  qed
                  done
              qed
            qed
          qed
        }
        ultimately show ?thesis by auto
      qed
    }
    moreover
    {fix li' ps
      assume bv: "b = VSince_never i li' ps"
      have li'_def: "li' = li"
        using q_val
        by (auto simp: Inr bv valid_def li)
      have "wqo minp q"
        using bv
      proof (cases p')
        case (Inl a')
        then obtain p1' ps' where a's: "a' = SSince p1' ps'"
          using p'_def
          unfolding optimal_def valid_def
          by (cases a') auto
        from a's Inl have "\<And>n. right I = enat n \<Longrightarrow> ETP rho (\<tau> rho i - n) \<le> s_at p1'
        \<and> s_at p1' < i" using p'_def i_props mem_imp_ge_etp[of i I "s_at p1'"]
          unfolding optimal_def valid_def
          apply (auto simp: Let_def)
          by (metis One_nat_def Suc_diff_1 le_imp_less_Suc)
        then have sp1'_bounds: "ETP rho (case right I of enat n \<Rightarrow> (\<tau> rho i - n) | \<infinity> \<Rightarrow> 0) \<le> s_at p1'
        \<and> s_at p1' < i \<and> s_at p1' \<le> LTP rho (\<tau> rho i - left I)"
          using a's Inl p'_def i_props mem_imp_le_ltp[of i I "s_at p1'"]
          unfolding optimal_def valid_def
          by (auto simp: Let_def split: enat.splits)
        from bv qr have mapt: "map v_at ps = [ETP rho (case right I of enat n \<Rightarrow> (\<tau> rho i - n) | \<infinity> \<Rightarrow> 0) ..< Suc (l rho i I)]"
          using q_val unfolding valid_def by (auto simp: Let_def split: enat.splits)
        then have ps_check: "\<forall>p \<in> set ps. v_check rho psi p"
          using bv qr q_val unfolding valid_def
          by (auto simp: Let_def)
        then have jc: "\<forall>j \<in> set (map v_at ps). \<exists>p. v_at p = j \<and> v_check rho psi p"
          using map_set_in_imp_set_in[OF ps_check] by auto
        from sp1'_bounds have p1'_in: "s_at p1' \<in> set (map v_at ps)" using mapt
          by (auto split: if_splits)
        from a's Inl have "s_check rho psi p1'" using p'_def
          unfolding optimal_def valid_def by (auto simp: Let_def)
        then have False using jc p1'_in check_consistent[OF bfpsi] by auto
        then show ?thesis by auto
      next
        case (Inr b')
        then have p'b': "p' = Inr b'" by auto
        then have b'v: "(\<exists>p ps. b' = VSince (i-1) p ps)
        \<or> (\<exists>ps. b' = VSince_never (i-1) li ps)"
          using Inr p'_def i_props i_props_imp_not_le[OF i_props p'_def]
          unfolding optimal_def valid_def by (cases b') (auto simp: Let_def li_def)
        moreover
        {fix vphi' vpsis'
          assume b'v: "b' = VSince (i-1) vphi' vpsis'"
          then have "wqo minp q"
          proof (cases p1)
            case (Inl a1)
            then show ?thesis
            proof (cases "left I = 0")
              case True
              then have form_min: "minp = p' \<oplus> p2" using b'v Inl minp Inr
                  val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doSince_def by (cases p2) (auto simp: min_list_wrt_def)
              then obtain p2' where p2r: "p2 = Inr p2'"
                using True b'v Inl minp Inr val_VIO_imp_r[OF bf vmin VIO]
                  filter_nnil
                unfolding doSince_def
                apply (cases p2; auto simp: min_list_wrt_def split: if_splits)
                by (metis Inl_Inr_False)
              then show ?thesis
                using form_min qr bv Inl p1_def q_val unfolding optimal_def valid_def
                apply (cases ps rule: rev_cases)
                apply (auto simp add: Let_def True i_ltp_to_tau i_etp_to_tau split: if_splits enat.splits)[1]
                subgoal premises prems for ys y
                proof -
                  from vmin form_min p2r have p_val: "valid rho i (Since phi I psi) (p' \<oplus> (Inr p2'))"
                    by auto
                  have check_p: "checkApp p' (Inr p2')"
                    using p'_def True
                    unfolding p2r b'v p'b'
                    by (auto simp: optimal_def intro!: valid_checkApp_VSince)
                  from prems have y_val: "valid rho i psi (Inr y)"
                    using q_val True i_le_ltpi i_props unfolding valid_def
                    by (auto simp: Let_def min_def split: if_splits)
                  have val_q': "valid rho (i - 1) (Since phi (subtract (delta rho i (i - 1)) I) psi) (Inr (VSince_never (i - 1) li' ys))"
                    using valid_shift_VSince_never[of i I phi psi li' ps] i_props q_val True prems(8)
                    by (auto simp: qr bv)
                  then have q_val2: "valid rho i (Since phi I psi) ((Inr (VSince_never (i-1) li ys)) \<oplus> (Inr y))"
                    using q_val prems i_props by (auto simp: li)
                  have check_q: "checkApp (Inr (VSince_never (i-1) li' ys)) (Inr y)"
                    using val_q' True
                    by (auto intro!: valid_checkApp_VSince_never)
                  from p'_def have wqo_p': "wqo p' (Inr (VSince_never (i - 1) li' ys))"
                    using val_q' unfolding optimal_def by simp
                  moreover have wqo_p2: "wqo p2 (Inr y)" using i_props p2_def y_val
                    unfolding optimal_def by auto
                  ultimately show ?thesis
                    unfolding prems using p'b' b'v p2_def q_val prems p2r unfolding valid_def optimal_def
                    using proofApp_mono[OF check_p check_q wqo_p' wqo_p2[unfolded p2r] p_val q_val2[folded li'_def]]
                    apply (auto simp: li'_def)
                    by (metis One_nat_def Suc_diff_1 i_props q_le qr)
                qed
                done
            next
              case False
              from p'_def have p'_val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) p'"
                unfolding optimal_def by auto
              from False have form_min: "minp = Inr (VSince i vphi' vpsis')"
                using b'v Inl minp Inr filter_nnil unfolding doSince_def
                by (cases p2) (auto simp: min_list_wrt_def)
              then show ?thesis using qr bv q_val i_props
                unfolding optimal_def valid_def
                apply (auto simp add: Let_def False i_etp_to_tau i_ltp_to_tau split: if_splits enat.splits)
                subgoal premises prems
                proof -
                  have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince_never (i-1) li' ps))"
                    using valid_shift_VSince_never[of i I phi psi li' ps] i_props q_val False
                    by (auto simp: qr bv)
                  then have "wqo p' (Inr (VSince_never (i-1) li' ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VSince)
                  moreover have "checkIncr (Inr (VSince_never (i - 1) li' ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VSince_never)
                  ultimately show ?thesis
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince_never (i-1) li' ps)"]
                      valid_q_before i_props prems(2-3,10)
                    unfolding p'b' b'v
                    by (auto simp add: proofIncr_def li'_def li intro: checkIncr.intros split: enat.splits)
                qed
                subgoal premises prems
                proof -
                  have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince_never (i-1) li' ps))"
                    using valid_shift_VSince_never[of i I phi psi li' ps] i_props q_val False
                    by (auto simp: qr bv)
                  then have "wqo p' (Inr (VSince_never (i-1) li' ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VSince)
                  moreover have "checkIncr (Inr (VSince_never (i - 1) li' ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VSince_never)
                  ultimately show ?thesis
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince_never (i-1) li' ps)"]
                      valid_q_before i_props prems
                    unfolding p'b' b'v
                    by (auto simp add: proofIncr_def li intro: checkIncr.intros)
                qed
                using p1_def False Inl q_val i_props vmin apply (auto simp: Let_def optimal_def valid_def i_ltp_to_tau i_etp_to_tau i_le_ltpi split: if_splits)
                apply (metis add_leD2 i_etp_to_tau i_ltp_to_tau le_diff_conv2 le_trans)
                subgoal premises prems for n
                proof -
                  have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince_never (i-1) li' ps))"
                    using valid_shift_VSince_never[of i I phi psi li' ps] i_props q_val False
                    by (auto simp: qr bv)
                  then have "wqo p' (Inr (VSince_never (i-1) li' ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VSince)
                  moreover have "checkIncr (Inr (VSince_never (i - 1) li' ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VSince_never)
                  ultimately show ?thesis
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince_never (i-1) li' ps)"]
                      valid_q_before i_props prems
                    unfolding p'b' b'v
                    by (auto simp add: proofIncr_def li'_def li intro: checkIncr.intros)
                qed
                done
            qed
          next
            case (Inr b1)
            then show ?thesis
            proof (cases "left I = 0")
              case True
              then have form: "minp = Inr (VSince i b1 [projr p2]) \<or> minp =  (p' \<oplus> p2)"
                using Inr p'b' b'v minp val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doSince_def by (cases p2) (auto simp: min_list_wrt_def)
              then obtain p2' where p2r: "p2 = Inr p2'"
                using p'b' b'v Inr True minp val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doSince_def
                by (cases p2; auto simp: min_list_wrt_def split: if_splits)
              then have res: "doSince i (left I) p1 p2 p' = [Inr (VSince i b1 [projr p2]), (p' \<oplus> p2)]"
                using True Inr p'b' b'v unfolding doSince_def by auto
              from True q_val qr bv have ps_not_nil: "ps \<noteq> []"
                unfolding valid_def
                apply (auto simp: Let_def i_etp_to_tau split: if_splits enat.splits)
                by (meson diff_le_self i_le_ltpi leD leI less_\<tau>D less_le_trans)
              then obtain y and ys where snoc_q: "ps = ys @ [y]"
                using qr bv
                by (cases ps rule: rev_cases; auto)
              then have y_val: "valid rho i psi (Inr y)"
                using q_val qr bv True unfolding valid_def
                by (auto simp: Let_def min_def i_le_ltpi split: if_splits)
              then have wqo_p2: "wqo (Inr p2') (Inr y)" using p2r p2_def
                unfolding optimal_def by auto
              then have q'_val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince_never (i-1) li ys))"
                using q_val snoc_q True qr bv etpi_imp_etp_suci i_props
                unfolding valid_def
                by (auto simp: Let_def min_def i_ltp_to_tau li_def split: if_splits enat.splits)
              then have wqo_p': "wqo p' (Inr (VSince_never (i-1) li ys))"
                using p'_def unfolding optimal_def by auto
              have check_q: "checkApp (Inr (VSince_never (i-1) li ys)) (Inr y)"
                using q'_val True
                by (auto intro!: valid_checkApp_VSince_never)
              have check_min: "checkApp p' (Inr p2')" using p2r p'b' b'v
                using p'_def True
                unfolding p2r b'v p'b'
                by (auto simp: optimal_def intro!: valid_checkApp_VSince)
              from res have val_min: "valid rho i (Since phi I psi) (p' \<oplus> (Inr p2'))"
                using b'v p'b' p2r
                  since_sound[OF i_props p1_def p2_def p'_def _ bf bf']
                by auto
              from q_val have q_val2: "valid rho i (Since phi I psi) ((Inr (VSince_never (i-1) li ys)) \<oplus> (Inr y))"
                using qr bv snoc_q i_props unfolding proofApp_def by (auto simp: li'_def)
              then have "wqo (p' \<oplus> (Inr p2')) q"
                using qr bv snoc_q p'b' b'v i_props
                  proofApp_mono[OF check_min check_q wqo_p' wqo_p2 val_min q_val2]
                by (auto simp: li'_def)
              moreover have "(p' \<oplus> (Inr p2')) \<in> set (doSince i (left I) p1 p2 p')"
                using form minp Inr p2r Inr True b'v p'b'
                unfolding doSince_def by auto
              ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                  since_sound[OF i_props p1_def p2_def p'_def _ bf bf'] form
                  pw_total[of i "Since phi I psi"] p'b' trans_wqo Inr b'v p2r
                unfolding proofApp_def
                apply (auto simp add: total_on_def)
                by (metis transpD)
            next
              case False
              from p'_def have p'_val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi)p'"
                unfolding optimal_def by auto
              from False have form: "minp = Inr (VSince i b1 [])
              \<or> minp = Inr (VSince i vphi' vpsis')" using Inr p'b' b'v minp
                val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doSince_def by (cases p2) (auto simp: min_list_wrt_def)
              then have res: "doSince i (left I) p1 p2 p' = [Inr (VSince i b1 []), Inr (VSince i vphi' vpsis')]"
                using False Inr p'b' b'v unfolding doSince_def by (cases p2; auto)
              then show ?thesis using qr bv q_val i_props
                unfolding optimal_def valid_def
                apply (auto simp add: Let_def False i_ltp_to_tau i_etp_to_tau split: if_splits)[1]
                subgoal premises prems
                proof -
                  have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince_never (i-1) li' ps))"
                    using valid_shift_VSince_never[of i I phi psi li' ps] i_props q_val False
                    by (auto simp: qr bv)
                  then have "wqo p' (Inr (VSince_never (i-1) li' ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VSince)
                  moreover have "checkIncr (Inr (VSince_never (i - 1) li' ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VSince_never)
                  ultimately have "wqo (Inr (VSince i vphi' vpsis')) q"
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince_never (i-1) li' ps)"]
                      valid_q_before i_props prems
                    unfolding p'b' b'v
                    by (auto simp add: proofIncr_def li'_def intro: checkIncr.intros)
                  moreover have comp_in: "(Inr (VSince i vphi' vpsis')) \<in> set (doSince i (left I) p1 p2 p')"
                    using Inr b'v p'b' res by auto
                  ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                      since_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                      pw_total[of i "Since phi I psi"] p'b' trans_wqo b'v prems res
                    apply (auto simp add: total_on_def)
                    by (metis transpD)
                qed
                using Inr 
                subgoal premises prems
                proof -
                  have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince_never (i-1) li ps))"
                    using prems val_ge_zero[OF p'b' b'v p'_val]
                    unfolding valid_def
                    by (auto simp add: le_diff_conv Let_def i_ltp_to_tau i_etp_to_tau split: enat.splits)
                  then have "wqo p' (Inr (VSince_never (i-1) li ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VSince)
                  moreover have "checkIncr (Inr (VSince_never (i - 1) li ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VSince_never)
                  ultimately have "wqo (Inr (VSince i vphi' vpsis')) q"
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince_never (i-1) li ps)"]
                      valid_q_before i_props prems
                    unfolding p'b' b'v
                    by (auto simp add: proofIncr_def li'_def intro: checkIncr.intros)
                  moreover have comp_in: "(Inr (VSince i vphi' vpsis')) \<in> set (doSince i (left I) p1 p2 p')"
                    using Inr b'v p'b' res by auto
                  ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                      since_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                      pw_total[of i "Since phi I psi"] p'b' trans_wqo b'v prems res
                    apply (auto simp add: total_on_def)
                    by (metis transpD)
                qed
                using p1_def False Inr q_val i_props vmin apply (auto simp: Let_def optimal_def valid_def i_ltp_to_tau i_etp_to_tau i_le_ltpi split: enat.splits)
                subgoal premises prems for n
                proof -
                  have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince_never (i-1) li' ps))"
                    using valid_shift_VSince_never[of i I phi psi li' ps] i_props q_val False
                    by (auto simp: qr bv)
                  then have "wqo p' (Inr (VSince_never (i-1) li' ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VSince)
                  moreover have "checkIncr (Inr (VSince_never (i - 1) li' ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VSince_never)
                  ultimately have "wqo (Inr (VSince i vphi' vpsis')) q"
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince_never (i-1) li' ps)"]
                      valid_q_before i_props prems
                    unfolding p'b' b'v
                    by (auto simp add: proofIncr_def li'_def intro: checkIncr.intros)
                  moreover have comp_in: "(Inr (VSince i vphi' vpsis')) \<in> set (doSince i (left I) p1 p2 p')"
                    using Inr b'v p'b' res by auto
                  ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                      since_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                      pw_total[of i "Since phi I psi"] p'b' trans_wqo b'v prems res
                    apply (auto simp add: total_on_def)
                    by (metis transpD)
                qed
                done
            qed
          qed
        }
        moreover
        {fix li'' vpsis'
          assume b'v: "b' = VSince_never (i-1) li'' vpsis'"
          have li''_def: "li'' = li"
            using p'_def
            by (auto simp: Inr b'v optimal_def valid_def li_def)
          have "wqo minp q"
            using b'v
          proof (cases p1)
            case (Inl a1)
            then show ?thesis
            proof (cases "left I = 0")
              case True
              then have form_min: "minp = p' \<oplus> p2" using Inl b'v p'b' minp
                  val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doSince_def by (cases p2) (auto simp: min_list_wrt_def)
              then obtain p2' where p2r: "p2 = Inr p2'"
                using True b'v Inl minp Inr val_VIO_imp_r[OF bf vmin VIO]
                  filter_nnil
                unfolding doSince_def
                apply (cases p2; auto simp: min_list_wrt_def split: if_splits)
                by (metis Inl_Inr_False)
              then show ?thesis
                using form_min qr bv Inl p1_def q_val unfolding optimal_def valid_def
                apply (cases ps rule: rev_cases)
                apply (auto simp add: Let_def True i_ltp_to_tau i_etp_to_tau split: if_splits enat.splits)[1]
                subgoal premises prems for ys y
                proof -
                  from vmin form_min p2r have p_val: "valid rho i (Since phi I psi) (p' \<oplus> (Inr p2'))"
                    by auto
                  have check_p: "checkApp p' (Inr p2')"
                    using p'_def True
                    unfolding p2r b'v p'b'
                    by (auto simp: optimal_def intro!: valid_checkApp_VSince_never)
                  from prems have y_val: "valid rho i psi (Inr y)"
                    using q_val True i_le_ltpi i_props unfolding valid_def
                    by (auto simp: Let_def min_def split: if_splits)
                  have val_q': "valid rho (i - 1) (Since phi (subtract (delta rho i (i - 1)) I) psi) (Inr (VSince_never (i - 1) li' ys))"
                    using valid_shift_VSince_never[of i I phi psi li' ps] i_props q_val True prems(8)
                    by (auto simp: qr bv)
                  then have q_val2: "valid rho i (Since phi I psi) ((Inr (VSince_never (i-1) li' ys)) \<oplus> (Inr y))"
                    using q_val prems i_props by (auto simp: li'_def)
                  have check_q: "checkApp (Inr (VSince_never (i-1) li' ys)) (Inr y)"
                    using val_q' True
                    by (auto intro!: valid_checkApp_VSince_never)
                  from p'_def have wqo_p': "wqo p' (Inr (VSince_never (i - 1) li' ys))"
                    using val_q' unfolding optimal_def by simp
                  moreover have wqo_p2: "wqo p2 (Inr y)" using i_props p2_def y_val
                    unfolding optimal_def by auto
                  ultimately show ?thesis
                    unfolding prems using p'b' b'v p2_def q_val prems p2r unfolding valid_def optimal_def
                    using proofApp_mono[OF check_p check_q wqo_p' wqo_p2[unfolded p2r] p_val q_val2]
                    apply (auto simp: li''_def li)
                    by (metis One_nat_def Suc_diff_1 bv i_props q_le qr)
                qed
                done
            next
              case False
              from p'_def have p'_val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) p'"
                unfolding optimal_def by auto
              from False have form: "minp = Inr (VSince_never i li vpsis')"
                using b'v Inl minp Inr filter_nnil unfolding doSince_def
                by (cases p2) (auto simp: min_list_wrt_def li''_def split: enat.splits)
              then show ?thesis using qr bv q_val i_props
                unfolding optimal_def valid_def
                apply (auto simp add: Let_def False i_ltp_to_tau i_etp_to_tau split: if_splits)[1]
                subgoal premises prems
                proof -
                  have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince_never (i-1) li' ps))"
                    using valid_shift_VSince_never[of i I phi psi li' ps] i_props q_val False
                    by (auto simp: qr bv)
                  then have "wqo p' (Inr (VSince_never (i-1) li' ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VSince_never)
                  moreover have "checkIncr (Inr (VSince_never (i - 1) li' ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VSince_never)
                  ultimately show ?thesis
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince_never (i-1) li' ps)"]
                      valid_q_before i_props prems
                    unfolding p'b' b'v
                    by (auto simp add: proofIncr_def li'_def li''_def intro: checkIncr.intros)
                qed
                subgoal premises prems
                proof -
                  have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince_never (i-1) li ps))"
                    using prems val_ge_zero_never[OF p'b' b'v p'_val] diff_cancel_middle[of "\<tau> rho i" "left I" "\<tau> rho (i-1)"]
                    unfolding valid_def
                    by (auto simp add: le_diff_conv Let_def i_ltp_to_tau i_etp_to_tau li'_def li''_def split: enat.splits)
                  then have "wqo p' (Inr (VSince_never (i-1) li ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VSince_never)
                  moreover have "checkIncr (Inr (VSince_never (i - 1) li ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VSince_never)
                  ultimately show ?thesis
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince_never (i-1) li ps)"]
                      valid_q_before i_props prems
                    unfolding p'b' b'v
                    by (auto simp add: proofIncr_def li'_def li''_def intro: checkIncr.intros)
                qed
                using p1_def False Inl q_val i_props vmin
                apply (auto simp: Let_def optimal_def valid_def i_ltp_to_tau i_etp_to_tau i_le_ltpi split: if_splits)
                using not_wqo vmin apply blast
                done
            qed
          next
            case (Inr b1)
            then show ?thesis
            proof (cases "left I = 0")
              case True
              then have form: "minp = Inr (VSince i b1 [projr p2]) \<or> minp = (p' \<oplus> p2)"
                using Inr p'b' b'v minp val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doSince_def by (cases p2) (auto simp: min_list_wrt_def)
              then obtain p2' where p2r: "p2 = Inr p2'"
                using p'b' b'v Inr True minp val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doSince_def
                by (cases p2; auto simp: min_list_wrt_def split: if_splits)
              then have res: "doSince i (left I) p1 p2 p' = [Inr (VSince i b1 [projr p2]), (p' \<oplus> p2)]"
                using True Inr p'b' b'v unfolding doSince_def by auto
              from True q_val qr bv have ps_not_nil: "ps \<noteq> []"
                unfolding valid_def
                apply (auto simp: Let_def i_etp_to_tau split: if_splits enat.splits)
                by (meson \<tau>_mono diff_le_self i_le_ltpi order_subst1)
              then obtain y and ys where snoc_q: "ps = ys @ [y]"
                using qr bv
                by (cases ps rule: rev_cases; auto)
              then have y_val: "valid rho i psi (Inr y)"
                using q_val qr bv True unfolding valid_def
                by (auto simp: Let_def min_def i_le_ltpi split: if_splits)
              then have wqo_p2: "wqo (Inr p2') (Inr y)" using p2r p2_def
                unfolding optimal_def by auto
              then have q'_val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince_never (i-1) li ys))"
                using q_val snoc_q True qr bv etpi_imp_etp_suci i_props
                unfolding valid_def
                by (auto simp: Let_def min_def i_ltp_to_tau li'_def li''_def split: if_splits enat.splits)
              then have wqo_p': "wqo p' (Inr (VSince_never (i-1) li ys))"
                using p'_def unfolding optimal_def by auto
              have check_q: "checkApp (Inr (VSince_never (i-1) li ys)) (Inr y)"
                using q'_val True
                by (auto intro!: valid_checkApp_VSince_never)
              have check_min: "checkApp p' (Inr p2')" using p2r p'b' b'v
                using p'_def True
                unfolding p2r b'v p'b'
                by (auto simp: optimal_def intro!: valid_checkApp_VSince_never)
              from res have val_min: "valid rho i (Since phi I psi) (p' \<oplus> (Inr p2'))"
                using b'v p'b' p2r
                  since_sound[OF i_props p1_def p2_def p'_def _ bf bf']
                by auto
              from q_val have q_val2: "valid rho i (Since phi I psi) ((Inr (VSince_never (i-1) li ys)) \<oplus> (Inr y))"
                using qr bv snoc_q i_props unfolding proofApp_def by (auto simp: li li'_def)
              then have "wqo (p' \<oplus> (Inr p2')) q"
                using qr bv snoc_q p'b' b'v i_props
                  proofApp_mono[OF check_min check_q wqo_p' wqo_p2 val_min q_val2]
                by (auto simp: li'_def)
              moreover have "(p' \<oplus> (Inr p2')) \<in> set (doSince i (left I) p1 p2 p')"
                using form minp Inr p2r Inr True b'v p'b'
                unfolding doSince_def by auto
              ultimately show ?thesis using minp min_list_wrt_le[OF _ refl_wqo]
                  since_sound[OF i_props p1_def p2_def p'_def _ bf bf'] form
                  pw_total[of i "Since phi I psi"] p'b' trans_wqo Inr b'v p2r
                unfolding proofApp_def
                apply (auto simp add: total_on_def)
                by (metis transpD)
            next
              case False
              then have lI: "left I \<noteq> 0" by auto
              then have form: "minp = Inr (VSince i b1 [])
                \<or> minp = Inr (VSince_never i li vpsis')" using Inr p'b' b'v minp
                val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doSince_def by (cases p2) (auto simp: min_list_wrt_def li''_def split: enat.splits)
              from p1_def Inr have b1i: "v_at b1 = i"
                unfolding optimal_def valid_def by auto
              from p'_def have p'_val: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) p'"
                unfolding optimal_def by auto
              from False Inr p'b' b'v have
                res: "doSince i (left I) p1 p2 p' = [Inr (VSince i b1 []), Inr (VSince_never i li vpsis')]"
                unfolding doSince_def by (cases p2; auto simp: li''_def)
              then show ?thesis using qr bv q_val i_props
                unfolding optimal_def valid_def
                apply (auto simp add: Let_def False i_ltp_to_tau i_etp_to_tau split: if_splits enat.splits)[1]
                subgoal premises prems
                proof -
                  have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince_never (i-1) li' ps))"
                    using valid_shift_VSince_never[of i I phi psi li' ps] i_props q_val False prems(8)
                    by (auto simp: qr bv)
                  then have "wqo p' (Inr (VSince_never (i-1) li' ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VSince_never)
                  moreover have "checkIncr (Inr (VSince_never (i - 1) li' ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VSince_never)
                  ultimately have "wqo (Inr (VSince_never i li' vpsis')) q"
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince_never (i-1) li' ps)"]
                      valid_q_before i_props prems
                    unfolding p'b' b'v
                    by (auto simp add: proofIncr_def simp: li'_def li''_def intro: checkIncr.intros)
                  moreover have comp_in: "(Inr (VSince_never i li' vpsis')) \<in> set (doSince i (left I) p1 p2 p')"
                    using Inr b'v p'b' res by (auto simp: li'_def)
                  ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                      since_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                      pw_total[of i "Since phi I psi"] p'b' trans_wqo b'v prems res
                    apply (auto simp add: total_on_def li'_def li''_def)
                    by (metis transpD)
                qed
                subgoal premises prems
                proof -
                  have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince_never (i-1) li' ps))"
                    using valid_shift_VSince_never[of i I phi psi li' ps] i_props q_val False prems(8)
                    by (auto simp: qr bv)
                  then have "wqo p' (Inr (VSince_never (i-1) li' ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VSince_never)
                  moreover have "checkIncr (Inr (VSince_never (i - 1) li' ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VSince_never)
                  ultimately have "wqo (Inr (VSince_never i li' vpsis')) q"
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince_never (i-1) li' ps)"]
                      valid_q_before i_props prems
                    unfolding p'b' b'v
                    by (auto simp add: proofIncr_def li_def li''_def intro: checkIncr.intros)
                  moreover have comp_in: "(Inr (VSince_never i li' vpsis')) \<in> set (doSince i (left I) p1 p2 p')"
                    using Inr b'v p'b' res by (auto simp: li'_def)
                  ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                      since_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                      pw_total[of i "Since phi I psi"] p'b' trans_wqo b'v prems res
                    apply (auto simp add: total_on_def)
                    by (metis transpD)
                qed
                using p1_def False Inr q_val i_props vmin apply (auto simp: Let_def optimal_def valid_def i_ltp_to_tau i_etp_to_tau i_le_ltpi split: enat.splits)
                subgoal premises prems for n
                proof -
                  have valid_q_before: "valid rho (i-1) (Since phi (subtract (\<Delta> rho i) I) psi) (Inr (VSince_never (i-1) li' ps))"
                    using valid_shift_VSince_never[of i I phi psi li' ps] i_props q_val False prems(8)
                    by (auto simp: qr bv)
                  then have "wqo p' (Inr (VSince_never (i-1) li' ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VSince_never)
                  moreover have "checkIncr (Inr (VSince_never (i - 1) li' ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VSince_never)
                  ultimately have "wqo (Inr (VSince_never i li' vpsis')) q"
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VSince_never (i-1) li' ps)"]
                      valid_q_before i_props prems
                    unfolding p'b' b'v
                    by (auto simp add: proofIncr_def li'_def li''_def intro: checkIncr.intros)
                  moreover have comp_in: "(Inr (VSince_never i li' vpsis')) \<in> set (doSince i (left I) p1 p2 p')"
                    using Inr b'v p'b' res by (auto simp: li'_def)
                  ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                      since_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                      pw_total[of i "Since phi I psi"] p'b' trans_wqo b'v prems res
                    apply (auto simp add: total_on_def)
                    by (metis transpD)
                qed
                done
            qed
          qed
        }
        ultimately show ?thesis by auto
      qed
    }
    ultimately show ?thesis by auto
  qed
  then show False using q_le by auto
qed

lemma valid_checkApp_VUntil: "valid rho j (Until phi I psi) (Inr (VUntil j vpsis' vphi')) \<Longrightarrow>
  left I = 0 \<or> ETP rho (\<tau> rho j + left I) \<le> v_at vphi' \<Longrightarrow> checkApp (Inr (VUntil j vpsis' vphi')) (Inr p2')"
  apply (auto simp: valid_def Let_def split: if_splits enat.splits intro!: checkApp.intros)
  using i_ge_etpi order_trans apply blast+
  done

lemma valid_checkApp_VUntil_never: "valid rho j (Until phi I psi) (Inr (VUntil_never j hi vpsis')) \<Longrightarrow>
  left I = 0 \<or> (case right I of \<infinity> \<Rightarrow> True | enat n \<Rightarrow> ETP rho (\<tau> rho j + left I) \<le> LTP rho (\<tau> rho j + n)) \<Longrightarrow>
  checkApp (Inr (VUntil_never j hi vpsis')) (Inr p2')"
  apply (auto simp: valid_def Let_def split: if_splits enat.splits intro!: checkApp.intros)
  using i_le_ltpi_add apply blast
  apply (meson i_ge_etpi i_le_ltpi_add le_trans)
  using i_le_ltpi_add by blast

lemma valid_checkIncr_VUntil: "valid rho j phi (Inr (VUntil j vpsis' vphi')) \<Longrightarrow>
  checkIncr (Inr (VUntil j vpsis' vphi' ))"
  apply (cases phi)
  apply (auto simp: valid_def Let_def split: if_splits enat.splits dest!: arg_cong[where ?x="map _ _" and ?f=set] intro!: checkIncr.intros)
  apply (drule imageI[where ?A="set vpsis'" and ?f=v_at])
  apply auto[1]
  apply (drule imageI[where ?A="set vpsis'" and ?f=v_at])
  apply auto[1]
  done

lemma valid_checkIncr_VUntil_never: "valid rho j phi (Inr (VUntil_never j hi vpsis')) \<Longrightarrow>
  checkIncr (Inr (VUntil_never j hi vpsis'))"
  apply (cases phi)
  apply (auto simp: valid_def Let_def split: if_splits enat.splits dest!: arg_cong[where ?x="map _ _" and ?f=set] intro!: checkIncr.intros)
  apply (drule imageI[where ?A="set vpsis'" and ?f=v_at])
  apply auto[1]
  done

lemma until_sound:
  assumes i_props: "right I \<ge> enat (\<Delta> rho (i+1))" and
    p1_def: "optimal i phi p1" and p2_def: "optimal i psi p2" and
    p'_def: "optimal (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
    and p_def: "p \<in> set (doUntil i (left I) p1 p2 p')"
    and bf: "bounded_future (Until phi I psi)"
    and bf': "bounded_future (Until phi (subtract (\<Delta> rho (i+1)) I) psi)"
  shows "valid rho i (Until phi I psi) p"
proof (cases p')
  case (Inl a)
  then have p'l: "p' = Inl a" by auto
  then have satp': "sat rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi)"
    using soundness[of _ _ "Until phi (subtract (\<Delta> rho (i+1)) I) psi"] p'_def check_sound(1)[of rho "Until phi (subtract (\<Delta> rho (i+1)) I) psi" a]
    unfolding optimal_def valid_def by auto
  then obtain q qs where a_def: "a = SUntil qs q" using Inl p'_def
    unfolding optimal_def valid_def by (cases a) auto
  then have a_val: "s_check rho (Until phi (subtract (\<Delta> rho (i+1)) I) psi) a"
    using Inl p'_def unfolding optimal_def valid_def by (auto simp: Let_def)
  then have mem: "mem (delta rho (s_at q) (i+1)) (subtract (\<Delta> rho (i+1)) I)"
    using a_def Inl p'_def s_check.simps unfolding optimal_def valid_def
    by (auto simp: Let_def)
  then have "left I - \<Delta> rho (i+1) \<le> delta rho (s_at q) (i+1) " by auto
  then have tmp: "left I \<le> \<tau> rho (i+1) - \<tau> rho i + (\<tau> rho (s_at q) - \<tau> rho (i+1))"
    by auto
  from a_val have qi: "i + 1\<le> s_at q" using a_def p'l p'_def
    unfolding optimal_def valid_def
    by (auto simp: Let_def)
  then have liq: "left I \<le> delta rho (s_at q) i" using diff_add_assoc tmp
    by auto
  from bf obtain n where n_def: "right I = enat n" by auto
  from mem n_def have "enat (delta rho (s_at q) (i+1))  \<le> enat n - enat (\<Delta> rho (i+1))"
    by auto
  then have "delta rho (s_at q) (i+1) + \<Delta> rho (i+1) \<le> n"
    apply auto
    by (metis Suc_eq_plus1 diff_add_inverse2 enat_ord_simps(1) i_props le_diff_conv le_diff_conv2 n_def)
  then have riq: "enat (delta rho (s_at q) i) \<le> right I" using n_def by auto
  then show ?thesis
  proof (cases "left I = 0")
    case True
    then show ?thesis
    proof (cases p1)
      case (Inl a1)
      then have p1l: "p1 = Inl a1" by auto
      then show ?thesis
      proof (cases p2)
        case (Inl a2)
        then have por: "p = p' \<oplus> p1 \<or> p = Inl (SUntil [] a2)"
          using a_def p'l p1l True p_def unfolding doUntil_def by auto
        moreover
        {
          assume pplus: "p = p' \<oplus> p1"
          then have "p = Inl (SUntil (a1 # qs) q)" using a_def p'l p1l
              p'_def p1_def unfolding proofApp_def by auto
          then have "valid rho i (Until phi I psi) p"
            using a_def True p'_def p1_def p'l p1l i_props liq riq
            unfolding optimal_def valid_def
            by (auto simp: upt_rec Let_def split: list.splits)
        }
        ultimately show ?thesis
          using Inl p1l True assms unfolding optimal_def valid_def
          by auto
      next
        case (Inr b2)
        then have pplus: "p = p' \<oplus> p1" using p1l p_def True p'l a_def
          unfolding doUntil_def by auto
        then have "p = Inl (SUntil (a1 # qs) q)" using a_def p'l p1l
            p'_def p1_def unfolding proofApp_def by auto
        then show ?thesis
          using a_def True p'_def p1_def p'l p1l i_props liq riq
          unfolding optimal_def valid_def
          by (auto simp: upt_rec Let_def split: list.splits)
      qed
    next
      case (Inr b1)
      then have p1r: "p1 = Inr b1" by auto
      then show ?thesis
      proof (cases p2)
        case (Inl a2)
        then have "p = Inl (SUntil [] a2)" using p_def Inr True p'l a_def
          unfolding doUntil_def by auto
        then show ?thesis using p2_def True Inl Inr p'l i_props zero_enat_def
          unfolding optimal_def valid_def by auto
      next
        case (Inr b2)
        then have "p = Inr (VUntil i [b2] b1)" using p1r True p'l p_def a_def
          unfolding doUntil_def by auto
        then show ?thesis using i_props p1_def p2_def True p1r Inr bf
          unfolding optimal_def valid_def
          apply (auto simp: upt_rec split: enat.splits)
          using i_le_ltpi_add apply blast
          using i_ge_etpi less_Suc_eq_le by blast
      qed
    qed
  next
    case False
    then show ?thesis
    proof (cases p1)
      case (Inl a1)
      then have pplus: "p = p' \<oplus> p1" using p_def False p'l a_def
        unfolding doUntil_def by (cases p2) auto
      then have pl: "p = Inl (SUntil (a1 # qs) q)" using a_def p'l Inl
        unfolding proofApp_def by auto
      then show ?thesis
        using False p1_def p'_def Inl i_props liq riq a_def p'l
        unfolding optimal_def valid_def
        by (auto simp: Cons_eq_upt_conv Let_def split: list.splits if_splits)
    next
      case (Inr b1)
      then have "p = Inr (VUntil i [] b1)" using Inr False p'l p_def a_def
        unfolding doUntil_def by (cases p2) auto
      then show ?thesis using p1_def i_props Inr False bf n_def i_le_ltpi_add
        unfolding optimal_def valid_def
        by (auto simp add: i_etp_to_tau Let_def False i_ltp_to_tau le_diff_conv2
            split: enat.splits)
    qed
  qed
next
  case (Inr b)
  then have p'r: "p' = Inr b" by auto
  from bf obtain n where n_def: "right I = enat n" by auto
  then show ?thesis
  proof (cases b)
    case (VFF n)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VAtm x11 x12)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VNeg x2)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VDisj x31 x32)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VConjL x31)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VConjR x32)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VImpl x71 x72)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VIff_sv x71 x72)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VIff_vs x71 x72)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VSince x51 x52 x53)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VSince_never x71 x72)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VSince_le x8)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VNext x9)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VNext_ge x10)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VNext_le x11a)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VPrev x12a)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VPrev_ge x13)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VPrev_le x14)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case VPrev_zero
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VUntil j qs q)
    then have j_def: "j = i+1" using p'r p'_def unfolding optimal_def valid_def
      by auto
    then show ?thesis
    proof (cases "left I = 0")
      case True
      then show ?thesis
      proof (cases p2)
        case (Inl a2)
        then have "p = Inl (SUntil [] a2)" using p_def p'r VUntil True
          unfolding doUntil_def by (cases p1) auto
        then show ?thesis using Inl p2_def True i_props zero_enat_def
          unfolding optimal_def valid_def by auto
      next
        case (Inr b2)
        then have p2r: "p2 = Inr b2" by auto
        {
          from i_ge_etpi have b2_ge: "v_at b2 \<ge> ETP rho (\<tau> rho (v_at b2))"
            using p2r p2_def
            unfolding optimal_def valid_def by auto
          then have nl_def: "v_at q \<ge> v_at b2 + 1" using VUntil p'r p'_def p2_def p2r
            unfolding optimal_def valid_def by (auto simp: Let_def)
          define l where l_def: "l \<equiv> [max (v_at b2+1) (ETP rho (\<tau> rho (v_at b2+1))) ..< v_at q]"
          then have l2_def: "l = [v_at b2+1..< v_at q ]" using i_ge_etpi[of rho "v_at b2 + 1"]
            by (auto simp add: max_def)
          then have b2_cons: "(max (v_at b2) (ETP rho (\<tau> rho (v_at b2)))) # l = v_at b2 # l"
            by (auto simp add: antisym b2_ge max_def)
          then have "v_at b2 # l = [max (v_at b2) (ETP rho (\<tau> rho (v_at b2))) ..< v_at q]"
            using nl_def l_def b2_ge
            apply (auto simp add: antisym b2_cons upt_eq_Cons_conv i_ge_etpi max_def)
            apply (metis antisym i_ge_etpi less_eq_Suc_le upt_conv_Cons)
            apply (metis Suc_le_eq l2_def upt_eq_Cons_conv)
            using b2_ge upt_conv_Cons by auto
        } note * = this
        then show ?thesis
        proof (cases p1)
          case (Inl a1)
          from Inl have "p = p' \<oplus> p2" using p2r VUntil p'r p_def True
            unfolding doUntil_def by auto
          then have "p = Inr (VUntil i (b2 # qs) q)" using VUntil p'r
              p2_def p2r i_props unfolding optimal_def valid_def proofApp_def j_def
            by auto
          then show ?thesis using p'_def p2_def i_props True Inl p2r VUntil p'r bf'
              j_def n_def *
            unfolding optimal_def valid_def
            apply (auto simp: add.commute Let_def i_ge_etpi)
            done
        next
          case (Inr b1)
          then have "p = Inr (VUntil i [b2] b1) \<or> p = p' \<oplus> p2"
            using p2r p'r VUntil True p_def unfolding doUntil_def by auto
          moreover
          {
            assume pplus: "p = p' \<oplus> p2"
            then have "p = Inr (VUntil i (b2 # qs) q)" using VUntil p'r
                p2_def p2r i_props unfolding optimal_def valid_def proofApp_def j_def
              by auto
            then have "valid rho i (Until phi I psi) p" using p'_def p2_def i_props True Inr p2r VUntil p'r bf'
                j_def n_def *
              unfolding optimal_def valid_def
              apply (auto simp: add.commute Let_def i_ge_etpi)
              done
          }
          moreover
          {
            assume p: "p = Inr (VUntil i [b2] b1)"
            then have "valid rho i (Until phi I psi) p"
              using p1_def p2_def Inr p2r bf True i_ge_etpi i_props n_def
              unfolding optimal_def valid_def
              by (auto simp add: i_le_ltpi_add split: enat.splits)
          }
          ultimately show ?thesis by auto
        qed
      qed
    next
      case False
      then show ?thesis
      proof (cases p1)
        case (Inl a1)
        from Inl have formp: "p = Inr (VUntil i qs q)" using VUntil p'r False p_def
          unfolding doUntil_def by (cases p2) auto
        from p'_def have v_at_qs: "map v_at qs = [lu rho (i + 1) (subtract (\<Delta> rho (i+1)) I) ..< Suc (v_at q)]"
          unfolding optimal_def valid_def VUntil p'r
          by (auto simp: Let_def)
        have l_subtract: "lu rho (i + 1) (subtract (\<Delta> rho (i+1)) I) = lu rho i I"
          using False i_props
          apply (auto simp: max_def)
          subgoal
            apply (rule antisym)
            subgoal apply (subst i_etp_to_tau)
              apply  (auto simp: gr0_conv_Suc not_le)
              by (smt add.commute add_0_right diff_is_0_eq' etp_ge i_etp_to_tau le_add_diff_inverse nat_le_linear nat_less_le not_less_eq_eq plus_1_eq_Suc)
            subgoal
              apply (auto simp: gr0_conv_Suc)
              by (metis add.commute diff_is_0_eq' i_etp_to_tau le_add_diff_inverse nat_le_linear)
            done
          subgoal
            using etp_to_delta nat_le_linear by fastforce
          subgoal
            by (simp add: i_etp_to_tau not_less_eq_eq)
          using etp_to_delta nat_le_linear by fastforce
        from p'_def have vq: "v_check rho phi q \<and> (\<forall>q \<in> set qs. v_check rho psi q)"
          unfolding optimal_def valid_def VUntil p'r
          by (auto simp: Let_def)
        from p'_def i_props have "i \<le> v_at q" using VUntil p'r
          unfolding optimal_def valid_def
          by (auto simp: Let_def)
        then show ?thesis using False i_props VUntil p'r bf' formp vq n_def
            v_at_qs[unfolded l_subtract] p'_def
          unfolding optimal_def valid_def
          by (auto simp: add.commute Let_def)
      next
        case (Inr b1)
        then have "p = Inr (VUntil i [] b1) \<or> p = Inr (VUntil i qs q)"
          using False p_def p'r VUntil unfolding doUntil_def
          by (cases p2) auto
        moreover
        {
          assume formp: "p = Inr (VUntil i [] b1)"
          then have "valid rho i (Until phi I psi) p"
            using False Inr p1_def i_props bf
            unfolding optimal_def valid_def
            apply (auto simp add: i_etp_to_tau)
            using i_le_ltpi_add by blast
        }
        moreover
        {
          assume formp: "p = Inr (VUntil i qs q)"
          from p'_def have v_at_qs: "map v_at qs = [lu rho (i+1) (subtract (\<Delta> rho (i+1)) I)..< Suc (v_at q)]"
            unfolding optimal_def valid_def VUntil p'r
            by (auto simp: Let_def)
          have l_subtract: "lu rho (i + 1) (subtract (\<Delta> rho (i+1)) I) = lu rho i I"
            using False i_props
            apply (auto simp: max_def)
            subgoal
              apply (rule antisym)
              subgoal apply (subst i_etp_to_tau)
                apply  (auto simp: gr0_conv_Suc not_le)
                by (smt add.commute add_0_right diff_is_0_eq' etp_ge i_etp_to_tau le_add_diff_inverse nat_le_linear nat_less_le not_less_eq_eq plus_1_eq_Suc)
              subgoal
                apply (auto simp: gr0_conv_Suc)
                by (metis add.commute diff_is_0_eq' i_etp_to_tau le_add_diff_inverse nat_le_linear)
              done
            subgoal
              using etp_to_delta nat_le_linear by fastforce
            subgoal
              by (simp add: i_etp_to_tau not_less_eq_eq)
            using etp_to_delta nat_le_linear by fastforce
          from p'_def have vq: "v_check rho phi q \<and> (\<forall>q \<in> set qs. v_check rho psi q)"
            unfolding optimal_def valid_def VUntil p'r
            by (auto simp: Let_def)
          from p'_def i_props have "i \<le> v_at q" using VUntil p'r
            unfolding optimal_def valid_def
            by (auto simp: Let_def)
          then have "valid rho i (Until phi I psi) p" using False i_props VUntil p'r
              bf' formp vq v_at_qs[unfolded l_subtract] p'_def n_def
            unfolding optimal_def valid_def
            by (auto simp: Let_def add.commute)
        }
        ultimately show ?thesis by auto
      qed
    qed
  next
    case (VUntil_never j hi qs)
    have hi_def: "hi = LTP rho (n + \<tau> rho i)"
      using p'_def
      apply (auto simp: Inr VUntil_never optimal_def valid_def n_def)
      by (smt (z3) Groups.ab_semigroup_add_class.add.commute diff_add_inverse2 enat_ord_simps(1) i_props le_add2 le_add_diff_inverse2 le_diff_conv2 le_trans n_def nat_le_linear plus_1_eq_Suc)
    have j_def: "j = i+1" using p'r p'_def unfolding optimal_def valid_def VUntil_never
      by auto
    then show ?thesis
    proof (cases "left I = 0")
      case True
      from bf obtain n where n_def: "right I = enat n" by auto
      then show ?thesis
      proof (cases p2)
        case (Inl a2)
        then have "p = Inl (SUntil [] a2)"
          using p'r VUntil_never True p_def unfolding doUntil_def
          by (cases p1) auto
        then show ?thesis using p2_def i_props Inl True zero_enat_def
          unfolding optimal_def valid_def by auto
      next
        case (Inr b2)
        then have p2r: "p2 = Inr b2" by auto
        {
          from i_ge_etpi have b2_ge: "v_at b2 \<ge> ETP rho (\<tau> rho (v_at b2))"
            using p2r p2_def
            unfolding optimal_def valid_def by auto
          then have nl_def: "LTP rho (\<tau> rho i + n) \<ge> v_at b2 + 1"
            using n_def VUntil_never p'r p'_def p2_def p2r
            unfolding optimal_def valid_def apply (auto simp: Let_def)
            by (metis diff_add_inverse diff_add_inverse2 enat_ord_simps(1) i_etp_to_tau i_le_ltpi_add i_props le_SucI le_add1 le_diff_iff le_imp_diff_is_add plus_1_eq_Suc)
          define l where l_def: "l \<equiv> [max (v_at b2+1) (ETP rho (\<tau> rho (v_at b2+1))) ..< LTP rho (\<tau> rho i + n)]"
          then have l2_def: "l = [v_at b2+1..< LTP rho (\<tau> rho i + n)]" using i_ge_etpi[of rho "v_at b2 + 1"]
            by (auto simp add: max_def)
          then have b2_cons: "(max (v_at b2) (ETP rho (\<tau> rho (v_at b2)))) # l = v_at b2 # l"
            by (auto simp add: antisym b2_ge max_def)
          then have "v_at b2 # l = [max (v_at b2) (ETP rho (\<tau> rho (v_at b2))) ..< LTP rho (\<tau> rho i + n)]"
            using nl_def l_def b2_ge
            apply (auto simp add: antisym b2_cons upt_eq_Cons_conv i_ge_etpi max_def)
            apply (metis antisym i_ge_etpi less_eq_Suc_le upt_conv_Cons)
            apply (metis Suc_le_eq l2_def upt_eq_Cons_conv)
            using b2_ge upt_conv_Cons by auto
        } note * = this
        then show ?thesis
        proof (cases p1)
          case (Inl a1)
          then have "p = p' \<oplus> p2" using p2r p'r VUntil_never True p_def
            unfolding doUntil_def by auto
          then have "p = Inr (VUntil_never i hi (b2 # qs))"
            using VUntil_never p'r p2_def p2r i_props
            unfolding optimal_def valid_def proofApp_def j_def
            by auto
          then show ?thesis using * n_def p'_def p2_def p2r p'r VUntil_never
              True i_props i_ge_etpi i_le_ltpi_add
            unfolding optimal_def valid_def
            apply (auto simp: Let_def add.commute split: if_splits)
            apply (smt Suc_leD i_ge_etpi le_trans)
            apply (smt Cons_eq_upt_conv Suc_le_mono i_ge_etpi le_SucE le_trans upt_conv_Nil)
            apply (smt Suc_le_mono i_ge_etpi le_SucE le_antisym le_trans)
            using max.orderE apply blast
            using le_trans by blast
        next
          case (Inr b1)
          then have "p = Inr (VUntil i [b2] b1) \<or> p = p' \<oplus> p2"
            using p2r True p'r VUntil_never p_def unfolding doUntil_def
            by auto
          moreover
          {
            assume "p = p' \<oplus> p2"
            then have "p = Inr (VUntil_never i hi (b2 # qs))"
              using VUntil_never p'r p2_def p2r i_props
              unfolding optimal_def valid_def proofApp_def j_def
              by auto
            then have "valid rho i (Until phi I psi) p" using * n_def p'_def p2_def p2r p'r VUntil_never
                True i_props i_ge_etpi i_le_ltpi_add
              unfolding optimal_def valid_def
              apply (auto simp: Let_def add.commute split: if_splits)
              apply (smt Suc_leD i_ge_etpi le_trans)
              apply (smt Cons_eq_upt_conv Suc_le_mono i_ge_etpi le_SucE le_trans upt_conv_Nil)
              apply (smt Suc_le_mono i_ge_etpi le_SucE le_antisym le_trans)
              using max.orderE apply blast
              using le_trans by blast
          }
          moreover
          {
            assume "p = Inr (VUntil i [b2] b1)"
            then have "valid rho i (Until phi I psi) p"
              using Inr p2r p1_def p2_def True i_props n_def
              unfolding optimal_def valid_def
              apply (auto simp add: i_etp_to_tau)
              using i_le_ltpi_add by blast
          }
          ultimately show ?thesis by auto
        qed
      qed
    next
      case False
      then show ?thesis
      proof (cases p1)
        case (Inl a1)
        then have formp: "p = Inr (VUntil_never i hi qs)"
          using False p_def p'r VUntil_never
          unfolding doUntil_def by (cases p2) auto
        from p'_def have v_at_qs: "map v_at qs = [lu rho (i+1) (subtract (\<Delta> rho (i+1)) I)..< Suc (LTP rho (\<tau> rho (i+1) + (n - \<Delta> rho (i+1))))]"
          using VUntil_never p'r n_def unfolding optimal_def valid_def
          by (auto simp: Let_def)
        have l_subtract: "lu rho (i + 1) (subtract (\<Delta> rho (i+1)) I) = lu rho i I"
          using False i_props
          apply (auto simp: max_def)
          subgoal
            apply (rule antisym)
            subgoal apply (subst i_etp_to_tau)
              apply  (auto simp: gr0_conv_Suc not_le)
              by (smt add.commute add_0_right diff_is_0_eq' etp_ge i_etp_to_tau le_add_diff_inverse nat_le_linear nat_less_le not_less_eq_eq plus_1_eq_Suc)
            subgoal
              apply (auto simp: gr0_conv_Suc)
              by (metis add.commute diff_is_0_eq' i_etp_to_tau le_add_diff_inverse nat_le_linear)
            done
          subgoal
            using etp_to_delta nat_le_linear by fastforce
          subgoal
            by (simp add: i_etp_to_tau not_less_eq_eq)
          using etp_to_delta nat_le_linear by fastforce
        from p'_def have vq: "(\<forall>q \<in> set qs. v_check rho psi q)"
          unfolding optimal_def valid_def VUntil_never p'r
          by (auto simp: Let_def split: enat.splits)
        from p'_def i_props have "i \<le> LTP rho (\<tau> rho (i+1) + (n - \<Delta> rho (i+1)))"
          using VUntil_never p'r n_def i_le_ltpi_add[of i rho n]
          unfolding optimal_def valid_def
          by (auto simp: Let_def add.commute)
        then show ?thesis using False i_props VUntil p'r
            bf' formp vq v_at_qs[unfolded l_subtract] p'_def n_def
          unfolding optimal_def valid_def
          by (auto simp: Let_def add.commute hi_def)
      next
        case (Inr b1)
        then have "p = Inr (VUntil i [] b1) \<or> p = Inr (VUntil_never i hi qs)"
          using p'r VUntil_never False p_def unfolding doUntil_def
          by (cases p2) auto
        moreover
        {
          assume formp: "p = Inr (VUntil_never i hi qs)"
          from p'_def have v_at_qs: "map v_at qs = [lu rho (i+1) (subtract (\<Delta> rho (i+1)) I)..< Suc (LTP rho (\<tau> rho (i+1) + (n - \<Delta> rho (i+1))))]"
            using VUntil_never p'r n_def unfolding optimal_def valid_def
            by (auto simp: Let_def)
          have l_subtract: "lu rho (i + 1) (subtract (\<Delta> rho (i+1)) I) = lu rho i I"
            using False i_props
            apply (auto simp: max_def)
            subgoal
              apply (rule antisym)
              subgoal apply (subst i_etp_to_tau)
                apply  (auto simp: gr0_conv_Suc not_le)
                by (smt add.commute add_0_right diff_is_0_eq' etp_ge i_etp_to_tau le_add_diff_inverse nat_le_linear nat_less_le not_less_eq_eq plus_1_eq_Suc)
              subgoal
                apply (auto simp: gr0_conv_Suc)
                by (metis add.commute diff_is_0_eq' i_etp_to_tau le_add_diff_inverse nat_le_linear)
              done
            subgoal
              using etp_to_delta nat_le_linear by fastforce
            subgoal
              by (simp add: i_etp_to_tau not_less_eq_eq)
            using etp_to_delta nat_le_linear by fastforce
          from p'_def have vq: "(\<forall>q \<in> set qs. v_check rho psi q)"
            unfolding optimal_def valid_def VUntil_never p'r
            by (auto simp: Let_def split: enat.splits)
          from p'_def i_props have "i \<le> LTP rho (\<tau> rho (i+1) + (n - \<Delta> rho (i+1)))"
            using VUntil_never p'r n_def i_le_ltpi_add[of i rho n]
            unfolding optimal_def valid_def
            by (auto simp: Let_def add.commute)
          then have "valid rho i (Until phi I psi) p"
            using False i_props VUntil p'r bf' formp vq
              v_at_qs[unfolded l_subtract] p'_def n_def
            unfolding optimal_def valid_def
            by (auto simp: Let_def add.commute hi_def)
        }
        moreover
        {
          assume formp: "p = Inr (VUntil i [] b1)"
          then have "valid rho i (Until phi I psi) p"
            using p1_def i_props Inr n_def False i_le_ltpi_add[of "v_at b1" rho n]
            unfolding optimal_def valid_def
            by (auto simp add: i_etp_to_tau add.commute)
        }
        ultimately show ?thesis by auto
      qed
    qed
      (*
  next
    case (VMatchP x12a)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VMatchF x13)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
  next
    case (VMatchP_le x14)
    then show ?thesis using p'r p'_def unfolding optimal_def valid_def by auto
*)
  qed
qed

lemma sval_to_sval'_u:
  assumes val: "valid rho i (Until phi I psi) (Inl (SUntil (y # ys) spsi))" and
    i_props: "enat (\<Delta> rho (i+1)) \<le> right I"
    and rI: "right I = enat n"
  shows "valid rho (i + 1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi)
     (Inl (SUntil ys spsi))"
proof -
  from val have spsi_i: "s_at spsi \<ge> s_at y" unfolding valid_def
    by (auto simp: Let_def)
  from val have y_i: "s_at y = i" unfolding valid_def
    by (auto simp: Let_def)
  then have map_ys: "map s_at ys = [Suc i ..< s_at spsi]" using val
    unfolding valid_def by (auto simp: Let_def Cons_eq_upt_conv split: if_splits)
  from val have "left I - (\<Delta> rho (i+1)) \<le> \<tau> rho (s_at spsi) - \<tau> rho (i+1)"
    unfolding valid_def
    apply (auto simp: Let_def split: if_splits)
    subgoal premises prems
    proof -
      from y_i prems(1-2) spsi_i have "left I + \<tau> rho i \<le> \<tau> rho (s_at spsi)"
        by (auto simp add: le_diff_conv2)
      then show ?thesis using y_i by auto
    qed
    done
  moreover have "\<tau> rho (s_at spsi) - \<tau> rho (i+1) \<le> n - (\<Delta> rho (i+1))"
    using val rI unfolding valid_def
    by (auto simp: Let_def split: if_splits)
  ultimately have mem': "mem (delta rho (s_at spsi) (i+1)) (subtract (\<Delta> rho (i+1)) I)"
    using rI by auto
  then show ?thesis
  proof (cases ys)
    case Nil
    then show ?thesis using assms y_i map_ys unfolding valid_def
      apply (auto simp add: Let_def le_diff_conv2 split: if_splits)
      prefer 2
      apply (metis le_Suc_eq neq_Nil_conv upt_eq_Nil_conv)
      by (metis le_Suc_eq not_Cons_self2 upt_eq_Nil_conv)
  next
    case (Cons a as)
    then have "s_at a = i + 1" using map_ys
      by (auto simp add: Cons_eq_upt_conv)
    then show ?thesis using mem' Cons assms y_i map_ys unfolding valid_def
      apply (auto simp: Let_def)
      by (meson Cons_eq_upt_conv nat_less_le)
  qed
qed

lemma mem_imp_le_ltp_u:
  assumes mem: "mem (delta rho j (Suc i)) (subtract (\<Delta> rho (Suc i)) I)" and
    j_ge: "j \<ge> Suc i" and rI: "right I = enat n" and i_props: "\<Delta> rho (Suc i) \<le> n"
  shows "j \<le> LTP rho (\<tau> rho i + n)"
  using assms apply (auto simp add: add.commute i_le_ltpi_add)
  by (metis add.commute i_le_ltpi_add le_add_diff_inverse le_diff_conv)

lemma mem_imp_ge_etp_u:
  assumes mem: "mem (delta rho j (Suc i)) (subtract (\<Delta> rho (Suc i)) I)" and
    j_ge: "j \<ge> Suc i" and rI: "right I = enat n" and i_props: "\<Delta> rho (Suc i) \<le> n"
  shows "j \<ge> ETP rho (\<tau> rho i + left I)"
proof -
  from assms have "left I \<le> \<tau> rho j - \<tau> rho i" using le_diff_conv by auto
  then show ?thesis using j_ge le_diff_conv2 by (auto simp add: i_etp_to_tau)
qed

lemma i_to_suci_le:
  assumes "left I + \<tau> rho i \<le> \<tau> rho j" and "\<tau> rho (Suc i) \<le> \<tau> rho j"
  shows "\<tau> rho (Suc i) + (left I + \<tau> rho i - \<tau> rho (Suc i)) \<le> \<tau> rho j"
  using le_diff_conv2 assms by auto

lemma valid_shift_VUntil:
  assumes i_props: "right I \<ge> enat (\<Delta> rho (i+1))"
    and valid: "valid rho i (Until phi I psi) (Inr (VUntil i ys p))"
    and v_at_p: "v_at p \<ge> i + Suc 0"
    and rfin: "right I \<noteq> \<infinity>"
  shows "valid rho (i + 1) (Until phi (subtract (delta rho (i + 1) i) I) psi) (Inr (VUntil (i + 1) (if left I = 0 then tl ys else ys) p))"
proof -
  obtain n where rI: "right I = enat n"
    using rfin by (cases "right I") auto
  show ?thesis
  proof (cases "left I = 0")
    case True
    obtain z zs where ys_def: "ys = z # zs"
      using valid True
      apply (cases ys)
      apply (auto simp: valid_def Let_def split: if_splits enat.splits)
      apply (meson i_ge_etpi order_trans)+
      done
    show ?thesis
      using i_props v_at_p valid
      unfolding valid_def
      apply (auto simp add: Let_def Cons_eq_append_conv Cons_eq_upt_conv add.commute True i_le_ltpi min_def i_ltp_to_tau rI ys_def i_etp_to_tau le_diff_conv split: if_splits)
      done
  next
    case False
    have rw: "\<tau> rho i - (left I + \<tau> rho i - \<tau> rho (Suc i)) =
    (if left I + \<tau> rho i \<ge> \<tau> rho (Suc i) then \<tau> rho (Suc i) - left I else \<tau> rho i)"
      by auto
    have e: "right I = enat n \<Longrightarrow> right (subtract (delta rho (Suc i) i) I) = enat n' \<Longrightarrow>
    ETP rho (\<tau> rho (Suc i) - n) = ETP rho (\<tau> rho i - n')" for n n'
      by auto (metis Suc_eq_plus1 diff_add_inverse2 diff_cancel_middle enat_ord_simps(1) i_props le_diff_conv)
    have t: "\<tau> rho (Suc i) + (left I + \<tau> rho i - \<tau> rho (Suc i)) =
    (if left I + \<tau> rho i \<ge> \<tau> rho (Suc i) then \<tau> rho i + left I else \<tau> rho (Suc i))"
      by auto
    have etp: "max (Suc i) (ETP rho (left I + \<tau> rho i)) = max i (ETP rho (left I + \<tau> rho i))"
      using False
      by (auto simp: max_def)
        (meson add_le_same_cancel2 i_etp_to_tau leD not_less_eq_eq)
    have ee: "\<not> \<tau> rho (Suc i) \<le> left I + \<tau> rho i \<Longrightarrow> ETP rho (\<tau> rho i + left I) = Suc i"
      by (metis Groups.ab_semigroup_add_class.add.commute Lattices.linorder_class.max.absorb1 etp i_etp_to_tau max_def n_not_Suc_n nat_le_linear)
    show ?thesis
      using False valid e v_at_p i_ge_etpi[of rho "Suc i"] ee etp i_props
      apply (cases ys rule: rev_cases)
      apply (auto simp: valid_def Let_def rw t rI add.commute split: if_splits)
      done
  qed
qed

lemma valid_shift_VUntil_never:
  assumes i_props: "right I \<ge> enat (\<Delta> rho (i+1))"
    and valid: "valid rho i (Until phi I psi) (Inr (VUntil_never i hi ys))"
    and rfin: "right I \<noteq> \<infinity>"
  shows "valid rho (i + 1) (Until phi (subtract (delta rho (i + 1) i) I) psi) (Inr (VUntil_never (i + 1) hi (if left I = 0 then tl ys else ys)))"
proof -
  obtain n where rI: "right I = enat n"
    using rfin by (cases "right I") auto
  show ?thesis
  proof (cases "left I = 0")
    case True
    obtain z zs where ys_def: "ys = z # zs"
      using valid True
      apply (cases ys)
      apply (auto simp: valid_def Let_def split: if_splits enat.splits)
      apply (meson i_le_ltpi_add)
      by (meson i_ge_etpi i_le_ltpi_add le_trans)
    show ?thesis
      using i_props valid
      unfolding valid_def
      apply (auto simp add: Let_def Cons_eq_append_conv Cons_eq_upt_conv add.commute True i_le_ltpi min_def i_ltp_to_tau rI ys_def i_etp_to_tau le_diff_conv split: if_splits)
      done
  next
    case False
    have rw: "\<tau> rho i - (left I + \<tau> rho i - \<tau> rho (Suc i)) =
    (if left I + \<tau> rho i \<ge> \<tau> rho (Suc i) then \<tau> rho (Suc i) - left I else \<tau> rho i)"
      by auto
    have e: "right I = enat n \<Longrightarrow> right (subtract (delta rho (Suc i) i) I) = enat n' \<Longrightarrow>
    ETP rho (\<tau> rho (Suc i) - n) = ETP rho (\<tau> rho i - n')" for n n'
      by auto (metis Suc_eq_plus1 diff_add_inverse2 diff_cancel_middle enat_ord_simps(1) i_props le_diff_conv)
    have t: "\<tau> rho (Suc i) + (left I + \<tau> rho i - \<tau> rho (Suc i)) =
    (if left I + \<tau> rho i \<ge> \<tau> rho (Suc i) then \<tau> rho i + left I else \<tau> rho (Suc i))"
      by auto
    have etp: "max (Suc i) (ETP rho (left I + \<tau> rho i)) = max i (ETP rho (left I + \<tau> rho i))"
      using False
      by (auto simp: max_def)
        (meson add_le_same_cancel2 i_etp_to_tau leD not_less_eq_eq)
    have ee: "\<not> \<tau> rho (Suc i) \<le> left I + \<tau> rho i \<Longrightarrow> ETP rho (\<tau> rho i + left I) = Suc i"
      by (metis Groups.ab_semigroup_add_class.add.commute Lattices.linorder_class.max.absorb1 etp i_etp_to_tau max_def n_not_Suc_n nat_le_linear)
    show ?thesis
      using False valid e i_ge_etpi[of rho "Suc i"] ee etp i_props
      apply (cases ys rule: rev_cases)
      apply (auto simp: valid_def Let_def rw t rI add.commute split: if_splits)
      done
  qed
qed

lemma until_optimal:
  assumes i_props: "right I \<ge> enat (\<Delta> rho (i+1))" and
    p1_def: "optimal i phi p1" and p2_def: "optimal i psi p2" and
    p'_def: "optimal (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
    and bf: "bounded_future (Until phi I psi)"
    and bf': "bounded_future (Until phi (subtract (\<Delta> rho (i+1)) I) psi)"
  shows "optimal i (Until phi I psi) (min_list_wrt wqo (doUntil i (left I) p1 p2 p'))"
proof (rule ccontr)
  define minp where minp: "minp \<equiv> min_list_wrt wqo (doUntil i (left I) p1 p2 p')"
  from bf have bfpsi: "bounded_future psi" by auto
  from bf have bfphi: "bounded_future phi" by auto
  from bf obtain n where n_def: "right I = enat n" by auto
  from pw_total[of i "Until phi I psi"]
  have total_set: "total_on wqo (set (doUntil i (left I) p1 p2 p'))"
    using until_sound[OF i_props p1_def p2_def p'_def _ bf bf']
    by (metis not_wqo total_onI)
  term v_check
  define hi where "hi = (case right I - enat (delta rho (i + Suc 0) i) of enat n \<Rightarrow> LTP rho (\<tau> rho (Suc i) + n))"
  have rfin: "right I \<noteq> \<infinity>" "right I - enat (delta rho (i + Suc 0) i) \<noteq> \<infinity>"
    using bf
    by auto
  have hi: "hi = (case right I of enat n \<Rightarrow> LTP rho (\<tau> rho i + n) | \<infinity> \<Rightarrow> 0)"
    using i_props rfin
    by (auto simp: hi_def add.commute split: enat.splits)
  from p'_def have p'_form: "(\<exists>p p''. p' = Inl (SUntil p p'')) \<or> (\<exists>p p''. p' = Inr (VUntil (i+1) p p''))
  \<or> (\<exists>p. p' = Inr (VUntil_never (i+1) hi p))"
  proof(cases "SAT rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi)")
    case True
    then show ?thesis
      using val_SAT_imp_l[OF bf', of "i+1" p'] p'_def
        valid_UntilE[of "i+1" phi "subtract (\<Delta> rho (i+1)) I" psi p']
      unfolding optimal_def
      by auto+
  next
    case False
    then have VIO: "VIO rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi)"
      using SAT_or_VIO
      by auto
    then obtain b' where b'_def: "p' = Inr b'"
      using val_VIO_imp_r[OF bf'] p'_def
      unfolding optimal_def
      by force
    then show ?thesis
      using p'_def
      unfolding optimal_def valid_def
      by (cases b') (auto simp: hi_def)
  qed
  from doUntil_def[of i "left I" p1 p2 p'] p'_form
  have nnil: "doUntil i (left I) p1 p2 p' \<noteq> []"
    by (cases p1; cases p2; cases "left I"; cases p'; auto)
  have filter_nnil: "filter (\<lambda>x. \<forall>y \<in> set (doUntil i (left I) p1 p2 p'). wqo x y) (doUntil i (left I) p1 p2 p') \<noteq> []"
    using refl_total_transp_imp_ex_min[OF nnil refl_wqo total_set trans_wqo]
      filter_empty_conv[of "(\<lambda>x. \<forall>y \<in> set (doUntil i (left I) p1 p2 p'). wqo x y)" "(doUntil i (left I) p1 p2 p')"]
    by simp
  assume nopt: "\<not> optimal i (Until phi I psi) minp"
  from until_sound[OF i_props p1_def p2_def p'_def min_list_wrt_in bf bf']
    total_set trans_wqo refl_wqo nnil minp
  have vmin: "valid rho i (Until phi I psi) minp"
    by auto
  then obtain q where q_val: "valid rho i (Until phi I psi) q" and
    q_le: "\<not> wqo minp q" using minp nopt unfolding optimal_def by auto
  then have "wqo minp q" using minp
  proof (cases q)
    case (Inl a)
    then have q_s: "q = Inl a" by auto
    then have SATs: "SAT rho i (Until phi I psi)" using q_val check_sound(1)
      unfolding valid_def by auto
    then have sats: "sat rho i (Until phi I psi)" using soundness
      by blast
    from Inl obtain spsi sphis where a_def: "a = SUntil sphis spsi"
      using q_val unfolding valid_def by (cases a) auto
    then have valpsi: "valid rho (s_at spsi) psi (Inl spsi)" using q_val Inl
      unfolding valid_def by (auto simp: Let_def)
    from q_val Inl a_def n_def
    have spsi_bounds: "s_at spsi \<le> LTP rho (\<tau> rho i + n) \<and> s_at spsi \<ge> i"
      unfolding valid_def
      apply (auto simp: Let_def i_le_ltpi_add split: list.splits if_splits)
      by (metis add.commute i_le_ltpi_add le_Suc_ex le_diff_conv)
    from valpsi val_SAT_imp_l[OF bf] SATs have check_spsi: "s_check rho psi spsi"
      unfolding valid_def by auto
    then show ?thesis
    proof (cases p')
      case (Inl a')
      then have p'l: "p' = Inl a'" by auto
      then obtain spsi' sphis' where a'_def: "a' = SUntil spsi' sphis'"
        using p'_def unfolding optimal_def valid_def
        by (cases a') auto
      from SATs vmin have minl: "\<exists>a. minp = Inl a" using minp val_SAT_imp_l[OF bf]
        by auto
      then show ?thesis
      proof (cases p1)
        case (Inl a1)
        then have p1l: "p1 = Inl a1" by auto
        then show ?thesis
        proof (cases "left I = 0")
          case True
          then show ?thesis
          proof (cases p2)
            case (Inl a2)
            then have form: "doUntil i (left I) p1 p2 p' = [(p' \<oplus> p1), Inl (SUntil [] a2)]"
              using p1l p'l True a'_def unfolding doUntil_def by auto
            then show ?thesis
            proof (cases sphis)
              case Nil
              then have "wqo (Inl (SUntil [] a2)) q"
                using Inl q_val p2_def SUntil_Nil[of a2 spsi]
                by (auto simp: optimal_def valid_def q_s a_def)
              moreover have "Inl (SUntil [] a2) \<in> set (doUntil i (left I) p1 p2 p')"
                using form by auto
              ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                  until_sound[OF i_props p1_def p2_def p'_def _ bf bf']
                  pw_total[of i "Until phi I psi"] q_val
                  trans_wqo q_s
                apply (auto simp add: total_on_def)
                by (metis transpD)
            next
              case (Cons y ys)
              from p'l p1l a'_def have check_p: "checkApp p' p1"
                by (auto intro: checkApp.intros)
              from form until_sound[OF i_props p1_def p2_def p'_def _ bf bf']
              have p_val: "valid rho i (Until phi I psi) (p' \<oplus> p1)"
                by auto
              from a_def Cons have y_val: "valid rho i phi (Inl y)"
                using q_s q_val True i_props unfolding valid_def
                by (auto simp: Let_def split: if_splits)
              with q_val have q'_val:
                "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inl (SUntil ys spsi))"
                using Cons n_def i_props sval_to_sval'_u[of i phi I psi y ys spsi n]
                unfolding q_s a_def
                by (auto simp: Let_def valid_def)
              then have q_eq: "q = (Inl (SUntil ys spsi)) \<oplus> (Inl y)"
                using q_s a_def Cons by auto
              then have q_val2: "valid rho i (Until phi I psi) ((Inl (SUntil ys spsi)) \<oplus> (Inl y))"
                using q_val by auto
              then have check_q: "checkApp (Inl (SUntil ys spsi)) (Inl y)"
                using checkApp.intros(2) by auto
              then have wqo_p': "wqo p' (Inl (SUntil ys spsi))" using q'_val p'_def
                unfolding optimal_def by auto
              moreover have wqo_p1: "wqo p1 (Inl y)" using i_props p1_def y_val
                unfolding optimal_def by auto
              ultimately have "wqo (p' \<oplus> p1) q"
                using Cons q_s a_def
                  proofApp_mono[OF check_p check_q wqo_p' wqo_p1 p_val q_val2]
                by auto
              moreover have "(p' \<oplus> p1) \<in> set (doUntil i (left I) p1 p2 p')"
                using form by auto
              ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                  until_sound[OF i_props p1_def p2_def p'_def _ bf bf']
                  pw_total[of i "Until phi I psi"] p'l trans_wqo q_s p1l a'_def
                unfolding proofApp_def
                apply (auto simp add: total_on_def)
                by (metis transpD)
            qed
          next
            case (Inr b2)
            then have form: "minp = p' \<oplus> p1"
              using Inr p1l p'l a'_def True minp filter_nnil
              unfolding doUntil_def by (auto simp: min_list_wrt_def)
            from p2_def Inr have psi_VIO: "VIO rho i psi"
              using check_consistent[OF bfpsi]
              unfolding optimal_def valid_def
              by (auto simp add: check_sound(2))
            then have spsi_greater: "s_at spsi > i"
              using a_def q_s q_val zero_enat_def unfolding valid_def
              apply (auto simp: Let_def split: list.splits if_splits)
              using bfpsi val_VIO_imp_r valpsi nat_less_le by auto
            then have sphis_not_nil: "sphis \<noteq> []" using a_def q_s q_val
              unfolding valid_def by auto
            then obtain y and ys where cons_q: "sphis = y # ys"
              using a_def q_s q_val spsi_greater unfolding valid_def
              apply (auto simp: Let_def split: if_splits)
              by (meson neq_Nil_conv)
            from p'l p1l a'_def have check_p: "checkApp p' p1"
              by (auto intro: checkApp.intros)
            from form vmin have p_val: "valid rho i (Until phi I psi) (p' \<oplus> p1)"
              using minp by auto
            from a_def cons_q have y_val: "valid rho i phi (Inl y)"
              using q_s q_val True i_props unfolding valid_def
              by (auto simp: Let_def case_snoc split: if_splits)
            with q_val have q'_val:
              "valid rho (i + 1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inl (SUntil ys spsi))"
              using y_val cons_q n_def i_props sval_to_sval'_u[of i phi I psi y ys spsi n]
              unfolding q_s a_def
              by (auto simp: Let_def valid_def)
            then have q_eq: "q = (Inl (SUntil ys spsi)) \<oplus> (Inl y)"
              using q_s a_def cons_q by auto
            then have q_val2: "valid rho i (Until phi I psi) ((Inl (SUntil ys spsi)) \<oplus> (Inl y))"
              using q_val by auto
            then have check_q: "checkApp (Inl (SUntil ys spsi)) (Inl y)"
              using checkApp.intros(2) by auto
            then have wqo_p': "wqo p' (Inl (SUntil ys spsi))" using q'_val p'_def
              unfolding optimal_def by auto
            moreover have wqo_p1: "wqo p1 (Inl y)" using i_props p1_def y_val
              unfolding optimal_def by auto
            ultimately show ?thesis
              using cons_q q_s a_def form
                proofApp_mono[OF check_p check_q wqo_p' wqo_p1 p_val q_val2]
              by auto
          qed
        next
          case False
          then have form: "minp = p' \<oplus> p1" using p1l p'l a'_def minp filter_nnil
            unfolding doUntil_def by (cases p2; auto simp: min_list_wrt_def)
          from False have spsi_less: "s_at spsi > i" using q_val a_def q_s
            unfolding valid_def
            apply (auto simp: Let_def split: if_splits)
            using le_zero_eq by fastforce
          then have sphis_not_nil: "sphis \<noteq> []" using a_def q_s q_val
            unfolding valid_def by auto
          then obtain y and ys where cons_q: "sphis = y # ys"
            using a_def q_s q_val spsi_less unfolding valid_def
            apply (auto simp: Let_def split: if_splits)
            by (meson neq_Nil_conv)
          from p'l p1l a'_def have check_p: "checkApp p' p1"
            by (auto intro: checkApp.intros)
          from form vmin have p_val: "valid rho i (Until phi I psi) (p' \<oplus> p1)"
            using minp by auto
          from a_def cons_q have y_val: "valid rho i phi (Inl y)"
            using q_s q_val i_props unfolding valid_def
            by (auto simp: Let_def split: if_splits)
          with q_val have q'_val:
            "valid rho (i + 1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inl (SUntil ys spsi))"
            using y_val cons_q n_def i_props sval_to_sval'_u[of i phi I psi y ys spsi n]
            unfolding q_s a_def
            by (auto simp: Let_def valid_def)
          then have q_eq: "q = (Inl (SUntil ys spsi)) \<oplus> (Inl y)"
            using q_s a_def cons_q by auto
          then have q_val2: "valid rho i (Until phi I psi) ((Inl (SUntil ys spsi)) \<oplus> (Inl y))"
            using q_val by auto
          then have check_q: "checkApp (Inl (SUntil ys spsi)) (Inl y)"
            using checkApp.intros(2) by auto
          then have wqo_p': "wqo p' (Inl (SUntil ys spsi))" using q'_val p'_def
            unfolding optimal_def by auto
          moreover have wqo_p1: "wqo p1 (Inl y)" using i_props p1_def y_val
            unfolding optimal_def by auto
          ultimately show ?thesis
            using cons_q q_s a_def form
              proofApp_mono[OF check_p check_q wqo_p' wqo_p1 p_val q_val2]
            by auto
        qed
      next
        case (Inr b1)
        then have phivio: "VIO rho i phi" using p1_def check_sound(2)
          unfolding optimal_def valid_def
          by auto
        from Inr have form_min: "minp = Inl (SUntil [] (projl p2))"
          using p'l minp minl a'_def filter_nnil unfolding doUntil_def
          by (cases p2; cases "left I = 0") (auto simp: min_list_wrt_def)
        then have sphis_nil: "sphis = []" using phivio q_val a_def i_props q_s
          unfolding valid_def
          apply (auto simp: Let_def split: if_splits list.splits)
          using bfphi check_sound(1) soundness by blast
        then have sc: "s_at spsi = i" using a_def q_s q_val unfolding valid_def
          by auto
        then obtain a2 where a2_def: "p2 = Inl a2"
          using bfpsi check_sound(1) check_spsi optimal_def p2_def val_SAT_imp_l
          by blast
        moreover have "wqo p2 (Inl spsi)" using valpsi sc p2_def
          unfolding optimal_def by auto
        ultimately show ?thesis using form_min q_s a_def sphis_nil a2_def
            SUntil_Nil[of a2 spsi] by auto
      qed
    next
      case (Inr b)
      then have formb: "(\<exists>q qs. b = VUntil (i+1) qs q) \<or> (\<exists>qs. b = VUntil_never (i+1) hi qs)"
        using p'_def i_props Inr unfolding optimal_def valid_def
        by (cases b) (auto simp: hi_def)
      then have viosp: "\<not> sat rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi)"
        using p'_def Inr check_sound(2)[of rho "Until phi (subtract (\<Delta> rho (i+1)) I) psi" b]
          soundness[of _ _ "Until phi (subtract (delta rho (i + 1) (i + 1 - 1)) I) psi"]
        unfolding optimal_def valid_def
        by (auto simp: Let_def)
      then have satc: "mem 0 I \<and> sat rho i psi"
        using i_props sats sat_Until_rec zero_enat_def
        apply auto
        apply (metis Suc_eq_plus1 add_implies_diff le_neq_implies_less less_nat_zero_code sat_Until_rec sats viosp)
        by (meson sat_Until_rec sats viosp)
      from vmin SATs val_SAT_imp_l obtain ap where ap_def: "minp = Inl ap"
        using minp unfolding valid_def apply auto
        using bf by blast
      then have aps: "ap = SUntil [] (projl p2)"
        using minp formb Inr satc filter_nnil
        unfolding doUntil_def proofApp_def
        by (cases p1; cases p2) (auto  simp: min_list_wrt_def split: if_splits)
      then obtain a2 where a2_def: "p2 = Inl a2"
        using ap_def minp satc formb Inr filter_nnil
        unfolding doUntil_def proofApp_def
        by (cases p1; cases p2) (auto  simp: min_list_wrt_def split: if_splits)
      then have max: "max (Suc i) (ETP rho (\<tau> rho (i+1) + (left (subtract (\<Delta> rho (i+1)) I)))) = Suc i"
        using satc apply auto
        by (metis max.orderE i_ge_etpi)
      {fix hi' qs
        assume bv: "b = VUntil_never (i+1) hi' qs"
        have hi'_def: "hi' = hi"
          using p'_def
          by (auto simp: Inr bv optimal_def valid_def hi_def)
        have tc: "map v_at qs = [Suc i ..< Suc (LTP rho (\<tau> rho i + n))]"
          using max n_def satc Inr p'_def i_props unfolding optimal_def valid_def
          by (auto simp: Let_def bv add.commute)
        then have qs_check: "\<forall>p \<in> set qs. v_check rho psi p"
          using bv n_def max satc Inr p'_def i_props
          unfolding optimal_def valid_def by auto
        then have jc: "\<forall>j \<in> set (map v_at qs). \<exists>p. v_at p = j \<and> v_check rho psi p"
          using map_set_in_imp_set_in[of qs psi] qs_check by auto
        then have "s_at spsi \<notin> set (map v_at qs)" using spsi_bounds
            check_consistent[OF bfpsi] check_spsi by auto
        then have "s_at spsi = i"
          using spsi_bounds tc
          by auto
      }
      moreover
      {fix qa qs
        assume bv: "b = VUntil (i+1) qs qa"
        then have tc: "map v_at qs = [Suc i ..< Suc (v_at qa)]"
          using max n_def Inr p'_def i_props
          unfolding optimal_def valid_def by (auto simp: Let_def)
        then have qs_check: "\<forall>p \<in> set qs. v_check rho psi p"
          using bv n_def max Inr p'_def i_props
          unfolding optimal_def valid_def by (auto simp: Let_def)
        then have jc: "\<forall>j \<in> set (map v_at qs). \<exists>p. v_at p = j \<and> v_check rho psi p"
          using map_set_in_imp_set_in[of qs psi] by auto
        then have spsi_not_in: "s_at spsi \<notin> set (map v_at qs)" using spsi_bounds
            check_consistent[OF bfpsi] check_spsi by auto
        from bv Inr p'_def have qa_ge_i: "v_at qa \<ge> i"
          unfolding optimal_def valid_def by (auto simp: Let_def)
        from bv Inr p'_def have qa_check: "v_check rho phi qa"
          unfolding optimal_def valid_def by (auto simp: Let_def)
        {
          assume spsi_ge: "s_at spsi > v_at qa"
          from a_def Inl q_val
          have tc_q: "map s_at sphis = [i ..< s_at spsi]" unfolding valid_def
            by (auto simp: Let_def)
          then have qa_in: "v_at qa \<in> set (map s_at sphis)" using spsi_ge qa_ge_i
            by (auto split: if_splits)
          from a_def Inl q_val have phis_check: "\<forall>p \<in> set sphis. s_check rho phi p"
            unfolding valid_def by (auto simp: Let_def)
          then have "\<forall>j \<in> set (map s_at sphis). \<exists>p. s_at p = j \<and> s_check rho phi p"
            using map_set_in_imp_set_in by auto
          then have spsi_le: "s_at spsi \<le> v_at qa" using qa_in qa_check spsi_ge
              check_consistent[OF bfphi]
            by auto
          then have False using spsi_ge by auto
        }
        then have spsi_le: "s_at spsi \<le> v_at qa" using not_le_imp_less by blast
        then have "s_at spsi = i" using spsi_bounds spsi_not_in tc
          by auto
      }
      ultimately have wqo: "wqo p2 (Inl spsi)" and s_at_spsi: "s_at spsi = i" using formb p2_def valpsi
        unfolding optimal_def by auto
      have sphis_Nil: "sphis = []"
        using q_val s_at_spsi
        by (auto simp: Inl a_def valid_def Let_def split: list.splits)
      show ?thesis using a_def Inl minp ap_def aps a2_def
          SUntil_Nil[of a2 spsi] wqo
        by (auto simp: map_idI sphis_Nil)
    qed
  next
    case (Inr b)
    then have qr: "q = Inr b" by auto
    then have VIO: "VIO rho i (Until phi I psi)"
      using q_val check_sound(2)[of rho "Until phi I psi" b]
      unfolding valid_def by auto
    then have formb: "(\<exists>p ps. b = VUntil i ps p) \<or> (\<exists>ps. b = VUntil_never i hi ps)"
      using Inr q_val i_props unfolding valid_def by (cases b) (auto simp: hi_def add.commute)
    moreover
    {fix p ps
      assume bv: "b = VUntil i ps p"
      from bv have vp: "valid rho (v_at p) phi (Inr p)" using q_val qr
        unfolding valid_def by (auto simp: Let_def)
      then have p_bounds: "LTP rho (\<tau> rho i + n) \<ge> v_at p \<and> v_at p \<ge> i"
        using n_def bv qr q_val unfolding valid_def by (auto simp: Let_def)
      then have "wqo minp q"
      proof (cases p')
        case (Inl a')
        then obtain p1' ps' where a's: "a' = SUntil ps' p1'" using p'_def
          unfolding optimal_def valid_def
          by (cases a') auto
        from a's Inl have ps'c: "map s_at ps' = [Suc i ..< s_at p1']"
          using p'_def unfolding optimal_def valid_def
          by (auto simp: Let_def)
        from a's Inl have ps'_check: "\<forall>p \<in> set ps'. s_check rho phi p"
          using p'_def unfolding optimal_def valid_def
          by (auto simp: Let_def)
        then have jc: "\<forall>j \<in> set (map s_at ps'). \<exists>p. s_at p = j \<and> s_check rho phi p"
          using map_set_in_imp_set_in by auto
        from a's Inl have sp1'_le_ltp: "s_at p1' \<ge> ETP rho (\<tau> rho i + left I)"
          using p'_def n_def i_props mem_imp_ge_etp_u[of i I "s_at p1'" n]
          unfolding optimal_def valid_def by (auto simp: Let_def)
        from a's Inl have sp1'_bounds: "LTP rho (\<tau> rho i + n) \<ge> s_at p1'
        \<and> s_at p1' > i" using p'_def i_props n_def
          mem_imp_le_ltp_u[of i I "s_at p1'" n] unfolding optimal_def valid_def
          by (auto simp: Let_def)
        from a's Inl have sp1': "s_check rho psi p1'" using p'_def
          unfolding optimal_def valid_def by (auto simp: Let_def)
        from jc have "v_at p \<notin> set (map s_at ps')" using vp bfphi check_consistent
          unfolding valid_def by auto
        then have "v_at p \<ge> s_at p1' \<or> v_at p = i" using sp1'_bounds ps'c p_bounds
          by auto
        moreover
        {
          assume p_ge_p1': "v_at p \<ge> s_at p1'"
          from bv qr q_val n_def
          have tc_q: "map v_at ps = [lu rho i I ..< Suc (v_at p)]"
            unfolding valid_def by (auto simp: Let_def)
          then have qa_in: "s_at p1' \<in> set (map v_at ps)"
            using p_ge_p1' sp1'_bounds sp1'_le_ltp
            by (auto split: if_splits)
          from bv qr q_val have phis_check: "\<forall>p \<in> set ps. v_check rho psi p"
            unfolding valid_def by (auto simp: Let_def)
          then have "\<forall>j \<in> set (map v_at ps). \<exists>p. v_at p = j \<and> v_check rho psi p"
            using map_set_in_imp_set_in by auto
          then have spsi_ge: "v_at p < s_at p1'" using qa_in sp1' p_ge_p1'
              check_consistent[OF bfpsi]
            by auto
          then have False using p_ge_p1' by auto
        }
        ultimately have p_eq_i: "v_at p = i" by auto
        from Inl have form_minp: "minp = Inr (VUntil i [projr p2] (projr p1) )
        \<or> minp = Inr (VUntil i [] (projr p1))"
          using vmin val_VIO_imp_r[OF bf vmin VIO] minp n_def a's filter_nnil
          unfolding doUntil_def proofApp_def
          by (cases p1; cases p2; cases "left I = 0") (auto simp: min_list_wrt_def split: if_splits)
        moreover
        {
          assume pv: "minp = Inr (VUntil i [projr p2] (projr p1))"
          then have l0: "left I = 0" using minp Inl a's filter_nnil
            unfolding doUntil_def proofApp_def
            by (cases p1; cases p2; cases "left I = 0") (auto simp: min_list_wrt_def split: if_splits)
          then obtain pps where pps: "ps = [pps] \<and> valid rho i psi (Inr pps)"
            using p_eq_i p_bounds qr bv q_val n_def unfolding valid_def
            by (auto simp add: i_ge_etpi split: if_splits)
          from pv l0 obtain a1 where a1_def: "p1 = Inr a1"
            using form_minp minp a's Inl filter_nnil
            unfolding doUntil_def proofApp_def
            by (cases p1; cases p2; cases "left I = 0") (auto simp: min_list_wrt_def split: if_splits)
          obtain a2 where a2_def: "p2 = Inr a2"
            using pps p2_def check_consistent[OF bfpsi]
            by (auto simp add: optimal_def valid_def split: sum.splits)
          from vp p_eq_i p1_def have "wqo p1 (Inr p)" unfolding optimal_def
            by auto
          moreover have lcomp: "wqo (Inr a2) (Inr pps)" using p2_def pps
            unfolding optimal_def by (auto simp: a2_def)
          ultimately have "wqo minp q"
            using a2_def bv qr pv a1_def VUntil[of a1 p] pps
            by auto
        }
        moreover
        {
          assume pv: "minp = Inr (VUntil i [] (projr p1))"
          then obtain a1 where a1_def: "p1 = Inr a1"
            using vmin val_VIO_imp_r[OF bf vmin VIO] minp n_def a's Inl filter_nnil
            unfolding doUntil_def proofApp_def
            by (cases p1; cases p2; cases "left I = 0") (auto simp: min_list_wrt_def split: if_splits)
          have wqo: "wqo p1 (Inr p)" using p1_def p_eq_i vp
            unfolding optimal_def by auto
          have "left I = 0 \<Longrightarrow> False"
            using vmin
            by (auto simp: pv valid_def Let_def n_def i_etp_to_tau split: if_splits enat.splits)
          then have ps_Nil: "ps = []"
            using q_val
            apply (cases "left I")
            apply (auto simp: Inr bv valid_def Let_def n_def split: if_splits enat.splits)
            apply (metis Suc_n_not_le_n i_etp_to_tau le_add1 le_trans p_eq_i)
            done
          have "wqo minp q"
            using VUntil_Nil[of a1 p] pv bv qr a1_def wqo
            by (auto simp: map_idI ps_Nil)
        }
        ultimately show ?thesis by auto
      next
        case (Inr b')
        then have p'b': "p' = Inr b'" by auto
        then have formb': "(\<exists>p ps. b' = VUntil (i+1) ps p)
        \<or> (\<exists>ps. b' = VUntil_never (i+1) hi ps)"
          using Inr p'_def n_def i_props
          unfolding optimal_def valid_def by (cases b') (auto simp: Let_def hi add.commute)
        moreover
        {fix vphi' vpsis'
          assume b'v: "b' = VUntil (i+1) vpsis' vphi'"
          then have "wqo minp q"
          proof (cases p1)
            case (Inl a1)
            then show ?thesis
            proof (cases "left I = 0")
              case True
              then have form_min: "minp = p' \<oplus> p2" using b'v Inl minp Inr
                  val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def by (cases p2) (auto simp: min_list_wrt_def)
              then obtain p2' where p2r: "p2 = Inr p2'"
                using True b'v Inl minp Inr val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def
                apply (cases p2; auto simp: min_list_wrt_def split: if_splits)
                by (metis Inl_Inr_False)
              then show ?thesis
                using form_min qr bv Inl p1_def q_val unfolding optimal_def valid_def
                apply (cases ps)
                apply (auto simp add: Let_def True i_etp_to_tau split: if_splits enat.splits)[1]
                subgoal premises prems for y ys
                proof -
                  from vmin form_min p2r have p_val: "valid rho i (Until phi I psi) (p' \<oplus> (Inr p2'))"
                    by auto
                  have check_p: "checkApp p' (Inr p2')"
                    using p'_def True
                    unfolding p2r b'v p'b'
                    by (auto simp: optimal_def intro!: valid_checkApp_VUntil)
                  from prems have y_val: "valid rho i psi (Inr y)"
                    using q_val True i_props n_def i_ge_etpi[of rho i] unfolding valid_def
                    apply (auto simp: Let_def max_def Cons_eq_append_conv split: if_splits)
                    using Cons_eq_upt_conv by blast
                  have "Suc i \<le> v_at p"
                    using q_val p1_def check_consistent[OF bfphi]
                    by (auto simp: Inl qr bv prems(8) optimal_def valid_def Let_def split: if_splits enat.splits)
                      (meson le_antisym not_less_eq_eq)+
                  then have val_q': "valid rho (i + 1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil (i+1) ys p))"
                    using valid_shift_VUntil[of i I phi psi ps p] rfin(1) i_props q_val
                    by (auto simp: qr bv True prems(8))
                  then have q_val2: "valid rho i (Until phi I psi) ((Inr (VUntil (i+1) ys p)) \<oplus> (Inr y))"
                    using q_val prems i_props by auto
                  have check_q: "checkApp (Inr (VUntil (i+1) ys p)) (Inr y)"
                    using val_q' True
                    by (auto intro!: valid_checkApp_VUntil)
                  from p'_def have wqo_p': "wqo p' (Inr (VUntil (i + 1) ys p))"
                    using val_q' unfolding optimal_def by simp
                  moreover have wqo_p2: "wqo p2 (Inr y)" using i_props p2_def y_val
                    unfolding optimal_def by auto
                  ultimately show ?thesis
                    unfolding prems using p'b' b'v p2_def q_val prems p2r unfolding valid_def optimal_def
                    using proofApp_mono[OF check_p check_q wqo_p' wqo_p2[unfolded p2r] p_val q_val2]
                    by auto
                qed
                done
            next
              case False
              then have form: "minp = Inr (VUntil i vpsis' vphi')"
                using b'v Inl minp Inr filter_nnil unfolding doUntil_def
                by (cases p2) (auto simp: min_list_wrt_def)
              then show ?thesis using qr bv q_val Inl p1_def i_props n_def
                unfolding optimal_def valid_def
                apply (cases ps)
                apply (auto simp add: Let_def False i_etp_to_tau split: if_splits)[1]
                subgoal premises prems
                proof -
                  from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                    unfolding optimal_def by auto
                  from p1_def Inl have p_ni: "\<not> v_at p = s_at a1"
                    using check_consistent[OF bfphi] prems(10-14)
                    unfolding optimal_def valid_def
                    by auto
                  then have p_le_predi: "v_at p \<ge> s_at a1 + 1"
                    using p_bounds prems by auto
                  then have valid_q_before: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil (i+1) ps p))"
                    using prems unfolding valid_def
                    by (auto simp add: le_diff_conv Let_def i_etp_to_tau add.commute)
                  then have "wqo p' (Inr (VUntil (i+1) ps p))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VUntil)
                  moreover have "checkIncr (Inr (VUntil (i + 1) ps p))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VUntil)
                  ultimately show ?thesis
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VUntil (i+1) ps p)"]
                      valid_q_before i_props prems(4)
                    unfolding p'b' b'v prems(11)[symmetric]
                    by (auto simp add: proofIncr_def intro: checkIncr.intros)
                qed
                subgoal premises prems for y ys
                proof -
                  from p1_def have a1_i: "s_at a1 = i" using Inl
                    unfolding optimal_def valid_def by auto
                  from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                    unfolding optimal_def by auto
                  from p'_def p'b' b'v n_def have suc_le_etp: "Suc i \<le> ETP rho (\<tau> rho i + left I)"
                    unfolding optimal_def valid_def
                    apply (auto simp: Let_def split: if_splits)
                    apply (meson False add_cancel_left_left etp_to_delta le_add2 le_antisym le_diff_conv2 le_refl not_less_eq_eq)
                    by (metis False diff_add_inverse diff_is_0_eq' i_etp_to_tau not_less_eq_eq)
                  from p1_def have p_ni: "\<not> v_at p = s_at a1"
                    using check_consistent[OF bfphi] prems
                    unfolding optimal_def valid_def
                    by auto
                  then have p_le_predi: "v_at p \<ge> s_at a1 + 1"
                    using p_bounds prems by auto
                  then have valid_q_before: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil (i+1) ps p))"
                    using valid_shift_VUntil[of i I phi psi ps p] rfin(1) i_props q_val False
                    by (auto simp: qr bv prems(8) a1_i)
                  then have "wqo p' (Inr (VUntil (i+1) ps p))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VUntil)
                  moreover have "checkIncr (Inr (VUntil (i + 1) ps p))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VUntil)
                  ultimately show ?thesis
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VUntil (i+1) ps p)"]
                      valid_q_before i_props prems(3) form qr
                    unfolding p'b' b'v a1_i[symmetric]
                    by (auto simp add: proofIncr_def intro: checkIncr.intros)
                qed
                done
            qed
          next
            case (Inr b1)
            then show ?thesis
            proof (cases "left I = 0")
              case True
              then have form: "minp = Inr (VUntil i [projr p2] b1) \<or> minp = (p' \<oplus> p2)"
                using Inr p'b' b'v minp val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def by (cases p2) (auto simp: min_list_wrt_def)
              then obtain p2' where p2r: "p2 = Inr p2'"
                using p'b' b'v Inr True minp val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def
                by (cases p2; auto simp: min_list_wrt_def split: if_splits)
              then have res: "doUntil i (left I) p1 p2 p' = [Inr (VUntil i [projr p2] b1), (p' \<oplus> p2)]"
                using True Inr p'b' b'v unfolding doUntil_def by auto
              from True q_val qr bv have ps_not_nil: "ps \<noteq> []"
                using n_def unfolding valid_def
                apply (auto simp: Let_def split: if_splits)
                using i_ge_etpi le_trans by blast
              then obtain y and ys where cons_q: "ps = y # ys"
                using qr bv
                by (cases ps; auto)
              then have y_val: "valid rho i psi (Inr y)"
                using q_val qr bv n_def True i_ge_etpi[of rho i] unfolding valid_def
                apply (auto simp: Let_def max_def Cons_eq_append_conv split: if_splits)
                by (metis upt_eq_Cons_conv)
              then have wqo_p2: "wqo (Inr p2') (Inr y)" using p2r p2_def
                unfolding optimal_def by auto
              then show ?thesis
              proof (cases ys)
                case Nil
                then have p_eq_i: "v_at p = i" using True bv qr q_val n_def
                    i_props i_ge_etpi[of rho i]
                  unfolding valid_def
                  apply (auto simp: Let_def max_def split: if_splits)
                  by (metis append.left_neutral list.simps(8) list.simps(9) add_cancel_right_right append1_eq_conv cons_q le_add2 le_antisym upt_eq_Nil_conv)
                then have p_val: "valid rho i phi (Inr p)" using vp
                  by auto
                from wqo_p2 have lcomp: "wqo (Inr p2') (Inr y)"
                  by auto
                moreover have wqo_p1: "wqo (Inr b1) (Inr p)"
                  using Inr p1_def p_val unfolding optimal_def by auto
                ultimately have "wqo (Inr (VUntil i [p2'] b1)) q"
                  using qr bv cons_q VUntil[OF wqo_p1 lcomp] Nil p2r
                  by auto
                moreover have "(Inr (VUntil i [p2'] b1)) \<in> set (doUntil i (left I) p1 p2 p')"
                  using form minp Inr p2r Inr True b'v p'b'
                  unfolding doUntil_def by auto
                ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                    until_sound[OF i_props p1_def p2_def p'_def _ bf bf'] form
                    pw_total[of i "Until phi I psi"] p'b' trans_wqo Inr b'v p2r
                  unfolding proofApp_def
                  apply (auto simp add: total_on_def)
                  by (metis transpD)
              next
                case (Cons a as)
                then have p_ge_suci: "v_at p \<ge> i + 1"
                  using True bv qr q_val n_def i_props cons_q i_ge_etpi[of rho i]
                  unfolding valid_def
                  apply (auto simp: Let_def max_def split: if_splits)
                  using not_less_eq_eq by fastforce
                then have q'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil (i+1) ys p))"
                  using q_val cons_q True qr bv n_def i_props
                  unfolding valid_def
                  apply (auto simp: Let_def max_def i_etp_to_tau True add.commute Cons_eq_append_conv Cons_eq_upt_conv split: if_splits)
                  using i_ge_etpi[of rho "Suc i"] i_ge_etpi[of rho i]
                  by auto
                then have wqo_p': "wqo p' (Inr (VUntil (i+1) ys p))"
                  using p'_def unfolding optimal_def by auto
                have check_q: "checkApp (Inr (VUntil (i+1) ys p)) (Inr y)"
                  using q'_val True
                  by (auto intro!: valid_checkApp_VUntil)
                have check_min: "checkApp p' (Inr p2')" using p2r p'b' b'v
                  using p'_def True
                  unfolding p2r b'v p'b'
                  by (auto simp: optimal_def intro!: valid_checkApp_VUntil)
                from res have val_min: "valid rho i (Until phi I psi) (p' \<oplus> (Inr p2'))"
                  using b'v p'b' p2r
                    until_sound[OF i_props p1_def p2_def p'_def _ bf bf']
                  by auto
                from q_val have q_val2: "valid rho i (Until phi I psi) ((Inr (VUntil (i+1) ys p)) \<oplus> (Inr y))"
                  using qr bv cons_q i_props unfolding proofApp_def by auto
                then have "wqo (p' \<oplus> (Inr p2')) q"
                  using qr bv cons_q p'b' b'v i_props
                    proofApp_mono[OF check_min check_q wqo_p' wqo_p2 val_min q_val2]
                  by auto
                moreover have "(p' \<oplus> (Inr p2')) \<in> set (doUntil i (left I) p1 p2 p')"
                  using form minp Inr p2r Inr True b'v p'b'
                  unfolding doUntil_def by auto
                ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                    until_sound[OF i_props p1_def p2_def p'_def _ bf bf'] form
                    pw_total[of i "Until phi I psi"] p'b' trans_wqo Inr b'v p2r
                  unfolding proofApp_def
                  apply (auto simp add: total_on_def)
                  by (metis transpD)
              qed
            next
              case False
              then have lI: "left I \<noteq> 0" by auto
              then have form: "minp = Inr (VUntil i [] b1)
                \<or> minp = Inr (VUntil i vpsis' vphi')" using Inr p'b' b'v minp
                val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def by (cases p2) (auto simp: min_list_wrt_def)
              from p1_def Inr have b1i: "v_at b1 = i"
                unfolding optimal_def valid_def by auto
              from False Inr p'b' b'v have
                res: "doUntil i (left I) p1 p2 p' = [Inr (VUntil i [] b1), Inr (VUntil i vpsis' vphi')]"
                unfolding doUntil_def by (cases p2; auto)
              then show ?thesis
              proof (cases "v_at p = i")
                case True
                then have ps_nil: "ps = []" using qr bv q_val n_def False
                  unfolding valid_def
                  apply (auto simp: Let_def max_def split: if_splits)
                  apply (metis add_le_same_cancel1 i_etp_to_tau lI le0 le_antisym le_refl)
                  by (meson add_le_same_cancel1 i_etp_to_tau lI le_0_eq nat_le_linear)
                from True vp have wqo_p1: "wqo (Inr b1) (Inr p)" using p1_def Inr
                  unfolding optimal_def by auto
                then have "wqo (Inr (VUntil i [] b1)) q"
                  using qr bv ps_nil VUntil_Nil[OF wqo_p1] by auto
                moreover have "(Inr (VUntil i [] b1)) \<in> set (doUntil i (left I) p1 p2 p')"
                  using Inr b'v p'b' res by auto
                ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                    until_sound[OF i_props p1_def p2_def p'_def _ bf bf'] form
                    pw_total[of i "Until phi I psi"] p'b' trans_wqo Inr b'v
                  apply (auto simp add: total_on_def)
                  by (metis transpD)
              next
                case False
                then have p_le_predi: "v_at p \<ge> i + 1" using p_bounds by auto
                from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                  unfolding optimal_def by auto
                then show ?thesis using qr bv q_val Inr p1_def i_props n_def
                  unfolding optimal_def valid_def
                  apply (cases ps)
                  apply (auto simp add: Let_def False i_etp_to_tau split: if_splits)[1]
                  subgoal premises prems
                  proof -
                    from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                      unfolding optimal_def by auto
                    then have valid_q_before: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil (i+1) ps p))"
                      using prems unfolding valid_def
                      apply (auto simp add: le_diff_conv Let_def i_etp_to_tau add.commute)
                      using p_le_predi apply linarith
                      using False by linarith
                    then have "wqo p' (Inr (VUntil (i+1) ps p))" using p'_def
                      unfolding optimal_def by auto
                    moreover have "checkIncr p'"
                      using p'_def
                      unfolding p'b' b'v
                      by (auto simp: optimal_def intro!: valid_checkIncr_VUntil)
                    moreover have "checkIncr (Inr (VUntil (i + 1) ps p))"
                      using valid_q_before
                      by (auto intro!: valid_checkIncr_VUntil)
                    ultimately have "wqo (Inr (VUntil i vpsis' vphi')) q"
                      using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VUntil (i+1) ps p)"]
                        valid_q_before i_props prems(4) qr bv
                      unfolding p'b' b'v prems(11)[symmetric]
                      by (auto simp add: proofIncr_def intro: checkIncr.intros)
                    moreover have comp_in: "(Inr (VUntil i vpsis' vphi')) \<in> set (doUntil i (left I) p1 p2 p')"
                      using Inr b'v p'b' res by auto
                    ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                        until_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                        pw_total[of i "Until phi I psi"] p'b' trans_wqo Inr b'v
                        res prems
                      unfolding prems(11)[symmetric]
                      apply (auto simp add: total_on_def)
                      by (metis transpD)
                  qed
                  subgoal premises prems for y ys
                  proof -
                    from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                      unfolding optimal_def by auto
                    from Inr p1_def have b1_i: "v_at b1 = i" unfolding optimal_def valid_def
                      by auto
                    from p'_def p'b' b'v n_def have suc_le_etp: "Suc i \<le> ETP rho (\<tau> rho i + left I)"
                      unfolding optimal_def valid_def
                      apply (auto simp: Let_def split: if_splits)
                      apply (meson add_eq_self_zero i_etp_to_tau lI le_add1 le_antisym not_less_eq_eq)
                      by (meson add_eq_self_zero i_etp_to_tau lI le_neq_implies_less not_add_less1 not_less_eq_eq)
                    have valid_q_before: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil (i+1) ps p))"
                      using p_le_predi valid_shift_VUntil[of i I phi psi ps p] rfin(1) i_props q_val False lI
                      by (auto simp: qr bv prems(8))
                    then have "wqo p' (Inr (VUntil (i+1) ps p))" using p'_def
                      unfolding optimal_def by auto
                    moreover have "checkIncr p'"
                      using p'_def
                      unfolding p'b' b'v
                      by (auto simp: optimal_def intro!: valid_checkIncr_VUntil)
                    moreover have "checkIncr (Inr (VUntil (i + 1) ps p))"
                      using valid_q_before
                      by (auto intro!: valid_checkIncr_VUntil)
                    ultimately have "wqo (Inr (VUntil i vpsis' vphi')) q"
                      using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VUntil (i+1) ps p)"]
                        valid_q_before i_props prems(4) qr bv
                      unfolding p'b' b'v b1_i[symmetric]
                      by (auto simp add: proofIncr_def intro: checkIncr.intros)
                    moreover have comp_in: "(Inr (VUntil i vpsis' vphi')) \<in> set (doUntil i (left I) p1 p2 p')"
                      using Inr b'v p'b' res by auto
                    ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                        until_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                        pw_total[of i "Until phi I psi"] p'b' trans_wqo Inr b'v
                        res prems
                      unfolding b1_i[symmetric]
                      apply (auto simp add: total_on_def)
                      by (metis transpD)
                  qed
                  done
              qed
            qed
          qed
        }
        moreover
        {fix hi' vpsis'
          assume b'v: "b' = VUntil_never (i+1) hi' vpsis'"
          have hi'_def: "hi' = hi"
            using p'_def
            by (auto simp: p'b' b'v optimal_def valid_def hi_def)
          have "wqo minp q"
            using b'v
          proof (cases p1)
            case (Inl a1)
            then show ?thesis
            proof (cases "left I = 0")
              case True
              then have form_min: "minp = p' \<oplus> p2" using b'v Inl minp Inr
                  val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def by (cases p2) (auto simp: min_list_wrt_def)
              then obtain p2' where p2r: "p2 = Inr p2'"
                using True b'v Inl minp Inr val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def
                apply (cases p2; auto simp: min_list_wrt_def split: if_splits)
                by (metis Inl_Inr_False)
              then show ?thesis
                using form_min qr bv Inl p1_def q_val unfolding optimal_def valid_def
                apply (cases ps)
                apply (auto simp add: Let_def True i_etp_to_tau split: if_splits enat.splits)[1]
                subgoal premises prems for y ys
                proof -
                  from vmin form_min p2r have p_val: "valid rho i (Until phi I psi) (p' \<oplus> (Inr p2'))"
                    by auto
                  from p2r b'v p'b' have check_p: "checkApp p' (Inr p2')"
                    using p'_def True
                    unfolding p2r b'v p'b'
                    by (auto simp: optimal_def intro!: valid_checkApp_VUntil_never)
                  from prems have y_val: "valid rho i psi (Inr y)"
                    using q_val True i_props n_def i_ge_etpi[of rho i] unfolding valid_def
                    apply (auto simp: Let_def max_def Cons_eq_append_conv split: if_splits)
                    using Cons_eq_upt_conv by blast
                  have val_q': "valid rho (i + 1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil (i+1) ys p))"
                    using qr bv Inl p1_def q_val i_props n_def check_consistent[OF bfphi]
                      prems
                    unfolding optimal_def valid_def
                    apply (auto simp add: Let_def True i_etp_to_tau split: if_splits)
                    using i_ge_etpi[of rho "s_at a1"] i_ge_etpi[of rho "Suc (s_at a1)"]
                    by (auto simp: max_def add.commute Cons_eq_append_conv Cons_eq_upt_conv split: if_splits)
                  then have q_val2: "valid rho i (Until phi I psi) ((Inr (VUntil (i+1) ys p)) \<oplus> (Inr y))"
                    using q_val prems i_props by auto
                  have check_q: "checkApp (Inr (VUntil (i+1) ys p)) (Inr y)"
                    using val_q' True
                    by (auto intro!: valid_checkApp_VUntil)
                  from p'_def have wqo_p': "wqo p' (Inr (VUntil (i + 1) ys p))"
                    using val_q' unfolding optimal_def by simp
                  moreover have wqo_p2: "wqo p2 (Inr y)" using i_props p2_def y_val
                    unfolding optimal_def by auto
                  ultimately show ?thesis
                    unfolding prems using p'b' b'v p2_def q_val prems p2r unfolding valid_def optimal_def
                    using proofApp_mono[OF check_p check_q wqo_p' wqo_p2[unfolded p2r] p_val q_val2]
                    by auto
                qed
                done
            next
              case False
              then have form: "minp = Inr (VUntil_never i hi' vpsis')"
                using b'v Inl minp Inr filter_nnil unfolding doUntil_def
                by (cases p2) (auto simp: min_list_wrt_def)
              then show ?thesis using qr bv q_val Inl p1_def i_props n_def
                unfolding optimal_def valid_def
                apply (cases ps)
                apply (auto simp add: Let_def False i_etp_to_tau split: if_splits)[1]
                subgoal premises prems
                proof -
                  from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                    unfolding optimal_def by auto
                  from p1_def Inl have p_ni: "\<not> v_at p = s_at a1"
                    using check_consistent[OF bfphi] prems(10-14)
                    unfolding optimal_def valid_def
                    by auto
                  then have p_le_predi: "v_at p \<ge> s_at a1 + 1"
                    using p_bounds prems by auto
                  then have valid_q_before: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil (i+1) ps p))"
                    using prems unfolding valid_def
                    by (auto simp add: le_diff_conv Let_def i_etp_to_tau add.commute)
                  then have "wqo p' (Inr (VUntil (i+1) ps p))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VUntil_never)
                  moreover have "checkIncr (Inr (VUntil (i + 1) ps p))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VUntil)
                  ultimately show ?thesis
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VUntil (i+1) ps p)"]
                      valid_q_before i_props prems(4)
                    unfolding p'b' b'v prems(11)[symmetric]
                    by (auto simp add: proofIncr_def intro: checkIncr.intros)
                qed
                subgoal premises prems for y ys
                proof -
                  from p1_def have a1_i: "s_at a1 = i" using Inl
                    unfolding optimal_def valid_def by auto
                  from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                    unfolding optimal_def by auto
                  from p'_def p'b' b'v n_def have suc_le_etp: "Suc i \<le> ETP rho (\<tau> rho i + left I)"
                    unfolding optimal_def valid_def
                    apply (auto simp: Let_def split: if_splits)
                    apply (meson False add_cancel_left_left etp_to_delta le_add2 le_antisym le_diff_conv2 le_refl not_less_eq_eq)
                    apply (metis False diff_add_inverse diff_is_0_eq' i_etp_to_tau not_less_eq_eq)
                    by (metis False diff_add_inverse diff_is_0_eq' i_etp_to_tau not_less_eq_eq)
                  from p1_def have p_ni: "\<not> v_at p = s_at a1"
                    using check_consistent[OF bfphi] prems
                    unfolding optimal_def valid_def
                    by auto
                  then have p_le_predi: "v_at p \<ge> s_at a1 + 1"
                    using p_bounds prems by auto
                  then have valid_q_before: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil (i+1) ps p))"
                    using prems False i_props p_ni suc_le_etp unfolding valid_def
                    apply (auto simp add: le_diff_conv Let_def i_etp_to_tau i_ltp_to_tau add.commute)
                    apply (simp add: max_def split: if_splits)
                    apply (metis (no_types, lifting) Nat.add_0_right add_diff_inverse_nat diff_is_0_eq i_etp_to_tau less_irrefl_nat nat_le_linear zero_less_diff)
                    using i_etp_to_tau i_ge_etpi i_to_suci_le le_trans by blast
                  then have "wqo p' (Inr (VUntil (i+1) ps p))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VUntil_never)
                  moreover have "checkIncr (Inr (VUntil (i + 1) ps p))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VUntil)
                  ultimately show ?thesis
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VUntil (i+1) ps p)"]
                      valid_q_before i_props prems(3) form qr
                    unfolding p'b' b'v a1_i[symmetric]
                    by (auto simp add: proofIncr_def intro: checkIncr.intros)
                qed
                done
            qed
          next
            case (Inr b1)
            then show ?thesis
            proof (cases "left I = 0")
              case True
              then have form: "minp = Inr (VUntil i [projr p2] b1) \<or> minp = (p' \<oplus> p2)"
                using Inr p'b' b'v minp val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def by (cases p2) (auto simp: min_list_wrt_def)
              then obtain p2' where p2r: "p2 = Inr p2'"
                using p'b' b'v Inr True minp val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def
                by (cases p2; auto simp: min_list_wrt_def split: if_splits)
              then have res: "doUntil i (left I) p1 p2 p' = [Inr (VUntil i [projr p2] b1), (p' \<oplus> p2)]"
                using True Inr p'b' b'v unfolding doUntil_def by auto
              from True q_val qr bv have ps_not_nil: "ps \<noteq> []"
                using n_def unfolding valid_def
                apply (auto simp: Let_def split: if_splits)
                using i_ge_etpi le_trans by blast
              then obtain y and ys where cons_q: "ps = y # ys"
                using qr bv
                by (cases ps; auto)
              then have y_val: "valid rho i psi (Inr y)"
                using q_val qr bv n_def True i_ge_etpi[of rho i] unfolding valid_def
                apply (auto simp: Let_def max_def Cons_eq_append_conv split: if_splits)
                by (metis upt_eq_Cons_conv)
              then have wqo_p2: "wqo (Inr p2') (Inr y)" using p2r p2_def
                unfolding optimal_def by auto
              then show ?thesis
              proof (cases ys)
                case Nil
                then have p_eq_i: "v_at p = i" using True bv qr q_val n_def
                    i_props i_ge_etpi[of rho i]
                  unfolding valid_def
                  apply (auto simp: Let_def max_def split: if_splits)
                  by (metis append.left_neutral list.simps(8) list.simps(9) add_cancel_right_right append1_eq_conv cons_q le_add2 le_antisym upt_eq_Nil_conv)
                then have p_val: "valid rho i phi (Inr p)" using vp
                  by auto
                from wqo_p2 have lcomp: "wqo (Inr p2') (Inr y)"
                  by auto
                moreover have wqo_p1: "wqo (Inr b1) (Inr p)"
                  using Inr p1_def p_val unfolding optimal_def by auto
                ultimately have "wqo (Inr (VUntil i [p2'] b1)) q"
                  using qr bv cons_q VUntil[OF wqo_p1 lcomp] Nil p2r
                  by auto
                moreover have "(Inr (VUntil i [p2'] b1)) \<in> set (doUntil i (left I) p1 p2 p')"
                  using form minp Inr p2r Inr True b'v p'b'
                  unfolding doUntil_def by auto
                ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                    until_sound[OF i_props p1_def p2_def p'_def _ bf bf'] form
                    pw_total[of i "Until phi I psi"] p'b' trans_wqo Inr b'v p2r
                  unfolding proofApp_def
                  apply (auto simp add: total_on_def)
                  by (metis transpD)
              next
                case (Cons a as)
                then have p_ge_suci: "v_at p \<ge> i + 1"
                  using True bv qr q_val n_def i_props cons_q i_ge_etpi[of rho i]
                  unfolding valid_def
                  apply (auto simp: Let_def max_def split: if_splits)
                  using not_less_eq_eq by fastforce
                then have q'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil (i+1) ys p))"
                  using q_val cons_q True qr bv n_def i_props
                  unfolding valid_def
                  apply (auto simp: Let_def max_def i_etp_to_tau True add.commute Cons_eq_append_conv Cons_eq_upt_conv split: if_splits)
                  using i_ge_etpi[of rho "Suc i"] i_ge_etpi[of rho i]
                  by auto
                then have wqo_p': "wqo p' (Inr (VUntil (i+1) ys p))"
                  using p'_def unfolding optimal_def by auto
                have check_q: "checkApp (Inr (VUntil (i+1) ys p)) (Inr y)"
                  using q'_val True
                  by (auto intro!: valid_checkApp_VUntil)
                have check_min: "checkApp p' (Inr p2')" using p2r p'b' b'v
                  using p'_def True
                  unfolding p2r b'v p'b'
                  by (auto simp: optimal_def intro!: valid_checkApp_VUntil_never)
                from res have val_min: "valid rho i (Until phi I psi) (p' \<oplus> (Inr p2'))"
                  using b'v p'b' p2r
                    until_sound[OF i_props p1_def p2_def p'_def _ bf bf']
                  by auto
                from q_val have q_val2: "valid rho i (Until phi I psi) ((Inr (VUntil (i+1) ys p)) \<oplus> (Inr y))"
                  using qr bv cons_q i_props unfolding proofApp_def by auto
                then have "wqo (p' \<oplus> (Inr p2')) q"
                  using qr bv cons_q p'b' b'v i_props
                    proofApp_mono[OF check_min check_q wqo_p' wqo_p2 val_min q_val2]
                  by auto
                moreover have "(p' \<oplus> (Inr p2')) \<in> set (doUntil i (left I) p1 p2 p')"
                  using form minp Inr p2r Inr True b'v p'b'
                  unfolding doUntil_def by auto
                ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                    until_sound[OF i_props p1_def p2_def p'_def _ bf bf'] form
                    pw_total[of i "Until phi I psi"] p'b' trans_wqo Inr b'v p2r
                  unfolding proofApp_def
                  apply (auto simp add: total_on_def)
                  by (metis transpD)
              qed
            next
              case False
              then have lI: "left I \<noteq> 0" by auto
              then have form: "minp = Inr (VUntil i [] b1)
                \<or> minp = Inr (VUntil_never i hi' vpsis')" using Inr p'b' b'v minp
                val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def by (cases p2) (auto simp: min_list_wrt_def)
              from p1_def Inr have b1i: "v_at b1 = i"
                unfolding optimal_def valid_def by auto
              from False Inr p'b' b'v have
                res: "doUntil i (left I) p1 p2 p' = [Inr (VUntil i [] b1), Inr (VUntil_never i hi' vpsis')]"
                unfolding doUntil_def by (cases p2; auto)
              then show ?thesis
              proof (cases "v_at p = i")
                case True
                then have ps_nil: "ps = []" using qr bv q_val n_def False
                  unfolding valid_def
                  apply (auto simp: Let_def max_def split: if_splits)
                  apply (metis add_le_same_cancel1 i_etp_to_tau lI le0 le_antisym le_refl)
                  by (meson add_le_same_cancel1 i_etp_to_tau lI le_0_eq nat_le_linear)
                from True vp have wqo_p1: "wqo (Inr b1) (Inr p)" using p1_def Inr
                  unfolding optimal_def by auto
                then have "wqo (Inr (VUntil i [] b1)) q"
                  using qr bv ps_nil VUntil_Nil[OF wqo_p1] by auto
                moreover have "(Inr (VUntil i [] b1)) \<in> set (doUntil i (left I) p1 p2 p')"
                  using Inr b'v p'b' res by auto
                ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                    until_sound[OF i_props p1_def p2_def p'_def _ bf bf'] form
                    pw_total[of i "Until phi I psi"] p'b' trans_wqo Inr b'v
                  apply (auto simp add: total_on_def)
                  by (metis transpD)
              next
                case False
                then have p_le_predi: "v_at p \<ge> i + 1" using p_bounds by auto
                from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                  unfolding optimal_def by auto
                then show ?thesis using qr bv q_val Inr p1_def i_props n_def
                  unfolding optimal_def valid_def
                  apply (cases ps)
                  apply (auto simp add: Let_def False i_etp_to_tau split: if_splits)[1]
                  subgoal premises prems
                  proof -
                    from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                      unfolding optimal_def by auto
                    then have valid_q_before: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil (i+1) ps p))"
                      using prems unfolding valid_def
                      apply (auto simp add: le_diff_conv Let_def i_etp_to_tau add.commute)
                      using p_le_predi apply linarith
                      using False by linarith
                    then have "wqo p' (Inr (VUntil (i+1) ps p))" using p'_def
                      unfolding optimal_def by auto
                    moreover have "checkIncr p'"
                      using p'_def
                      unfolding p'b' b'v
                      by (auto simp: optimal_def intro!: valid_checkIncr_VUntil_never)
                    moreover have "checkIncr (Inr (VUntil (i + 1) ps p))"
                      using valid_q_before
                      by (auto intro!: valid_checkIncr_VUntil)
                    ultimately  have "wqo (Inr (VUntil_never i hi' vpsis')) q"
                      using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VUntil (i+1) ps p)"]
                        valid_q_before i_props prems(4) qr bv
                      unfolding p'b' b'v prems(11)[symmetric]
                      by (auto simp add: proofIncr_def intro: checkIncr.intros)
                    moreover have comp_in: "(Inr (VUntil_never i hi' vpsis')) \<in> set (doUntil i (left I) p1 p2 p')"
                      using Inr b'v p'b' res by auto
                    ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                        until_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                        pw_total[of i "Until phi I psi"] p'b' trans_wqo Inr b'v
                        res prems
                      unfolding prems(11)[symmetric]
                      apply (auto simp add: total_on_def)
                      by (metis transpD)
                  qed
                  subgoal premises prems for y ys
                  proof -
                    from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                      unfolding optimal_def by auto
                    from Inr p1_def have b1_i: "v_at b1 = i" unfolding optimal_def valid_def
                      by auto
                    from p'_def p'b' b'v n_def have suc_le_etp: "Suc i \<le> ETP rho (\<tau> rho i + left I)"
                      unfolding optimal_def valid_def
                      apply (auto simp: Let_def split: if_splits)
                      apply (meson add_eq_self_zero i_etp_to_tau lI le_add1 le_antisym not_less_eq_eq)
                      apply (meson add_eq_self_zero i_etp_to_tau lI le_neq_implies_less not_add_less1 not_less_eq_eq)
                      by (metis diff_add_inverse diff_is_0_eq' i_etp_to_tau lI not_less_eq_eq)
                    then have valid_q_before: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil (i+1) ps p))"
                      using prems False i_props unfolding valid_def
                      apply (auto simp add: le_diff_conv Let_def i_etp_to_tau i_ltp_to_tau add.commute)
                      apply (simp add: max_def split: if_splits)
                      apply (metis (no_types, lifting) Nat.add_0_right add_diff_inverse_nat diff_is_0_eq i_etp_to_tau less_irrefl_nat nat_le_linear zero_less_diff)
                      by (meson i_etp_to_tau i_ge_etpi i_to_suci_le le_trans)
                    then have "wqo p' (Inr (VUntil (i+1) ps p))" using p'_def
                      unfolding optimal_def by auto
                    moreover have "checkIncr p'"
                      using p'_def
                      unfolding p'b' b'v
                      by (auto simp: optimal_def intro!: valid_checkIncr_VUntil_never)
                    moreover have "checkIncr (Inr (VUntil (i + 1) ps p))"
                      using valid_q_before
                      by (auto intro!: valid_checkIncr_VUntil)
                    ultimately have "wqo (Inr (VUntil_never i hi' vpsis')) q"
                      using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VUntil (i+1) ps p)"]
                        valid_q_before i_props prems(4) qr bv
                      unfolding p'b' b'v b1_i[symmetric]
                      by (auto simp add: proofIncr_def intro: checkIncr.intros)
                    moreover have comp_in: "(Inr (VUntil_never i hi' vpsis')) \<in> set (doUntil i (left I) p1 p2 p')"
                      using Inr b'v p'b' res by auto
                    ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                        until_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                        pw_total[of i "Until phi I psi"] p'b' trans_wqo Inr b'v
                        res prems
                      unfolding b1_i[symmetric]
                      apply (auto simp add: total_on_def)
                      by (metis transpD)
                  qed
                  done
              qed
            qed
          qed
        }
        ultimately show ?thesis by auto
      qed
    }
    moreover
    {fix hi' ps
      assume bv: "b = VUntil_never i hi' ps"
      have hi'_def: "hi' = hi"
        using q_val
        by (auto simp: Inr bv valid_def hi)
      have "wqo minp q"
        using bv
      proof (cases p')
        case (Inl a')
        then obtain p1' ps' where a's: "a' = SUntil ps' p1'"
          using p'_def
          unfolding optimal_def valid_def
          by (cases a') auto
        from a's Inl have "LTP rho (\<tau> rho i + n) \<ge> s_at p1'
        \<and> s_at p1' > i" using p'_def i_props mem_imp_le_ltp_u[of i I "s_at p1'" n]
          n_def
          unfolding optimal_def valid_def
          by (auto simp: Let_def)
        then have sp1'_bounds: "LTP rho (\<tau> rho i + n) \<ge> s_at p1'
        \<and> s_at p1' > i \<and> s_at p1' \<ge> ETP rho (\<tau> rho i + left I)"
          using a's Inl p'_def i_props mem_imp_ge_etp_u[of i I "s_at p1'" n] n_def
          unfolding optimal_def valid_def
          by (auto simp: Let_def)
        from bv qr have mapt: "map v_at ps = [lu rho i I  ..< Suc (LTP rho (\<tau> rho i + n))]"
          using q_val n_def unfolding valid_def by (auto simp: Let_def)
        then have ps_check: "\<forall>p \<in> set ps. v_check rho psi p"
          using bv qr q_val n_def unfolding valid_def
          by (auto simp: Let_def)
        then have jc: "\<forall>j \<in> set (map v_at ps). \<exists>p. v_at p = j \<and> v_check rho psi p"
          using map_set_in_imp_set_in[OF ps_check] by auto
        from sp1'_bounds have p1'_in: "s_at p1' \<in> set (map v_at ps)" using mapt
          by auto
        from a's Inl have "s_check rho psi p1'" using p'_def
          unfolding optimal_def valid_def by (auto simp: Let_def)
        then have False using jc p1'_in check_consistent[OF bfpsi] by auto
        then show ?thesis by auto
      next
        case (Inr b')
        then have p'b': "p' = Inr b'" by auto
        then have b'v: "(\<exists>p ps. b' = VUntil (i+1) ps p)
        \<or> (\<exists>ps. b' = VUntil_never (i+1) hi ps)"
          using Inr p'_def n_def i_props
          unfolding optimal_def valid_def by (cases b') (auto simp: Let_def hi add.commute)
        moreover
        {fix vphi' vpsis'
          assume b'v: "b' = VUntil (i+1) vpsis' vphi'"
          then have "wqo minp q"
          proof (cases p1)
            case (Inl a1)
            then show ?thesis
            proof (cases "left I = 0")
              case True
              then have form_min: "minp = p' \<oplus> p2" using b'v Inl minp Inr
                  val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def by (cases p2) (auto simp: min_list_wrt_def)
              then obtain p2' where p2r: "p2 = Inr p2'"
                using True b'v Inl minp Inr val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def
                apply (cases p2; auto simp: min_list_wrt_def split: if_splits)
                by (metis Inl_Inr_False)
              then show ?thesis
                using form_min qr bv Inl p1_def q_val n_def
                unfolding optimal_def valid_def
                apply (cases ps)
                apply (auto simp add: Let_def True i_le_ltpi_add i_etp_to_tau split: if_splits)
                subgoal premises prems for y ys
                proof -
                  from vmin form_min p2r have p_val: "valid rho i (Until phi I psi) (p' \<oplus> (Inr p2'))"
                    by auto
                  from p2r b'v p'b' have check_p: "checkApp p' (Inr p2')"
                    using p'_def True
                    unfolding p2r b'v p'b'
                    by (auto simp: optimal_def intro!: valid_checkApp_VUntil)
                  from prems have y_val: "valid rho i psi (Inr y)"
                    using q_val True i_ge_etpi[of rho "s_at a1"] i_props unfolding valid_def
                    apply (auto simp: Let_def split: if_splits)
                    apply (auto simp add: max_def Cons_eq_append_conv split: if_splits)
                    using Cons_eq_upt_conv by blast
                  have val_q': "valid rho (i + 1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil_never (i+1) hi' ys))"
                    using valid_shift_VUntil_never[of i I phi psi hi' ps] rfin(1) i_props q_val
                    by (auto simp: True prems(2) qr bv)
                  then have q_val2: "valid rho i (Until phi I psi) ((Inr (VUntil_never (i+1) hi' ys)) \<oplus> (Inr y))"
                    using q_val prems i_props by auto
                  have check_q: "checkApp (Inr (VUntil_never (i+1) hi' ys)) (Inr y)"
                    using val_q' True
                    by (auto intro!: valid_checkApp_VUntil_never)
                  from p'_def have wqo_p': "wqo p' (Inr (VUntil_never (i + 1) hi' ys))"
                    using val_q' unfolding optimal_def by simp
                  moreover have wqo_p2: "wqo p2 (Inr y)" using i_props p2_def y_val
                    unfolding optimal_def by auto
                  ultimately show ?thesis
                    unfolding prems using p'b' b'v p2_def q_val prems p2r unfolding valid_def optimal_def
                    using proofApp_mono[OF check_p check_q wqo_p' wqo_p2[unfolded p2r] p_val q_val2]
                    by auto
                qed
                done
            next
              case False
              from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                unfolding optimal_def by auto
              from False have form_min: "minp = Inr (VUntil i vpsis' vphi')"
                using b'v Inl minp Inr filter_nnil unfolding doUntil_def
                by (cases p2) (auto simp: min_list_wrt_def)
              then show ?thesis using qr bv q_val i_props n_def
                unfolding optimal_def valid_def
                apply (cases ps)
                apply (auto simp add: Let_def False i_le_ltpi_add split: if_splits)[1]
                subgoal premises prems
                proof -
                  have valid_q_before: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil_never (i+1) hi' ps))"
                    using valid_shift_VUntil_never[of i I phi psi hi' ps] rfin(1) i_props q_val False
                    by (auto simp: prems(2) qr bv)
                  then have "wqo p' (Inr (VUntil_never (i+1) hi' ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VUntil)
                  moreover have "checkIncr (Inr (VUntil_never (i + 1) hi' ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VUntil_never)
                  ultimately show ?thesis
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VUntil_never (i+1) hi' ps)"]
                      valid_q_before i_props prems(3)
                    unfolding p'b' b'v
                    by (auto simp add: proofIncr_def hi'_def hi n_def intro: checkIncr.intros)
                qed
                subgoal premises prems for y ys
                proof -
                  from p1_def have a1_i: "s_at a1 = i" using Inl
                    unfolding optimal_def valid_def by auto
                  from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                    unfolding optimal_def by auto
                  from p'_def p'b' b'v n_def have suc_le_etp: "Suc i \<le> ETP rho (\<tau> rho i + left I)"
                    unfolding optimal_def valid_def
                    apply (auto simp: Let_def split: if_splits)
                    apply (meson False add_cancel_left_left etp_to_delta le_add2 le_antisym le_diff_conv2 le_refl not_less_eq_eq)
                    by (metis False diff_add_inverse diff_is_0_eq' i_etp_to_tau not_less_eq_eq)
                  then have valid_q_before: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil_never (i+1) hi' ps))"
                    using valid_shift_VUntil_never[of i I phi psi hi' ps] rfin(1) i_props q_val False
                    by (auto simp: qr bv)
                  then have "wqo p' (Inr (VUntil_never (i+1) hi' ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VUntil)
                  moreover have "checkIncr (Inr (VUntil_never (i + 1) hi' ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VUntil_never)
                  ultimately show ?thesis
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VUntil_never (i+1) hi' ps)"]
                      valid_q_before i_props prems(3) form_min qr
                    unfolding p'b' b'v a1_i[symmetric]
                    by (auto simp add: proofIncr_def intro: checkIncr.intros)
                qed
                done
            qed
          next
            case (Inr b1)
            then show ?thesis
            proof (cases "left I = 0")
              case True
              then have form: "minp = Inr (VUntil i [projr p2] b1) \<or> minp = (p' \<oplus> p2)"
                using Inr p'b' b'v minp val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def by (cases p2) (auto simp: min_list_wrt_def)
              then obtain p2' where p2r: "p2 = Inr p2'"
                using p'b' b'v Inr True minp val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def
                by (cases p2; auto simp: min_list_wrt_def split: if_splits)
              then have res: "doUntil i (left I) p1 p2 p' = [Inr (VUntil i [projr p2] b1), (p' \<oplus> p2)]"
                using True Inr p'b' b'v unfolding doUntil_def by auto
              from True q_val qr bv have ps_not_nil: "ps \<noteq> []"
                using n_def i_le_ltpi_add unfolding valid_def
                by (auto simp: Let_def i_etp_to_tau split: if_splits)
              then obtain y and ys where cons_q: "ps = y # ys"
                using qr bv
                by (cases ps; auto)
              then have y_val: "valid rho i psi (Inr y)"
                using q_val qr bv n_def True i_ge_etpi[of rho i] unfolding valid_def
                apply (auto simp: Let_def max_def Cons_eq_append_conv split: if_splits)
                by (metis upt_eq_Cons_conv)
              then have wqo_p2: "wqo (Inr p2') (Inr y)" using p2r p2_def
                unfolding optimal_def by auto
              then have q'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil_never (i+1) hi' ys))"
                using valid_shift_VUntil_never[of i I phi psi hi' ps] rfin(1) i_props q_val
                by (auto simp: True qr bv cons_q)
              then have wqo_p': "wqo p' (Inr (VUntil_never (i+1) hi' ys))"
                using p'_def unfolding optimal_def by auto
              have check_q: "checkApp (Inr (VUntil_never (i+1) hi' ys)) (Inr y)"
                using q'_val True
                by (auto intro!: valid_checkApp_VUntil_never)
              have check_min: "checkApp p' (Inr p2')" using p2r p'b' b'v
                using p'_def True
                unfolding p2r b'v p'b'
                by (auto simp: optimal_def intro!: valid_checkApp_VUntil)
              from res have val_min: "valid rho i (Until phi I psi) (p' \<oplus> (Inr p2'))"
                using b'v p'b' p2r
                  until_sound[OF i_props p1_def p2_def p'_def _ bf bf']
                by auto
              from q_val have q_val2: "valid rho i (Until phi I psi) ((Inr (VUntil_never (i+1) hi' ys)) \<oplus> (Inr y))"
                using qr bv cons_q i_props unfolding proofApp_def by auto
              then have "wqo (p' \<oplus> (Inr p2')) q"
                using qr bv cons_q p'b' b'v i_props
                  proofApp_mono[OF check_min check_q wqo_p' wqo_p2 val_min q_val2]
                by auto
              moreover have "(p' \<oplus> (Inr p2')) \<in> set (doUntil i (left I) p1 p2 p')"
                using form minp Inr p2r Inr True b'v p'b'
                unfolding doUntil_def by auto
              ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                  until_sound[OF i_props p1_def p2_def p'_def _ bf bf'] form
                  pw_total[of i "Until phi I psi"] p'b' trans_wqo Inr b'v p2r
                unfolding proofApp_def
                apply (auto simp add: total_on_def)
                by (metis transpD)
            next
              case False
              from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                unfolding optimal_def by auto
              from False have form: "minp = Inr (VUntil i [] b1)
              \<or> minp = Inr (VUntil i vpsis' vphi')" using Inr p'b' b'v minp
                val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def by (cases p2) (auto simp: min_list_wrt_def)
              then have res: "doUntil i (left I) p1 p2 p' = [Inr (VUntil i [] b1), Inr (VUntil i vpsis' vphi')]"
                using False Inr p'b' b'v unfolding doUntil_def by (cases p2; auto)
              then show ?thesis using qr bv q_val Inr p1_def i_props n_def
                unfolding optimal_def valid_def
                apply (cases ps)
                apply (auto simp add: Let_def False i_le_ltpi_add split: if_splits)[1]
                subgoal premises prems
                proof -
                  from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                    unfolding optimal_def by auto
                  then have valid_q_before: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil_never (i+1) hi' ps))"
                    using valid_shift_VUntil_never[of i I phi psi hi' ps] rfin(1) i_props q_val False
                    by (auto simp: prems(2) qr bv)
                  then have "wqo p' (Inr (VUntil_never (i+1) hi' ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VUntil)
                  moreover have "checkIncr (Inr (VUntil_never (i + 1) hi' ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VUntil_never)
                  ultimately have "wqo (Inr (VUntil i vpsis' vphi')) q"
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VUntil_never (i+1) hi' ps)"]
                      valid_q_before i_props prems(4) qr bv
                    unfolding p'b' b'v
                    by (auto simp add: proofIncr_def intro: checkIncr.intros)
                  moreover have comp_in: "(Inr (VUntil i vpsis' vphi')) \<in> set (doUntil i (left I) p1 p2 p')"
                    using Inr b'v p'b' res by auto
                  ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                      until_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                      pw_total[of i "Until phi I psi"] p'b' trans_wqo Inr b'v
                      res prems
                    unfolding prems(11)[symmetric]
                    apply (auto simp add: total_on_def)
                    by (metis transpD)
                qed
                subgoal premises prems for y ys
                proof -
                  from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                    unfolding optimal_def by auto
                  from Inr p1_def have b1_i: "v_at b1 = i" unfolding optimal_def valid_def
                    by auto
                  from p'_def p'b' b'v n_def have suc_le_etp: "Suc i \<le> ETP rho (\<tau> rho i + left I)"
                    unfolding optimal_def valid_def
                    apply (auto simp: Let_def split: if_splits)
                    apply (meson add_eq_self_zero i_etp_to_tau False le_add1 le_antisym not_less_eq_eq)
                    by (meson add_eq_self_zero i_etp_to_tau False le_neq_implies_less not_add_less1 not_less_eq_eq)
                  then have valid_q_before: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil_never (i+1) hi' ps))"
                    using valid_shift_VUntil_never[of i I phi psi hi' ps] rfin(1) i_props q_val False
                    by (auto simp: qr bv)
                  then have "wqo p' (Inr (VUntil_never (i+1) hi' ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VUntil)
                  moreover have "checkIncr (Inr (VUntil_never (i + 1) hi' ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VUntil_never)
                  ultimately have "wqo (Inr (VUntil i vpsis' vphi')) q"
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VUntil_never (i+1) hi' ps)"]
                      valid_q_before i_props prems(4) qr bv
                    unfolding p'b' b'v b1_i[symmetric]
                    by (auto simp add: proofIncr_def intro: checkIncr.intros)
                  moreover have comp_in: "(Inr (VUntil i vpsis' vphi')) \<in> set (doUntil i (left I) p1 p2 p')"
                    using Inr b'v p'b' res by auto
                  ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                      until_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                      pw_total[of i "Until phi I psi"] p'b' trans_wqo Inr b'v
                      res prems
                    unfolding b1_i[symmetric]
                    apply (auto simp add: total_on_def)
                    by (metis transpD)
                qed
                done
            qed
          qed
        }
        moreover
        {fix hi'' vpsis'
          assume b'v: "b' = VUntil_never (i+1) hi'' vpsis'"
          have hi''_def: "hi'' = hi"
            using p'_def rfin
            by (auto simp: Inr b'v optimal_def valid_def hi_def)
          have "wqo minp q"
            using b'v
          proof (cases p1)
            case (Inl a1)
            then show ?thesis
            proof (cases "left I = 0")
              case True
              then have form_min: "minp = p' \<oplus> p2" using Inl b'v p'b' minp
                  val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def by (cases p2) (auto simp: min_list_wrt_def)
              then obtain p2' where p2r: "p2 = Inr p2'"
                using True b'v Inl minp Inr val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def
                apply (cases p2; auto simp: min_list_wrt_def split: if_splits)
                by (metis Inl_Inr_False)
              then show ?thesis
                using form_min qr bv Inl p1_def q_val n_def unfolding optimal_def valid_def
                apply (cases ps)
                apply (auto simp add: Let_def True i_etp_to_tau i_le_ltpi_add split: if_splits enat.splits)[1]
                subgoal premises prems for y ys
                proof -
                  from vmin form_min p2r have p_val: "valid rho i (Until phi I psi) (p' \<oplus> (Inr p2'))"
                    by auto
                  from p2r b'v p'b' have check_p: "checkApp p' (Inr p2')"
                    using p'_def True
                    unfolding p2r b'v p'b'
                    by (auto simp: optimal_def intro!: valid_checkApp_VUntil_never)
                  from prems have y_val: "valid rho i psi (Inr y)"
                    using q_val True i_ge_etpi[of rho "s_at a1"] i_props unfolding valid_def
                    apply (auto simp: Let_def split: if_splits)
                    apply (auto simp add: max_def Cons_eq_append_conv split: if_splits)
                    using Cons_eq_upt_conv by blast
                  have val_q': "valid rho (i + 1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil_never (i+1) hi' ys))"
                    using valid_shift_VUntil_never[of i I phi psi hi' ps] rfin(1) i_props q_val
                    by (auto simp: True prems(9) qr bv)
                  then have q_val2: "valid rho i (Until phi I psi) ((Inr (VUntil_never (i+1) hi' ys)) \<oplus> (Inr y))"
                    using q_val prems i_props by auto
                  have check_q: "checkApp (Inr (VUntil_never (i+1) hi' ys)) (Inr y)"
                    using val_q' True
                    by (auto intro!: valid_checkApp_VUntil_never)
                  from p'_def have wqo_p': "wqo p' (Inr (VUntil_never (i + 1) hi' ys))"
                    using val_q' unfolding optimal_def by simp
                  moreover have wqo_p2: "wqo p2 (Inr y)" using i_props p2_def y_val
                    unfolding optimal_def by auto
                  ultimately show ?thesis
                    unfolding prems using p'b' b'v p2_def q_val prems p2r unfolding valid_def optimal_def
                    using proofApp_mono[OF check_p check_q wqo_p' wqo_p2[unfolded p2r] p_val q_val2]
                    by auto
                qed
                done
            next
              case False
              from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                unfolding optimal_def by auto
              from False have form_min: "minp = Inr (VUntil_never i hi' vpsis')"
                using b'v Inl minp Inr filter_nnil unfolding doUntil_def
                by (cases p2) (auto simp: min_list_wrt_def hi''_def hi'_def)
              then show ?thesis using qr bv q_val i_props n_def
                unfolding optimal_def valid_def
                apply (cases ps)
                apply (auto simp add: Let_def False i_le_ltpi_add split: if_splits)[1]
                subgoal premises prems
                proof -
                  have valid_q_before: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil_never (i+1) hi' ps))"
                    using prems
                    unfolding valid_def
                    by (auto simp add: add.commute le_diff_conv Let_def i_etp_to_tau split: if_splits)
                  then have "wqo p' (Inr (VUntil_never (i+1) hi' ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VUntil_never)
                  moreover have "checkIncr (Inr (VUntil_never (i + 1) hi' ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VUntil_never)
                  ultimately show ?thesis
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VUntil_never (i+1) hi' ps)"]
                      valid_q_before i_props prems(3)
                    unfolding p'b' b'v
                    by (auto simp add: proofIncr_def hi hi'_def hi''_def n_def intro: checkIncr.intros)
                qed
                subgoal premises prems for y ys
                proof -
                  from p1_def have a1_i: "s_at a1 = i" using Inl
                    unfolding optimal_def valid_def by auto
                  from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                    unfolding optimal_def by auto
                  from p'_def p'b' b'v n_def have suc_le_etp: "Suc i \<le> ETP rho (\<tau> rho i + left I)"
                    unfolding optimal_def valid_def
                    apply (auto simp: Let_def split: if_splits)
                    apply (meson False add_cancel_left_left etp_to_delta le_add2 le_antisym le_diff_conv2 le_refl not_less_eq_eq)
                    using i_le_ltpi_add apply blast
                    by (metis False diff_add_inverse diff_is_0_eq' i_etp_to_tau not_less_eq_eq)
                  then have valid_q_before: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil_never (i+1) hi' ps))"
                    using valid_shift_VUntil_never[of i I phi psi hi' ps] rfin(1) i_props q_val False
                    by (auto simp: qr bv)
                  then have "wqo p' (Inr (VUntil_never (i+1) hi' ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VUntil_never)
                  moreover have "checkIncr (Inr (VUntil_never (i + 1) hi' ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VUntil_never)
                  ultimately show ?thesis
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VUntil_never (i+1) hi' ps)"]
                      valid_q_before i_props prems(3) form_min qr
                    unfolding p'b' b'v a1_i[symmetric]
                    by (auto simp add: proofIncr_def hi'_def hi''_def intro: checkIncr.intros)
                qed
                done
            qed
          next
            case (Inr b1)
            then show ?thesis
            proof (cases "left I = 0")
              case True
              then have form: "minp = Inr (VUntil i [projr p2] b1) \<or> minp =  (p' \<oplus> p2)"
                using Inr p'b' b'v minp val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def by (cases p2) (auto simp: min_list_wrt_def)
              then obtain p2' where p2r: "p2 = Inr p2'"
                using p'b' b'v Inr True minp val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def
                by (cases p2; auto simp: min_list_wrt_def split: if_splits)
              then have res: "doUntil i (left I) p1 p2 p' = [Inr (VUntil i [projr p2] b1), (p' \<oplus> p2)]"
                using True Inr p'b' b'v unfolding doUntil_def by auto
              from True q_val qr bv have ps_not_nil: "ps \<noteq> []"
                using n_def i_le_ltpi_add unfolding valid_def
                by (auto simp: Let_def i_etp_to_tau split: if_splits)
              then obtain y and ys where cons_q: "ps = y # ys"
                using qr bv
                by (cases ps; auto)
              then have y_val: "valid rho i psi (Inr y)"
                using q_val qr bv n_def True i_ge_etpi[of rho i] unfolding valid_def
                apply (auto simp: Let_def max_def Cons_eq_append_conv split: if_splits)
                by (metis upt_eq_Cons_conv)
              then have wqo_p2: "wqo (Inr p2') (Inr y)" using p2r p2_def
                unfolding optimal_def by auto
              then have q'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil_never (i+1) hi' ys))"
                using valid_shift_VUntil_never[of i I phi psi hi' ps] rfin(1) i_props q_val
                by (auto simp: True qr bv cons_q)
              then have wqo_p': "wqo p' (Inr (VUntil_never (i+1) hi' ys))"
                using p'_def unfolding optimal_def by auto
              have check_q: "checkApp (Inr (VUntil_never (i+1) hi' ys)) (Inr y)"
                using q'_val True
                by (auto intro!: valid_checkApp_VUntil_never)
              have check_min: "checkApp p' (Inr p2')" using p2r p'b' b'v
                using p'_def True
                unfolding p2r b'v p'b'
                by (auto simp: optimal_def intro!: valid_checkApp_VUntil_never)
              from res have val_min: "valid rho i (Until phi I psi) (p' \<oplus> (Inr p2'))"
                using b'v p'b' p2r
                  until_sound[OF i_props p1_def p2_def p'_def _ bf bf']
                by auto
              from q_val have q_val2: "valid rho i (Until phi I psi) ((Inr (VUntil_never (i+1) hi' ys)) \<oplus> (Inr y))"
                using qr bv cons_q i_props unfolding proofApp_def by auto
              then have "wqo (p' \<oplus> (Inr p2')) q"
                using qr bv cons_q p'b' b'v i_props
                  proofApp_mono[OF check_min check_q wqo_p' wqo_p2 val_min q_val2]
                by auto
              moreover have "(p' \<oplus> (Inr p2')) \<in> set (doUntil i (left I) p1 p2 p')"
                using form minp Inr p2r Inr True b'v p'b'
                unfolding doUntil_def by auto
              ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                  until_sound[OF i_props p1_def p2_def p'_def _ bf bf'] form
                  pw_total[of i "Until phi I psi"] p'b' trans_wqo Inr b'v p2r
                unfolding proofApp_def
                apply (auto simp add: total_on_def)
                by (metis transpD)
            next
              case False
              from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                unfolding optimal_def by auto
              from False have form: "minp = Inr (VUntil i [] b1)
              \<or> minp = Inr (VUntil_never i hi' vpsis')" using Inr p'b' b'v minp
                val_VIO_imp_r[OF bf vmin VIO] filter_nnil
                unfolding doUntil_def by (cases p2) (auto simp: min_list_wrt_def hi'_def hi''_def)
              then have res: "doUntil i (left I) p1 p2 p' = [Inr (VUntil i [] b1), Inr (VUntil_never i hi' vpsis')]"
                using False Inr p'b' b'v unfolding doUntil_def by (cases p2; auto simp: hi'_def hi''_def)
              then show ?thesis using qr bv q_val Inr p1_def i_props n_def
                unfolding optimal_def valid_def
                apply (cases ps)
                apply (auto simp add: Let_def False i_le_ltpi_add split: if_splits)[1]
                subgoal premises prems
                proof -
                  from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                    unfolding optimal_def by auto
                  then have valid_q_before: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil_never (i+1) hi' ps))"
                    using valid_shift_VUntil_never[of i I phi psi hi' ps] rfin(1) i_props q_val False
                    by (auto simp: prems(9) qr bv)
                  then have "wqo p' (Inr (VUntil_never (i+1) hi' ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VUntil_never)
                  moreover have "checkIncr (Inr (VUntil_never (i + 1) hi' ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VUntil_never)
                  ultimately  have "wqo (Inr (VUntil_never i hi' vpsis')) q"
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VUntil_never (i+1) hi' ps)"]
                      valid_q_before i_props prems(4) qr bv
                    unfolding p'b' b'v
                    by (auto simp add: proofIncr_def hi'_def hi''_def intro: checkIncr.intros)
                  moreover have comp_in: "(Inr (VUntil_never i hi' vpsis')) \<in> set (doUntil i (left I) p1 p2 p')"
                    using Inr b'v p'b' res by auto
                  ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                      until_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                      pw_total[of i "Until phi I psi"] p'b' trans_wqo Inr b'v
                      res prems
                    unfolding prems(11)[symmetric]
                    apply (auto simp add: total_on_def)
                    by (metis transpD)
                qed
                subgoal premises prems for y ys
                proof -
                  from p'_def have p'_val: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) p'"
                    unfolding optimal_def by auto
                  from Inr p1_def have b1_i: "v_at b1 = i" unfolding optimal_def valid_def
                    by auto
                  from p'_def p'b' b'v n_def have suc_le_etp: "Suc i \<le> ETP rho (\<tau> rho i + left I)"
                    unfolding optimal_def valid_def
                    apply (auto simp: Let_def i_le_ltpi_add split: if_splits)
                    apply (meson add_eq_self_zero i_etp_to_tau False le_add1 le_antisym not_less_eq_eq)
                    by (meson add_eq_self_zero i_etp_to_tau False le_neq_implies_less not_add_less1 not_less_eq_eq)
                  then have valid_q_before: "valid rho (i+1) (Until phi (subtract (\<Delta> rho (i+1)) I) psi) (Inr (VUntil_never (i+1) hi' ps))"
                    using valid_shift_VUntil_never[of i I phi psi hi' ps] rfin(1) i_props q_val False
                    by (auto simp: prems(9) qr bv)
                  then have "wqo p' (Inr (VUntil_never (i+1) hi' ps))" using p'_def
                    unfolding optimal_def by auto
                  moreover have "checkIncr p'"
                    using p'_def
                    unfolding p'b' b'v
                    by (auto simp: optimal_def intro!: valid_checkIncr_VUntil_never)
                  moreover have "checkIncr (Inr (VUntil_never (i + 1) hi' ps))"
                    using valid_q_before
                    by (auto intro!: valid_checkIncr_VUntil_never)
                  ultimately have "wqo (Inr (VUntil_never i hi' vpsis')) q"
                    using proofIncr_mono[OF _ _ _ p'_val, of "Inr (VUntil_never (i+1) hi' ps)"]
                      valid_q_before i_props prems(4) qr bv
                    unfolding p'b' b'v b1_i[symmetric]
                    by (auto simp add: proofIncr_def hi hi'_def hi''_def intro: checkIncr.intros)
                  moreover have comp_in: "(Inr (VUntil_never i hi' vpsis')) \<in> set (doUntil i (left I) p1 p2 p')"
                    using Inr b'v p'b' res by auto
                  ultimately show ?thesis using minp min_list_wrt_le[OF total_set refl_wqo]
                      until_sound[OF i_props p1_def p2_def p'_def comp_in bf bf'] form
                      pw_total[of i "Until phi I psi"] p'b' trans_wqo Inr b'v
                      res prems
                    unfolding b1_i[symmetric]
                    apply (auto simp add: total_on_def)
                    by (metis transpD)
                qed
                done
            qed
          qed
        }
        ultimately show ?thesis by auto
      qed
    }
    ultimately show ?thesis by auto
  qed
  then show False using q_le by auto
qed

lemma neg_sound:
  assumes p'_opt: "optimal i phi (Opt i phi)" and
    p_def: "p \<in> set (Cand i (Neg phi))"
  shows "valid rho i (Neg phi) p"
proof -
  define p1 where p1_def: "p1 = Opt i phi"
  then show ?thesis
  proof (cases p1)
    case (Inl a)
    then have "SAT rho i phi" using p1_def p'_opt check_sound(1)[of _ phi a]
      unfolding optimal_def valid_def by auto
    then show ?thesis using p1_def p'_opt Inl p_def
      unfolding optimal_def valid_def
      by (auto simp: sum.case_eq_if Let_def isl_def split: if_splits)
  next
    case (Inr b)
    then have "VIO rho i phi" using p1_def p'_opt check_sound(2)[of rho phi b]
      unfolding optimal_def valid_def by auto
    then show ?thesis using p1_def p'_opt Inr p_def
      unfolding optimal_def valid_def
      by (auto simp: sum.case_eq_if Let_def isl_def split: if_splits)
  qed
qed

lemma neg_optimal:
  assumes p'_opt: "optimal i phi (Opt i phi)" and bf: "bounded_future (Neg phi)"
  shows "optimal i (Neg phi) (min_list_wrt wqo (Cand i (Neg phi)))"
proof (rule ccontr)
  assume nopt: "\<not> optimal i (Neg phi) (min_list_wrt wqo (Cand i (Neg phi)))"
  define p1 where p1_def: "p1 = Opt i phi"
  define minp where minp: "minp = min_list_wrt wqo (Cand i (Neg phi))"
  from bf have bfphi: "bounded_future phi" by auto
  have nnil: "Cand i (Neg phi) \<noteq> []"
    by (auto simp: Let_def)
  from pw_total[of i "Neg phi"]
  have total_set: "total_on wqo (set (Cand i (Neg phi)))"
    using neg_sound[OF p'_opt]
    by (metis not_wqo total_onI)
  have filter_nnil: "filter (\<lambda>x. \<forall>y \<in> set (Cand i (Neg phi)). wqo x y) (Cand i (Neg phi)) \<noteq> []"
    using refl_total_transp_imp_ex_min[OF nnil refl_wqo total_set trans_wqo]
      filter_empty_conv[of "(\<lambda>x. \<forall>y \<in> set (Cand i (Neg phi)). wqo x y)" "(Cand i (Neg phi))"]
    by simp
  from neg_sound[OF p'_opt min_list_wrt_in, of wqo] total_set refl_wqo trans_wqo
    nnil minp
  have vmin: "valid rho i (Neg phi) minp"
    by auto
  then obtain q where q_val: "valid rho i (Neg phi) q" and q_le: "\<not> wqo minp q"
    using minp nopt unfolding optimal_def by auto
  then show False
  proof (cases q)
    case (Inl a)
    then obtain a' where a'_val: "valid rho i phi (Inr a')" and a'_def: "a = SNeg a'"
      using q_val unfolding valid_def by (cases a; auto)
    from p'_opt p1_def have p1_val: "valid rho i phi p1" unfolding optimal_def
      by auto
    from a'_val have "VIO rho i phi" using check_sound(2)[of rho phi a']
      unfolding valid_def by auto
    then obtain p1' where p1'_def: "p1 = Inr p1'" using val_VIO_imp_r[OF bfphi p1_val]
      by auto
    then have "wqo (Inr p1') (Inr a')" using p'_opt p1_def a'_val
      unfolding optimal_def by auto
    then show ?thesis using q_le Inl minp p1_def SNeg p1'_def a'_def filter_nnil
        min_list_wrt_in[OF nnil total_set refl_wqo trans_wqo]
      by (auto simp: Let_def isl_def split: if_splits)
  next
    case (Inr b)
    then obtain b' where a'_val: "valid rho i phi (Inl b')" and a'_def: "b = VNeg b'"
      using q_val unfolding valid_def by (cases b; auto)
    from p'_opt p1_def have p1_val: "valid rho i phi p1" unfolding optimal_def
      by auto
    from a'_val have "SAT rho i phi" using check_sound(1)[of rho phi b']
      unfolding valid_def by auto
    then obtain p1' where p1'_def: "p1 = Inl p1'" using val_SAT_imp_l[OF bfphi p1_val]
      by auto
    then have "wqo (Inl p1') (Inl b')" using p'_opt p1_def a'_val
      unfolding optimal_def by auto
    then show ?thesis using q_le Inr minp p'_opt vmin p1_def
        VNeg p1'_def a'_def min_list_wrt_in[OF nnil total_set refl_wqo trans_wqo]
      unfolding valid_def
      apply (auto simp: Let_def isl_def split: if_splits)
      by metis
  qed
qed

lemma s_check_AtomE[elim]:
  "s_check rho (Atom x) p \<Longrightarrow> (\<And>i. p = SAtm x i \<Longrightarrow> x \<in> \<Gamma> rho i \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases p) auto

lemma s_check_PrevE[elim]:
  "s_check rho (Prev I \<phi>) p \<Longrightarrow>
     (\<And>q. s_at p > 0 \<Longrightarrow> p = SPrev q \<Longrightarrow> s_check rho \<phi> q \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases p) (auto simp: Let_def)

lemma s_check_SinceE[elim]:
  "s_check rho (Since phi I psi) p \<Longrightarrow>
     (\<And>q qs. p = SSince q qs \<Longrightarrow> s_check rho psi q \<Longrightarrow> list_all (s_check rho phi) qs \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases p) (auto simp: Let_def list.pred_set)

thm Cand_Opt.induct(1)
thm Cand_Opt.induct(2)

theorem alg_optimal:
  "bounded_future phi \<Longrightarrow> optimal i phi (Opt i phi)"
proof (induction i phi rule: Cand_Opt.induct(2)[where P = "\<lambda>i phi. bounded_future phi \<longrightarrow>
  (\<forall>x \<in> set (Cand i phi). valid rho i phi x) \<and>
  (\<exists>x \<in> set (Cand i phi). optimal i phi x)",
      case_names TT FF Atom Disj Conj Impl Iff Neg Prev Next Since Until (*MatchP MatchF*) Opt])
  case (TT i)
  then show ?case unfolding optimal_def valid_def
    by (auto simp: refl_wqo[unfolded reflp_def] s_check.simps
        split: sum.splits sproof.splits vproof.splits)
next
  case (FF i)
  then show ?case unfolding optimal_def valid_def
    by (auto simp: refl_wqo[unfolded reflp_def] s_check.simps
        split: sum.splits sproof.splits vproof.splits)
next
  case (Atom i x)
  then show ?case unfolding optimal_def valid_def
    by (cases "x \<in> \<Gamma> rho i"; auto simp: refl_wqo[unfolded reflp_def]
        split: sum.splits vproof.splits)
next
  note Opt.simps[simp del]
  case (Neg i phi')
  then show ?case using NegBF[of phi'] neg_sound[OF Neg] neg_optimal[OF Neg]
    unfolding valid_def
    by (auto simp: min_list_wrt_def Let_def VNeg optimal_def SNeg)
next
  note Opt.simps[simp del]
  case (Disj i phi' psi)
  then have "doDisj (Opt i phi') (Opt i psi) \<noteq> []"
    unfolding doDisj_def
    apply auto
    by (metis (mono_tags, lifting) List.list.distinct(1) Sum_Type.sum.case_eq_if)
  then show ?case
    using Disj trans_wqo refl_wqo pw_total
    apply (auto intro!: bexI[OF _ min_list_wrt_in] disj_optimal disj_sound)
    using disj_sound not_wqo total_on_def
    by fastforce
next
  note Opt.simps[simp del]
  case (Conj i phi' psi)
  then have "doConj (Opt i phi') (Opt i psi) \<noteq> []"
    unfolding doConj_def
    apply auto
    by (metis (mono_tags, lifting) List.list.distinct(1) Sum_Type.sum.case_eq_if)
  then show ?case
    using Conj trans_wqo refl_wqo pw_total
    apply (auto intro!: bexI[OF _ min_list_wrt_in] conj_optimal conj_sound)
    using conj_sound not_wqo total_on_def
    by fastforce
next
  note Opt.simps[simp del]
  case (Impl i phi' psi)
  then have "doImpl (Opt i phi') (Opt i psi) \<noteq> []"
    unfolding doImpl_def
    apply auto
    by (metis (mono_tags, lifting) List.list.distinct(1) Sum_Type.sum.case_eq_if)
  then show ?case
    using Impl trans_wqo refl_wqo pw_total
    apply (auto intro!: bexI[OF _ min_list_wrt_in] impl_optimal impl_sound)
    using impl_sound not_wqo total_on_def
    by fastforce
next
  note Opt.simps[simp del]
  case (Iff i phi' psi)
  then have "doIff (Opt i phi') (Opt i psi) \<noteq> []"
    unfolding doIff_def
    apply auto
    by (metis (mono_tags, lifting) List.list.distinct(1) Sum_Type.sum.case_eq_if)
  then show ?case
    using Iff trans_wqo refl_wqo pw_total
    apply (auto intro!: bexI[OF _ min_list_wrt_in] iff_optimal iff_sound)
    using iff_sound not_wqo total_on_def
    by fastforce
next
  note Opt.simps[simp del]
  case (Next i I phi')
  then have "doNext i I (\<Delta> rho (i+1)) (Opt (Suc i) phi') \<noteq> []"
    unfolding doNext_def
    by (auto split: sum.splits bool.splits)
  then show ?case
    using trans_wqo refl_wqo pw_total[of i "Next I phi'"] Next next_sound
    by (auto simp: total_on_def intro!: bexI[OF _ min_list_wrt_in] next_optimal[simplified])
next
  note Opt.simps[simp del]
  case (Prev i I phi')
  then have "doPrev i I (\<Delta> rho i) (Opt (i - 1) phi') \<noteq> []"
    unfolding doPrev_def
    by (auto split: sum.splits bool.splits)
  moreover have "optimal 0 (Prev I phi') (Inr VPrev_zero)"
    using refl_wqo
    by (auto simp: optimal_def valid_def reflp_def split: sum.splits vproof.splits)
  ultimately show ?case thm Cand.simps
    using trans_wqo refl_wqo pw_total[of i "Prev I phi'"] Prev prev_optimal[of i, OF _ Prev] prev_sound[of i, OF _ Prev]
    apply (cases i)
    apply (auto simp: doPrev_def valid_def split: sum.splits bool.splits)[1]
    by (auto simp: total_on_def elim: bounded_future.cases intro!: bexI[OF _ min_list_wrt_in, of _ wqo])
next
  note Opt.simps[simp del]
  case (Since i phi' I psi)
  show ?case using Since
    apply auto
    apply (auto simp: optimal_def valid_def refl_wqo[unfolded reflp_def]
        split: sum.splits)[1]
    subgoal
      using check_consistent[of "Since phi' I psi"]
      apply (auto simp: optimal_def valid_def refl_wqo[unfolded reflp_def]
          split: sum.splits vproof.splits)[1]
      by (metis VSince_le bounded_future_simps(11) check_complete check_consistent)
    subgoal
      by (auto simp: Let_def dest!: sinceBase0_sound[rotated -1] sinceBaseNZ_sound[rotated -1]
          since_sound[rotated -3, of _ _ _ _ _ _ phi' psi] split: if_splits)
    subgoal
      apply (auto simp: Let_def split: if_splits)
      subgoal premises prems
      proof -
        define p1 where p1_def: "p1 = Opt i phi'"
        define p2 where p2_def: "p2 \<equiv> Opt i psi"
        from prems have i_props: "i = 0 \<and>  \<tau> rho 0 + left I \<le> \<tau> rho i"
          by simp
        from pw_total[of 0 "Since phi' I psi"]
        have total_set: "total_on wqo (set (doSinceBase i (left I) p1 p2))"
          using sinceBase0_sound[OF _ _ i_props] i_props prems(1,2)
            p1_def p2_def
          by (fastforce simp: total_on_def)
        from prems p1_def p2_def have "doSinceBase i (left I) p1 p2 \<noteq> []"
          unfolding doSinceBase_def
          by (auto split: sum.splits bool.splits)
        then show ?thesis
          using trans_wqo refl_wqo total_set prems Since p1_def p2_def
          apply auto
          apply (rule bexI[OF _ min_list_wrt_in])
          apply (rule sinceBase0_optimal[simplified]; auto)
          by auto
      qed
      subgoal premises prems
      proof -
        define p1 where p1_def: "p1 = Opt i phi'"
        define p2 where p2_def: "p2 \<equiv> Opt i psi"
        define p' where p'_def: "p' \<equiv> Opt (i - 1) (Since phi' (subtract (delta rho i (i - 1)) I) psi)"
        from prems have i_props: "0 < i \<and>  \<tau> rho 0 + left I \<le> \<tau> rho i
        \<and> enat (delta rho i (i - 1)) \<le> right I"
          by simp
        from prems p'_def
        have opt: "optimal (i - 1) (Since phi' (subtract (delta rho i (i - 1)) I) psi) p'"
          by simp
        from prems(5-7) have bf: "bounded_future (Since phi' I psi)"
          and bf': "bounded_future (Since phi' (subtract (delta rho i (i - 1)) I) psi)"
          by (auto intro: SinceBF)
        from pw_total[of i "Since phi' I psi"]
        have total_set: "total_on wqo (set (doSince i (left I) p1 p2 p'))"
          using since_sound[OF i_props prems(1) prems(2) opt _ bf bf']
            p'_def p1_def p2_def
          by (auto simp: total_on_def)
        from opt have not_le: "p' \<noteq> Inr (VSince_le (i-1))"
          using i_props_imp_not_le[OF i_props opt] p'_def
          by auto
        then have nnil: "doSince i (left I) p1 p2 p' \<noteq> []"
          using opt p1_def p2_def p'_def
          unfolding doSince_def
          apply (auto simp: optimal_def valid_def split: sum.splits bool.splits)
          by (auto simp: Let_def split: vproof.splits)
        then show ?thesis
          using trans_wqo refl_wqo total_set prems Since p'_def p1_def p2_def
          apply auto
          apply (rule bexI[OF _ min_list_wrt_in])
          apply (rule since_optimal[simplified]; auto)
          by auto
      qed
      subgoal premises prems
      proof -
        from prems(3, 6) left_right[of I]
        have False 
          by auto
        then show ?thesis
          by auto
      qed
      subgoal premises prems
      proof -
        define p1 where p1_def: "p1 = Opt i phi'"
        define p2 where p2_def: "p2 \<equiv> Opt i psi"
        from prems have i_props: "0 < i \<and>  \<tau> rho 0 + left I \<le> \<tau> rho i
        \<and> right I < enat (delta rho i (i - 1))"
          by simp
        from pw_total[of i "Since phi' I psi"]
        have total_set: "total_on wqo (set (doSinceBase i (left I) p1 p2))"
          using sinceBaseNZ_sound[OF i_props prems(1) prems(2)]
            p1_def p2_def
          by (auto simp: total_on_def)
        from prems p1_def p2_def have "doSinceBase i (left I) p1 p2 \<noteq> []"
          unfolding doSinceBase_def
          by (auto split: sum.splits bool.splits)
        then show ?thesis
          using trans_wqo refl_wqo total_set prems Since p1_def p2_def
          apply auto
          apply (rule bexI[OF _ min_list_wrt_in])
          apply (rule sinceBaseNZ_optimal[simplified]; auto)
          by auto
      qed
      done
    done
next
  note Opt.simps[simp del]
  case (Until i phi' I psi)
  then show ?case using trans_wqo pw_total refl_wqo
    apply auto
    apply (auto simp: Let_def dest!: untilBase_sound[rotated -1]
        until_sound[rotated -3, of _ _ _ _ _ _ phi' psi] split: if_splits)[1]
    subgoal for x
      apply (auto simp: Let_def split: if_splits)
      subgoal premises prems
      proof -
        define p1 where p1_def: "p1 = Opt i phi'"
        define p2 where p2_def: "p2 \<equiv> Opt i psi"
        define p' where p'_def: "p' \<equiv> Opt (i + 1) (Until phi' (subtract (delta rho (i + 1) i) I) psi)"
        from prems(9,10) have i_props: "enat (\<Delta> rho (i+1)) \<le> right I"
          by auto
        from prems p'_def
        have opt: "optimal (i + 1) (Until phi' (subtract (\<Delta> rho (i+1)) I) psi) p'"
          by simp
        from prems(7-9) have bf: "bounded_future (Until phi' I psi)"
          and bf': "bounded_future (Until phi' (subtract (\<Delta> rho (i+1)) I) psi)"
          by (auto intro: UntilBF)
        from pw_total[of i "Until phi' I psi"]
        have total_set: "total_on wqo (set (doUntil i (left I) p1 p2 p'))"
          using until_sound[OF i_props prems(1) prems(2) opt _ bf bf']
            p'_def p1_def p2_def
          by (auto simp: total_on_def)
        have nnil: "doUntil i (left I) p1 p2 p' \<noteq> []"
          using opt p1_def p2_def p'_def prems(9)
          unfolding doUntil_def
          apply (auto simp: optimal_def valid_def split: sum.splits bool.splits)
          by (auto simp: Let_def split: sproof.splits vproof.splits)
        then show ?thesis
          using trans_wqo refl_wqo total_set prems Until p'_def p1_def p2_def
          apply auto
          apply (rule bexI[OF _ min_list_wrt_in])
          apply (rule until_optimal[simplified]; auto)
          by auto
      qed
      subgoal premises prems
      proof -
        define p1 where p1_def: "p1 = Opt i phi'"
        define p2 where p2_def: "p2 \<equiv> Opt i psi"
        from prems(8,9) have i_props: "right I < enat (\<Delta> rho (i+1))"
          by simp
        from pw_total[of i "Until phi' I psi"]
        have total_set: "total_on wqo (set (doUntilBase i (left I) p1 p2))"
          using untilBase_sound[OF i_props prems(1) prems(2)]
            p1_def p2_def
          by (auto simp: total_on_def)
        from prems p1_def p2_def have "doUntilBase i (left I) p1 p2 \<noteq> []"
          unfolding doUntilBase_def
          by (auto split: sum.splits bool.splits)
        then show ?thesis
          using trans_wqo refl_wqo total_set prems Until p1_def p2_def
          apply auto
          apply (rule bexI[OF _ min_list_wrt_in])
          apply (rule untilBase_optimal[simplified]; auto)
          by auto
      qed
      done
    done
next
  case (Opt i phi')
  then show ?case
    using trans_wqo pw_total refl_wqo
    unfolding optimal_def
    apply (auto simp: total_on_def)
    apply (metis empty_iff empty_set min_list_wrt_in total_onI)
    apply (rule trans_wqo[unfolded transp_def, rule_format, rotated])
    apply (drule spec, erule mp, assumption)
    apply (rule min_list_wrt_le[of wqo])
    apply (auto simp: total_on_def refl_wqo dest: not_wqo[rotated -1])
    done
qed

end

end
