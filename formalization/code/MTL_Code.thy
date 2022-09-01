theory MTL_Code
  imports Explanator.MTL "HOL-Library.Code_Target_Nat" Containers.Containers
begin

primrec progress :: "'a trace \<Rightarrow> 'a mtl \<Rightarrow> nat \<Rightarrow> nat" where
  "progress \<sigma> TT j = j"
| "progress \<sigma> FF j = j"
| "progress \<sigma> (Atom e) j = j"
| "progress \<sigma> (Neg \<phi>) j = progress \<sigma> \<phi> j"
| "progress \<sigma> (Disj \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (Conj \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (Impl \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (Iff \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (Prev I \<phi>) j = (if j = 0 then 0 else min (Suc (progress \<sigma> \<phi> j)) j)"
| "progress \<sigma> (Next I \<phi>) j = progress \<sigma> \<phi> j - 1"
| "progress \<sigma> (Once I \<phi>) j = progress \<sigma> \<phi> j"
| "progress \<sigma> (Historically I \<phi>) j = progress \<sigma> \<phi> j"
| "progress \<sigma> (Since \<phi> I \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (Eventually I \<phi>) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> (progress \<sigma> \<phi> j) \<longrightarrow> (\<tau> \<sigma> k - \<tau> \<sigma> i) \<le> right I}"
| "progress \<sigma> (Always I \<phi>) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> (progress \<sigma> \<phi> j) \<longrightarrow> (\<tau> \<sigma> k - \<tau> \<sigma> i) \<le> right I}"
| "progress \<sigma> (Until \<phi> I \<psi>) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j) \<longrightarrow> (\<tau> \<sigma> k - \<tau> \<sigma> i) \<le> right I}"

lemma Inf_Min:
  fixes P :: "nat \<Rightarrow> bool"
  assumes "P j"
  shows "Inf (Collect P) = Min (Set.filter P {..j})"
  using Min_in[where ?A="Set.filter P {..j}"] assms
  by (auto simp: Set.filter_def intro: cInf_lower intro!: antisym[OF _ Min_le])
    (metis Inf_nat_def1 empty_iff mem_Collect_eq)

lemma progress_Eventually_code: "progress \<sigma> (Eventually I \<phi>) j =
  (let m = min j (Suc (progress \<sigma> \<phi> j)) - 1 in Min (Set.filter (\<lambda>i. enat (delta \<sigma> m i) \<le> right I) {..j}))"
proof -
  define P where "P \<equiv> (\<lambda>i. \<forall>k. k < j \<and> k \<le> (progress \<sigma> \<phi> j) \<longrightarrow> enat (delta \<sigma> k i) \<le> right I)"
  have P_j: "P j"
    by (auto simp: P_def enat_0)
  have all_wit: "(\<forall>k \<in> {..<m}. enat (delta \<sigma> k i) \<le> right I) \<longleftrightarrow> (enat (delta \<sigma> (m - 1) i) \<le> right I)" for i m
  proof (cases m)
    case (Suc ma)
    have "k < Suc ma \<Longrightarrow> delta \<sigma> k i \<le> delta \<sigma> ma i" for k
      using \<tau>_mono
      unfolding less_Suc_eq_le
      by (rule diff_le_mono)
    then show ?thesis
      by (auto simp: Suc) (meson order.trans enat_ord_simps(1))
  qed (auto simp: enat_0)
  show ?thesis
    unfolding progress.simps Let_def P_def[symmetric] Inf_Min[where ?P=P, OF P_j] all_wit[symmetric]
    by (fastforce simp: P_def intro: arg_cong[where ?f=Min])
qed

lemma progress_Always_code: "progress \<sigma> (Always I \<phi>) j =
  (let m = min j (Suc (progress \<sigma> \<phi> j)) - 1 in Min (Set.filter (\<lambda>i. enat (delta \<sigma> m i) \<le> right I) {..j}))"
proof -
  define P where "P \<equiv> (\<lambda>i. \<forall>k. k < j \<and> k \<le> (progress \<sigma> \<phi> j) \<longrightarrow> enat (delta \<sigma> k i) \<le> right I)"
  have P_j: "P j"
    by (auto simp: P_def enat_0)
  have all_wit: "(\<forall>k \<in> {..<m}. enat (delta \<sigma> k i) \<le> right I) \<longleftrightarrow> (enat (delta \<sigma> (m - 1) i) \<le> right I)" for i m
  proof (cases m)
    case (Suc ma)
    have "k < Suc ma \<Longrightarrow> delta \<sigma> k i \<le> delta \<sigma> ma i" for k
      using \<tau>_mono
      unfolding less_Suc_eq_le
      by (rule diff_le_mono)
    then show ?thesis
      by (auto simp: Suc) (meson order.trans enat_ord_simps(1))
  qed (auto simp: enat_0)
  show ?thesis
    unfolding progress.simps Let_def P_def[symmetric] Inf_Min[where ?P=P, OF P_j] all_wit[symmetric]
    by (fastforce simp: P_def intro: arg_cong[where ?f=Min])
qed

lemma progress_Until_code: "progress \<sigma> (Until \<phi> I \<psi>) j =
  (let m = min j (Suc (min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j))) - 1 in Min (Set.filter (\<lambda>i. enat (delta \<sigma> m i) \<le> right I) {..j}))"
proof -
  define P where "P \<equiv> (\<lambda>i. \<forall>k. k < j \<and> k \<le> min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j) \<longrightarrow> enat (delta \<sigma> k i) \<le> right I)"
  have P_j: "P j"
    by (auto simp: P_def enat_0)
  have all_wit: "(\<forall>k \<in> {..<m}. enat (delta \<sigma> k i) \<le> right I) \<longleftrightarrow> (enat (delta \<sigma> (m - 1) i) \<le> right I)" for i m
  proof (cases m)
    case (Suc ma)
    have "k < Suc ma \<Longrightarrow> delta \<sigma> k i \<le> delta \<sigma> ma i" for k
      using \<tau>_mono
      unfolding less_Suc_eq_le
      by (rule diff_le_mono)
    then show ?thesis
      by (auto simp: Suc) (meson order.trans enat_ord_simps(1))
  qed (auto simp: enat_0)
  show ?thesis
    unfolding progress.simps Let_def P_def[symmetric] Inf_Min[where ?P=P, OF P_j] all_wit[symmetric]
    by (fastforce simp: P_def intro: arg_cong[where ?f=Min])
qed

lemmas progress_code[code] = progress.simps(1-13) progress_Eventually_code progress_Always_code progress_Until_code

(* Lexicographic combination *)

locale scmonotone = fixes wqo :: "'a sproof + 'a vproof \<Rightarrow> 'a sproof + 'a vproof \<Rightarrow> bool"
  assumes
    SNeg: "\<And>p p'. strict wqo (Inr p) (Inr p') \<Longrightarrow> strict wqo (Inl (SNeg p)) (Inl (SNeg p'))"
and VNeg: "\<And>p p'. strict wqo (Inl p) (Inl p') \<Longrightarrow> strict wqo (Inr (VNeg p)) (Inr (VNeg p'))"
and SDisjL: "\<And>p p'. strict wqo (Inl p) (Inl p') \<Longrightarrow> strict wqo (Inl (SDisjL p)) (Inl (SDisjL p'))"
and SDisjR: "\<And>p p'. strict wqo (Inl p) (Inl p') \<Longrightarrow> strict wqo (Inl (SDisjR p)) (Inl (SDisjR p'))"
and VDisjL: "\<And>p1 p1' p2 p2'. strict wqo (Inr p1) (Inr p1') \<Longrightarrow> wqo (Inr p2) (Inr p2' ) \<Longrightarrow>
  strict wqo (Inr (VDisj p1 p2)) (Inr (VDisj p1' p2'))"
and VDisjR: "\<And>p1 p1' p2 p2'. wqo (Inr p1) (Inr p1') \<Longrightarrow> strict wqo (Inr p2) (Inr p2' ) \<Longrightarrow>
  strict wqo (Inr (VDisj p1 p2)) (Inr (VDisj p1' p2'))"
and SConjL: "\<And>p1 p1' p2 p2'. strict wqo (Inl p1) (Inl p1') \<Longrightarrow> wqo (Inl p2) (Inl p2' ) \<Longrightarrow>
  strict wqo (Inl (SConj p1 p2)) (Inl (SConj p1' p2'))"
and SConjR: "\<And>p1 p1' p2 p2'. wqo (Inl p1) (Inl p1') \<Longrightarrow> strict wqo (Inl p2) (Inl p2' ) \<Longrightarrow>
  strict wqo (Inl (SConj p1 p2)) (Inl (SConj p1' p2'))"
and VConjL: "\<And>p p'. strict wqo (Inr p) (Inr p') \<Longrightarrow> strict wqo (Inr (VConjL p)) (Inr (VConjL p'))"
and VConjR: "\<And>p p'. strict wqo (Inr p) (Inr p') \<Longrightarrow> strict wqo (Inr (VConjR p)) (Inr (VConjR p'))"
and SSince: "\<And>p p'. strict wqo (Inl p) (Inl p') \<Longrightarrow> strict wqo (Inl (SSince p [])) (Inl (SSince p' []))"
and VSince_Nil: "\<And>i p p'. strict wqo (Inr p) (Inr p') \<Longrightarrow> strict wqo (Inr (VSince i p [])) (Inr (VSince i p' []))"
and VSinceL: "\<And>i p p' q q'. strict wqo (Inr p) (Inr p') \<Longrightarrow> wqo (Inr q) (Inr q') \<Longrightarrow>
  strict wqo (Inr (VSince i p [q])) (Inr (VSince i p' [q']))"
and VSinceR: "\<And>i p p' q q'. wqo (Inr p) (Inr p') \<Longrightarrow> strict wqo (Inr q) (Inr q') \<Longrightarrow>
  strict wqo (Inr (VSince i p [q])) (Inr (VSince i p' [q']))"
and VSince_never: "\<And>i li q q'. strict wqo (Inr q) (Inr q') \<Longrightarrow>
  strict wqo (Inr (VSince_never i li [q])) (Inr (VSince_never i li [q']))"
and SUntil_Nil: "\<And>p p'. strict wqo (Inl p) (Inl p') \<Longrightarrow>
  strict wqo (Inl (SUntil [] p)) (Inl (SUntil [] p'))"
and SUntilL: "\<And>p p' q q'. strict wqo (Inl p) (Inl p') \<Longrightarrow> wqo (Inl q) (Inl q') \<Longrightarrow>
  strict wqo (Inl (SUntil [q] p)) (Inl (SUntil [q'] p'))"
and SUntilR: "\<And>p p' q q'. wqo (Inl p) (Inl p') \<Longrightarrow> strict wqo (Inl q) (Inl q') \<Longrightarrow>
  strict wqo (Inl (SUntil [q] p)) (Inl (SUntil [q'] p'))"
and VUntil_Nil: "\<And>i p p'. strict wqo (Inr p) (Inr p') \<Longrightarrow>
  strict wqo (Inr (VUntil i [] p)) (Inr (VUntil i [] p'))"
and VUntilL: "\<And>i p p' q q'. strict wqo (Inr p) (Inr p') \<Longrightarrow> wqo (Inr q) (Inr q') \<Longrightarrow>
  strict wqo (Inr (VUntil i [q] p)) (Inr (VUntil i [q'] p'))"
and VUntilR: "\<And>i p p' q q'. wqo (Inr p) (Inr p') \<Longrightarrow> strict wqo (Inr q) (Inr q') \<Longrightarrow>
  strict wqo (Inr (VUntil i [q] p)) (Inr (VUntil i [q'] p'))"
and VUntil_never: "\<And>i hi q q'. strict wqo (Inr q) (Inr q') \<Longrightarrow>
  strict wqo (Inr (VUntil_never i hi [q])) (Inr (VUntil_never i hi [q']))"
and SNext: "\<And>p p'. strict wqo (Inl p) (Inl p') \<Longrightarrow> strict wqo (Inl (SNext p)) (Inl (SNext p'))"
and VNext: "\<And>p p'. strict wqo (Inr p) (Inr p') \<Longrightarrow> strict wqo (Inr (VNext p)) (Inr (VNext p'))"
and SPrev: "\<And>p p'. strict wqo (Inl p) (Inl p') \<Longrightarrow> strict wqo (Inl (SPrev p)) (Inl (SPrev p'))"
and VPrev: "\<And>p p'. strict wqo (Inr p) (Inr p') \<Longrightarrow> strict wqo (Inr (VPrev p)) (Inr (VPrev p'))"
and SImplR: "\<And>p p'. strict wqo (Inl p) (Inl p') \<Longrightarrow> strict wqo (Inl (SImplR p)) (Inl (SImplR p'))"
and SImplL: "\<And>p p'. strict wqo (Inr p) (Inr p') \<Longrightarrow> strict wqo (Inl (SImplL p)) (Inl (SImplL p'))"
and VImplL: "\<And>p1 p1' p2 p2'. strict wqo (Inl p1) (Inl p1') \<Longrightarrow> wqo (Inr p2) (Inr p2') \<Longrightarrow>
  strict wqo (Inr (VImpl p1 p2)) (Inr (VImpl p1' p2'))"
and VImplR: "\<And>p1 p1' p2 p2'. wqo (Inl p1) (Inl p1') \<Longrightarrow> strict wqo (Inr p2) (Inr p2') \<Longrightarrow>
  strict wqo (Inr (VImpl p1 p2)) (Inr (VImpl p1' p2'))"
and SIff_ssL: "\<And>p1 p1' p2 p2'. strict wqo (Inl p1) (Inl p1') \<Longrightarrow> wqo (Inl p2) (Inl p2') \<Longrightarrow>
  strict wqo (Inl (SIff_ss p1 p2)) (Inl (SIff_ss p1' p2'))"
and SIff_ssR: "\<And>p1 p1' p2 p2'. wqo (Inl p1) (Inl p1') \<Longrightarrow> strict wqo (Inl p2) (Inl p2') \<Longrightarrow>
  strict wqo (Inl (SIff_ss p1 p2)) (Inl (SIff_ss p1' p2'))"
and SIff_vvL: "\<And>p1 p1' p2 p2'. strict wqo (Inr p1) (Inr p1') \<Longrightarrow> wqo (Inr p2) (Inr p2') \<Longrightarrow>
  strict wqo (Inl (SIff_vv p1 p2)) (Inl (SIff_vv p1' p2'))"
and SIff_vvR: "\<And>p1 p1' p2 p2'. wqo (Inr p1) (Inr p1') \<Longrightarrow> strict wqo (Inr p2) (Inr p2') \<Longrightarrow>
  strict wqo (Inl (SIff_vv p1 p2)) (Inl (SIff_vv p1' p2'))"
and VIff_svL: "\<And>p1 p1' p2 p2'. strict wqo (Inl p1) (Inl p1') \<Longrightarrow> wqo (Inr p2) (Inr p2') \<Longrightarrow>
  strict wqo (Inr (VIff_sv p1 p2)) (Inr (VIff_sv p1' p2'))"
and VIff_svR: "\<And>p1 p1' p2 p2'. wqo (Inl p1) (Inl p1') \<Longrightarrow> strict wqo (Inr p2) (Inr p2') \<Longrightarrow>
  strict wqo (Inr (VIff_sv p1 p2)) (Inr (VIff_sv p1' p2'))"
and VIff_vsL: "\<And>p1 p1' p2 p2'. strict wqo (Inr p1) (Inr p1') \<Longrightarrow> wqo (Inl p2) (Inl p2' ) \<Longrightarrow>
  strict wqo (Inr (VIff_vs p1 p2)) (Inr (VIff_vs p1' p2'))"
and VIff_vsR: "\<And>p1 p1' p2 p2'. wqo (Inr p1) (Inr p1') \<Longrightarrow> strict wqo (Inl p2) (Inl p2' ) \<Longrightarrow>
  strict wqo (Inr (VIff_vs p1 p2)) (Inr (VIff_vs p1' p2'))"
and SOnce: "\<And>i p p'. strict wqo (Inl p) (Inl p') \<Longrightarrow> strict wqo (Inl (SOnce i p)) (Inl (SOnce i p'))"
and VOnce: "\<And>i li q q'. strict wqo (Inr q) (Inr q') \<Longrightarrow>
  strict wqo (Inr (VOnce i li [q])) (Inr (VOnce i li [q']))"
and SHistorically: "\<And>i li q q'. strict wqo (Inl q) (Inl q') \<Longrightarrow>
  strict wqo (Inl (SHistorically i li [q])) (Inl (SHistorically i li [q']))"
and VHistorically: "\<And>i p p'. strict wqo (Inr p) (Inr p') \<Longrightarrow> strict wqo (Inr (VHistorically i p)) (Inr (VHistorically i p'))"
and SEventually: "\<And>i p p'. strict wqo (Inl p) (Inl p') \<Longrightarrow> strict wqo (Inl (SEventually i p)) (Inl (SEventually i p'))"
and VEventually: "\<And>i hi q q'. strict wqo (Inr q) (Inr q') \<Longrightarrow>
  strict wqo (Inr (VEventually i hi [q])) (Inr (VEventually i hi [q']))"
and SAlways: "\<And>i hi q q'. strict wqo (Inl q) (Inl q') \<Longrightarrow>
  strict wqo (Inl (SAlways i hi [q])) (Inl (SAlways i hi [q']))"
and VAlways: "\<And>i p p'. strict wqo (Inr p) (Inr p') \<Longrightarrow> strict wqo (Inr (VAlways i p)) (Inr (VAlways i p'))"
and proofApp_monoL: "\<And>i phi p p' r r'. checkApp p r \<Longrightarrow> checkApp p' r' \<Longrightarrow> strict wqo p p' \<Longrightarrow> wqo r r' \<Longrightarrow>
  valid rho i phi (p \<oplus> r) \<Longrightarrow> valid rho i phi (p' \<oplus> r') \<Longrightarrow> strict wqo (p \<oplus> r) (p' \<oplus> r')"
and proofApp_monoR: "\<And>i phi p p' r r'. checkApp p r \<Longrightarrow> checkApp p' r' \<Longrightarrow> wqo p p' \<Longrightarrow> strict wqo r r' \<Longrightarrow>
  valid rho i phi (p \<oplus> r) \<Longrightarrow> valid rho i phi (p' \<oplus> r') \<Longrightarrow> strict wqo (p \<oplus> r) (p' \<oplus> r')"
and proofIncr_mono: "\<And>i phi p p'. checkIncr p \<Longrightarrow> checkIncr p' \<Longrightarrow> strict wqo p p' \<Longrightarrow>
  valid rho i phi p \<Longrightarrow> valid rho i phi p' \<Longrightarrow> strict wqo (proofIncr p) (proofIncr p')"

definition "lex_wqo wqo wqo' = (\<lambda>x y. wqo x y \<and> (wqo y x \<longrightarrow> wqo' x y))"

locale lex_trans_wqo = a: trans_wqo wqo rho + b: trans_wqo wqo' rho + c: scmonotone wqo
  for wqo wqo' rho
begin

lemma lex_refl_wqo: "reflp (lex_wqo wqo wqo')"
  using a.refl_wqo b.refl_wqo
  by (auto simp: reflp_def lex_wqo_def)

lemma lex_trans_wqo: "transp (lex_wqo wqo wqo')"
  using a.trans_wqo b.trans_wqo
  by (auto simp: transp_def lex_wqo_def)

lemma lex_pw_total: "total_on (lex_wqo wqo wqo') {p. valid rho i \<phi> p}"
  using a.pw_total b.pw_total
  by (fastforce simp: total_on_def lex_wqo_def)

lemma lex_trans_wqo_axioms: "trans_wqo (lex_wqo wqo wqo') rho"
  apply unfold_locales
  using a.SNeg b.SNeg c.SNeg apply (auto simp: lex_wqo_def)[1]
  using a.VNeg b.VNeg c.VNeg apply (auto simp: lex_wqo_def)[1]
  using a.SDisjL b.SDisjL c.SDisjL apply (auto simp: lex_wqo_def)[1]
  using a.SDisjR b.SDisjR c.SDisjR apply (auto simp: lex_wqo_def)[1]
  using a.VDisj b.VDisj c.VDisjL c.VDisjR apply (auto simp: lex_wqo_def)[1]
  using a.SConj b.SConj c.SConjL c.SConjR apply (auto simp: lex_wqo_def)[1]
  using a.VConjL b.VConjL c.VConjL apply (auto simp: lex_wqo_def)[1]
  using a.VConjR b.VConjR c.VConjR apply (auto simp: lex_wqo_def)[1]
  using a.SImplR b.SImplR c.SImplR apply (auto simp: lex_wqo_def)[1]
  using a.SImplL b.SImplL c.SImplL apply (auto simp: lex_wqo_def)[1]
  using a.VImpl b.VImpl c.VImplL c.VImplR apply (auto simp: lex_wqo_def)[1]
  using a.SIff_ss b.SIff_ss c.SIff_ssL c.SIff_ssR apply (auto simp: lex_wqo_def)[1]
  using a.SIff_vv b.SIff_vv c.SIff_vvL c.SIff_vvR apply (auto simp: lex_wqo_def)[1]
  using a.VIff_sv b.VIff_sv c.VIff_svL c.VIff_svR apply (auto simp: lex_wqo_def)[1]
  using a.VIff_vs b.VIff_vs c.VIff_vsL c.VIff_vsR apply (auto simp: lex_wqo_def)[1]
  using a.SOnce b.SOnce c.SOnce apply (auto simp: lex_wqo_def)[1]
  using a.VOnce b.VOnce c.VOnce apply (auto simp: lex_wqo_def)[1]
  using a.SHistorically b.SHistorically c.SHistorically apply (auto simp: lex_wqo_def)[1]
  using a.VHistorically b.VHistorically c.VHistorically apply (auto simp: lex_wqo_def)[1]
  using a.SEventually b.SEventually c.SEventually apply (auto simp: lex_wqo_def)[1]
  using a.VEventually b.VEventually c.VEventually apply (auto simp: lex_wqo_def)[1]
  using a.SAlways b.SAlways c.SAlways apply (auto simp: lex_wqo_def)[1]
  using a.VAlways b.VAlways c.VAlways apply (auto simp: lex_wqo_def)[1]
  using a.SSince b.SSince c.SSince apply (auto simp: lex_wqo_def)[1]
  using a.VSince_Nil b.VSince_Nil c.VSince_Nil apply (auto simp: lex_wqo_def)[1]
  using a.VSince b.VSince c.VSinceL c.VSinceR apply (auto simp: lex_wqo_def)[1]
  using a.VSince_never b.VSince_never c.VSince_never apply (auto simp: lex_wqo_def)[1]
  using a.SUntil_Nil b.SUntil_Nil c.SUntil_Nil apply (auto simp: lex_wqo_def)[1]
  using a.SUntil b.SUntil c.SUntilL c.SUntilR apply (auto simp: lex_wqo_def)[1]
  using a.VUntil_Nil b.VUntil_Nil c.VUntil_Nil apply (auto simp: lex_wqo_def)[1]
  using a.VUntil b.VUntil c.VUntilL c.VUntilR apply (auto simp: lex_wqo_def)[1]
  using a.VUntil_never b.VUntil_never c.VUntil_never apply (auto simp: lex_wqo_def)[1]
  using a.SNext b.SNext c.SNext apply (auto simp: lex_wqo_def)[1]
  using a.VNext b.VNext c.VNext apply (auto simp: lex_wqo_def)[1]
  using a.SPrev b.SPrev c.SPrev apply (auto simp: lex_wqo_def)[1]
  using a.VPrev b.VPrev c.VPrev apply (auto simp: lex_wqo_def)[1]
  subgoal for rho i phi p p' r r'
    using a.proofApp_mono b.proofApp_mono c.proofApp_monoL c.proofApp_monoR
    by (auto simp: lex_wqo_def)
  subgoal for rho i phi p p'
    using a.proofIncr_mono b.proofIncr_mono c.proofIncr_mono
    by (auto simp: lex_wqo_def)
  using lex_refl_wqo lex_trans_wqo lex_pw_total
  by auto

end

locale lex_scmonotone = lex_trans_wqo + d: scmonotone wqo'
begin

lemma lex_scmonotone_axioms: "scmonotone (lex_wqo wqo wqo')"
  apply unfold_locales
  using a.SNeg b.SNeg c.SNeg d.SNeg apply (auto simp: lex_wqo_def)[1]
  using a.VNeg b.VNeg c.VNeg d.VNeg apply (auto simp: lex_wqo_def)[1]
  using a.SDisjL b.SDisjL c.SDisjL d.SDisjL apply (auto simp: lex_wqo_def)[1]
  using a.SDisjR b.SDisjR c.SDisjR d.SDisjR apply (auto simp: lex_wqo_def)[1]
  using a.VDisj b.VDisj c.VDisjL d.VDisjL c.VDisjR d.VDisjR apply (auto simp: lex_wqo_def)[1]
  using a.VDisj b.VDisj c.VDisjL d.VDisjL c.VDisjR d.VDisjR apply (auto simp: lex_wqo_def)[1]
  using a.SConj b.SConj c.SConjL d.SConjL c.SConjR d.SConjR apply (auto simp: lex_wqo_def)[1]
  using a.SConj b.SConj c.SConjL d.SConjL c.SConjR d.SConjR apply (auto simp: lex_wqo_def)[1]
  using a.VConjL b.VConjL c.VConjL d.VConjL apply (auto simp: lex_wqo_def)[1]
  using a.VConjR b.VConjR c.VConjR d.VConjR apply (auto simp: lex_wqo_def)[1]
  using a.SSince b.SSince c.SSince d.SSince apply (auto simp: lex_wqo_def)[1]
  using a.VSince_Nil b.VSince_Nil c.VSince_Nil d.VSince_Nil apply (auto simp: lex_wqo_def)[1]
  using a.VSince b.VSince c.VSinceL d.VSinceL c.VSinceR d.VSinceR apply (auto simp: lex_wqo_def)[1]
  using a.VSince b.VSince c.VSinceL d.VSinceL c.VSinceR d.VSinceR apply (auto simp: lex_wqo_def)[1]
  using a.VSince_never b.VSince_never c.VSince_never d.VSince_never apply (auto simp: lex_wqo_def)[1]
  using a.SUntil_Nil b.SUntil_Nil c.SUntil_Nil d.SUntil_Nil apply (auto simp: lex_wqo_def)[1]
  using a.SUntil b.SUntil c.SUntilL d.SUntilL c.SUntilR d.SUntilR apply (auto simp: lex_wqo_def)[1]
  using a.SUntil b.SUntil c.SUntilL d.SUntilL c.SUntilR d.SUntilR apply (auto simp: lex_wqo_def)[1]
  using a.VUntil_Nil b.VUntil_Nil c.VUntil_Nil d.VUntil_Nil apply (auto simp: lex_wqo_def)[1]
  using a.VUntil b.VUntil c.VUntilL d.VUntilL c.VUntilR d.VUntilR apply (auto simp: lex_wqo_def)[1]
  using a.VUntil b.VUntil c.VUntilL d.VUntilL c.VUntilR d.VUntilR apply (auto simp: lex_wqo_def)[1]
  using a.VUntil_never b.VUntil_never c.VUntil_never d.VUntil_never apply (auto simp: lex_wqo_def)[1]
  using a.SNext b.SNext c.SNext d.SNext apply (auto simp: lex_wqo_def)[1]
  using a.VNext b.VNext c.VNext d.VNext apply (auto simp: lex_wqo_def)[1]
  using a.SPrev b.SPrev c.SPrev d.SPrev apply (auto simp: lex_wqo_def)[1]
  using a.VPrev b.VPrev c.VPrev d.VPrev apply (auto simp: lex_wqo_def)[1]
  using a.SImplR b.SImplR c.SImplR d.SImplR apply (auto simp: lex_wqo_def)[1]
  using a.SImplL b.SImplL c.SImplL d.SImplL apply (auto simp: lex_wqo_def)[1]
  using a.VImpl b.VImpl c.VImplL d.VImplL c.VImplR d.VImplR apply (auto simp: lex_wqo_def)[1]
  using a.VImpl b.VImpl c.VImplL d.VImplL c.VImplR d.VImplR apply (auto simp: lex_wqo_def)[1]
  using a.SIff_ss b.SIff_ss c.SIff_ssL d.SIff_ssL c.SIff_ssR d.SIff_ssR apply (auto simp: lex_wqo_def)[1]
  using a.SIff_ss b.SIff_ss c.SIff_ssL d.SIff_ssL c.SIff_ssR d.SIff_ssR apply (auto simp: lex_wqo_def)[1]
  using a.SIff_vv b.SIff_vv c.SIff_vvL c.SIff_vvR d.SIff_vvL d.SIff_vvR apply (auto simp: lex_wqo_def)[1]
  using a.SIff_vv b.SIff_vv c.SIff_vvL c.SIff_vvR d.SIff_vvL d.SIff_vvR apply (auto simp: lex_wqo_def)[1]
  using a.VIff_sv b.VIff_sv c.VIff_svL c.VIff_svR d.VIff_svL d.VIff_svR apply (auto simp: lex_wqo_def)[1]
  using a.VIff_sv b.VIff_sv c.VIff_svL c.VIff_svR d.VIff_svL d.VIff_svR apply (auto simp: lex_wqo_def)[1]
  using a.VIff_vs b.VIff_vs c.VIff_vsL c.VIff_vsR d.VIff_vsL d.VIff_vsR apply (auto simp: lex_wqo_def)[1]
  using a.VIff_vs b.VIff_vs c.VIff_vsL c.VIff_vsR d.VIff_vsL d.VIff_vsR apply (auto simp: lex_wqo_def)[1]
  using a.SOnce b.SOnce c.SOnce d.SOnce apply (auto simp: lex_wqo_def)[1]
  using a.VOnce b.VOnce c.VOnce d.VOnce apply (auto simp: lex_wqo_def)[1]
  using a.SHistorically b.SHistorically c.SHistorically d.SHistorically apply (auto simp: lex_wqo_def)[1]
  using a.VHistorically b.VHistorically c.VHistorically d.VHistorically apply (auto simp: lex_wqo_def)[1]
  using a.SEventually b.SEventually c.SEventually d.SEventually apply (auto simp: lex_wqo_def)[1]
  using a.VEventually b.VEventually c.VEventually d.VEventually apply (auto simp: lex_wqo_def)[1]
  using a.SAlways b.SAlways c.SAlways d.SAlways apply (auto simp: lex_wqo_def)[1]
  using a.VAlways b.VAlways c.VAlways d.VAlways apply (auto simp: lex_wqo_def)[1]
  subgoal for rho i phi p p' r r'
    using a.proofApp_mono b.proofApp_mono c.proofApp_monoL c.proofApp_monoR d.proofApp_monoL d.proofApp_monoR
    by (auto simp: lex_wqo_def simp del: a.proofApp_simps)
  subgoal for rho i phi p p' r r'
    using a.proofApp_mono b.proofApp_mono c.proofApp_monoL c.proofApp_monoR d.proofApp_monoL d.proofApp_monoR
    by (auto simp: lex_wqo_def simp del: a.proofApp_simps)
  subgoal for rho i phi p p'
    using a.proofIncr_mono b.proofIncr_mono c.proofIncr_mono d.proofIncr_mono
    by (auto simp: lex_wqo_def)
  done 

end

(* Flipped preference order *)

context trans_wqo
begin

lemma flipped_trans_wqo_axioms: "trans_wqo wqo\<inverse>\<inverse> rho"
  apply unfold_locales
  using SNeg VNeg SDisjL SDisjR VDisj SConj VConjL VConjR SSince VSince_Nil VSince VSince_never 
    SUntil_Nil SUntil VUntil_Nil VUntil VUntil_never SNext VNext SPrev VPrev SImplL SImplR VImpl 
    SIff_ss SIff_vv VIff_sv VIff_vs SOnce VOnce SHistorically VHistorically SEventually VEventually 
    SAlways VAlways proofApp_mono proofIncr_mono
                      apply (auto simp: simp del: proofApp_simps)[38]
  using refl_wqo trans_wqo pw_total
    apply (fastforce simp: reflp_def transp_def total_on_def)+
  done

end

lemma conversep_code[code]: "P\<inverse>\<inverse> = (\<lambda>x y. P y x)"
  by auto

(* Explanator setup *)

definition strs_check :: "String.literal trace \<Rightarrow> _ mtl \<Rightarrow> _ sproof \<Rightarrow> bool"
  where "strs_check = s_check"

definition strs_at :: "String.literal sproof \<Rightarrow> nat"
  where "strs_at = s_at"

definition strv_check :: "String.literal trace \<Rightarrow> _ mtl \<Rightarrow> _ vproof \<Rightarrow> bool"
  where "strv_check = v_check"

definition strv_at :: "String.literal vproof \<Rightarrow> nat"
  where "strv_at = v_at"

declare bounded_future_simps[code]

context trans_wqo
begin

lemma optimal_code[code]: "optimal i phi p = (if bounded_future phi then
  valid rho i phi p \<and> wqo p (Opt i phi) else Code.abort (STR ''optimal: not bounded future'') (\<lambda>_. optimal i phi p))"
  using alg_optimal[of phi i] trans_wqo
  by (auto simp: optimal_def transp_def)

end

(* Setup for maximum measures *)

definition "max_proofs f xs = (case xs of [] \<Rightarrow> 0 | _ \<Rightarrow> Max (f ` set xs))"

lemma max_proofs_empty[simp]: "max_proofs f [] = 0"
  by (auto simp: max_proofs_def)

lemma max_proofs_singleton[simp]: "max_proofs f [x] = f x"
  by (auto simp: max_proofs_def)

lemma max_proofs_sound: "x \<in> set xs \<Longrightarrow> f x \<le> max_proofs f xs"
  by (auto simp: max_proofs_def split: list.splits)

lemma max_proofs_fundef_cong[fundef_cong]: "(\<And>x. x \<in> set xs \<Longrightarrow> f x = f' x) \<Longrightarrow>
  max_proofs f xs = max_proofs f' xs"
  by (auto simp: max_proofs_def split: list.splits)

lemma max_proofs_Cons:
  fixes f :: "'a \<Rightarrow> nat"
  shows "max_proofs f (p # qs) = max (f p) (max_proofs f qs)"
  by (auto simp: max_proofs_def split: list.splits)

lemma max_Max_insert: "finite Z \<Longrightarrow> max x (Max (insert y Z)) = Max ({x, y} \<union> Z)"
  by auto

lemma max_proofs_app:
  fixes f :: "'a \<Rightarrow> nat"
  shows "max_proofs f (qs @ [p]) = max (f p) (max_proofs f qs)"
  apply (auto simp: max_proofs_def split: list.splits)
  subgoal for x xs
    unfolding max_Max_insert[OF finite_imageI[OF finite_set]]
    by (rule arg_cong[of _ _ Max]) auto
  done

(* Setup for minimum measures *)

definition "min_proofs f xs = (case xs of [] \<Rightarrow> \<infinity> | _ \<Rightarrow> Min (f ` set xs))"

lemma min_proofs_empty[simp]: "min_proofs f [] = \<infinity>"
  by (auto simp: min_proofs_def)

lemma min_proofs_singleton[simp]: "min_proofs f [x] = f x"
  by (auto simp: min_proofs_def)

lemma min_proofs_sound: "x \<in> set xs \<Longrightarrow> min_proofs f xs \<le> f x"
  by (auto simp: min_proofs_def split: list.splits)

lemma min_proofs_fundef_cong[fundef_cong]: "(\<And>x. x \<in> set xs \<Longrightarrow> f x = f' x) \<Longrightarrow>
  min_proofs f xs = min_proofs f' xs"
  by (auto simp: min_proofs_def split: list.splits)

lemma min_proofs_Cons:
  fixes f :: "'a \<Rightarrow> enat"
  shows "min_proofs f (p # qs) = (case qs of [] \<Rightarrow> f p | _ \<Rightarrow> min (f p) (min_proofs f qs))"
  by (auto simp: min_proofs_def split: list.splits)

lemma min_Min_insert: "finite Z \<Longrightarrow> min x (Min (insert y Z)) = Min ({x, y} \<union> Z)"
  by auto

lemma min_proofs_app:
  fixes f :: "'a \<Rightarrow> enat"
  shows "min_proofs f (qs @ [p]) = (case qs of [] \<Rightarrow> f p | _ \<Rightarrow> min (f p) (min_proofs f qs))"
  apply (auto simp: min_proofs_def split: list.splits)
  subgoal for x xs
    unfolding min_Min_insert[OF finite_imageI[OF finite_set]]
    by (rule arg_cong[of _ _ Min]) auto
  done

(* Setup for sum measures *)

definition "sum_proofs f xs = sum_list (map f xs)"

lemma sum_proofs_empty[simp]: "sum_proofs f [] = 0"
  by (auto simp: sum_proofs_def)

lemma sum_proofs_fundef_cong[fundef_cong]: "(\<And>x. x \<in> set xs \<Longrightarrow> f x = f' x) \<Longrightarrow>
  sum_proofs f xs = sum_proofs f' xs"
  by (induction xs) (auto simp: sum_proofs_def)

lemma sum_proofs_Cons:
  fixes f :: "'a \<Rightarrow> nat"
  shows "sum_proofs f (p # qs) = f p + sum_proofs f qs"
  by (auto simp: sum_proofs_def split: list.splits)

lemma sum_proofs_app:
  fixes f :: "'a \<Rightarrow> nat"
  shows "sum_proofs f (qs @ [p]) = f p + sum_proofs f qs"
  by (auto simp: sum_proofs_def split: list.splits)

(* Setup for time-point measures *)

fun s_htp :: "'a sproof \<Rightarrow> nat" and v_htp :: "'a vproof \<Rightarrow> nat" where
  "s_htp (STT i) = i"
| "s_htp (SAtm atm i) = i"
| "s_htp (SNeg p) = v_htp p"
| "s_htp (SDisjL p) = s_htp p"
| "s_htp (SDisjR q) = s_htp q"
| "s_htp (SConj p q) = max (s_htp p) (s_htp q)"
| "s_htp (SSince p qs) = max_proofs s_htp (p # qs)"
| "s_htp (SUntil qs p) = max_proofs s_htp (qs @ [p])"
| "s_htp (SNext p) = s_htp p"
| "s_htp (SPrev p) = max (s_at (SPrev p)) (s_htp p)"
| "s_htp (SImplL p) = v_htp p"
| "s_htp (SImplR q) = s_htp q"
| "s_htp (SIff_ss p q) = max (s_htp p) (s_htp q)"
| "s_htp (SIff_vv p q) = max (v_htp p) (v_htp q)"
| "s_htp (SOnce i p) = max i (s_htp p)"
| "s_htp (SEventually i p) = max i (s_htp p)"
| "s_htp (SHistorically i li qs) = max (max i li) (max_proofs s_htp qs)"
| "s_htp (SHistorically_le i) = i"
| "s_htp (SAlways i hi qs) = max (max i (Suc hi)) (max_proofs s_htp qs)"
| "v_htp (VFF i) = i"
| "v_htp (VAtm atm i) = i"
| "v_htp (VNeg p) = s_htp p"
| "v_htp (VDisj p q) = max (v_htp p) (v_htp q)"
| "v_htp (VConjL p) = v_htp p"
| "v_htp (VConjR q) = v_htp q"
| "v_htp (VSince i p qs) = max i (max_proofs v_htp (p # qs))"
| "v_htp (VUntil i qs p) = max i (max_proofs v_htp (qs @ [p]))"
| "v_htp (VSince_never i li qs) = max (max i li) (max_proofs v_htp qs)"
| "v_htp (VUntil_never i hi qs) = max (max i (Suc hi)) (max_proofs v_htp qs)"
| "v_htp (VSince_le i) = i"
| "v_htp (VNext p) = v_htp p"
| "v_htp (VNext_le i) = Suc i"
| "v_htp (VNext_ge i) = Suc i"
| "v_htp (VPrev p) = max (v_at (VPrev p)) (v_htp p)"
| "v_htp (VPrev_le i) = i"
| "v_htp (VPrev_ge i) = i"
| "v_htp (VPrev_zero) = 0"
| "v_htp (VImpl p q) = max (s_htp p) (v_htp q)"
| "v_htp (VIff_sv p q) = max (s_htp p) (v_htp q)"
| "v_htp (VIff_vs p q) = max (v_htp p) (s_htp q)"
| "v_htp (VOnce_le i) = i"
| "v_htp (VOnce i li qs) = max (max i li) (max_proofs v_htp qs)"
| "v_htp (VEventually i hi qs) = max (max i (Suc hi)) (max_proofs v_htp qs)"
| "v_htp (VHistorically i p) = max i (v_htp p)"
| "v_htp (VAlways i p) = max i (v_htp p)"

lemma at_htp:
  fixes p :: "'a sproof" and p' :: "'a vproof"
  shows "s_at p \<le> s_htp p" "v_at p' \<le> v_htp p'"
   apply (induction rule: s_at_v_at.induct)
  using max_proofs_sound[where ?f=s_htp]
  by (fastforce simp: max_proofs_Cons dest!: last_in_set split: list.splits if_splits)+

fun s_ltp :: "'a sproof \<Rightarrow> enat" and v_ltp :: "'a vproof \<Rightarrow> enat" where
  "s_ltp (STT i) = i"
| "s_ltp (SAtm atm i) = i"
| "s_ltp (SNeg p) = v_ltp p"
| "s_ltp (SDisjL p) = s_ltp p"
| "s_ltp (SDisjR q) = s_ltp q"
| "s_ltp (SConj p q) = min (s_ltp p) (s_ltp q)"
| "s_ltp (SSince p qs) = min_proofs s_ltp (p # qs)"
| "s_ltp (SUntil qs p) = min_proofs s_ltp (qs @ [p])"
| "s_ltp (SNext p) = min (s_at (SNext p)) (s_ltp p)"
| "s_ltp (SPrev p) = s_ltp p"

| "s_ltp (SImplL p) = v_ltp p"
| "s_ltp (SImplR q) = s_ltp q"
| "s_ltp (SIff_ss p q) = min (s_ltp p) (s_ltp q)"
| "s_ltp (SIff_vv p q) = min (v_ltp p) (v_ltp q)"
| "s_ltp (SOnce i p) = min i (s_ltp p)"
| "s_ltp (SEventually i p) = min i (s_ltp p)"
| "s_ltp (SHistorically i li qs) = min (min i li) (min_proofs s_ltp qs)"
| "s_ltp (SHistorically_le i) = i"
| "s_ltp (SAlways i hi qs) = min (min i hi) (min_proofs s_ltp qs)"

| "v_ltp (VFF i) = i"
| "v_ltp (VAtm atm i) = i"
| "v_ltp (VNeg p) = s_ltp p"
| "v_ltp (VDisj p q) = min (v_ltp p) (v_ltp q)"
| "v_ltp (VConjL p) = v_ltp p"
| "v_ltp (VConjR q) = v_ltp q"
| "v_ltp (VSince i p qs) = 0"
| "v_ltp (VUntil i qs p) = min i (min_proofs v_ltp (qs @ [p]))"
| "v_ltp (VSince_never i li qs) = 0"
| "v_ltp (VUntil_never i hi qs) = min (min i hi) (min_proofs v_ltp qs)"
| "v_ltp (VSince_le i) = 0"
| "v_ltp (VNext p) = min (v_at (VNext p)) (v_ltp p)"
| "v_ltp (VNext_le i) = i"
| "v_ltp (VNext_ge i) = i"
| "v_ltp (VPrev p) = v_ltp p"
| "v_ltp (VPrev_le i) = i - 1"
| "v_ltp (VPrev_ge i) = i - 1"
| "v_ltp (VPrev_zero) = 0"

| "v_ltp (VImpl p q) = min (s_ltp p) (v_ltp q)"
| "v_ltp (VIff_sv p q) = min (s_ltp p) (v_ltp q)"
| "v_ltp (VIff_vs p q) = min (v_ltp p) (s_ltp q)"
| "v_ltp (VOnce_le i) = 0"
| "v_ltp (VOnce i li qs) = 0"
| "v_ltp (VEventually i hi qs) = min (max i hi) (min_proofs v_htp qs)"
| "v_ltp (VHistorically i p) = min i (v_htp p)"
| "v_ltp (VAlways i p) = min i (v_htp p)"

lemma le_enat_SucI: "x \<le> enat n \<Longrightarrow> x \<le> enat (Suc n)"
  by (metis eSuc_enat ile_eSuc order_trans)

lemma enat_minus_leI: "enat n - m \<le> enat n"
  by (cases m) auto

lemma case_list_app: "(case ys @ [y] of [] \<Rightarrow> a | _ \<Rightarrow> b) = b"
  by (auto split: list.splits)

(* lemma at_ltp:
  fixes p :: "'a sproof" and p' :: "'a vproof"
  shows "s_ltp p \<le> s_at p" "v_ltp p' \<le> v_at p'"
proof (induction rule: s_at_v_at.induct)
  case (9 spsi sphis)
  then show ?case
  proof (cases sphis rule: rev_cases)
    case (snoc ys y)
    have IH: "s_ltp y \<le> enat (s_at y)"
      using 9(2)
      apply (cases sphis)
       apply (auto simp: snoc split: if_splits)
      apply (metis last_ConsR last_snoc)
      done
    then show ?thesis
      apply (auto simp: case_list_app)
      apply (metis list.case_eq_if list.discI order.trans append_is_Nil_conv last_ConsR last_in_set last_snoc min_proofs_sound snoc)
      done
  qed simp
next
  case (10 sphis spsi)
  then show ?case
    apply (auto split: list.splits)
    apply (meson list.set_intros(1) order.trans min_proofs_sound)
    done
qed (auto simp: min.coboundedI1 intro: le_enat_SucI enat_minus_leI) *)

(* Depth measure *)

fun s_depth :: "'a sproof \<Rightarrow> nat" and v_depth :: "'a vproof \<Rightarrow> nat" where
  "s_depth (STT i) = 1"
| "s_depth (SAtm atm i) = 1"
| "s_depth (SNeg p) = Suc (v_depth p)"
| "s_depth (SDisjL p) = Suc (s_depth p)"
| "s_depth (SDisjR q) = Suc (s_depth q)"
| "s_depth (SConj p q) = Suc (max (s_depth p) (s_depth q))"
| "s_depth (SSince p qs) = Suc (max_proofs s_depth (p # qs))"
| "s_depth (SUntil qs p) = Suc (max_proofs s_depth (qs @ [p]))"
| "s_depth (SNext p) = Suc (s_depth p)"
| "s_depth (SPrev p) = Suc (s_depth p)"
| "v_depth (VFF i) = 1"
| "v_depth (VAtm atm i) = 1"
| "v_depth (VNeg p) = Suc (s_depth p)"
| "v_depth (VDisj p q) = Suc (max (v_depth p) (v_depth q))"
| "v_depth (VConjL p) = Suc (v_depth p)"
| "v_depth (VConjR q) = Suc (v_depth q)"
| "v_depth (VSince i p qs) = Suc (max_proofs v_depth (p # qs))"
| "v_depth (VUntil i qs p) = Suc (max_proofs v_depth (qs @ [p]))"
| "v_depth (VSince_never i li qs) = Suc (max_proofs v_depth qs)"
| "v_depth (VUntil_never i hi qs) = Suc (max_proofs v_depth qs)"
| "v_depth (VSince_le i) = 1"
| "v_depth (VNext p) = Suc (v_depth p)"
| "v_depth (VNext_le i) = 1"
| "v_depth (VNext_ge i) = 1"
| "v_depth (VPrev p) = Suc (v_depth p)"
| "v_depth (VPrev_le i) = 1"
| "v_depth (VPrev_ge i) = 1"
| "v_depth (VPrev_zero) = 1"

definition mdepth :: "'a sproof + 'a vproof \<Rightarrow> nat" where
  "mdepth = case_sum s_depth v_depth"

definition strmdepth :: "String.literal sproof + String.literal vproof \<Rightarrow> nat" where
  "strmdepth = mdepth"

definition "rdepth p1 p2 \<longleftrightarrow> strmdepth p1 \<le> strmdepth p2"

global_interpretation mdepth_trans_wqo: trans_wqo rdepth
  defines opt_depth = "mdepth_trans_wqo.Opt"
      and cand_depth = "mdepth_trans_wqo.Cand"
      and is_opt_depth = "mdepth_trans_wqo.optimal"
  apply (unfold_locales)
  unfolding rdepth_def strmdepth_def
                      apply (auto simp: reflp_def transp_def total_on_def mdepth_def max_proofs_Cons)
  subgoal for rho i phi p p' r r'
    by (rule checkApp.cases[of p r]; rule checkApp.cases[of p' r'])
       (auto simp: valid_def proofApp_def mdepth_def max_proofs_Cons max_proofs_app split: sum.splits)
  subgoal for rho i phi p p'
    by (rule checkIncr.cases[of p]; rule checkIncr.cases[of p])
       (auto simp add: valid_def proofIncr_def checkIncr.simps split: sum.splits)
  done

definition "rrdepth = rdepth\<inverse>\<inverse>"

global_interpretation mmdepth_trans_wqo: trans_wqo rrdepth
  defines opt_flipped_depth = "mmdepth_trans_wqo.Opt"
      and cand_flipped_depth = "mmdepth_trans_wqo.Cand"
      and is_opt_flipped_depth = "mmdepth_trans_wqo.optimal"
  using mdepth_trans_wqo.flipped_trans_wqo_axioms
  by (auto simp: rrdepth_def)

(* (Weighted) size measure *)

context
  fixes w :: "'a \<Rightarrow> nat"
begin

fun s_atm :: "'a sproof \<Rightarrow> nat" and v_atm :: "'a vproof \<Rightarrow> nat" where
  "s_atm (STT i) = 1"
| "s_atm (SAtm atm i) = w atm"
| "s_atm (SNeg p) = Suc (v_atm p)"
| "s_atm (SDisjL p) = Suc (s_atm p)"
| "s_atm (SDisjR q) = Suc (s_atm q)"
| "s_atm (SConj p q) = Suc ((s_atm p) + (s_atm q))"
| "s_atm (SSince p qs) = Suc (sum_proofs s_atm (p # qs))"
| "s_atm (SUntil qs p) = Suc (sum_proofs s_atm (qs @ [p]))"
| "s_atm (SNext p) = Suc (s_atm p)"
| "s_atm (SPrev p) = Suc (s_atm p)"
| "v_atm (VFF i) = 1"
| "v_atm (VAtm atm i) = w atm"
| "v_atm (VNeg p) = Suc (s_atm p)"
| "v_atm (VDisj p q) = Suc ((v_atm p) + (v_atm q))"
| "v_atm (VConjL p) = Suc (v_atm p)"
| "v_atm (VConjR q) = Suc (v_atm q)"
| "v_atm (VSince i p qs) = Suc (sum_proofs v_atm (p # qs))"
| "v_atm (VUntil i qs p) = Suc (sum_proofs v_atm (qs @ [p]))"
| "v_atm (VSince_never i li qs) = Suc (sum_proofs v_atm qs)"
| "v_atm (VUntil_never i hi qs) = Suc (sum_proofs v_atm qs)"
| "v_atm (VSince_le _) = 1"
| "v_atm (VNext p) = Suc (v_atm p)"
| "v_atm (VNext_le i) = 1"
| "v_atm (VNext_ge i) = 1"
| "v_atm (VPrev p) = Suc (v_atm p)"
| "v_atm (VPrev_le i) = 1"
| "v_atm (VPrev_ge i) = 1"
| "v_atm (VPrev_zero) = 1"

definition matm :: "'a sproof + 'a vproof \<Rightarrow> nat" where
  "matm = case_sum s_atm v_atm"

end

definition strmatm :: "(String.literal \<Rightarrow> nat) \<Rightarrow> String.literal sproof + String.literal vproof \<Rightarrow> nat" where
  "strmatm = matm"

definition "ratm f p1 p2 \<longleftrightarrow> strmatm f p1 \<le> strmatm f p2"

global_interpretation matm_trans_wqo: trans_wqo "ratm w"
  for w
  defines opt_atm = "matm_trans_wqo.Opt"
      and cand_atm = "matm_trans_wqo.Cand"
      and is_opt_atm = "matm_trans_wqo.optimal"
  apply (unfold_locales)
  unfolding ratm_def strmatm_def
                      apply (auto simp: reflp_def transp_def total_on_def matm_def sum_proofs_Cons)
  subgoal for rho i phi p p' r r'
    by (rule checkApp.cases[of p r]; rule checkApp.cases[of p' r'])
       (auto simp: valid_def matm_def sum_proofs_Cons sum_proofs_app split: sum.splits)
  subgoal for rho i phi p p'
    by (rule checkIncr.cases[of p]; rule checkIncr.cases[of p])
       (auto simp add: valid_def proofIncr_def checkIncr.simps split: sum.splits)
  done

definition "rratm w = (ratm w)\<inverse>\<inverse>"

global_interpretation mmatm_trans_wqo: trans_wqo "rratm w"
  for w
  defines opt_flipped_atm = "mmatm_trans_wqo.Opt"
      and cand_flipped_atm = "mmatm_trans_wqo.Cand"
      and is_opt_flipped_atm = "mmatm_trans_wqo.optimal"
  using matm_trans_wqo.flipped_trans_wqo_axioms
  by (auto simp: rratm_def)

global_interpretation matm_scmonotone: scmonotone "ratm w"
  for w
  apply (unfold_locales)
  unfolding ratm_def strmatm_def
                      apply (auto simp: matm_def sum_proofs_Cons)[26]
  subgoal for rho i phi p p' r r'
    by (rule checkApp.cases[of p r]; rule checkApp.cases[of p' r'])
       (auto simp: valid_def matm_def sum_proofs_Cons sum_proofs_app split: sum.splits)
  subgoal for rho i phi p p' r r'
    by (rule checkApp.cases[of p r]; rule checkApp.cases[of p' r'])
       (auto simp: valid_def matm_def sum_proofs_Cons sum_proofs_app split: sum.splits)
  subgoal for rho i phi p p'
    by (rule checkIncr.cases[of p]; rule checkIncr.cases[of p])
       (auto simp add: valid_def matm_def proofIncr_def checkIncr.simps split: sum.splits)
  done

(* Reach measure *)

lemma valid_sat: "valid rho i phi (Inl p) \<Longrightarrow> sat rho i phi"
  "valid rho i phi (Inr p') \<Longrightarrow> \<not>sat rho i phi"
  using check_sound soundness
  by (fastforce simp: valid_def)+

lemma check_cases:
  "\<And>x y. s_check rho phi (SSince x y) \<Longrightarrow> (case phi of Since _ _ _ \<Rightarrow> True | _ \<Rightarrow> False)"
  "\<And>x y. s_check rho phi (SUntil x y) \<Longrightarrow> (case phi of Until _ _ _ \<Rightarrow> True | _ \<Rightarrow> False)"
  "\<And>i x y. v_check rho phi (VSince i x y) \<Longrightarrow> (case phi of Since _ _ _ \<Rightarrow> True | _ \<Rightarrow> False)"
  "\<And>i li x. v_check rho phi (VSince_never i li x) \<Longrightarrow> (case phi of Since _ _ _ \<Rightarrow> True | _ \<Rightarrow> False)"
  "\<And>i x y. v_check rho phi (VUntil i x y) \<Longrightarrow> (case phi of Until _ _ _ \<Rightarrow> True | _ \<Rightarrow> False)"
  "\<And>i hi x. v_check rho phi (VUntil_never i hi x) \<Longrightarrow> (case phi of Until _ _ _ \<Rightarrow> True | _ \<Rightarrow> False)"
  using check_sound soundness
  by (auto split: mtl.splits)

lemma checkApp_at: "checkApp p r \<Longrightarrow> checkApp p' r' \<Longrightarrow>
  valid rho i phi (p \<oplus> r) \<Longrightarrow> valid rho i phi (p' \<oplus> r') \<Longrightarrow>
  p_at p = p_at p' \<Longrightarrow> p_at r = p_at r' \<Longrightarrow> p_at (p \<oplus> r) = p_at (p' \<oplus> r')"
  by (rule checkApp.cases[of p r]; rule checkApp.cases[of p' r'])
     (auto simp: checkApp.simps p_at_def valid_def split: list.splits)

lemma Cons2_rangeD:
  assumes "a # b # cs = [x..<y] @ [y]"
  shows "x < y \<and> a = x \<and> b = Suc x"
proof -
  have "y = Suc x \<or> Suc x < y"
    using assms
    by (cases "y \<le> x") auto
  then show ?thesis
    using assms
    by (auto simp: upt_conv_Cons)
qed

lemma "valid rho i phi (Inr (VUntil i (r # p1) p2)) \<Longrightarrow> p1 \<noteq> [] \<Longrightarrow> Suc i \<le> v_at p2"
  by (cases phi; cases p1) (auto simp: valid_def Let_def dest: Cons2_rangeD split: if_splits)

lemma checkIncr_at: "checkIncr p \<Longrightarrow> checkIncr p' \<Longrightarrow> p_at p = p_at p' \<Longrightarrow>
  valid rho i phi p \<Longrightarrow> valid rho i phi p' \<Longrightarrow> p_at (proofIncr p) = p_at (proofIncr p')"
  by (rule checkIncr.cases[of p]; rule checkIncr.cases[of p'])
     (auto simp: p_at_def proofIncr_def valid_def dest!: check_cases split: mtl.splits)

definition "incroff p = (case p of Inr (VSince _ _ _) \<Rightarrow> Suc (p_at p) | Inr (VSince_never _ _ _) \<Rightarrow> Suc (p_at p)
  | Inr (VUntil _ _ _) \<Rightarrow> p_at p - 1 | Inr (VUntil_never _ _ _) \<Rightarrow> p_at p - 1)"

lemma p_at_incroff: "valid rho i phi p \<Longrightarrow> checkIncr p \<Longrightarrow>
    valid rho i phi p' \<Longrightarrow> checkIncr p' \<Longrightarrow>
    p_at p = p_at p' \<Longrightarrow> incroff p = incroff p'"
  by (cases phi; rule checkIncr.cases[of p]; rule checkIncr.cases[of p'])
     (auto simp: incroff_def valid_def p_at_def)



definition minreach :: "'a sproof + 'a vproof \<Rightarrow> enat" where
  "minreach = case_sum s_ltp v_ltp"

definition strminreach :: "String.literal sproof + String.literal vproof \<Rightarrow> enat" where
  "strminreach = minreach"

definition "rminminreach p1 p2 \<longleftrightarrow> p_at p1 = p_at p2 \<and> strminreach p1 \<le> strminreach p2"
definition "rmaxminreach p1 p2 \<longleftrightarrow> p_at p1 = p_at p2 \<and> strminreach p1 \<ge> strminreach p2"

lemma valid_VSince_nonempty:
  "valid rho (Suc i) phi (Inr (VSince (Suc i) p1 (p2 @ [r]))) \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> v_at p1 \<le> i"
  by (cases phi; cases p2)
     (auto simp: valid_def Let_def Cons_eq_upt_conv dest: Cons2_rangeD split: if_splits)

lemma valid_VSince_never_nonempty:
  "valid rho (Suc i) phi (Inr (VSince_never (Suc i) li (a # list @ [s]))) \<Longrightarrow> v_at a \<le> enat i"
  by (cases phi) (auto simp: valid_def Cons_eq_upt_conv split: if_splits enat.splits)

lemma min_permute1: fixes x0 :: "'a :: linorder"
  shows "x1 \<le> x4 \<Longrightarrow> min x0 (min x1 (case p2 of [] \<Rightarrow> x2 | a # list \<Rightarrow> min x2 x3)) =
    min x0 (min (min x4 (case p2 of [] \<Rightarrow> x1 | a # list \<Rightarrow> min x1 x3)) x2)"
  by (auto simp: min_def split: list.splits)

lemma min_permute2: fixes x0 :: "'a :: linorder"
  shows "x5 \<le> x1 \<Longrightarrow> min (min x0 x2) (min x5 (case list of [] \<Rightarrow> x3 | a # lista \<Rightarrow> min x3 x4)) =
    min x0 (min (min (min x1 x2) (case list of [] \<Rightarrow> x5 | aa # lista \<Rightarrow> min x5 x4)) x3)"
  by (auto simp: min_def split: list.splits)

lemma min_permute3: fixes x0 :: "'a :: linorder"
  shows "x0 \<le> x5 \<Longrightarrow> min x0 (min x1 (min x2 x3)) = min x0 (min (min x5 (min x2 x3)) x1)"
  by (auto simp: min_def split: list.splits)

lemma min_permute4: fixes x0 :: "'a :: linorder"
  shows "x1 \<le> x0 \<Longrightarrow> x0 \<le> x1 \<Longrightarrow> x0 \<le> x2 \<Longrightarrow> min x0 (min x3 x4) = min x1 (min (min x2 x4) x3)"
  by (auto simp: min_def split: list.splits)

lemma checkApp_minreach: "checkApp p r \<Longrightarrow>
  valid rho i phi (p \<oplus> r) \<Longrightarrow> minreach (p \<oplus> r) = min (p_at (p \<oplus> r)) (min (minreach p) (minreach r))"
  apply (rule checkApp.cases[of p r])
        apply simp
  subgoal for p1 p2 r
    using at_ltp(1)[of r]
    apply (auto simp: minreach_def min_proofs_Cons min_proofs_app case_list_app p_at_def)   
    apply (auto simp: min_def split: list.split)
    done
  subgoal for p1 p2 r
    using at_ltp(1)[of r]
    apply (auto simp: minreach_def min_proofs_Cons min_proofs_app case_list_app p_at_def)   
    apply (auto simp: min_def split: list.split)
    done
  subgoal for p2 j p1 s
    using at_ltp(2)[of p1] valid_VSince_nonempty[of rho j phi p1 p2 s] order_subst1
    by (fastforce simp: minreach_def min_proofs_Cons min_proofs_app case_list_app p_at_def valid_def split: if_splits intro!: min_permute1)
  subgoal for p1 j li s
    apply (cases p1)
    using valid_VSince_never_nonempty at_ltp(2)
    by (auto simp: minreach_def case_list_app min_proofs_Cons min_proofs_app p_at_def valid_def intro!: min_permute2)
  subgoal for p1 j p2 s
    using at_ltp(2)[of p2]
    by (cases p1) (auto simp: minreach_def min_proofs_Cons min_proofs_app case_list_app p_at_def valid_def split: if_splits intro!: min_permute3)
  subgoal for p1 j hi s
    by (cases phi; cases p1) (auto simp: minreach_def p_at_def min_proofs_Cons valid_def i_le_ltpi_add intro!: min_permute4)
  done

lemma v_at_ltp_chain: "v_at p1 \<le> i \<Longrightarrow> enat i \<le> v_ltp p1 \<Longrightarrow> v_ltp p1 = enat i"
  using at_ltp(2)[of p1]
  by (meson Orderings.order_class.dual_order.antisym enat_ord_simps(1) order_trans)

lemma min_permute5: fixes x0 :: "'a :: linorder"
  shows "x0 \<le> x2 \<Longrightarrow> min x0 x1 = min (min x2 x1) x0"
  by (auto simp: min_def)

lemma min_permute6: fixes x0 :: "'a :: linorder"
  shows "x1 \<le> x3 \<Longrightarrow> min (min x0 x1) x2 = min (min (min x3 x1) x2) x0"
  by (auto simp: min_def)

lemma min_permute7:
  shows "x0 \<le> x1 \<Longrightarrow> min (enat (min x0 x2)) x3 =
    min (min (enat (min x1 x2)) x3) (enat x0)"
  apply (auto simp: min_def)
    apply (meson order.trans enat_ord_simps(1))
   apply (meson enat_ord_simps(1) order_trans)
  apply (meson order.trans enat_ord_simps(1) linear)
  done

lemma v_check_VSince_never_li: "v_check rho phi (VSince_never i li p1) \<Longrightarrow> li \<le> i"
  apply (cases phi)
           apply (auto split: enat.splits if_splits)
   apply (meson diff_le_self i_etp_to_tau)+
  done

lemma minr: "checkIncr p \<Longrightarrow> valid rho i phi p \<Longrightarrow> minreach (proofIncr p) = min (minreach p) (incroff p)"
  apply (rule checkIncr.cases[of p])
      apply (auto simp: proofIncr_def minreach_def valid_def incroff_def min_proofs_Cons min_proofs_app p_at_def)
  subgoal for p1 p2
    by (rule min_permute5) auto
  subgoal for p1 li
    by (rule min_permute7) auto
  done

global_interpretation minminreach_trans_wqo: trans_wqo rminminreach
  defines opt_minminreach = "minminreach_trans_wqo.Opt"
    and cand_minminreach = "minminreach_trans_wqo.Cand"
    and is_opt_minminreach = "minminreach_trans_wqo.optimal"
  apply (unfold_locales)
  unfolding rminminreach_def strminreach_def
                      apply (auto simp: p_at_def minreach_def min_proofs_Cons Lattices.linorder_class.min.coboundedI1 Lattices.linorder_class.min.coboundedI2)[21]
  subgoal for rho i phi p p' r r'
    using checkApp_at[of p r p' r' rho i phi]
    by (auto simp only: checkApp_minreach min_def split: if_splits)
  subgoal for rho i phi p p'
    using checkIncr_at[of p p' rho i phi] p_at_incroff[of rho i phi p p']
    by (auto simp only: minr min_def split: if_splits)
  apply (auto simp: reflp_def transp_def total_on_def valid_def p_at_def split: sum.splits)
  done

global_interpretation maxminreach_trans_wqo: trans_wqo rmaxminreach
  defines opt_maxminreach = "maxminreach_trans_wqo.Opt"
    and cand_maxminreach = "maxminreach_trans_wqo.Cand"
    and is_opt_maxminreach = "maxminreach_trans_wqo.optimal"
  apply (unfold_locales)
  unfolding rmaxminreach_def strminreach_def
                      apply (auto simp: p_at_def minreach_def min_proofs_Cons Lattices.linorder_class.min.coboundedI1 Lattices.linorder_class.min.coboundedI2)[21]
  subgoal for rho i phi p p' r r'
    using checkApp_at[of p r p' r' rho i phi]
    by (auto simp only: checkApp_minreach min_def split: if_splits)
  subgoal for rho i phi p p'
    using checkIncr_at[of p p' rho i phi] p_at_incroff[of rho i phi p p']
    by (auto simp only: minr min_def split: if_splits)
  apply (auto simp: reflp_def transp_def total_on_def valid_def p_at_def split: sum.splits)
  done


definition maxreach :: "'a sproof + 'a vproof \<Rightarrow> nat" where
  "maxreach = case_sum s_htp v_htp"

definition strmaxreach :: "String.literal sproof + String.literal vproof \<Rightarrow> nat" where
  "strmaxreach = maxreach"

definition "rminmaxreach p1 p2 \<longleftrightarrow> p_at p1 = p_at p2 \<and> strmaxreach p1 \<le> strmaxreach p2"
definition "rmaxmaxreach p1 p2 \<longleftrightarrow> p_at p1 = p_at p2 \<and> strmaxreach p1 \<ge> strmaxreach p2"

lemma checkApp_maxreach: "checkApp p r \<Longrightarrow>
  valid rho i phi (p \<oplus> r) \<Longrightarrow> maxreach (p \<oplus> r) = max (p_at (p \<oplus> r)) (max (maxreach p) (maxreach r))"
  apply (rule checkApp.cases[of p r])
        apply (auto simp: maxreach_def max_proofs_Cons max_proofs_app p_at_def split: list.splits)
  subgoal for p1 p
    using at_htp(1)[of p]
    by auto
  subgoal for p1 p2 r p ps
    using at_htp(1)[of r]
    by (cases ps rule: rev_cases) auto
  subgoal for p1 p2 r
    using at_htp(1)[of r]
    by auto
  subgoal for p1 j p2 r
    using at_htp(2)[of p2]
    by (cases phi; cases p1; cases j)
       (auto simp: valid_def Let_def dest!: Cons2_rangeD split: if_splits)
  subgoal for p1 j hi r
    by (cases phi; cases p1; cases j)
       (auto simp: valid_def Let_def max_def dest!: Cons2_rangeD split: if_splits)
  done

lemma v_check_VUntil_never_hi: "v_check rho phi (VUntil_never i hi ps) \<Longrightarrow> i \<le> hi"
  using i_le_ltpi_add
  by (cases phi) fastforce+

lemma maxr: "checkIncr p \<Longrightarrow> valid rho i phi p \<Longrightarrow> maxreach (proofIncr p) = max (maxreach p) (incroff p)"
  by (rule checkIncr.cases[of p])
     (auto simp: proofIncr_def maxreach_def valid_def incroff_def max_proofs_Cons max_proofs_app p_at_def dest: v_check_VUntil_never_hi le_trans[OF _ at_htp(2), of i])

global_interpretation minmaxreach_trans_wqo: trans_wqo rminmaxreach
  defines opt_minmaxreach = "minmaxreach_trans_wqo.Opt"
    and cand_minmaxreach = "minmaxreach_trans_wqo.Cand"
    and is_opt_minmaxreach = "minmaxreach_trans_wqo.optimal"
  apply (unfold_locales)
  unfolding rminmaxreach_def strmaxreach_def
                      apply (auto simp: p_at_def maxreach_def max_proofs_Cons)[21]
  subgoal for rho i phi p p' r r'
    using checkApp_at[of p r p' r' rho i phi]
    by (auto simp only: checkApp_maxreach)
  subgoal for rho i phi p p'
    using checkIncr_at[of p p' rho i phi] p_at_incroff[of rho i phi p p']
    by (auto simp only: maxr)
  apply (auto simp: reflp_def transp_def total_on_def valid_def p_at_def split: sum.splits)
  done

global_interpretation maxmaxreach_trans_wqo: trans_wqo rmaxmaxreach
  defines opt_maxmaxreach = "maxmaxreach_trans_wqo.Opt"
    and cand_maxmaxreach = "maxmaxreach_trans_wqo.Cand"
    and is_opt_maxmaxreach = "maxmaxreach_trans_wqo.optimal"
  apply (unfold_locales)
  unfolding rmaxmaxreach_def strmaxreach_def
                      apply (auto simp: p_at_def maxreach_def max_proofs_Cons)[21]
  subgoal for rho i phi p p' r r'
    using checkApp_at[of p r p' r' rho i phi]
    by (auto simp only: checkApp_maxreach)
  subgoal for rho i phi p p'
    using checkIncr_at[of p p' rho i phi] p_at_incroff[of rho i phi p p']
    by (auto simp only: maxr)
  apply (auto simp: reflp_def transp_def total_on_def valid_def p_at_def split: sum.splits)
  done

definition "rlex_atm_minmaxreach w = lex_wqo (ratm w) rminmaxreach"

global_interpretation lex_ratm_minmaxreach_trans_wqo: trans_wqo "rlex_atm_minmaxreach w"
  for w
  defines opt_lex_atm_minmaxreach = "lex_ratm_minmaxreach_trans_wqo.Opt"
      and cand_lex_atm_minmaxreach = "lex_ratm_minmaxreach_trans_wqo.Cand"
      and is_opt_lex_atm_minmaxreach = "lex_ratm_minmaxreach_trans_wqo.optimal"
  unfolding rlex_atm_minmaxreach_def
  by (rule lex_trans_wqo.lex_trans_wqo_axioms) unfold_locales

(* Code setup for v_check *)

lemma ETP_minus_le_iff: "ETP rho (\<tau> rho i - n) \<le> j \<longleftrightarrow> delta rho i j \<le> n"
  by (simp add: Groups.ab_semigroup_add_class.add.commute i_etp_to_tau le_diff_conv)

lemma ETP_minus_gt_iff: "j < ETP rho (\<tau> rho i - n) \<longleftrightarrow> delta rho i j > n"
  by (meson ETP_minus_le_iff leD le_less_linear)

lemma nat_le_iff_less:
  fixes n :: nat
  shows "(j \<le> n) \<longleftrightarrow> (j = 0 \<or> j - 1 < n)"
  by auto

lemma ETP_minus_eq_iff: "j = ETP rho (\<tau> rho i - n) \<longleftrightarrow> ((j = 0 \<or> n < delta rho i (j - 1)) \<and> delta rho i j \<le> n)"
  unfolding eq_iff[of j "ETP rho (\<tau> rho i - n)"]
  unfolding nat_le_iff_less[of j]
  unfolding ETP_minus_le_iff ETP_minus_gt_iff
  by auto

lemma LTP_minus_ge_iff: "\<tau> rho 0 + n \<le> \<tau> rho i \<Longrightarrow> j \<le> LTP rho (\<tau> rho i - n) \<longleftrightarrow>
  (case n of 0 \<Rightarrow> delta rho j i = 0 | _ \<Rightarrow> j \<le> i \<and> delta rho i j \<ge> n)"
  by (auto simp add: i_ltp_to_tau split: nat.splits)
     (smt (z3) Groups.ab_semigroup_add_class.add.commute add_Suc_right add_leD2 etp_ge i_etp_to_tau le_diff_conv2 less_le_trans less_or_eq_imp_le plus_1_eq_Suc)

lemma LTP_plus_ge_iff: "j \<le> LTP rho (\<tau> rho i + n) \<longleftrightarrow> delta rho j i \<le> n"
  by (smt (z3) MTL_Code.minminreach_trans_wqo.diff_cancel_middle \<tau>_mono diff_self_eq_0 i_ltp_to_tau le_diff_conv le_imp_diff_is_add nat_le_iff_add trans_le_add2 add.commute)

lemma LTP_minus_lt_if:
  assumes "j \<le> i" "\<tau> rho 0 + n \<le> \<tau> rho i" "delta rho i j < n"
  shows "LTP rho (\<tau> rho i - n) < j"
proof -
  have not_in: "k \<notin> {ia. \<tau> rho ia \<le> \<tau> rho i - n}" if "j \<le> k" for k
    using assms \<tau>_mono[OF that, of rho]
    by auto
  then have "{ia. \<tau> rho ia \<le> \<tau> rho i - n} \<subseteq> {0..<j}"
    apply auto
    using not_le_imp_less
    by blast
  then have "finite {ia. \<tau> rho ia \<le> \<tau> rho i - n}"
    using subset_eq_atLeast0_lessThan_finite
    by blast
  moreover have "0 \<in> {ia. \<tau> rho ia \<le> \<tau> rho i - n}"
    using assms(2)
    by auto
  ultimately show ?thesis
    unfolding LTP_def
    by (metis Max_in not_in empty_iff not_le_imp_less)
qed

lemma LTP_minus_lt_iff:
  assumes "\<tau> rho 0 + n \<le> \<tau> rho i"
  shows "LTP rho (\<tau> rho i - n) < j \<longleftrightarrow> (if \<not> j \<le> i \<and> n = 0 then delta rho j i > 0 else delta rho i j < n)"
proof (cases "j \<le> i")
  case True
  then show ?thesis
    using assms i_le_ltpi_minus[of rho n i] LTP_minus_lt_if[of j i rho n]
    apply (cases n)
     apply auto
     apply (meson i_le_ltpi leD le_trans)
    apply (smt (verit) MTL_Code.minminreach_trans_wqo.diff_cancel_middle \<tau>_mono diff_is_0_eq diff_le_self i_ltp_to_tau le_add_diff_inverse2 le_trans not_le_imp_less zero_less_diff)
    done
next
  case False
  have delta: "delta rho i j = 0"
    using False
    by auto
  show ?thesis
  proof (cases n)
    case 0
    show ?thesis
      using False assms
      by (auto simp: 0 i_ltp_to_tau not_le_imp_less)
         (metis delta diff_is_0_eq i_le_ltpi leD le_neq_implies_less)
  next
    case (Suc n')
    then show ?thesis
      using False assms
      by auto (metis (no_types, lifting) Zero_not_Suc add_Suc_right add_diff_cancel_left' diff_is_0_eq' i_le_ltpi_minus le_less_trans less_or_eq_imp_le neq0_conv not_le_imp_less)
  qed
qed

lemma LTP_minus_eq_iff:
  assumes "\<tau> rho 0 + n \<le> \<tau> rho i"
  shows "j = LTP rho (\<tau> rho i - n) \<longleftrightarrow>
  (case n of 0 \<Rightarrow> i \<le> j \<and> delta rho j i = 0 \<and> delta rho (Suc j) j > 0
  | _ \<Rightarrow> j \<le> i \<and> n \<le> delta rho i j \<and> delta rho i (Suc j) < n)"
proof (cases n)
  case 0
  show ?thesis
    using assms
    apply (auto simp: 0 i_le_ltpi)
      apply (metis "0" Nat.add_0_right assms i_ltp_to_tau order_refl)
     apply (metis Groups.monoid_add_class.add.right_neutral Suc_n_not_le_n \<tau>_mono eq_imp_le i_ltp_to_tau le_add2 le_neq_implies_less plus_1_eq_Suc)
    apply (metis "0" Groups.monoid_add_class.add.right_neutral assms i_ltp_to_tau leD le_\<tau>_less le_less_Suc_eq le_less_linear le_neq_implies_less)
    done
next
  case (Suc n')
  show ?thesis
    using assms
    by (simp add: Suc eq_iff[of j "LTP rho (\<tau> rho i - Suc n')"] less_Suc_eq_le[of "LTP rho (\<tau> rho i - Suc n')" j, symmetric] LTP_minus_ge_iff LTP_minus_lt_iff)
qed

lemma LTP_plus_eq_iff:
  shows "j = LTP rho (\<tau> rho i + n) \<longleftrightarrow> (delta rho j i \<le> n \<and> delta rho (Suc j) i > n)"
  unfolding eq_iff[of j "LTP rho (\<tau> rho i + n)"]
  unfolding LTP_plus_ge_iff
  apply auto
   apply (meson LTP_plus_ge_iff le_less_linear not_less_eq_eq)
  apply (meson LTP_plus_ge_iff leD not_less_eq_eq)
  done

lemma l_def: "\<tau> rho 0 + left I \<le> \<tau> rho i \<Longrightarrow> l rho i I = (case left I of 0 \<Rightarrow> i | _ \<Rightarrow> LTP rho (\<tau> rho i - left I))"
  using i_le_ltpi
  by (auto simp: min_def split: nat.splits)
     (metis Suc_le_lessD add_Suc_right i_le_ltpi_minus leD le_zero_eq not_add_less1 not_le_imp_less zero_less_Suc)

definition "check_upt_l rho I li xs i \<longleftrightarrow> (case xs of [] \<Rightarrow>
  (case left I of 0 \<Rightarrow> i < li | Suc n \<Rightarrow>
    (if \<not> li \<le> i \<and> left I = 0 then 0 < delta rho li i else delta rho i li < left I))
  | _ \<Rightarrow> xs = [li..<li + length xs] \<and>
    (case left I of 0 \<Rightarrow> li + length xs - 1 = i | Suc n \<Rightarrow>
      (li + length xs - 1 \<le> i \<and> left I \<le> delta rho i (li + length xs - 1) \<and> delta rho i (li + length xs) < left I)))"

lemma check_upt_l_cong:
  assumes "\<And>j. j \<le> max i li \<Longrightarrow> \<tau> rho j = \<tau> rho' j"
  shows "check_upt_l rho I li xs i = check_upt_l rho' I li xs i"
proof -
  have "li + length ys \<le> i \<Longrightarrow> Suc n \<le> delta rho' i (li + length ys) \<Longrightarrow>
    (Suc (li + length ys)) \<le> i" for ys :: "nat list" and n
    by (cases "li + length ys = i") auto
  then show ?thesis
    using assms
    by (fastforce simp: check_upt_l_def Let_def simp del: upt.simps split: list.splits nat.splits)
qed

lemma check_upt_l_eq:
  assumes "\<tau> rho 0 + left I \<le> \<tau> rho i"
  shows "xs = [li..<Suc (l rho i I)] \<longleftrightarrow> check_upt_l rho I li xs i"
proof -
  have "li + length xs = Suc (l rho i I) \<longleftrightarrow> li + length xs - 1 = l rho i I" if "xs \<noteq> []"
    using that
    by (cases xs) auto
  then have "xs = [li..<Suc (l rho i I)] \<longleftrightarrow> (xs = [] \<and> l rho i I < li) \<or>
    (xs \<noteq> [] \<and> xs = [li..<li + length xs] \<and> li + length xs - 1 = l rho i I)"
    by auto
  moreover have "\<dots> \<longleftrightarrow> (xs = [] \<and>
    (case left I of 0 \<Rightarrow> i < li | Suc n \<Rightarrow>
      (if \<not> li \<le> i \<and> left I = 0 then 0 < delta rho li i else delta rho i li < left I))) \<or>
    (xs \<noteq> [] \<and> xs = [li..<li + length xs] \<and>
    (case left I of 0 \<Rightarrow> li + length xs - 1 = i | Suc n \<Rightarrow>
      (case left I of 0 \<Rightarrow> i \<le> li + length xs - 1 \<and>
        delta rho (li + length xs - 1) i = 0 \<and> 0 < delta rho (Suc (li + length xs - 1)) (li + length xs - 1)
      | Suc n \<Rightarrow> li + length xs - 1 \<le> i \<and>
        left I \<le> delta rho i (li + length xs - 1) \<and> delta rho i (Suc (li + length xs - 1)) < left I)))"
    using l_def[OF assms, symmetric]
    unfolding LTP_minus_lt_iff[OF assms, symmetric]
    unfolding LTP_minus_eq_iff[OF assms, symmetric]
    by (auto split: nat.splits)
  moreover have "\<dots> \<longleftrightarrow> (case xs of [] \<Rightarrow>
    (case left I of 0 \<Rightarrow> i < li | Suc n \<Rightarrow>
      (if \<not> li \<le> i \<and> left I = 0 then 0 < delta rho li i else delta rho i li < left I))
    | _ \<Rightarrow> xs = [li..<li + length xs] \<and>
      (case left I of 0 \<Rightarrow> li + length xs - 1 = i | Suc n \<Rightarrow>
        (li + length xs - 1 \<le> i \<and> left I \<le> delta rho i (li + length xs - 1) \<and> delta rho i (li + length xs) < left I)))"
    by (auto split: nat.splits list.splits)
  ultimately show ?thesis
    unfolding check_upt_l_def
    by simp
qed

declare v_check_simps(9)[code del]

lemma v_check_Since_code[code]: "v_check rho (Since phi I psi) p = (case p of
  VSince i vphi vpsis \<Rightarrow>
   let j = v_at vphi
   in (case right I of enat n \<Rightarrow> delta rho i j \<le> n | \<infinity> \<Rightarrow> True) \<and>
      j \<le> i \<and>
      \<tau> rho 0 + left I \<le> \<tau> rho i \<and>
      check_upt_l rho I j (map v_at vpsis) i \<and>
      v_check rho phi vphi \<and> Ball (set vpsis) (v_check rho psi)
  | VSince_never i li vpsis \<Rightarrow>
     (case right I of enat n \<Rightarrow> ((li = 0 \<or> n < delta rho i (li - 1)) \<and> delta rho i li \<le> n) | \<infinity> \<Rightarrow> li = 0) \<and>
     \<tau> rho 0 + left I \<le> \<tau> rho i \<and>
     check_upt_l rho I li (map v_at vpsis) i \<and> Ball (set vpsis) (v_check rho psi)
  | VSince_le i \<Rightarrow> \<tau> rho i < \<tau> rho 0 + left I | _ \<Rightarrow> False)"
  by (auto simp: Let_def check_upt_l_eq ETP_minus_le_iff ETP_minus_eq_iff split: vproof.splits enat.splits simp del: upt_Suc)

lemma lu_le_iff: "max i (ETP rho (\<tau> rho i + n)) \<le> j \<longleftrightarrow> i \<le> j \<and> delta rho j i \<ge> n"
  by (metis Groups.ab_semigroup_add_class.add.commute Lattices.linorder_class.max.bounded_iff
      \<tau>_mono i_etp_to_tau le_diff_conv2)

lemma lu_ge_iff: "j \<le> max i (ETP rho (\<tau> rho i + n)) \<longleftrightarrow> (case n of 0 \<Rightarrow> j \<le> i
  | Suc n' \<Rightarrow> (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> delta rho j' i < n))"
proof (cases n)
  case 0
  show ?thesis
    by (auto simp: 0 max_def) (metis i_ge_etpi verit_la_disequality)
next
  case (Suc n')
  have max: "max i (ETP rho (\<tau> rho i + n)) = ETP rho (\<tau> rho i + n)"
    by (auto simp: max_def Suc)
       (metis Groups.ab_semigroup_add_class.add.commute etp_ge less_or_eq_imp_le plus_1_eq_Suc)
  have "j \<le> max i (ETP rho (\<tau> rho i + n)) \<longleftrightarrow> (\<forall>ia. \<tau> rho i + n \<le> \<tau> rho ia \<longrightarrow> j \<le> ia)"
    unfolding max
    unfolding ETP_def
    by (meson LeastI_ex Least_le order.trans ex_le_\<tau>)
  moreover have "\<dots> \<longleftrightarrow> (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> \<not>\<tau> rho i + n \<le> \<tau> rho j')"
    by (auto split: nat.splits) (meson i_etp_to_tau le_trans not_less_eq_eq)
  moreover have "\<dots> \<longleftrightarrow> (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> delta rho j' i < n)"
    by (auto simp: Suc split: nat.splits)
  ultimately show ?thesis
    by (auto simp: Suc)
qed

definition "check_upt_lu rho I i xs hi \<longleftrightarrow> (let j = Suc hi - length xs in
  (case xs of [] \<Rightarrow> (case left I of 0 \<Rightarrow> Suc hi \<le> i | Suc n' \<Rightarrow> delta rho hi i < left I)
  | _ \<Rightarrow> (xs = [j..<Suc hi] \<and>
  (case left I of 0 \<Rightarrow> j \<le> i | Suc n' \<Rightarrow>
  (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> delta rho j' i < left I)) \<and>
  i \<le> j \<and> left I \<le> delta rho j i)))"

lemma check_upt_lu_cong:
  assumes "\<And>j. min i hi \<le> j \<and> j \<le> max i hi \<Longrightarrow> \<tau> rho j = \<tau> rho' j"
  shows "check_upt_lu rho I i xs hi = check_upt_lu rho' I i xs hi"
  using assms
  apply (auto simp: check_upt_lu_def Let_def simp del: upt.simps split: list.splits nat.splits)
   apply (smt (z3) Lattices.linorder_class.min.coboundedI1 \<tau>_mono diff_is_0_eq diff_le_self le_Suc_eq le_add2 le_max_iff_disj le_trans plus_1_eq_Suc)
  apply (smt (z3) Lattices.linorder_class.min.coboundedI1 \<tau>_mono diff_is_0_eq diff_le_self le_Suc_eq le_add2 le_max_iff_disj le_trans plus_1_eq_Suc)
  done

lemma check_upt_lu_eq: "xs = [lu rho i I..<Suc hi] \<longleftrightarrow> check_upt_lu rho I i xs hi"
proof -
  have F1: "(case left I of 0 \<Rightarrow> Suc hi \<le> i | Suc n' \<Rightarrow> delta rho hi i < left I) =
    (Suc hi \<le> lu rho i I)"
    unfolding lu_ge_iff[where ?j="Suc hi" and ?n="left I"]
    by (auto split: nat.splits)
  have "xs = [lu rho i I..<Suc hi] \<longleftrightarrow> (let j = Suc hi - length xs in
    (xs = [] \<and> (case left I of 0 \<Rightarrow> Suc hi \<le> i | Suc n' \<Rightarrow> delta rho hi i < left I)) \<or>
    (xs \<noteq> [] \<and> xs = [j..<Suc hi] \<and>
    (case left I of 0 \<Rightarrow> j \<le> i | Suc n' \<Rightarrow>
    (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> delta rho j' i < left I)) \<and>
    i \<le> j \<and> left I \<le> delta rho j i))"
    unfolding F1
    unfolding Let_def
    unfolding lu_ge_iff[where ?n="left I", symmetric]
    unfolding lu_le_iff[where ?n="left I", symmetric]
    unfolding eq_iff[of _ "lu rho i I", symmetric]
    by auto
  moreover have "\<dots> \<longleftrightarrow> (let j = Suc hi - length xs in
    (case xs of [] \<Rightarrow> (case left I of 0 \<Rightarrow> Suc hi \<le> i | Suc n' \<Rightarrow> delta rho hi i < left I)
    | _ \<Rightarrow> (xs = [j..<Suc hi] \<and>
    (case left I of 0 \<Rightarrow> j \<le> i | Suc n' \<Rightarrow>
    (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> delta rho j' i < left I)) \<and>
    i \<le> j \<and> left I \<le> delta rho j i)))"
    by (auto simp: Let_def split: list.splits)
  finally show ?thesis
    unfolding check_upt_lu_def .
qed

declare v_check_simps(10)[code del]

lemma v_check_Until_code[code]: "v_check rho (Until phi I psi) p = (case p of
  VUntil i vpsis vphi \<Rightarrow>
    let j = v_at vphi
    in (case right I of enat n \<Rightarrow> delta rho j i \<le> n | \<infinity> \<Rightarrow> True) \<and>
      i \<le> j \<and> check_upt_lu rho I i (map v_at vpsis) j \<and>
      v_check rho phi vphi \<and> Ball (set vpsis) (v_check rho psi)
 | VUntil_never i hi vpsis \<Rightarrow>
    (case right I of enat n \<Rightarrow> (delta rho hi i \<le> n \<and> n < delta rho (Suc hi) i) | \<infinity> \<Rightarrow> False) \<and>
     check_upt_lu rho I i (map v_at vpsis) hi \<and> Ball (set vpsis) (v_check rho psi)
 | _ \<Rightarrow> False)"
  by (auto simp: Let_def LTP_plus_ge_iff LTP_plus_eq_iff check_upt_lu_eq simp del: upt_Suc
      split: vproof.splits enat.splits)

(* Check trace invariance *)

lemma check_tp_cong_aux: "(\<And>i. s_ltp p \<le> i \<and> i \<le> s_htp p \<Longrightarrow> \<tau> rho i = \<tau> rho' i) \<Longrightarrow>
  (\<And>i. s_ltp p \<le> i \<and> i \<le> s_htp p \<Longrightarrow> \<Gamma> rho i = \<Gamma> rho' i) \<Longrightarrow> \<forall>phi. s_check rho phi p \<longrightarrow> s_check rho' phi p"
  "(\<And>i. v_ltp p' \<le> i \<and> i \<le> v_htp p' \<Longrightarrow> \<tau> rho i = \<tau> rho' i) \<Longrightarrow>
  (\<And>i. v_ltp p' \<le> i \<and> i \<le> v_htp p' \<Longrightarrow> \<Gamma> rho i = \<Gamma> rho' i) \<Longrightarrow> \<forall>phi. v_check rho phi p' \<longrightarrow> v_check rho' phi p'"
proof (induction rule: s_htp_v_htp.induct)
  case (1 i)
  show ?case
    apply (rule allI)
    subgoal for phi
      by (cases phi) auto
    done
next
  case (2 atm i)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 2
      by (cases phi) auto
    done
next
  case (3 p)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 3
      by (cases phi) auto
    done
next
  case (4 p)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 4
      by (cases phi) auto
    done
next
  case (5 q)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 5
      by (cases phi) auto
    done
next
  case (6 p q)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 6
      by (cases phi) (auto simp add: Lattices.linorder_class.min.coboundedI1 Lattices.linorder_class.min.coboundedI2 le_max_iff_disj)
    done
next
  case (7 p qs)
  have s_at_htp: "s_ltp (SSince p qs) \<le> s_at p \<and> s_at p \<le> s_htp (SSince p qs)"
    using at_htp(1)[of p] at_ltp(1)[of p] min_proofs_sound[where ?xs="p # qs" and ?f=s_ltp]
    by (force simp: max_proofs_Cons)
  have aux: "x \<in> set (p # qs) \<Longrightarrow> s_ltp (SSince p qs) \<le> s_ltp x \<and> s_htp x \<le> s_htp (SSince p qs)" for x
    using max_proofs_sound[where ?x=x and ?xs="p # qs" and ?f=s_htp]
      min_proofs_sound[where ?x=x and ?xs="p # qs" and ?f=s_ltp]
    by auto
  have IH: "x \<in> set (p # qs) \<Longrightarrow> s_check rho phi x \<Longrightarrow> s_check rho' phi x" for x phi
    using 7(1)[OF _ 7(2,3)] aux
    by force
  show ?case
    apply (rule allI)
    subgoal for phi
      using IH
      by (cases phi) (auto simp: Let_def 7(2)[OF conjI[OF at_ltp(1) at_htp(1)]] 7(2)[OF s_at_htp] simp del: s_at.simps)
    done
next
  case (8 qs p)
  have s_at_htp: "s_ltp (SUntil qs p) \<le> s_at p \<and> s_at p \<le> s_htp (SUntil qs p)"
    using at_htp(1)[of p] at_ltp(1)[of p] min_proofs_sound[where ?xs="qs @ [p]" and ?f=s_ltp]
    by (force simp: max_proofs_app)
  have aux: "x \<in> set (qs @ [p]) \<Longrightarrow> s_ltp (SUntil qs p) \<le> s_ltp x \<and> s_htp x \<le> s_htp (SUntil qs p)" for x
    using max_proofs_sound[where ?x=x and ?xs="qs @ [p]" and ?f=s_htp]
      min_proofs_sound[where ?x=x and ?xs="qs @ [p]" and ?f=s_ltp]
    by auto
  have IH: "x \<in> set (qs @ [p]) \<Longrightarrow> s_check rho phi x \<Longrightarrow> s_check rho' phi x" for x phi
    using 8(1)[OF _ 8(2,3)] aux
    by force
  show ?case
    apply (rule allI)
    subgoal for phi
      using IH
      by (cases phi) (auto simp: Let_def 8(2)[OF conjI[OF at_ltp(1) at_htp(1)]] 8(2)[OF s_at_htp] simp del: s_at.simps)
    done
next
  case (9 p)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 9
      apply (cases phi)
               apply (auto simp: Let_def)
        apply (metis Lattices.linorder_class.min.cobounded1 at_htp(1) diff_le_self le_enat_SucI le_trans)
       apply (metis Lattices.linorder_class.min.cobounded1 at_htp(1) diff_le_self le_enat_SucI le_trans)
      using Lattices.linorder_class.min.coboundedI2
      apply blast
      done
    done
next
  case (10 p)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 10
      by (cases phi) (auto simp add: at_ltp(1) le_enat_SucI le_max_iff_disj)
    done
next
  case (11 i)
  show ?case
    apply (rule allI)
    subgoal for phi
      by (cases phi) auto
    done
next
  case (12 atm i)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 12
      by (cases phi) auto
    done
next
  case (13 p)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 13
      by (cases phi) auto
    done
next
  case (14 p q)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 14
      by (cases phi) (auto simp add: Lattices.linorder_class.min.coboundedI1 Lattices.linorder_class.min.coboundedI2 le_max_iff_disj)
    done
next
  case (15 p)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 15
      by (cases phi) auto
    done
next
  case (16 q)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 16
      by (cases phi) auto
    done
next
  case (17 i p qs)
  have at_le_htp: "v_ltp (VSince i p qs) \<le> i \<and> i \<le> v_htp (VSince i p qs)"
    "v_ltp (VSince i p qs) \<le> v_at p \<and> v_at p \<le> v_htp (VSince i p qs)"
    "v_ltp (VSince i p qs) \<le> enat 0 \<and> 0 \<le> v_htp (VSince i p qs)"
    using at_htp(2)[of p]
    by (auto simp: max_proofs_Cons)
  have aux: "x \<in> set (p # qs) \<Longrightarrow> v_ltp (VSince i p qs) \<le> v_ltp x \<and> v_htp x \<le> v_htp (VSince i p qs)" for x
    using max_proofs_sound[where ?x=x and ?xs="p # qs" and ?f=v_htp]
    by auto
  have IH: "x \<in> set (p # qs) \<Longrightarrow> v_check rho phi x \<Longrightarrow> v_check rho' phi x" for x phi
    using 17(1)[OF _ 17(2,3)] aux
    by force
  show ?case
    apply (rule allI)
    subgoal for phi
      using IH check_upt_l_cong[OF 17(2)] at_le_htp
      by (cases phi) (auto simp: v_check_Since_code Let_def 17(2)[OF at_le_htp(1)]
          17(2)[OF at_le_htp(2)] 17(2)[OF at_le_htp(3)] simp del: v_check_simps(9) split: enat.splits)
    done
next
  case (18 i qs p)
  have at_le_htp: "v_ltp (VUntil i qs p) \<le> i \<and> i \<le> v_htp (VUntil i qs p)"
    "v_ltp (VUntil i qs p) \<le> v_at p \<and> v_at p \<le> v_htp (VUntil i qs p)"
    using at_htp(2)[of p] at_ltp(2)[of p] min_proofs_sound[where ?xs="qs @ [p]" and ?f=v_ltp]
    by (auto simp: max_proofs_app) (metis Lattices.linorder_class.min.coboundedI2 order_trans)
  have aux: "x \<in> set (qs @ [p]) \<Longrightarrow> v_ltp (VUntil i qs p) \<le> v_ltp x \<and> v_htp x \<le> v_htp (VUntil i qs p)" for x
    using max_proofs_sound[where ?x=x and ?xs="qs @ [p]" and ?f=v_htp]
      min_proofs_sound[where ?x=x and ?xs="qs @ [p]" and ?f=v_ltp]
    by auto (meson Lattices.linorder_class.min.coboundedI2)+
  have IH: "x \<in> set (qs @ [p]) \<Longrightarrow> v_check rho phi x \<Longrightarrow> v_check rho' phi x" for x phi
    using 18(1)[OF _ 18(2,3)] aux
    by force
  have foo: "min i (v_at p) \<le> j \<and> j \<le> max i (v_at p) \<Longrightarrow>
          v_ltp (VUntil i qs p) \<le> enat j \<and> j \<le> v_htp (VUntil i qs p)" for j
    using at_le_htp
    by (auto simp: min_def split: if_splits) (meson enat_ord_simps(1) order_trans)+
  show ?case
    apply (rule allI)
    subgoal for phi
      using IH check_upt_lu_cong[OF 18(2)] foo
      by (cases phi) (auto simp: v_check_Until_code Let_def 18(2)[OF at_le_htp(1)]
          18(2)[OF at_le_htp(2)] simp del: v_check_simps(10) split: enat.splits)
    done
next
  case (19 i li qs)
  have le_htp: "v_ltp (VSince_never i li qs) \<le> i \<and> i \<le> v_htp (VSince_never i li qs)"
    "v_ltp (VSince_never i li qs) \<le> li \<and> li \<le> v_htp (VSince_never i li qs)"
    "v_ltp (VSince_never i li qs) \<le> li - Suc 0 \<and> li - Suc 0 \<le> v_htp (VSince_never i li qs)"
    "v_ltp (VSince_never i li qs) \<le> enat 0 \<and> 0 \<le> v_htp (VSince_never i li qs)"
    by auto
  have aux: "x \<in> set qs \<Longrightarrow> v_htp x \<le> v_htp (VSince_never i li qs)" for x
    using max_proofs_sound[where ?x=x and ?xs=qs and ?f=v_htp]
    by (auto simp: max_proofs_app)
  have IH: "x \<in> set qs \<Longrightarrow> v_check rho phi x \<Longrightarrow> v_check rho' phi x" for x phi
    using 19(1)[OF _ 19(2,3)] aux
    by force
  show ?case
    apply (rule allI)
    subgoal for phi
      using IH check_upt_l_cong[OF 19(2)] le_htp(1-2)
      by (cases phi) (auto simp: v_check_Since_code 19(2)[OF le_htp(1)] 19(2)[OF le_htp(2)] 19(2)[OF le_htp(3)] 19(2)[OF le_htp(4)]
          simp del: v_check_simps(9) split: enat.splits)
    done
next
  case (20 i hi qs)
  have at_le_htp: "v_ltp (VUntil_never i hi qs) \<le> i \<and> i \<le> v_htp (VUntil_never i hi qs)"
    "v_ltp (VUntil_never i hi qs) \<le> hi \<and> hi \<le> v_htp (VUntil_never i hi qs)"
    "v_ltp (VUntil_never i hi qs) \<le> Suc hi \<and> Suc hi \<le> v_htp (VUntil_never i hi qs)"
    using min_proofs_sound[where ?xs="qs" and ?f=v_ltp]
    by (auto simp add: Lattices.linorder_class.min.coboundedI1)
  have aux: "x \<in> set (qs) \<Longrightarrow> v_ltp (VUntil_never i hi qs) \<le> v_ltp x \<and> v_htp x \<le> v_htp (VUntil_never i hi qs)" for x
    using max_proofs_sound[where ?x=x and ?xs="qs" and ?f=v_htp]
      min_proofs_sound[where ?x=x and ?xs="qs" and ?f=v_ltp]
    by auto (meson Lattices.linorder_class.min.coboundedI2)+
  have IH: "x \<in> set (qs) \<Longrightarrow> v_check rho phi x \<Longrightarrow> v_check rho' phi x" for x phi
    using 20(1)[OF _ 20(2,3)] aux
    by force
  have foo: "min i hi \<le> j \<and> j \<le> max i hi \<Longrightarrow>
          v_ltp (VUntil_never i hi qs) \<le> enat j \<and> j \<le> v_htp (VUntil_never i hi qs)" for j
    using at_le_htp
    by (auto simp: min_def split: if_splits) (meson enat_ord_simps(1) order_trans)+
  show ?case
    apply (rule allI)
    subgoal for phi
      using IH check_upt_lu_cong[OF 20(2)] foo
      by (cases phi) (auto simp: v_check_Until_code Let_def 20(2)[OF at_le_htp(1)] 20(2)[OF at_le_htp(2)] 20(2)[OF at_le_htp(3)]
          simp del: v_check_simps(10) split: enat.splits)
    done
next
  case (21 i)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 21
      by (cases phi) auto
    done
next
  case (22 p)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 22 Lattices.linorder_class.min.coboundedI2
      by (cases phi) fastforce+
    done
next
  case (23 i)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 23
      by (cases phi) auto
    done
next
  case (24 i)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 24
      by (cases phi) auto
    done
next
  case (25 p)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 25
      by (cases phi) (auto simp add: le_max_iff_disj)
    done
next
  case (26 i)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 26
      apply (cases phi)
               apply auto
      apply (metis One_nat_def diff_le_self enat_minus_leI eq_iff idiff_enat_enat one_enat_def)
      done
    done
next
  case (27 i)
  show ?case
    apply (rule allI)
    subgoal for phi
      using 27
      apply (cases phi)
               apply auto
      apply (metis One_nat_def diff_le_self enat_minus_leI eq_iff idiff_enat_enat one_enat_def)
      done
    done
next
  case 28
  show ?case
    apply (rule allI)
    subgoal for phi
      by (cases phi) auto
    done
qed

lemma check_tp_cong: "(\<And>i. s_ltp p \<le> i \<and> i \<le> s_htp p \<Longrightarrow> \<tau> rho i = \<tau> rho' i) \<Longrightarrow>
  (\<And>i. s_ltp p \<le> i \<and> i \<le> s_htp p \<Longrightarrow> \<Gamma> rho i = \<Gamma> rho' i) \<Longrightarrow>
  s_check rho phi p \<longleftrightarrow> s_check rho' phi p"
  "(\<And>i. v_ltp p' \<le> i \<and> i \<le> v_htp p' \<Longrightarrow> \<tau> rho i = \<tau> rho' i) \<Longrightarrow>
  (\<And>i. v_ltp p' \<le> i \<and> i \<le> v_htp p' \<Longrightarrow> \<Gamma> rho i = \<Gamma> rho' i) \<Longrightarrow>
  v_check rho phi p' \<longleftrightarrow> v_check rho' phi p'"
  using check_tp_cong_aux(1)[where ?p=p and ?rho=rho and ?rho'=rho']
    check_tp_cong_aux(1)[where ?p=p and ?rho=rho' and ?rho'=rho]
    check_tp_cong_aux(2)[where ?p'=p' and ?rho=rho and ?rho'=rho']
    check_tp_cong_aux(2)[where ?p'=p' and ?rho=rho' and ?rho'=rho]
  by auto

(* Trace code setup *)

lemma extend_is_stream: assumes "sorted (map snd list)"
  "\<And>x. x \<in> set list \<Longrightarrow> snd x \<le> m"
  shows "ssorted (smap snd (list @- smap (\<lambda>n. ({}, n + m)) nats)) \<and>
    sincreasing (smap snd (list @- smap (\<lambda>n. ({}, n + m)) nats))"
proof -
  have A: "\<forall>x\<in>set list. n \<le> snd x \<Longrightarrow> n \<le> m \<Longrightarrow>
    n \<le> (map snd list @- smap (\<lambda>x. x + m) nats) !! i" for n i and
    list :: "('a set \<times> nat) list"
    apply (induction i arbitrary: n list)
     apply (auto simp add: List.list.map_sel(1))
    by (smt (verit, best) List.list.set_sel(2) map_tl)
  have "ssorted (smap snd (list @- smap (\<lambda>n. ({}, n + m)) nats))"
    using assms
    apply (induction list)
     apply (auto simp: ssorted_iff_mono stream.map_comp o_def)
    subgoal for a b list i j
      using A
      by (cases i; cases j) fastforce+
    done
  moreover have "sincreasing (smap snd (list @- smap (\<lambda>n. ({}, n + m)) nats))"
    using assms
  proof (induction list)
    case (Cons a as)
    have IH: "\<exists>j>i. smap snd (as @- smap (\<lambda>n. ({}, n + m)) nats) !! i
            < smap snd (as @- smap (\<lambda>n. ({}, n + m)) nats) !! j" for i
      using Cons
      by (auto simp: sincreasing_def)
    obtain j where j_def: "0 < j" "smap snd (as @- smap (\<lambda>n. ({}, n + m)) nats) !! 0
          < smap snd (as @- smap (\<lambda>n. ({}, n + m)) nats) !! j"
      using IH[of 0]
      by auto
    show ?case
      apply (auto simp: sincreasing_def)
      subgoal for i
        apply (cases i)
        subgoal
          using j_def Cons
          apply (auto simp: List.list.map_sel(1) intro!: exI[of _ "Suc j"] split: if_splits)
          by (metis (mono_tags, lifting) List.list.set_sel(1) le_trans not_less)
        subgoal for nat
          using IH[of nat]
          by auto
        done
      done
  qed (auto simp: sincreasing_def)
  ultimately show ?thesis
    by auto
qed

typedef 'a trace_rbt = "{(n, m, t) :: (nat \<times> nat \<times> (nat, 'a set \<times> nat) mapping) |
  n m t. Mapping.keys t = {..<n} \<and>
  sorted (map (snd \<circ> (the \<circ> Mapping.lookup t)) [0..<n]) \<and>
  (case n of 0 \<Rightarrow> True | Suc n' \<Rightarrow> (case Mapping.lookup t n' of Some (X', t') \<Rightarrow> t' \<le> m | None \<Rightarrow> False))}"
  by (rule exI[of _ "(0, 0, Mapping.empty)"]) auto

setup_lifting type_definition_trace_rbt

lemma lookup_bulkload_Some: "i < length list \<Longrightarrow>
  Mapping.lookup (Mapping.bulkload list) i = Some (list ! i)"
  by transfer (auto simp: Map_To_Mapping.map_apply_def)

lift_definition trace_rbt_of_list :: "('a set \<times> nat) list \<Rightarrow> 'a trace_rbt" is
  "\<lambda>xs. if sorted (map snd xs) then (if xs = [] then (0, 0, Mapping.empty)
  else (length xs, snd (last xs), Mapping.bulkload xs))
  else (0, 0, Mapping.empty)"
  by (auto simp: lookup_bulkload_Some sorted_iff_nth_Suc last_conv_nth split: option.splits nat.splits)

lift_definition trace_rbt_nth :: "'a trace_rbt \<Rightarrow> nat \<Rightarrow> ('a set \<times> nat)" is
  "\<lambda>(n, m, t) i. if i < n then the (Mapping.lookup t i) else ({}, (i - n) + m)" .

lift_definition Trace_RBT :: "'a trace_rbt \<Rightarrow> 'a trace" is
  "\<lambda>(n, m, t). map (the \<circ> Mapping.lookup t) [0..<n] @- smap (\<lambda>n. ({} :: 'a set, n + m)) nats"
  subgoal premises prems for prod
  proof -
    obtain n m t where prod_def: "prod = (n, m, t)"
      by (cases prod) auto
    have props: "Mapping.keys t = {..<n}"
      "sorted (map (snd \<circ> (the \<circ> Mapping.lookup t)) [0..<n])"
      "(case n of 0 \<Rightarrow> True | Suc n' \<Rightarrow> (case Mapping.lookup t n' of Some (X', t') \<Rightarrow> t' \<le> m | None \<Rightarrow> False))"
      using prems
      by (auto simp: prod_def)
    have aux: "x \<in> set (map (the \<circ> Mapping.lookup t) [0..<n]) \<Longrightarrow> snd x \<le> m" for x
      using props(2,3) less_Suc_eq_le
      by (fastforce simp: sorted_iff_nth_mono split: nat.splits option.splits)
    show ?thesis
      apply (simp add: prod_def del: smap_shift)
      apply (rule extend_is_stream[where ?m=m])
      using props aux
      by (auto simp: prod_def)
  qed
  done

code_datatype Trace_RBT

definition "trace_of_list xs = Trace_RBT (trace_rbt_of_list xs)"

lemma \<Gamma>_rbt_code[code]: "\<Gamma> (Trace_RBT t) i = fst (trace_rbt_nth t i)"
  by transfer (auto split: prod.splits)

lemma \<tau>_rbt_code[code]: "\<tau> (Trace_RBT t) i = snd (trace_rbt_nth t i)"
  by transfer (auto split: prod.splits)

lemma trace_rbt_of_list_sound: "sorted (map snd xs) \<Longrightarrow> i < length xs \<Longrightarrow>
  xs ! i = (\<Gamma> (trace_of_list xs) i, \<tau> (trace_of_list xs) i)"
  unfolding trace_of_list_def
  by transfer (auto simp: lookup_bulkload_Some)

(* Code export *)

instantiation enat :: ccompare begin
definition ccompare_enat :: "enat comparator option" where
  "ccompare_enat = Some (\<lambda>x y. if x = y then order.Eq else if x < y then order.Lt else order.Gt)"

instance by intro_classes
    (auto simp: ccompare_enat_def split: if_splits intro!: comparator.intro)
end

derive (eq) ceq enat

instantiation enat :: set_impl begin
definition set_impl_enat :: "(enat, set_impl) phantom" where
  "set_impl_enat = phantom set_RBT"

instance ..
end

definition strset :: "String.literal list \<Rightarrow> String.literal set" where
  "strset = set"

definition sprogress :: "String.literal trace \<Rightarrow> String.literal mtl \<Rightarrow> nat \<Rightarrow> nat" where
  "sprogress = progress"

export_code strset trace_of_list strs_at strv_at strs_check strv_check sprogress
  opt_depth is_opt_depth rdepth strmdepth opt_atm is_opt_atm ratm strmatm
  opt_flipped_depth is_opt_flipped_depth rrdepth opt_flipped_atm is_opt_flipped_atm rratm
  opt_minminreach is_opt_minminreach rminminreach opt_maxminreach is_opt_maxminreach rmaxminreach strminreach
  opt_minmaxreach is_opt_minmaxreach rminmaxreach opt_maxmaxreach is_opt_maxmaxreach rmaxmaxreach strmaxreach
  opt_lex_atm_minmaxreach is_opt_lex_atm_minmaxreach rlex_atm_minmaxreach
  TT STT Inl interval enat nat_of_integer integer_of_nat
  in OCaml module_name Explanator file_prefix "explanator"

(* ETP/LTP code setup *)

lemma etp_aux: "\<not> t \<le> \<tau> rho i \<Longrightarrow> i \<le> (LEAST i. t \<le> \<tau> rho i)"
  by (meson LeastI_ex \<tau>_mono ex_le_\<tau> nat_le_linear order_trans)

function etp_rec where
  "etp_rec rho t i = (if \<tau> rho i \<ge> t then i else etp_rec rho t (i + 1))"
  by pat_completeness auto
termination
  using etp_aux
  by (relation "measure (\<lambda>(rho, t, i). Suc (ETP rho t) - i)") (fastforce simp: ETP_def)+

lemma etp_rec_sound: "etp_rec rho t j = (LEAST i. i \<ge> j \<and> t \<le> \<tau> rho i)"
proof (induction rho t j rule: etp_rec.induct)
  case (1 rho t i)
  show ?case
  proof (cases "\<tau> rho i \<ge> t")
    case True
    then show ?thesis
      by auto (metis (no_types, lifting) Least_equality order_refl)
  next
    case False
    then show ?thesis
      using 1[OF False]
      by (auto simp del: etp_rec.simps simp add: etp_rec.simps[of _ _ i])
         (metis Suc_leD le_antisym not_less_eq_eq)
  qed
qed

lemma ETP_code[code]: "ETP rho t = etp_rec rho t 0"
  using etp_rec_sound[of rho t 0]
  by (auto simp: ETP_def)

lemma ltp_aux:
  assumes "\<tau> rho (Suc i) \<le> t"
  shows "i \<le> Max {i. \<tau> rho i \<le> t}"
proof -
  have "finite {i. \<tau> rho i \<le> t}"
    by (smt (verit, del_insts) \<tau>_mono finite_nat_set_iff_bounded_le i_ltp_to_tau le0 le_trans
        mem_Collect_eq)
  moreover have "i \<in> {i. \<tau> rho i \<le> t}"
    using le_trans[OF \<tau>_mono[of i "Suc i" rho] assms]
    by auto
  ultimately show ?thesis
    by (rule Max_ge)
qed

function ltp_rec where
  "ltp_rec rho t i = (if \<tau> rho (Suc i) \<le> t then ltp_rec rho t (i + 1) else i)"
  by pat_completeness auto
termination
  using ltp_aux
  by (relation "measure (\<lambda>(rho, t, i). Suc (LTP rho t) - i)") (fastforce simp: LTP_def)+

lemma max_aux: "finite X \<Longrightarrow> Suc j \<in> X \<Longrightarrow> Max (insert (Suc j) (X - {j})) = Max (insert j X)"
  by (smt (verit) Lattices.linorder_class.max.orderI
      Lattices_Big.linorder_class.Max.insert_remove Max_ge Max_insert empty_iff insert_Diff_single
      insert_absorb insert_iff max_def not_less_eq_eq)

lemma ltp_rec_sound: "ltp_rec rho t j = Max ({i. i \<ge> j \<and> (\<tau> rho i) \<le> t} \<union> {j})"
proof (induction rho t j rule: ltp_rec.induct)
  case (1 rho t j)
  have fin: "finite {i. j \<le> i \<and> \<tau> rho i \<le> t}"
    by (smt (verit, del_insts) \<tau>_mono finite_nat_set_iff_bounded_le i_ltp_to_tau le0 le_trans
        mem_Collect_eq)
  show ?case
  proof (cases "\<tau> rho (Suc j) \<le> t")
    case True
    have diffI: "{i. Suc j \<le> i \<and> \<tau> rho i \<le> t} = {i. j \<le> i \<and> \<tau> rho i \<le> t} - {j}"
      by auto
    show ?thesis
      using 1[OF True] True fin
      by (auto simp del: ltp_rec.simps simp add: ltp_rec.simps[of _ _ j] diffI intro: max_aux)
  next
    case False
    then show ?thesis
      using fin
      by auto (smt (verit) Max_insert2 \<tau>_mono mem_Collect_eq not_less_eq_eq order_trans)
  qed
qed

lemma LTP_code[code]: "LTP rho t = (if t < \<tau> rho 0
  then Code.abort (STR ''LTP: undefined'') (\<lambda>_. LTP rho t)
  else ltp_rec rho t 0)"
  using ltp_rec_sound[of rho t 0]
  by (auto simp: LTP_def insert_absorb simp del: ltp_rec.simps)

end