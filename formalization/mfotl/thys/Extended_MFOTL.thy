(*<*)
theory Extended_MFOTL
  imports MFOTL_Monitor.Interval MFOTL_Monitor.Trace MFOTL_Monitor.Abstract_Monitor
begin
(*>*)

section \<open>Extended Metric First-Order Temporal Logic\<close>

context begin

subsection \<open>Formulas and Satisfiability\<close>

qualified type_synonym name = string
qualified type_synonym 'a event = "(name \<times> 'a list)"
qualified type_synonym 'a database = "'a event set"
qualified type_synonym 'a prefix = "(name \<times> 'a list) prefix"
qualified type_synonym 'a trace = "(name \<times> 'a list) trace"

qualified type_synonym 'a env = "'a list"

qualified datatype 'a trm = is_Var: Var nat | is_Const: Const 'a

qualified primrec fvi_trm :: "nat \<Rightarrow> 'a trm \<Rightarrow> nat set" where
  "fvi_trm b (Var x) = (if b \<le> x then {x - b} else {})"
| "fvi_trm b (Const _) = {}"

abbreviation "fv_trm \<equiv> fvi_trm 0"

qualified primrec eval_trm :: "'a env \<Rightarrow> 'a trm \<Rightarrow> 'a" where
  "eval_trm v (Var x) = v ! x"
| "eval_trm v (Const x) = x"

lemma eval_trm_cong: "\<forall>x\<in>fv_trm t. v ! x = v' ! x \<Longrightarrow> eval_trm v t = eval_trm v' t"
  by (cases t) simp_all

qualified datatype (discs_sels) 'a formula = 
  TT
| FF
| Pred name "'a trm list" 
| Eq "'a trm" "'a trm"
| Neg "'a formula" 
| Or "'a formula" "'a formula" 
| And "'a formula" "'a formula"
| Imp "'a formula" "'a formula"
| Iff "'a formula" "'a formula"
| Exists "'a formula"
| Prev \<I> "'a formula" 
| Next \<I> "'a formula"
| Once \<I> "'a formula" 
| Hist \<I> "'a formula"
| Event \<I> "'a formula" 
| Always \<I> "'a formula"
| Since "'a formula" \<I> "'a formula" 
| Until "'a formula" \<I> "'a formula"

qualified primrec fvi :: "nat \<Rightarrow> 'a formula \<Rightarrow> nat set" where
  "fvi b (Pred r ts) = (\<Union>t\<in>set ts. fvi_trm b t)"
| "fvi b (Eq t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (TT) = {}"
| "fvi b (FF) = {}"
| "fvi b (Neg \<phi>) = fvi b \<phi>"
| "fvi b (Or \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (And \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Imp \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Iff \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Exists \<phi>) = fvi (Suc b) \<phi>"
| "fvi b (Prev I \<phi>) = fvi b \<phi>"
| "fvi b (Next I \<phi>) = fvi b \<phi>"
| "fvi b (Once I \<phi>) = fvi b \<phi>"
| "fvi b (Hist I \<phi>) = fvi b \<phi>"
| "fvi b (Event I \<phi>) = fvi b \<phi>"
| "fvi b (Always I \<phi>) = fvi b \<phi>"
| "fvi b (Since \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Until \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"

abbreviation "fv \<equiv> fvi 0"

lemma finite_fvi_trm[simp]: "finite (fvi_trm b t)"
  by (cases t) simp_all

lemma finite_fvi[simp]: "finite (fvi b \<phi>)"
  by (induction \<phi> arbitrary: b) simp_all

lemma fvi_trm_Suc: "x \<in> fvi_trm (Suc b) t \<longleftrightarrow> Suc x \<in> fvi_trm b t"
  by (cases t) auto

lemma fvi_Suc: "x \<in> fvi (Suc b) \<phi> \<longleftrightarrow> Suc x \<in> fvi b \<phi>"
  by (induction \<phi> arbitrary: b) (simp_all add: fvi_trm_Suc)

lemma fvi_Suc_bound:
  assumes "\<forall>i\<in>fvi (Suc b) \<phi>. i < n"
  shows "\<forall>i\<in>fvi b \<phi>. i < Suc n"
proof
  fix i
  assume "i \<in> fvi b \<phi>"
  with assms show "i < Suc n" by (cases i) (simp_all add: fvi_Suc)
qed

qualified definition nfv :: "'a formula \<Rightarrow> nat" where
  "nfv \<phi> = Max (insert 0 (Suc ` fv \<phi>))"

qualified definition envs :: "'a formula \<Rightarrow> 'a env set" where
  "envs \<phi> = {v. length v = nfv \<phi>}"

lemma nfv_simps[simp]:
  "nfv (Neg \<phi>) = nfv \<phi>"
  "nfv (Or \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (And \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Imp \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Iff \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Prev I \<phi>) = nfv \<phi>"
  "nfv (Next I \<phi>) = nfv \<phi>"
  "nfv (Once I \<phi>) = nfv \<phi>"
  "nfv (Hist I \<phi>) = nfv \<phi>"
  "nfv (Event I \<phi>) = nfv \<phi>"
  "nfv (Always I \<phi>) = nfv \<phi>"
  "nfv (Since \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Until \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  unfolding nfv_def by (simp_all add: image_Un Max_Un[symmetric])

lemma fvi_less_nfv: "\<forall>i\<in>fv \<phi>. i < nfv \<phi>"
  unfolding nfv_def
  by (auto simp add: Max_gr_iff intro: max.strict_coboundedI2)

qualified fun future_bounded :: "'a formula \<Rightarrow> bool" where
  "future_bounded (TT) = True"
| "future_bounded (FF) = True"
| "future_bounded (Pred _ _) = True"
| "future_bounded (Eq _ _) = True"
| "future_bounded (Neg \<phi>) = future_bounded \<phi>"
| "future_bounded (Or \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (And \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Imp \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Iff \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Exists \<phi>) = future_bounded \<phi>"
| "future_bounded (Prev I \<phi>) = future_bounded \<phi>"
| "future_bounded (Next I \<phi>) = future_bounded \<phi>"
| "future_bounded (Once I \<phi>) = future_bounded \<phi>"
| "future_bounded (Hist I \<phi>) = future_bounded \<phi>"
| "future_bounded (Event I \<phi>) = (future_bounded \<phi> \<and> right I \<noteq> \<infinity>)"
| "future_bounded (Always I \<phi>) = (future_bounded \<phi> \<and> right I \<noteq> \<infinity>)"
| "future_bounded (Since \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Until \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi> \<and> right I \<noteq> \<infinity>)"

qualified primrec sat :: "'a trace \<Rightarrow> 'a env \<Rightarrow> nat \<Rightarrow> 'a formula \<Rightarrow> bool" where
  "sat \<sigma> v i (TT) = True"
| "sat \<sigma> v i (FF) = False"
| "sat \<sigma> v i (Pred r ts) = ((r, map (eval_trm v) ts) \<in> \<Gamma> \<sigma> i)"
| "sat \<sigma> v i (Eq t1 t2) = (eval_trm v t1 = eval_trm v t2)"
| "sat \<sigma> v i (Neg \<phi>) = (\<not> sat \<sigma> v i \<phi>)"
| "sat \<sigma> v i (Or \<phi> \<psi>) = (sat \<sigma> v i \<phi> \<or> sat \<sigma> v i \<psi>)"
| "sat \<sigma> v i (And \<phi> \<psi>) = (sat \<sigma> v i \<phi> \<and> sat \<sigma> v i \<psi>)"
| "sat \<sigma> v i (Imp \<phi> \<psi>) = (sat \<sigma> v i \<phi> \<longrightarrow> sat \<sigma> v i \<psi>)"
| "sat \<sigma> v i (Iff \<phi> \<psi>) = (sat \<sigma> v i \<phi> \<longleftrightarrow> sat \<sigma> v i \<psi>)"
| "sat \<sigma> v i (Exists \<phi>) = (\<exists>z. sat \<sigma> (z # v) i \<phi>)"
| "sat \<sigma> v i (Prev I \<phi>) = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> sat \<sigma> v j \<phi>)"
| "sat \<sigma> v i (Next I \<phi>) = (mem (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) I \<and> sat \<sigma> v (Suc i) \<phi>)"
| "sat \<sigma> v i (Once I \<phi>) = (\<exists>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> sat \<sigma> v j \<phi>)"
| "sat \<sigma> v i (Hist I \<phi>) = (\<forall>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<longrightarrow> sat \<sigma> v j \<phi>)"
| "sat \<sigma> v i (Event I \<phi>) = (\<exists>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> sat \<sigma> v j \<phi>)"
| "sat \<sigma> v i (Always I \<phi>) = (\<forall>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<longrightarrow> sat \<sigma> v j \<phi>)"
| "sat \<sigma> v i (Since \<phi> I \<psi>) = (\<exists>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> sat \<sigma> v j \<psi> \<and> (\<forall>k \<in> {j <.. i}. sat \<sigma> v k \<phi>))"
| "sat \<sigma> v i (Until \<phi> I \<psi>) = (\<exists>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> sat \<sigma> v j \<psi> \<and> (\<forall>k \<in> {i ..< j}. sat \<sigma> v k \<phi>))"

lemma sat_Until_rec: "sat \<sigma> v i (Until \<phi> I \<psi>) \<longleftrightarrow>
  mem 0 I \<and> sat \<sigma> v i \<psi> \<or>
  (\<Delta> \<sigma> (i + 1) \<le> right I \<and> sat \<sigma> v i \<phi> \<and> sat \<sigma> v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>))"
  (is "?L \<longleftrightarrow> ?R")
proof (rule iffI; (elim disjE conjE)?)
  assume ?L
  then obtain j where j: "i \<le> j" "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I" "sat \<sigma> v j \<psi>" "\<forall>k \<in> {i ..< j}. sat \<sigma> v k \<phi>"
    by auto
  then show ?R
  proof (cases "i = j")
    case False
    with j(1,2) have "\<Delta> \<sigma> (i + 1) \<le> right I"
      by (auto elim: order_trans[rotated] simp: diff_le_mono)
    moreover from False j(1,4) have "sat \<sigma> v i \<phi>" by auto
    moreover from False j have "sat \<sigma> v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>)"
      by (cases "right I") (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j])
    ultimately show ?thesis by blast
  qed simp
next
  assume \<Delta>: "\<Delta> \<sigma> (i + 1) \<le> right I" and now: "sat \<sigma> v i \<phi>" and
   "next": "sat \<sigma> v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>)"
  from "next" obtain j where j: "i + 1 \<le> j" "mem (\<tau> \<sigma> j - \<tau> \<sigma> (i + 1)) ((subtract (\<Delta> \<sigma> (i + 1)) I))"
      "sat \<sigma> v j \<psi>" "\<forall>k \<in> {i + 1 ..< j}. sat \<sigma> v k \<phi>"
    by auto
  from \<Delta> j(1,2) have "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I"
    by (cases "right I") (auto simp: le_diff_conv2)
  with now j(1,3,4) show ?L by (auto simp: le_eq_less_or_eq[of i] intro!: exI[of _ j])
qed auto

lemma sat_Since_rec: "sat \<sigma> v i (Since \<phi> I \<psi>) \<longleftrightarrow>
  mem 0 I \<and> sat \<sigma> v i \<psi> \<or>
  (i > 0 \<and> \<Delta> \<sigma> i \<le> right I \<and> sat \<sigma> v i \<phi> \<and> sat \<sigma> v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>))"
  (is "?L \<longleftrightarrow> ?R")
proof (rule iffI; (elim disjE conjE)?)
  assume ?L
  then obtain j where j: "j \<le> i" "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I" "sat \<sigma> v j \<psi>" "\<forall>k \<in> {j <.. i}. sat \<sigma> v k \<phi>"
    by auto
  then show ?R
  proof (cases "i = j")
    case False
    with j(1) obtain k where [simp]: "i = k + 1"
      by (cases i) auto
    with j(1,2) False have "\<Delta> \<sigma> i \<le> right I"
      by (auto elim: order_trans[rotated] simp: diff_le_mono2 le_Suc_eq)
    moreover from False j(1,4) have "sat \<sigma> v i \<phi>" by auto
    moreover from False j have "sat \<sigma> v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>)"
      by (cases "right I") (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j])
    ultimately show ?thesis by auto
  qed simp
next
  assume i: "0 < i" and \<Delta>: "\<Delta> \<sigma> i \<le> right I" and now: "sat \<sigma> v i \<phi>" and
   "prev": "sat \<sigma> v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>)"
  from "prev" obtain j where j: "j \<le> i - 1" "mem (\<tau> \<sigma> (i - 1) - \<tau> \<sigma> j) ((subtract (\<Delta> \<sigma> i) I))"
      "sat \<sigma> v j \<psi>" "\<forall>k \<in> {j <.. i - 1}. sat \<sigma> v k \<phi>"
    by auto
  from \<Delta> i j(1,2) have "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I"
    by (cases "right I") (auto simp: le_diff_conv2)
  with now i j(1,3,4) show ?L by (auto simp: le_Suc_eq gr0_conv_Suc intro!: exI[of _ j])
qed auto

lemma sat_Since_0: "sat \<sigma> v 0 (Since \<phi> I \<psi>) \<longleftrightarrow> mem 0 I \<and> sat \<sigma> v 0 \<psi>"
  by auto

lemma sat_Since_point: "sat \<sigma> v i (Since \<phi> I \<psi>) \<Longrightarrow>
    (\<And>j. j \<le> i \<Longrightarrow> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<Longrightarrow> sat \<sigma> v i (Since \<phi> (point (\<tau> \<sigma> i - \<tau> \<sigma> j)) \<psi>) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto intro: diff_le_self)

lemma sat_Since_pointD: "sat \<sigma> v i (Since \<phi> (point t) \<psi>) \<Longrightarrow> mem t I \<Longrightarrow> sat \<sigma> v i (Since \<phi> I \<psi>)"
  by auto

lemma eval_trm_fvi_cong: "\<forall>x\<in>fv_trm t. v!x = v'!x \<Longrightarrow> eval_trm v t = eval_trm v' t"
  by (cases t) simp_all

lemma sat_fvi_cong: "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> sat \<sigma> v i \<phi> = sat \<sigma> v' i \<phi>"
proof (induct \<phi> arbitrary: v v' i)
  case (Pred n ts)
  show ?case by (simp cong: map_cong eval_trm_fvi_cong[OF Pred[simplified, THEN bspec]])
next
  case (Eq x1 x2)
  then show ?case  unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fvi_cong)
next
  case (Exists \<phi>)
  then show ?case unfolding sat.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
qed (auto 8 0 simp add: nth_Cons' split: nat.splits intro!: iff_exI)

lemma sat_Once_Since: "sat \<sigma> v i (Once I \<phi>) = sat \<sigma> v i (Since TT I \<phi>)"
  by auto

lemma sat_Once_rec: "sat \<sigma> v i (Once I \<phi>) \<longleftrightarrow>
  mem 0 I \<and> sat \<sigma> v i \<phi> \<or> 
  (i > 0 \<and> \<Delta> \<sigma> i \<le> right I \<and> sat \<sigma> v (i - 1) (Once (subtract (\<Delta> \<sigma> i) I) \<phi>))"
  unfolding sat_Once_Since
  by (subst sat_Since_rec) auto

lemma sat_Hist_Once: "sat \<sigma> v i (Hist I \<phi>) = sat \<sigma> v i (Neg (Once I (Neg \<phi>)))"
  by auto

lemma sat_Hist_rec: "sat \<sigma> v i (Hist I \<phi>) \<longleftrightarrow>
  (mem 0 I \<longrightarrow> sat \<sigma> v i \<phi>) \<and> 
  (i > 0 \<longrightarrow> \<Delta> \<sigma> i \<le> right I \<longrightarrow> sat \<sigma> v (i - 1) (Hist (subtract (\<Delta> \<sigma> i) I) \<phi>))"
  unfolding sat_Hist_Once sat.simps(5)
  by (subst sat_Once_rec) auto

lemma sat_Event_Until: "sat \<sigma> v i (Event I \<phi>) = sat \<sigma> v i (Until TT I \<phi>)"
  by auto

lemma sat_Event_rec: "sat \<sigma> v i (Event I \<phi>) \<longleftrightarrow>
  mem 0 I \<and> sat \<sigma> v i \<phi> \<or> 
  (\<Delta> \<sigma> (i + 1) \<le> right I \<and> sat \<sigma> v (i + 1) (Event (subtract (\<Delta> \<sigma> (i + 1)) I) \<phi>))"
  unfolding sat_Event_Until
  by (subst sat_Until_rec) auto

lemma sat_Always_Event: "sat \<sigma> v i (Always I \<phi>) = sat \<sigma> v i (Neg (Event I (Neg \<phi>)))"
  by auto

lemma sat_Always_rec: "sat \<sigma> v i (Always I \<phi>) \<longleftrightarrow>
  (mem 0 I \<longrightarrow> sat \<sigma> v i \<phi>) \<and> 
  (\<Delta> \<sigma> (i + 1) \<le> right I \<longrightarrow> sat \<sigma> v (i + 1) (Always (subtract (\<Delta> \<sigma> (i + 1)) I) \<phi>))"
  unfolding sat_Always_Event sat.simps(5)
  by (subst sat_Event_rec) auto


subsection \<open>Safe Formulas\<close>

fun remove_neg :: "'a formula \<Rightarrow> 'a formula" where
  "remove_neg (Neg \<phi>) = \<phi>"
| "remove_neg \<phi> = \<phi>"

lemma fvi_remove_neg[simp]: "fvi b (remove_neg \<phi>) = fvi b \<phi>"
  by (cases \<phi>) simp_all

lemma partition_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x\<in>set xs \<Longrightarrow> f x = g x) \<Longrightarrow> partition f xs = partition g ys"
  by (induction xs arbitrary: ys) auto

lemma size_remove_neg[termination_simp]: "size (remove_neg \<phi>) \<le> size \<phi>"
  by (cases \<phi>) simp_all

fun is_constraint :: "'a formula \<Rightarrow> bool" where
  "is_constraint (Eq t1 t2) = True"
| "is_constraint (Neg (Eq t1 t2)) = True"
| "is_constraint _ = False"

definition safe_assignment :: "nat set \<Rightarrow> 'a formula \<Rightarrow> bool" where
  "safe_assignment X \<phi> = (case \<phi> of
       Eq (Var x) (Var y) \<Rightarrow> (x \<notin> X \<longleftrightarrow> y \<in> X)
     | Eq (Var x) t \<Rightarrow> (x \<notin> X \<and> fv_trm t \<subseteq> X)
     | Eq t (Var x) \<Rightarrow> (x \<notin> X \<and> fv_trm t \<subseteq> X)
     | _ \<Rightarrow> False)"

fun safe_formula :: "'a formula \<Rightarrow> bool" where
  "safe_formula (TT) = True"
| "safe_formula (FF) = True"
| "safe_formula (Pred e ts) = (\<forall>t\<in>set ts. is_Var t \<or> is_Const t)"
| "safe_formula (Eq t1 t2) = (is_Const t1 \<and> (is_Const t2 \<or> is_Var t2) \<or> is_Var t1 \<and> is_Const t2)"
| "safe_formula (Neg (Eq (Var x) (Var y))) = (x = y)"
| "safe_formula (Neg \<phi>) = (fv \<phi> = {} \<and> safe_formula \<phi>)"
| "safe_formula (Or \<phi> \<psi>) = (fv \<psi> = fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (And \<phi> \<psi>) = (safe_formula \<phi> \<and>
    (safe_assignment (fv \<phi>) \<psi> \<or> safe_formula \<psi> \<or>
      fv \<psi> \<subseteq> fv \<phi> \<and> (is_constraint \<psi> \<or> (case \<psi> of Neg \<psi>' \<Rightarrow> safe_formula \<psi>' | _ \<Rightarrow> False))))"
| "safe_formula (Imp \<phi> \<psi>) = (fv \<psi> = {} \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (Iff \<phi> \<psi>) = (fv \<phi> = {} \<and> fv \<psi> = {} \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (Exists \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Prev I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Next I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Once I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Hist I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Event I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Always I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Since \<phi> I \<psi>) = (fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)) \<and> safe_formula \<psi>)"
| "safe_formula (Until \<phi> I \<psi>) = (fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)) \<and> safe_formula \<psi>)"


lemma disjE_Not2: "P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (\<not>P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R"
  by auto

term "\<And>c d. P (Eq (Const c) (Const d))"
term "P (TT)"

lemma safe_formula_induct[consumes 1, case_names TT FF Pred Eq_Const Eq_Var1 Eq_Var2 neq_Var
    Neg Or And_assign And_safe And_constraint And_Not Exists Prev Next Once Hist Event Always
    Since Not_Since Until Not_Until]:
  assumes "safe_formula \<phi>"
    and TT: "True \<Longrightarrow> P (TT)"
    and TT: "True \<Longrightarrow> P (FF)"
    and Pred: "\<And>e ts. \<forall>t\<in>set ts. is_Var t \<or> is_Const t \<Longrightarrow> P (Pred e ts)"
    and Eq_Const: "\<And>c d. P (Eq (Const c) (Const d))"
    and Eq_Var1: "\<And>c x. P (Eq (Const c) (Var x))"
    and Eq_Var2: "\<And>c x. P (Eq (Var x) (Const c))"
    and neq_Var: "\<And>x. P (Neg (Eq (Var x) (Var x)))"
    and Neg: "\<And>\<phi>. fv \<phi> = {} \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Neg \<phi>)"
    and Or: "\<And>\<phi> \<psi>. fv \<psi> = fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Or \<phi> \<psi>)"
    and And_assign: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and And_safe: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow>
      P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and And_constraint: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> \<not> safe_formula \<psi> \<Longrightarrow>
      fv \<psi> \<subseteq> fv \<phi> \<Longrightarrow> is_constraint \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and And_Not: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) (Neg \<psi>) \<Longrightarrow> \<not> safe_formula (Neg \<psi>) \<Longrightarrow>
      fv (Neg \<psi>) \<subseteq> fv \<phi> \<Longrightarrow> \<not> is_constraint (Neg \<psi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> (Neg \<psi>))"
    and Imp: "\<And>\<phi> \<psi>. fv \<psi> = {} \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and Iff: "\<And>\<phi> \<psi>. fv \<phi> = {} \<Longrightarrow> fv \<psi> = {} \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and Exists: "\<And>\<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Exists \<phi>)"
    and Prev: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Prev I \<phi>)"
    and Next: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Next I \<phi>)"
    and Once: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Once I \<phi>)"
    and Hist: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Hist I \<phi>)"
    and Event: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Event I \<phi>)"
    and Always: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Always I \<phi>)"
    and Since: "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Since \<phi> I \<psi>)"
    and Not_Since: "\<And>\<phi> I \<psi>. fv (Neg \<phi>) \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow>
      \<not> safe_formula (Neg \<phi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Since (Neg \<phi>) I \<psi> )"
    and Until: "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Until \<phi> I \<psi>)"
    and Not_Until: "\<And>\<phi> I \<psi>. fv (Neg \<phi>) \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow>
      \<not> safe_formula (Neg \<phi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Until (Neg \<phi>) I \<psi>)"
  shows "P \<phi>"
  using assms(1) proof (induction \<phi> rule: safe_formula.induct)
  case (4 t1 t2)
  then show ?case using Eq_Const Eq_Var1 Eq_Var2 by (auto simp: trm.is_Const_def trm.is_Var_def)
next
  case (8 \<phi> \<psi>)
  from \<open>safe_formula (And \<phi> \<psi>)\<close> have "safe_formula \<phi>" by simp
  from \<open>safe_formula (And \<phi> \<psi>)\<close> consider
    (a) "safe_assignment (fv \<phi>) \<psi>"
    | (b) "\<not> safe_assignment (fv \<phi>) \<psi>" "safe_formula \<psi>"
    | (c) "fv \<psi> \<subseteq> fv \<phi>" "\<not> safe_assignment (fv \<phi>) \<psi>" "\<not> safe_formula \<psi>" "is_constraint \<psi>"
    | (d) \<psi>' where "fv \<psi> \<subseteq> fv \<phi>" "\<not> safe_assignment (fv \<phi>) \<psi>" "\<not> safe_formula \<psi>" "\<not> is_constraint \<psi>"
        "\<psi> = Neg \<psi>'" "safe_formula \<psi>'"
    by (cases \<psi>) auto
  then show ?case proof cases
    case a
    then show ?thesis using "8.IH" \<open>safe_formula \<phi>\<close> by (intro And_assign)
  next
    case b
    then show ?thesis using "8.IH" \<open>safe_formula \<phi>\<close> by (intro And_safe)
  next
    case c
    then show ?thesis using "8.IH" \<open>safe_formula \<phi>\<close> by (intro And_constraint)
  next
    case d
    then show ?thesis using "8.IH" \<open>safe_formula \<phi>\<close> by (blast intro!: And_Not)
  qed
next
  case (9 \<phi> \<psi>)
  then show ?case sorry
next
  case (10 \<phi> \<psi>)
  then show ?case sorry
next
  case (18 \<phi> I \<psi>)
  then show ?case
  by (cases \<phi>; auto 0 3 elim!: disjE_Not2 intro: Since Not_Since) (*SLOW*)
next
  case (19 \<phi> I \<psi>)
  then show ?case
  by (cases \<phi>; auto 0 3 elim!: disjE_Not2 intro: Until Not_Until) (*SLOW*)
next
qed (auto simp: assms)


subsection \<open>Slicing traces\<close>

qualified primrec matches :: "'a env \<Rightarrow> 'a formula \<Rightarrow> name \<times> 'a list \<Rightarrow> bool" where
  "matches v (Pred r ts) e = (r = fst e \<and> map (eval_trm v) ts = snd e)"
| "matches v (Eq _ _) e = False"
| "matches v (Neg \<phi>) e = matches v \<phi> e"
| "matches v (Or \<phi> \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Exists \<phi>) e = (\<exists>z. matches (z # v) \<phi> e)"
| "matches v (Prev I \<phi>) e = matches v \<phi> e"
| "matches v (Next I \<phi>) e = matches v \<phi> e"
| "matches v (Since \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Until \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"

lemma matches_fvi_cong: "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> matches v \<phi> e = matches v' \<phi> e"
proof (induct \<phi> arbitrary: v v')
  case (Pred n ts)
  show ?case by (simp cong: map_cong eval_trm_fvi_cong[OF Pred[simplified, THEN bspec]])
next
  case (Exists \<phi>)
  then show ?case unfolding matches.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
qed (auto 5 0 simp add: nth_Cons')

abbreviation relevant_events where "relevant_events \<phi> S \<equiv> {e. S \<inter> {v. matches v \<phi> e} \<noteq> {}}"

lemma sat_slice_strong: "relevant_events \<phi> S \<subseteq> E \<Longrightarrow> v \<in> S \<Longrightarrow>
  sat \<sigma> v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) v i \<phi>"
proof (induction \<phi> arbitrary: v S i)
  case (Pred r ts)
  then show ?case by (auto simp: subset_eq)
next
  case (Eq t1 t2)
  show ?case
    unfolding sat.simps
    by simp
next
  case (Neg \<phi>)
  then show ?case by simp
next
  case (Or \<phi> \<psi>)
  show ?case using Or.IH[of S] Or.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Exists \<phi>)
  have "sat \<sigma> (z # v) i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) (z # v) i \<phi>" for z
    using Exists.prems by (auto intro!: Exists.IH[of "{z # v | v. v \<in> S}"])
  then show ?case by simp
next
  case (Prev I \<phi>)
  then show ?case by (auto cong: nat.case_cong)
next
  case (Next I \<phi>)
  then show ?case by simp
next
  case (Since \<phi> I \<psi>)
  show ?case using Since.IH[of S] Since.prems
   by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Until \<phi> I \<psi>)
  show ?case using Until.IH[of S] Until.prems
   by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
qed

end (*context*)

interpretation MFOTL_slicer: abstract_slicer "relevant_events \<phi>" for \<phi> .

lemma sat_slice_iff:
  assumes "v \<in> S"
  shows "sat \<sigma> v i \<phi> \<longleftrightarrow> sat (MFOTL_slicer.slice \<phi> S \<sigma>) v i \<phi>"
  by (rule sat_slice_strong[of S, OF subset_refl assms])

lemma slice_replace_prefix:
  "prefix_of (MFOTL_slicer.pslice \<phi> R \<pi>) \<sigma> \<Longrightarrow>
    MFOTL_slicer.slice \<phi> R (replace_prefix \<pi> \<sigma>) = MFOTL_slicer.slice \<phi> R \<sigma>"
  by (rule map_\<Gamma>_replace_prefix) auto

(*<*)
end
(*>*)