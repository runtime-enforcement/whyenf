(*<*)
theory Formula
  imports MFOTL_Monitor.Interval Trace Event_Data
begin
(*>*)

section \<open>Metric First-Order Temporal Logic\<close>

context begin

subsection \<open>Formulas and Satisfiability\<close>

qualified type_synonym name = string8
qualified type_synonym 'a event = "(name \<times> 'a list)"
qualified type_synonym 'a database = "'a event set"
qualified type_synonym 'a prefix = "(name \<times> 'a list) prefix"
qualified type_synonym 'a trace = "(name \<times> 'a list) trace"
qualified type_synonym 'a env = "name \<Rightarrow> 'a"
qualified type_synonym 'a envset = "name \<Rightarrow> 'a set"

qualified datatype 'a trm = is_Var: Var name | is_Const: Const 'a

qualified primrec fv_trm :: "'a trm \<Rightarrow> name set" where
  "fv_trm (Var x) = {x}"
| "fv_trm (Const _) = {}"

qualified primrec eval_trm :: "'a env \<Rightarrow> 'a trm \<Rightarrow> 'a" where
  "eval_trm v (Var x) = v x"
| "eval_trm v (Const x) = x"

lemma eval_trm_fv_cong: "\<forall>x\<in>fv_trm t. v x = v' x \<Longrightarrow> eval_trm v t = eval_trm v' t"
  by (induction t) simp_all

qualified definition eval_trms :: "'a env \<Rightarrow> 'a trm list \<Rightarrow> 'a list" where
  "eval_trms v ts = map (eval_trm v) ts"

lemma eval_trms_fv_cong: 
  "\<forall>t\<in>set ts. \<forall>x\<in>fv_trm t. v x = v' x \<Longrightarrow> eval_trms v ts = eval_trms v' ts"
  using eval_trm_fv_cong[of _ v v']
  by (auto simp: eval_trms_def)

(* vs :: "'a envset" is used whenever we define executable functions *)
qualified primrec eval_trm_set :: "'a envset \<Rightarrow> 'a trm \<Rightarrow> 'a trm \<times> 'a set" where
  "eval_trm_set vs (Formula.Var x) = (Var x, vs x)"
| "eval_trm_set vs (Formula.Const x) = (Const x, {x})"

qualified definition eval_trms_set :: "'a envset \<Rightarrow> 'a trm list \<Rightarrow> ('a trm \<times> 'a set) list" 
  where "eval_trms_set vs ts = map (eval_trm_set vs) ts"

lemma eval_trms_set_Nil: "eval_trms_set vs [] = []"
  by (simp add: eval_trms_set_def)

lemma eval_trms_set_Cons: 
  "eval_trms_set vs (t # ts) = eval_trm_set vs t # (eval_trms_set vs ts)"
  by (simp add: eval_trms_set_def)

qualified datatype 'a formula = 
  TT
| FF
| Eq_Const name 'a
| Pred name "'a trm list" 
| Neg "'a formula" 
| Or "'a formula" "'a formula" 
| And "'a formula" "'a formula"
| Imp "'a formula" "'a formula"
| Iff "'a formula" "'a formula"
| Exists "name" "'a formula"
| Forall "name" "'a formula"
| Prev \<I> "'a formula" 
| Next \<I> "'a formula"
| Once \<I> "'a formula" 
| Historically \<I> "'a formula"
| Eventually \<I> "'a formula" 
| Always \<I> "'a formula"
| Since "'a formula" \<I> "'a formula" 
| Until "'a formula" \<I> "'a formula"

qualified primrec fv :: "'a formula \<Rightarrow> name set" where
  "fv (Pred r ts) = (\<Union>t\<in>set ts. fv_trm t)"
| "fv (TT) = {}"
| "fv (FF) = {}"
| "fv (Eq_Const x c) = {x}"
| "fv (Neg \<phi>) = fv \<phi>"
| "fv (Or \<phi> \<psi>) = fv \<phi> \<union> fv \<psi>"
| "fv (And \<phi> \<psi>) = fv \<phi> \<union> fv \<psi>"
| "fv (Imp \<phi> \<psi>) = fv \<phi> \<union> fv \<psi>"
| "fv (Iff \<phi> \<psi>) = fv \<phi> \<union> fv \<psi>"
| "fv (Exists x \<phi>) = fv \<phi> - {x}"
| "fv (Forall x \<phi>) = fv \<phi> - {x}"
| "fv (Prev I \<phi>) = fv \<phi>"
| "fv (Next I \<phi>) = fv \<phi>"
| "fv (Once I \<phi>) = fv \<phi>"
| "fv (Historically I \<phi>) = fv \<phi>"
| "fv (Eventually I \<phi>) = fv \<phi>"
| "fv (Always I \<phi>) = fv \<phi>"
| "fv (Since \<phi> I \<psi>) = fv \<phi> \<union> fv \<psi>"
| "fv (Until \<phi> I \<psi>) = fv \<phi> \<union> fv \<psi>"

qualified primrec "consts" :: "'a formula \<Rightarrow> 'a set" where
  "consts (Pred r ts) = {}" \<comment> \<open>terms may also contain constants,
     but these only filter out values from the trace and do not introduce
     new values of interest (i.e., do not extend the active domain)\<close>
| "consts (TT) = {}"
| "consts (FF) = {}"
| "consts (Eq_Const x c) = {c}"
| "consts (Neg \<phi>) = consts \<phi>"
| "consts (Or \<phi> \<psi>) = consts \<phi> \<union> consts \<psi>"
| "consts (And \<phi> \<psi>) = consts \<phi> \<union> consts \<psi>"
| "consts (Imp \<phi> \<psi>) = consts \<phi> \<union> consts \<psi>"
| "consts (Iff \<phi> \<psi>) = consts \<phi> \<union> consts \<psi>"
| "consts (Exists x \<phi>) = consts \<phi>"
| "consts (Forall x \<phi>) = consts \<phi>"
| "consts (Prev I \<phi>) = consts \<phi>"
| "consts (Next I \<phi>) = consts \<phi>"
| "consts (Once I \<phi>) = consts \<phi>"
| "consts (Historically I \<phi>) = consts \<phi>"
| "consts (Eventually I \<phi>) = consts \<phi>"
| "consts (Always I \<phi>) = consts \<phi>"
| "consts (Since \<phi> I \<psi>) = consts \<phi> \<union> consts \<psi>"
| "consts (Until \<phi> I \<psi>) = consts \<phi> \<union> consts \<psi>"

lemma finite_fv_trm[simp]: "finite (fv_trm t)"
  by (cases t) simp_all

lemma finite_fv[simp]: "finite (fv \<phi>)"
  by (induction \<phi>) simp_all

lemma finite_consts[simp]: "finite (consts \<phi>)"
  by (induction \<phi>) simp_all

qualified definition nfv :: "'a formula \<Rightarrow> nat" where
  "nfv \<phi> = card (fv \<phi>)"

qualified fun future_bounded :: "'a formula \<Rightarrow> bool" where
  "future_bounded (TT) = True"
| "future_bounded (FF) = True"
| "future_bounded (Pred _ _) = True"
| "future_bounded (Eq_Const _ _) = True"
| "future_bounded (Neg \<phi>) = future_bounded \<phi>"
| "future_bounded (Or \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (And \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Imp \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Iff \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Exists _ \<phi>) = future_bounded \<phi>"
| "future_bounded (Forall _ \<phi>) = future_bounded \<phi>"
| "future_bounded (Prev I \<phi>) = future_bounded \<phi>"
| "future_bounded (Next I \<phi>) = future_bounded \<phi>"
| "future_bounded (Once I \<phi>) = future_bounded \<phi>"
| "future_bounded (Historically I \<phi>) = future_bounded \<phi>"
| "future_bounded (Eventually I \<phi>) = (future_bounded \<phi> \<and> right I \<noteq> \<infinity>)"
| "future_bounded (Always I \<phi>) = (future_bounded \<phi> \<and> right I \<noteq> \<infinity>)"
| "future_bounded (Since \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Until \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi> \<and> right I \<noteq> \<infinity>)"

qualified primrec sat :: "'a trace \<Rightarrow> 'a env \<Rightarrow> nat \<Rightarrow> 'a formula \<Rightarrow> bool" where
  "sat \<sigma> v i (TT) = True"
| "sat \<sigma> v i (FF) = False"
| "sat \<sigma> v i (Pred r ts) = ((r, eval_trms v ts) \<in> \<Gamma> \<sigma> i)"
| "sat \<sigma> v i (Eq_Const x c) = (v x = c)"
| "sat \<sigma> v i (Neg \<phi>) = (\<not> sat \<sigma> v i \<phi>)"
| "sat \<sigma> v i (Or \<phi> \<psi>) = (sat \<sigma> v i \<phi> \<or> sat \<sigma> v i \<psi>)"
| "sat \<sigma> v i (And \<phi> \<psi>) = (sat \<sigma> v i \<phi> \<and> sat \<sigma> v i \<psi>)"
| "sat \<sigma> v i (Imp \<phi> \<psi>) = (sat \<sigma> v i \<phi> \<longrightarrow> sat \<sigma> v i \<psi>)"
| "sat \<sigma> v i (Iff \<phi> \<psi>) = (sat \<sigma> v i \<phi> \<longleftrightarrow> sat \<sigma> v i \<psi>)"
| "sat \<sigma> v i (Exists x \<phi>) = (\<exists>z. sat \<sigma> (v (x := z)) i \<phi>)"
| "sat \<sigma> v i (Forall x \<phi>) = (\<forall>z. sat \<sigma> (v (x := z)) i \<phi>)" 
| "sat \<sigma> v i (Prev I \<phi>) = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> sat \<sigma> v j \<phi>)"
| "sat \<sigma> v i (Next I \<phi>) = (mem (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) I \<and> sat \<sigma> v (Suc i) \<phi>)"
| "sat \<sigma> v i (Once I \<phi>) = (\<exists>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> sat \<sigma> v j \<phi>)"
| "sat \<sigma> v i (Historically I \<phi>) = (\<forall>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<longrightarrow> sat \<sigma> v j \<phi>)"
| "sat \<sigma> v i (Eventually I \<phi>) = (\<exists>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> sat \<sigma> v j \<phi>)"
| "sat \<sigma> v i (Always I \<phi>) = (\<forall>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<longrightarrow> sat \<sigma> v j \<phi>)"
| "sat \<sigma> v i (Since \<phi> I \<psi>) = (\<exists>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> sat \<sigma> v j \<psi> \<and> (\<forall>k \<in> {j <.. i}. sat \<sigma> v k \<phi>))"
| "sat \<sigma> v i (Until \<phi> I \<psi>) = (\<exists>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> sat \<sigma> v j \<psi> \<and> (\<forall>k \<in> {i ..< j}. sat \<sigma> v k \<phi>))"

lemma sat_fv_cong: "\<forall>x\<in>fv \<phi>. v x = v' x \<Longrightarrow> sat \<sigma> v i \<phi> = sat \<sigma> v' i \<phi>"
proof (induct \<phi> arbitrary: v v' i rule: formula.induct)
  case (Pred n ts)
  thus ?case
    by (simp cong: map_cong eval_trms_fv_cong[rule_format, OF Pred[simplified, rule_format]] 
        split: option.splits)
next
  case (Exists t \<phi>)
  then show ?case unfolding sat.simps 
    by (intro iff_exI) (simp add: nth_Cons')
next
  case (Forall t \<phi>)
  then show ?case unfolding sat.simps 
    by (intro iff_allI) (simp add: nth_Cons')
qed (auto 10 0 simp: Let_def split: nat.splits intro!: iff_exI eval_trm_fv_cong)

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

lemma sat_Once_Since: "sat \<sigma> v i (Once I \<phi>) = sat \<sigma> v i (Since TT I \<phi>)"
  by auto

lemma sat_Once_rec: "sat \<sigma> v i (Once I \<phi>) \<longleftrightarrow>
  mem 0 I \<and> sat \<sigma> v i \<phi> \<or> 
  (i > 0 \<and> \<Delta> \<sigma> i \<le> right I \<and> sat \<sigma> v (i - 1) (Once (subtract (\<Delta> \<sigma> i) I) \<phi>))"
  unfolding sat_Once_Since
  by (subst sat_Since_rec) auto

lemma sat_Historically_Once: "sat \<sigma> v i (Historically I \<phi>) = sat \<sigma> v i (Neg (Once I (Neg \<phi>)))"
  by auto

lemma sat_Historically_rec: "sat \<sigma> v i (Historically I \<phi>) \<longleftrightarrow>
  (mem 0 I \<longrightarrow> sat \<sigma> v i \<phi>) \<and> 
  (i > 0 \<longrightarrow> \<Delta> \<sigma> i \<le> right I \<longrightarrow> sat \<sigma> v (i - 1) (Historically (subtract (\<Delta> \<sigma> i) I) \<phi>))"
  unfolding sat_Historically_Once sat.simps(5)
  by (subst sat_Once_rec) auto

lemma sat_Eventually_Until: "sat \<sigma> v i (Eventually I \<phi>) = sat \<sigma> v i (Until TT I \<phi>)"
  by auto

lemma sat_Eventually_rec: "sat \<sigma> v i (Eventually I \<phi>) \<longleftrightarrow>
  mem 0 I \<and> sat \<sigma> v i \<phi> \<or> 
  (\<Delta> \<sigma> (i + 1) \<le> right I \<and> sat \<sigma> v (i + 1) (Eventually (subtract (\<Delta> \<sigma> (i + 1)) I) \<phi>))"
  unfolding sat_Eventually_Until
  by (subst sat_Until_rec) auto

lemma sat_Always_Eventually: "sat \<sigma> v i (Always I \<phi>) = sat \<sigma> v i (Neg (Eventually I (Neg \<phi>)))"
  by auto

lemma sat_Always_rec: "sat \<sigma> v i (Always I \<phi>) \<longleftrightarrow>
  (mem 0 I \<longrightarrow> sat \<sigma> v i \<phi>) \<and> 
  (\<Delta> \<sigma> (i + 1) \<le> right I \<longrightarrow> sat \<sigma> v (i + 1) (Always (subtract (\<Delta> \<sigma> (i + 1)) I) \<phi>))"
  unfolding sat_Always_Eventually sat.simps(5)
  by (subst sat_Eventually_rec) auto

end (*context*)

bundle MFOTL_no_notation
begin

text \<open> For bold font, type ``backslash'' followed by the word ``bold''  \<close>
no_notation trm.Var ("\<^bold>v")
     and trm.Const ("\<^bold>c")

text \<open> For subscripts type ``backslash'' followed by ``sub''  \<close>
no_notation formula.TT ("\<top>")
     and formula.FF ("\<bottom>")
     and formula.Pred ("_ \<dagger> _" [85, 85] 85)
     and formula.Eq_Const ("_ \<^bold>\<approx> _" [85, 85] 85)
     and formula.Neg ("\<not>\<^sub>F _" [82] 82)
     and formula.And (infixr "\<and>\<^sub>F" 80)
     and formula.Or (infixr "\<or>\<^sub>F" 80)
     and formula.Imp (infixr "\<longrightarrow>\<^sub>F" 79)
     and formula.Iff (infixr "\<longleftrightarrow>\<^sub>F" 79)
     and formula.Exists ("\<exists>\<^sub>F_. _" [70,70] 70)
     and formula.Forall ("\<forall>\<^sub>F_. _" [70,70] 70)
     and formula.Prev ("\<^bold>Y _ _" [55, 65] 65)
     and formula.Next ("\<^bold>X _ _" [55, 65] 65)
     and formula.Once ("\<^bold>P _ _" [55, 65] 65)
     and formula.Eventually ("\<^bold>F _ _" [55, 65] 65)
     and formula.Once ("\<^bold>H _ _" [55, 65] 65)
     and formula.Eventually ("\<^bold>G _ _" [55, 65] 65)
     and formula.Since ("_ \<^bold>S _ _" [60,55,60] 60)
     and formula.Until ("_ \<^bold>U _ _" [60,55,60] 60)

no_notation Formula.fv_trm ("fv\<^sub>t")
     and Formula.fv ("fv")
     and Formula.eval_trm ("_\<lbrakk>_\<rbrakk>" [51,89] 89)
     and Formula.sat ("\<langle>_, _, _\<rangle> \<Turnstile> _" [56, 56, 56, 56] 55)
     and Interval.interval ("\<^bold>[_,_\<^bold>]")

end

bundle MFOTL_notation
begin

notation trm.Var ("\<^bold>v")
     and trm.Const ("\<^bold>c")

notation formula.TT ("\<top>")
     and formula.FF ("\<bottom>")
     and formula.Pred ("_ \<dagger> _" [85, 85] 85)
     and formula.Eq_Const ("_ \<^bold>\<approx> _" [85, 85] 85)
     and formula.Neg ("\<not>\<^sub>F _" [82] 82)
     and formula.And (infixr "\<and>\<^sub>F" 80)
     and formula.Or (infixr "\<or>\<^sub>F" 80)
     and formula.Imp (infixr "\<longrightarrow>\<^sub>F" 79)
     and formula.Iff (infixr "\<longleftrightarrow>\<^sub>F" 79)
     and formula.Exists ("\<exists>\<^sub>F_. _" [70,70] 70)
     and formula.Forall ("\<forall>\<^sub>F_. _" [70,70] 70)
     and formula.Prev ("\<^bold>Y _ _" [55, 65] 65)
     and formula.Next ("\<^bold>X _ _" [55, 65] 65)
     and formula.Once ("\<^bold>P _ _" [55, 65] 65)
     and formula.Eventually ("\<^bold>F _ _" [55, 65] 65)
     and formula.Once ("\<^bold>H _ _" [55, 65] 65)
     and formula.Eventually ("\<^bold>G _ _" [55, 65] 65)
     and formula.Since ("_ \<^bold>S _ _" [60,55,60] 60)
     and formula.Until ("_ \<^bold>U _ _" [60,55,60] 60)

notation Formula.fv_trm ("fv\<^sub>t")
     and Formula.fv ("fv")
     and Formula.eval_trm ("_\<lbrakk>_\<rbrakk>" [51,89] 89)
     and Formula.sat ("\<langle>_, _, _\<rangle> \<Turnstile> _" [56, 56, 56, 56] 55)
     and Interval.interval ("\<^bold>[_,_\<^bold>]")

end

(*<*)
end
(*>*)