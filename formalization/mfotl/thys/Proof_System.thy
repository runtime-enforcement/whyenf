theory Proof_System
  imports MFOTL
begin

definition ETP:: "'a trace \<Rightarrow> nat \<Rightarrow> nat"  where
    "ETP \<sigma> ts = (LEAST i. \<tau> \<sigma> i \<ge> ts)"

definition LTP:: "'a trace \<Rightarrow> nat \<Rightarrow> nat" where
    "LTP \<sigma> ts = Max {i. (\<tau> \<sigma> i) \<le> ts}"

abbreviation "LTP_p \<sigma> i I \<equiv> min i (LTP \<sigma> ((\<tau> \<sigma> i) - left I))"
abbreviation "ETP_f \<sigma> i I \<equiv> max i (ETP \<sigma> ((\<tau> \<sigma> i) + left I))"

inductive SAT and VIO :: "'a Extended_MFOTL.trace \<Rightarrow> 'a Extended_MFOTL.env \<Rightarrow> nat \<Rightarrow> 'a Extended_MFOTL.formula \<Rightarrow> bool" where
  SPred: "(r, map (Extended_MFOTL.eval_trm v) trms) \<in> \<Gamma> \<sigma> i \<Longrightarrow> SAT \<sigma> v i (Extended_MFOTL.Pred r trms)"
| VPred: "(r, map (Extended_MFOTL.eval_trm v) trms) \<notin> \<Gamma> \<sigma> i \<Longrightarrow> VIO \<sigma> v i (Extended_MFOTL.Pred r trms)"
| SEq: "(Extended_MFOTL.eval_trm v t1) = (Extended_MFOTL.eval_trm v t2) \<Longrightarrow> SAT \<sigma> v i (Extended_MFOTL.Eq t1 t2)"
| VEq: "(Extended_MFOTL.eval_trm v t1) \<noteq> (Extended_MFOTL.eval_trm v t2) \<Longrightarrow> VIO \<sigma> v i (Extended_MFOTL.Eq t1 t2)"
| SNeg: "VIO \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i (Extended_MFOTL.Neg \<phi>)"
| VNeg: "SAT \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i (Extended_MFOTL.Neg \<phi>)"
| SDisjL: "SAT \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i (Extended_MFOTL.Or \<phi> \<psi>)"
| SDisjR: "SAT \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (Extended_MFOTL.Or \<phi> \<psi>)"
| VDisj: "VIO \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (Extended_MFOTL.Or \<phi> \<psi>)"

| SExists: "SAT \<sigma> (x # v) i \<phi> \<Longrightarrow> SAT \<sigma> v i (Extended_MFOTL.Exists \<phi>)"
| VExists: "VIO \<sigma> (x # v) i \<phi> \<Longrightarrow> VIO \<sigma> v i (Extended_MFOTL.Exists \<phi>)"


| SNext: "mem (\<Delta> \<sigma> (i+1)) I \<Longrightarrow> SAT \<sigma> v (i+1) \<phi> \<Longrightarrow> SAT \<sigma> v i (Extended_MFOTL.Next I \<phi>)"
| VNext: "VIO \<sigma> v (i+1) \<phi> \<Longrightarrow> VIO \<sigma> v i (Extended_MFOTL.Next I \<phi>)"
| VNext_le: "(\<Delta> \<sigma> (i+1)) < (left I) \<Longrightarrow> VIO \<sigma> v i (Extended_MFOTL.Next I \<phi>)"
| VNext_ge: "enat (\<Delta> \<sigma> (i+1)) > (right I) \<Longrightarrow> VIO \<sigma> v i (Extended_MFOTL.Next I \<phi>)"
| SPrev: "i > 0 \<Longrightarrow> mem (\<Delta> \<sigma> i) I \<Longrightarrow> SAT \<sigma> v (i-1) \<phi> \<Longrightarrow> SAT \<sigma> v i (Extended_MFOTL.Prev I \<phi>)"
| VPrev: "i > 0 \<Longrightarrow> VIO \<sigma> v (i-1) \<phi> \<Longrightarrow> VIO \<sigma> v i (Extended_MFOTL.Prev I \<phi>)"
| VPrev_zero: "i = 0 \<Longrightarrow> VIO \<sigma> v i (Extended_MFOTL.Prev I \<phi>)"
| VPrev_le: "i > 0 \<Longrightarrow> (\<Delta> \<sigma> i) < (left I) \<Longrightarrow> VIO \<sigma> v i (Extended_MFOTL.Prev I \<phi>)"
| VPrev_ge: "i > 0 \<Longrightarrow> enat (\<Delta> \<sigma> i) > (right I) \<Longrightarrow> VIO \<sigma> v i (Extended_MFOTL.Prev I \<phi>)"
| SSince: "j \<le> i \<Longrightarrow> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I  \<Longrightarrow> SAT \<sigma> v j \<psi> \<Longrightarrow> (\<And>k. k \<in> {j <.. i}
            \<Longrightarrow> SAT \<sigma> v k \<phi>) \<Longrightarrow> SAT \<sigma> v i (Extended_MFOTL.Since \<phi> I \<psi>)"
| VSince_le: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I \<Longrightarrow> VIO \<sigma> v i (Extended_MFOTL.Since \<phi> I \<psi>)"
| VSince: "(case right I of \<infinity> \<Rightarrow> True 
            | enat b \<Rightarrow> ETP \<sigma> ((\<tau> \<sigma> i) - b) \<le> j) \<Longrightarrow> 
            j \<le> i \<Longrightarrow> (\<tau> \<sigma> 0) + left I \<le> (\<tau> \<sigma> i) \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow>
            (\<And>k. k \<in> {j .. (LTP_p \<sigma> i I)} \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow> VIO \<sigma> v i (Extended_MFOTL.Since \<phi> I \<psi>)"
| VSince_never: "j = (case right I of \<infinity> \<Rightarrow> 0 
                      | enat b \<Rightarrow> ETP \<sigma> ((\<tau> \<sigma> i) - b)) \<Longrightarrow>
                   (\<tau> \<sigma> i) \<ge> (\<tau> \<sigma> 0) + left I \<Longrightarrow> 
                   (\<And>k. k \<in> {j .. (LTP \<sigma> ((\<tau> \<sigma> i) - left I))} \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow> VIO \<sigma> v i (Extended_MFOTL.Since \<phi> I \<psi>)"
| SUntil: "j \<ge> i \<Longrightarrow> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I  \<Longrightarrow> SAT \<sigma> v j \<psi> \<Longrightarrow> (\<And>k. k \<in> {i ..< j} \<Longrightarrow> SAT \<sigma> v k \<phi>)
             \<Longrightarrow> SAT \<sigma> v i (Extended_MFOTL.Until \<phi> I \<psi>)"
| VUntil: "(case right I of \<infinity> \<Rightarrow> True 
            | enat b \<Rightarrow> j \<le> LTP \<sigma> ((\<tau> \<sigma> i) + b)) \<Longrightarrow> 
             j \<ge> i \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow> (\<And>k. k \<in> {ETP_f \<sigma> i I .. j} \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow> VIO \<sigma> v i (Extended_MFOTL.Until \<phi> I \<psi>)"
| VUntil_never: "(\<And>k. k \<in> (case right I of \<infinity> \<Rightarrow> {ETP_f \<sigma> i I ..} 
                            | enat b \<Rightarrow> {ETP_f \<sigma> i I .. LTP \<sigma> ((\<tau> \<sigma> i) + b)}) \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow>
                  VIO \<sigma> v i (Extended_MFOTL.Until \<phi> I \<psi>)"

lemma soundness: "(SAT \<sigma> v i \<phi> \<longrightarrow> Extended_MFOTL.sat \<sigma> v i \<phi>) \<and> (VIO \<sigma> v i \<phi> \<longrightarrow> \<not> Extended_MFOTL.sat \<sigma> v i \<phi>)"
  oops

lemma completeness: "(Extended_MFOTL.sat \<sigma> v i \<phi> \<longrightarrow> SAT \<sigma> v i \<phi>) \<and> (\<not> Extended_MFOTL.sat \<sigma> v i \<phi> \<longrightarrow> VIO \<sigma> v i \<phi>)"
  oops

end