theory Monitor_Code
  imports Explanator2.Monitor "HOL-Library.Code_Target_Nat" Containers.Containers
begin

lemma extend_is_stream: 
  assumes "sorted (map snd list)"
  and "\<And>x. x \<in> set list \<Longrightarrow> snd x \<le> m"
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
    case Nil
    then show ?case
      by (simp add: sincreasing_def) presburger
  next
    case (Cons a as)
    have IH: "\<exists>j>i. smap snd (as @- smap (\<lambda>n. ({}, n + m)) nats) !! i
            < smap snd (as @- smap (\<lambda>n. ({}, n + m)) nats) !! j" for i
      using Cons
      by (auto simp: sincreasing_grD sincreasing_def)
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
          by (auto simp: list.map_sel(1) intro!: exI[of _ "Suc j"] split: if_splits)
        subgoal for nat
          using IH[of nat] 
          apply clarsimp
          sorry
        done
      done
  qed
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

end