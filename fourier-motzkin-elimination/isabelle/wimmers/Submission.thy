theory Submission
  imports Defs
begin

text \<open>Some auxiliary lemmas\<close>

lemma map2_update1:
  "map2 f (xs[n:=k]) ys = (map2 f xs ys)[n:=f k (ys ! n)]"
  by (metis (no_types, lifting) case_prod_conv list_update_id map_update zip_update)

lemma map2_update2:
  "map2 f xs (ys[n:=k]) = (map2 f xs ys)[n:=f (xs ! n) k]"
  by (metis (no_types, lifting) case_prod_conv list_update_id map_update zip_update)

lemma (in ab_group_add) sum_list_update:
  "k < size xs \<Longrightarrow> sum_list (xs[k := x]) = sum_list xs + x - xs ! k"
  by(induction xs arbitrary: k) (auto simp: add_ac add_diff_eq split: nat.split)

lemma sum_list_update':
  fixes xs :: "rat list"
  shows "k < size xs \<Longrightarrow> sum_list (xs[k := x]) = sum_list xs + x - xs ! k"
  by(induction xs arbitrary: k) (auto split: nat.split)

lemma sum_list_distrib:
  fixes xs gcs lcs :: "('a::ring) list"
  assumes "length gcs = length xs" "length lcs = length xs"
  shows
  "sum_list (map2 (*) (map2 (+) gcs lcs) xs) =
  sum_list (map2 (*) gcs xs) + sum_list (map2 (*) lcs xs)"
  using assms
  apply (induction "length xs" arbitrary: xs gcs lcs)
  apply simp
  subgoal for x xs cgs cls
    apply (cases xs, simp)
    apply (cases cgs, simp)
    apply (cases cls, simp)
    apply (simp add:algebra_simps)
    done
  done

lemma (in ring) sum_list2_aux:
  assumes "length gcs = length xs" "n < length xs"
  shows "sum_list (map2 (*) gcs xs) = sum_list (map2 (*) (gcs[n := 0]) xs) + (gcs ! n * xs ! n)"
  using assms by (simp add: map2_update1 sum_list_update)



lemmas GZL_defs = GZL_def G_def Z_def L_def

lemma GZL_set:
  assumes "GZL ps n = triple a b c"
  shows "set ps = set a \<union> set b \<union> set c"
  using assms unfolding GZL_defs by (auto split: ineq.splits)

lemma GZL_sorting_sat: 
  "triple_sat (GZL ps n) xs \<longleftrightarrow> pol_sat ps xs"
  using GZL_set unfolding triple_sat_def pol_sat_def by (auto split: triple.splits)

context
  fixes N :: nat \<comment> \<open>Number of coefficients/variables\<close>
begin

definition
  "pol_lengths ps = (\<forall>p \<in> set ps. (case p of (ineq cs k) \<Rightarrow> length cs = N))"

definition
  "triple_lengths \<equiv> \<lambda>triple gs zs ls \<Rightarrow> pol_lengths gs \<and> pol_lengths zs \<and> pol_lengths ls"

context
  fixes n :: nat \<comment> \<open>Index of variable to be eliminated\<close>
  assumes n_bound[simp, intro]: "n < N"
begin

abbreviation
  "G_inv \<equiv> \<lambda>ineq gcs gk \<Rightarrow> gcs!n = 1"

abbreviation
  "Z_inv \<equiv> \<lambda>ineq gcs gk \<Rightarrow> gcs!n = 0"

abbreviation
  "L_inv \<equiv> \<lambda>ineq gcs gk \<Rightarrow> gcs!n = -1"

abbreviation
  "GS_inv gs \<equiv> \<forall>g \<in> set gs. G_inv g"

abbreviation
  "ZS_inv gs \<equiv> \<forall>g \<in> set gs. Z_inv g"

abbreviation
  "LS_inv gs \<equiv> \<forall>g \<in> set gs. L_inv g"

definition
  "GZL_inv \<equiv> \<lambda>triple gs zs ls \<Rightarrow> GS_inv gs \<and> ZS_inv zs \<and> LS_inv ls"

definition GZL_sorted where
  "GZL_sorted \<equiv> \<lambda>triple gs zs ls \<Rightarrow>
  (\<forall>g \<in> set gs. case g of ineq cs k \<Rightarrow> cs ! n > 0) \<and>
  (\<forall>g \<in> set zs. case g of ineq cs k \<Rightarrow> cs ! n = 0) \<and>
  (\<forall>g \<in> set ls. case g of ineq cs k \<Rightarrow> cs ! n < 0)"

lemma GZL_sorts: 
  "GZL_sorted (GZL ps n)"
  unfolding GZL_defs GZL_sorted_def by (auto split: triple.splits ineq.splits)

context
  fixes xs :: "rat list"
  assumes len_xs[simp]: "length xs = N"
begin

paragraph \<open>@{term list_div}\<close>

lemma GZL_sorting_lengths:
  "pol_lengths ps \<Longrightarrow> triple_lengths (GZL ps n)"
  unfolding triple_lengths_def GZL_defs pol_lengths_def by (auto split:ineq.splits)

lemma list_div_sat [simp]: "cn > 0 \<Longrightarrow>  eval_term (list_div cs cn) xs = (eval_term cs xs)/cn"
  unfolding list_div_def
  unfolding eval_term_def
  \<comment> \<open>Simon: This could actually be an interesting simple task by itself.\<close>
  apply (induction cs arbitrary:xs)
  apply (auto simp:zip_Cons1 split:list.splits)
  apply (simp add:field_simps)
  done

lemma ineq_div_sat [simp]: "(cs!n) \<noteq> 0 \<Longrightarrow> 
  ineq_sat (ineq_div (ineq cs k) n) xs = ineq_sat (ineq cs k) xs"
  unfolding ineq_div_def
  unfolding ineq_sat_def
  by (simp add: divide_le_cancel)

paragraph \<open>@{term pol_div}\<close>

lemma pol_div_sat [simp]: 
"(\<forall>p \<in> set ps. (case p of ineq cs k \<Rightarrow> cs!n \<noteq> 0)) \<Longrightarrow>
pol_sat (pol_div ps n) xs = pol_sat ps xs"
  unfolding pol_div_def pol_sat_def
  by simp (metis (mono_tags, lifting) ineq_div_sat ineq.case ineq.exhaust)

paragraph \<open>@{term GZL_div}\<close>

lemma GZL_div_triple_lengths:
  assumes "triple_lengths ps"
  shows "triple_lengths (GZL_div ps n)"
  using assms
  unfolding GZL_div_def triple_lengths_def pol_lengths_def pol_div_def ineq_div_def list_div_def
  by (force split: ineq.split triple.split)

lemma G_inv_ineq_div:
  "G_inv (ineq_div (ineq gcs k) n)" if "gcs!n > 0" "length gcs = N"
  unfolding ineq_div_def list_div_def using that by simp

lemma L_inv_ineq_div:
  "L_inv (ineq_div (ineq gcs k) n)" if "gcs!n < 0" "length gcs = N"
  unfolding ineq_div_def list_div_def using that by simp

lemma GZL_inv:
  assumes "triple_lengths ps" "GZL_sorted ps"
  shows "GZL_inv (GZL_div ps n)"
  using assms
  unfolding triple_lengths_def GZL_sorted_def GZL_div_def GZL_inv_def pol_div_def pol_lengths_def
   apply (auto split:triple.split)
  subgoal for _ _ _ g
    by (cases g) (auto intro!: G_inv_ineq_div)
  subgoal for _ _ _ l
    by (cases l) (auto intro!: L_inv_ineq_div)
  done

lemma GZL_div_sat:
  "n < length xs \<Longrightarrow> GZL_sorted ps \<Longrightarrow> triple_sat (GZL_div ps n) xs = triple_sat ps xs"
  unfolding GZL_div_def triple_sat_def GZL_sorted_def
  apply (simp split: triple.split_asm)
  apply (subst pol_div_sat)
  subgoal
    by (auto split:ineq.splits)
  apply (subst pol_div_sat)
  apply (auto split: ineq.split)
  done

\<comment> \<open>Phase 3: @{term GZL_product}\<close>
lemma ineq_add_assoc:
"
  length gcs = N \<Longrightarrow>
  length lcs = N \<Longrightarrow>
  ineq_sat (ineq_add (ineq gcs gk) (ineq lcs lk)) xs \<longleftrightarrow>
  eval_term gcs xs + eval_term lcs xs \<le> gk + lk"
  unfolding ineq_add_def ineq_sat_def eval_term_def by (simp add: sum_list_distrib)

\<comment> \<open>Also, possible exercise.\<close>
lemma eval_term_sum_update_cancel:
  "length gcs = N \<Longrightarrow> length lcs = N \<Longrightarrow> gcs!n = 1 \<Longrightarrow> lcs!n = -1 \<Longrightarrow>
  eval_term (gcs[n := 0]) xs + eval_term (lcs[n := 0]) xs = eval_term gcs xs + eval_term lcs xs"
  unfolding eval_term_def
  apply -
  apply (subst (3) sum_list2_aux[where n = n]; simp)
  apply (subst (2) sum_list2_aux[where n = n]; simp)
  done

theorem ineq_add_cancel':
  assumes "length gcs = N" "gcs!n = 1" "length lcs = N" "lcs!n = -1"
  shows
  "ineq_sat (ineq_add (ineq gcs gk) (ineq lcs lk)) xs \<longleftrightarrow>
  eval_term (gcs[n := 0]) xs + eval_term (lcs[n := 0]) xs \<le> gk + lk"
  using assms by (simp add: ineq_add_assoc eval_term_sum_update_cancel)

theorem eval_term_nth_split':
  assumes "length gcs = N"
  shows "eval_term gcs (xs[n := t]) = eval_term (gcs[n := 0]) xs + gcs!n * t"
  using assms unfolding eval_term_def
  by (smt (z3) sum_list2_aux lambda_zero len_xs length_list_update list_update_id map2_update2
        n_bound nth_list_update_eq)

lemma term_pairing_if:
  assumes
    "GS_inv gs" "LS_inv ls" "pol_lengths gs" "pol_lengths ls"
    "pol_sat gs (xs[n:=t])" "pol_sat ls (xs[n:=t])"
  shows "pol_sat (term_pairing gs ls) xs"
proof -
  have "ineq_sat (ineq_add y x) xs"
    if "y \<in> set gs" "x \<in> set ls" "x = ineq lcs lk" "y = ineq gcs gk" for x y lcs gcs lk gk
  proof -
    from that assms(5,6) have "ineq_sat x (xs[n:=t])" "ineq_sat y (xs[n:=t])"
      unfolding pol_sat_def  by auto
    moreover have "length lcs = N" "length gcs = N"
      using assms that unfolding pol_lengths_def by auto
    moreover have "lcs!n = -1" "gcs!n = 1"
      using assms(1,2) that by auto
    ultimately show ?thesis
      unfolding \<open>x = _\<close> \<open>y = _\<close>
      by - (subst ineq_add_cancel', assumption+,
            simp add: eval_term_nth_split' ineq_sat_def ineq_add_def)
  qed
  then show ?thesis
    unfolding term_pairing_def
    unfolding pol_sat_def
    unfolding pol_add_def
    apply (clarsimp split: ineq.split)
    subgoal for x y
      using assms
      apply (cases x)
      apply (cases y)
      apply simp
      done
    done
qed

lemma term_pairing_only_if1:
  assumes
    "ls \<noteq> []" "GS_inv gs" "LS_inv ls" "pol_lengths gs" "pol_lengths ls"
    "pol_sat (term_pairing gs ls) xs"
  shows "\<exists>t. pol_sat gs (xs[n:=t]) \<and> pol_sat ls (xs[n:=t])"
proof -
  let ?L = "{eval_term (lcs[n:=0]) xs - lk | lcs lk. ineq lcs lk \<in> set ls}"
  let ?t = "Max ?L"
  have "finite ?L"
    using [[simproc add: finite_Collect]] by (auto intro!: injI finite_vimageI)
  have *: "eval_term (lcs[n:=0]) xs - lk \<le> gk - eval_term (gcs[n:=0]) xs"
    if "ineq lcs lk \<in> set ls" "ineq gcs gk \<in> set gs" for lcs gcs lk gk
  proof -
    from that \<open>pol_sat _ _\<close> have "ineq_sat (ineq_add (ineq gcs gk) (ineq lcs lk)) xs"
      unfolding pol_sat_def term_pairing_def pol_add_def by auto
    with that assms show ?thesis
      by (subst (asm) ineq_add_cancel') (auto simp: pol_lengths_def)
  qed
  obtain lcs1 lk1 where t: "?t = eval_term (lcs1[n:=0]) xs - lk1" "ineq lcs1 lk1 \<in> set ls"
  (* s/h *)
  proof -
    have f1: "\<forall>p. p (Max (Collect p)::rat) \<or> infinite (Collect p) \<or> {} = Collect p"
      using Max_eq_iff by blast
    have "\<exists>rs r. ineq rs r \<in> set ls"
      by (metis assms(1) ex_in_conv ineq.exhaust set_empty2)
    then show thesis
      using f1 \<open>finite {eval_term (lcs[n := 0]) xs - lk |lcs lk. ineq lcs lk \<in> set ls}\<close> that by auto
  qed
  have "pol_sat ls (xs[n:=?t])"
  proof -
    have "eval_term lcs (xs[n := ?t]) \<le> lk" if prems: "ineq lcs lk \<in> set ls" for lcs lk
    proof -
      from prems assms have "length lcs = N"
        unfolding pol_lengths_def by auto
      moreover from prems assms have "lcs!n = -1"
        by auto
      moreover from prems \<open>finite ?L\<close> have "eval_term (lcs[n:=0]) xs - lk \<le> ?t"
        by (intro Max_ge) auto
      ultimately show "eval_term lcs (xs[n := ?t]) \<le> lk"
        by (simp add: eval_term_nth_split')
    qed
    then show ?thesis
      unfolding pol_sat_def ineq_sat_def by (clarsimp split: ineq.split)
  qed
  moreover have "pol_sat gs (xs[n:=?t])"
  proof -
    have "eval_term gcs (xs[n := ?t]) \<le> gk" if prems: "ineq gcs gk \<in> set gs" for gcs gk
    proof -
      from prems assms have "length gcs = N"
        unfolding pol_lengths_def by auto
      moreover from prems assms have "gcs!n = 1"
        by auto
      moreover from prems have "?t \<le> gk - eval_term (gcs[n:=0]) xs"
        using * t(1) t(2) by presburger
      ultimately show ?thesis
        by (simp add: eval_term_nth_split')
    qed
    then show ?thesis
      unfolding pol_sat_def ineq_sat_def by (clarsimp split: ineq.split)
  qed
  ultimately show ?thesis
    by blast
qed

lemma term_pairing_only_if2:
  assumes
    "ls = []" "GS_inv gs" "LS_inv ls" "pol_lengths gs" "pol_lengths ls"
    "pol_sat (term_pairing gs ls) xs"
  shows "\<exists>t. pol_sat gs (xs[n:=t]) \<and> pol_sat ls (xs[n:=t])"
proof (cases "gs = []")
  case True
  with assms show ?thesis
    unfolding pol_sat_def by auto
next
  case False
  let ?G = "{gk - eval_term (gcs[n:=0]) xs | gcs gk. ineq gcs gk \<in> set gs}"
  let ?t = "Min ?G"
  have "finite ?G"
    using [[simproc add: finite_Collect]] by (auto intro!: injI finite_vimageI)
  have "pol_sat gs (xs[n:=?t])"
  proof -
    have "eval_term gcs (xs[n := ?t]) \<le> gk" if prems: "ineq gcs gk \<in> set gs" for gcs gk
    proof -
      from prems assms have "length gcs = N"
        unfolding pol_lengths_def by auto
      moreover from prems assms have "gcs!n = 1"
        by auto
      moreover from prems \<open>finite ?G\<close> have "?t \<le> gk - eval_term (gcs[n:=0]) xs"
        by (intro Min_le) auto
      ultimately show ?thesis
        by (simp add: eval_term_nth_split')
    qed
    then show ?thesis
      unfolding pol_sat_def ineq_sat_def by (clarsimp split: ineq.split)
  qed
  with assms show ?thesis
    unfolding pol_sat_def by auto
qed

lemma term_pairing_iff:
"GS_inv gs \<Longrightarrow> LS_inv ls \<Longrightarrow> pol_lengths gs \<Longrightarrow> pol_lengths ls \<Longrightarrow>
 pol_sat (term_pairing gs ls) xs = (\<exists>t. pol_sat gs (xs[n:=t]) \<and> pol_sat ls (xs[n:=t]))"
  using term_pairing_only_if1 term_pairing_only_if2 term_pairing_if by metis

lemma GZL_product_sat_iff:
  assumes "GZL_inv (triple gs zs ls)" "triple_lengths (triple gs zs ls)"
  shows "pol_sat (GZL_product (triple gs zs ls)) xs =
    (\<exists>t. triple_sat (triple gs zs ls) (xs[n := t]))"
proof -
  from assms have "ZS_inv zs"
    unfolding GZL_inv_def by simp
  then have "pol_sat zs (xs[n := t]) = pol_sat zs xs" for t
    unfolding pol_sat_def ineq_sat_def eval_term_def
    by (auto split: ineq.split)
       (metis (mono_tags, lifting) ineq.case list_update_id map2_update2 mult_zero_left)+
  moreover have "pol_sat (zs @ term_pairing gs ls) xs
    \<longleftrightarrow> pol_sat zs xs \<and> pol_sat (term_pairing gs ls) xs"
    unfolding pol_sat_def by auto
  ultimately show ?thesis
    using assms unfolding GZL_inv_def triple_lengths_def
    unfolding GZL_product_def triple_sat_def
    by (auto simp add: term_pairing_iff)
qed

theorem FM_preserves_solution':
  assumes "pol_lengths ps" "pol_sat ps (xs[n := t])"
  shows "pol_sat (FM ps n) xs"
  by (metis (mono_tags, lifting) Submission.GZL_div_sat GZL_div_def GZL_div_triple_lengths GZL_inv
        GZL_product_sat_iff GZL_def GZL_sorting_lengths GZL_sorting_sat GZL_sorts
        len_xs length_list_update n_bound FM_def triple.simps(2) assms)

theorem FM_sat_has_solution':
  assumes "pol_lengths ps" "pol_sat (FM ps n) xs"
  shows "\<exists>t. pol_sat ps (xs[n := t])"
  by (metis (mono_tags, lifting) Submission.GZL_div_sat GZL_div_def GZL_div_triple_lengths GZL_inv
        GZL_product_sat_iff GZL_def GZL_sorting_lengths GZL_sorting_sat GZL_sorts
        len_xs length_list_update n_bound FM_def triple.simps(2) assms)

theorem FM_sat_equivalent:
  assumes "pol_lengths ps"
  shows "pol_sat (FM ps n) xs \<longleftrightarrow> (\<exists>t. pol_sat ps (xs[n := t]))"
  using FM_preserves_solution' FM_sat_has_solution' assms by metis

end
end
end

theorem ineq_add_cancel:
  assumes "length gcs = length xs" "n < length xs" "gcs!n = 1" "length lcs = length xs" "lcs!n = -1"
  shows
  "ineq_sat (ineq_add (ineq gcs gk) (ineq lcs lk)) xs \<longleftrightarrow>
  eval_term (gcs[n := 0]) xs + eval_term (lcs[n := 0]) xs \<le> gk + lk"
  using assms by (intro ineq_add_cancel') (auto simp: pol_lengths_def)

theorem eval_term_nth_split:
  assumes "length gcs = length xs" "n < length xs"
  shows "eval_term gcs (xs[n := t]) = eval_term (gcs[n := 0]) xs + gcs!n * t"
  using assms by (intro eval_term_nth_split') (auto simp: pol_lengths_def)

theorem FM_preserves_solution:
  assumes "\<forall>p \<in> set ps. (case p of (ineq cs k) \<Rightarrow> length cs = length xs)" "n < length xs"
    "pol_sat ps (xs[n := t])"
  shows "pol_sat (FM ps n) xs"
  using assms by (intro FM_preserves_solution') (auto simp: pol_lengths_def)

theorem FM_sat_has_solution:
  assumes "\<forall>p \<in> set ps. (case p of (ineq cs k) \<Rightarrow> length cs = length xs)" "n < length xs"
    "pol_sat (FM ps n) xs"
  shows "\<exists>t. pol_sat ps (xs[n := t])"
  using assms by (intro FM_sat_has_solution') (auto simp: pol_lengths_def)

end