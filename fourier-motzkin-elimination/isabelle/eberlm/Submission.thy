theory Submission
  imports Defs
begin

lemma eval_term_map2_add [simp]:
  assumes "length as = length bs" "length bs = length xs"
  shows "eval_term (map2 (+) as bs) xs = eval_term as xs + eval_term bs xs"
  using assms
  by (induction rule: list_induct3) (auto simp: eval_term_def algebra_simps)

lemma eval_term_kill:
  assumes "length gcs = length xs" "n < length xs"
  shows   "eval_term (gcs[n := 0]) xs = eval_term gcs xs - gcs ! n * xs ! n"
  using assms
  by (induction arbitrary: n rule: list_induct2)
     (auto split: list.splits nat.splits simp: eval_term_def)

text \<open>Prove the following helpful lemmas for proof of the main correctness theorem:\<close>
theorem ineq_add_cancel:
  assumes "length gcs = length xs" "n < length xs" "gcs!n = 1" "length lcs = length xs" "lcs!n = -1"
  shows   "ineq_sat (ineq_add (ineq gcs gk) (ineq lcs lk)) xs \<longleftrightarrow>
           eval_term (gcs[n := 0]) xs + eval_term (lcs[n := 0]) xs \<le> gk + lk"
  using assms by (auto simp: ineq_sat_def ineq_add_def eval_term_kill)

theorem eval_term_nth_split:
  assumes "length gcs = length xs" "n < length xs"
  shows "eval_term gcs (xs[n := t]) = eval_term (gcs[n := 0]) xs + gcs!n * t"
  using assms unfolding eval_term_def
  by (induction arbitrary: n rule: list_induct2)
     (auto split: list.splits nat.splits simp: eval_term_def)

lemma eval_term_list_div [simp]:
  assumes "length xs = length ys"
  shows   "eval_term (list_div xs \<bar>z\<bar>) ys = eval_term xs ys / \<bar>z\<bar>"
  using assms
  by (induction rule: list_induct2)
     (simp_all add: eval_term_def list_div_def divide_simps split: if_splits)

lemma triple_sat_GZL [simp]: "triple_sat (GZL ps n) xs \<longleftrightarrow> pol_sat ps xs"
  apply (auto simp: triple_sat_def GZL_def pol_sat_def G_def Z_def L_def)
  by (metis (mono_tags, lifting) ineq.case ineq.exhaust not_less_iff_gr_or_eq)

lemma ineq_sat_div:
  assumes "case p of ineq xs c \<Rightarrow> length xs = length ys \<and> xs ! n \<noteq> 0" "n < length ys"
  shows "ineq_sat (ineq_div p n) ys \<longleftrightarrow> ineq_sat p ys"
  using assms by (simp add: ineq_sat_def ineq_div_def field_simps split: ineq.splits)

lemma pol_sat_div:
  assumes "n < length ys" 
  assumes "\<forall>pa\<in>set xs. case pa of ineq xs c \<Rightarrow> length xs = length ys \<and> xs ! n \<noteq> 0"
  shows   "pol_sat (pol_div xs n) ys \<longleftrightarrow> pol_sat xs ys"
  using assms by (auto simp: pol_sat_def pol_div_def ineq_sat_div)

lemma Ball_mono:
  assumes "\<forall>x\<in>A. P x" "\<forall>x\<in>A. P x \<longrightarrow> Q x"
  shows   "\<forall>x\<in>A. Q x"
  using assms by blast

lemma triple_sat_GZL_div:
  assumes "case tr of triple ls es gs \<Rightarrow>
             (\<forall>p\<in>set ls. case p of ineq q _ \<Rightarrow> length q = length xs \<and> q ! n > 0) \<and>
             (\<forall>p\<in>set gs. case p of ineq q _ \<Rightarrow> length q = length xs \<and> q ! n < 0)" "n < length xs"
  shows   "triple_sat (GZL_div tr n) xs \<longleftrightarrow> triple_sat tr xs"
proof -
  obtain ls es gs where tr: "tr = triple ls es gs"
    by (cases tr) auto
  have "\<forall>p\<in>set ls. case p of ineq q _ \<Rightarrow> length q = length xs \<and> q ! n > 0"
    using assms(1) by (auto simp: tr)
  hence 1: "\<forall>p\<in>set ls. case p of ineq q _ \<Rightarrow> length q = length xs \<and> q ! n \<noteq> 0"
    by (rule Ball_mono) (auto simp: ineq.splits)
  have "\<forall>p\<in>set gs. case p of ineq q _ \<Rightarrow> length q = length xs \<and> q ! n < 0"
    using assms(1) by (auto simp: tr)
  hence 2: "\<forall>p\<in>set gs. case p of ineq q _ \<Rightarrow> length q = length xs \<and> q ! n \<noteq> 0"
    by (rule Ball_mono) (auto simp: ineq.splits)
  from 1 2 show ?thesis
   unfolding triple_sat_def GZL_div_def using assms(2)
   by (auto split: triple.splits simp: pol_sat_div tr)
qed

lemma pol_sat_GZL_product_preserves_solution:
  assumes "case tr of triple ls es gs \<Rightarrow>
             (\<forall>p\<in>set ls. case p of ineq q _ \<Rightarrow> length q = length xs \<and> q ! n = 1) \<and>
             (\<forall>p\<in>set es. case p of ineq q _ \<Rightarrow> length q = length xs \<and> q ! n = 0) \<and>
             (\<forall>p\<in>set gs. case p of ineq q _ \<Rightarrow> length q = length xs \<and> q ! n = -1)" "n < length xs"
  assumes "triple_sat tr xs"
  shows   "pol_sat (GZL_product tr) (xs[n := t])"
proof -
  obtain ls es gs where tr: "tr = triple ls es gs"
    by (cases tr) auto

  have *: "ineq_sat p (xs[n := t])" if "p \<in> set (term_pairing ls gs)" for p
  proof -
    from that obtain l g where lg: "l \<in> set ls" "g \<in> set gs" "p = ineq_add l g"
      by (auto simp: term_pairing_def pol_add_def)
    obtain cs1 c1 where l: "l = ineq cs1 c1"
      by (cases l)
    obtain cs2 c2 where g: "g = ineq cs2 c2"
      by (cases g)
    from assms lg have l': "length cs1 = length xs \<and> cs1 ! n = 1"
      by (auto simp: l tr)
    from assms lg have g': "length cs2 = length xs \<and> cs2 ! n = -1"
      by (auto simp: g tr)

    have "eval_term cs1 xs + eval_term cs2 xs \<le> c1 + c2"
      using assms(3) l g lg
      by (intro add_mono) (auto simp: triple_sat_def tr pol_sat_def ineq_sat_def)
    also have "eval_term cs1 xs + eval_term cs2 xs =
               eval_term cs1 (xs[n := t]) + eval_term cs2 (xs[n := t])"
      using lg l g l' g' assms(2)
      by (auto simp: eval_term_nth_split eval_term_kill)
    finally show "ineq_sat p (xs[n := t])" using l' g' \<open>n < length xs\<close>
      by (auto simp: lg l g ineq_add_cancel[where n = n] eval_term_kill)
  qed

  have **: "ineq_sat p (xs[n := t])" if "p \<in> set es" for p
  proof -
    obtain cs c where p: "p = ineq cs c"
      by (cases p)
    from assms that have p': "length cs = length xs \<and> cs ! n = 0"
      by (auto simp: p tr)
    have "eval_term cs xs \<le> c"
      using assms that by (auto simp: triple_sat_def tr pol_sat_def p ineq_sat_def)
    also have "eval_term cs xs = eval_term cs (xs[n := t])"
      using p' \<open>n < length xs\<close> by (auto simp: eval_term_nth_split eval_term_kill)
    finally show ?thesis
      using that p p' assms
      by (auto simp: ineq_sat_def eval_term_kill eval_term_nth_split triple_sat_def tr)
  qed

  show ?thesis
    using assms(3) * **
    by (auto simp: pol_sat_def GZL_product_def triple_sat_def tr)
qed

definition eval_ineq where "eval_ineq p xs = (case p of ineq cs c \<Rightarrow> eval_term cs xs - c)"

lemma pol_sat_GZL_product_has_solution_aux:
  assumes "finite A" "finite B" "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> x \<le> y"
  shows   "\<exists>z::rat. (\<forall>x\<in>A. x \<le> z) \<and> (\<forall>y\<in>B. z \<le> y)"
  using assms by (metis finite_has_maximal finite_has_minimal le_less_linear less_le)

lemma pol_sat_GZL_product_has_solution:
  assumes "case tr of triple ls es gs \<Rightarrow>
             (\<forall>p\<in>set ls. case p of ineq q _ \<Rightarrow> length q = length xs \<and> q ! n = 1) \<and>
             (\<forall>p\<in>set es. case p of ineq q _ \<Rightarrow> length q = length xs \<and> q ! n = 0) \<and>
             (\<forall>p\<in>set gs. case p of ineq q _ \<Rightarrow> length q = length xs \<and> q ! n = -1)" "n < length xs"
  assumes "pol_sat (GZL_product tr) xs"
  shows   "\<exists>t. triple_sat tr (xs[n := t])"
proof -
  obtain ls es gs where tr: "tr = triple ls es gs"
    by (cases tr) auto

  have "\<exists>t. (\<forall>x\<in>(\<lambda>p. eval_ineq p (xs[n := 0]))`set gs. t \<ge> x) \<and>
            (\<forall>x\<in>(\<lambda>p. -eval_ineq p (xs[n := 0]))`set ls. t \<le> x)"
  proof (rule pol_sat_GZL_product_has_solution_aux; (safe)?, goal_cases)
    fix l g assume lg: "l \<in> set ls" "g \<in> set gs"
    obtain cs1 c1 where l: "l = ineq cs1 c1"
      by (cases l)
    obtain cs2 c2 where g: "g = ineq cs2 c2"
      by (cases g)
    from assms lg have l': "length cs1 = length xs \<and> cs1 ! n = 1"
      by (auto simp: l tr)
    from assms lg have g': "length cs2 = length xs \<and> cs2 ! n = -1"
      by (auto simp: g tr)

    have "ineq_add l g \<in> set (GZL_product tr)"
      using lg by (auto simp: l g tr GZL_product_def term_pairing_def pol_add_def)
    with assms have "ineq_sat (ineq_add l g) xs"
      by (auto simp: pol_sat_def)
    thus "eval_ineq g (xs[n := 0]) \<le> - eval_ineq l (xs[n := 0])"
      using lg l' g' \<open>n < _\<close>
      by (auto simp: ineq_sat_def l g ineq_add_def eval_ineq_def eval_term_nth_split eval_term_kill)
  qed auto
  then obtain t where t:
    "\<And>p. p \<in> set gs \<Longrightarrow> t \<ge> eval_ineq p (xs[n := 0])"
    "\<And>p. p \<in> set ls \<Longrightarrow> t \<le> -eval_ineq p (xs[n := 0])"
    by fast

  have 1: "ineq_sat p (xs[n := t])" if "p \<in> set gs" for p
  proof -
    obtain cs c where p: "p = ineq cs c"
      by (cases p)
    from assms that have p': "length cs = length xs \<and> cs ! n = -1"
      by (auto simp: p tr)
    have "t \<ge> eval_ineq p (xs[n := 0])"
      using that by (intro t(1)) auto
    hence "eval_term cs xs + xs ! n - t \<le> eval_term cs xs + xs ! n - eval_ineq p (xs[n := 0])"
      by simp
    also have "\<dots> = c"
      using p' \<open>n < length xs\<close>
      by (auto simp: p ineq_sat_def eval_term_nth_split eval_term_kill eval_ineq_def)
    finally show ?thesis
      using p' \<open>n < length xs\<close>
      by (auto simp: p ineq_sat_def eval_term_nth_split eval_term_kill eval_ineq_def)
  qed

  have 2: "ineq_sat p (xs[n := t])" if "p \<in> set ls" for p
  proof -
    obtain cs c where p: "p = ineq cs c"
      by (cases p)
    from assms that have p': "length cs = length xs \<and> cs ! n = 1"
      by (auto simp: p tr)
    have "t \<le> -eval_ineq p (xs[n := 0])"
      using that by (intro t(2)) auto
    hence "eval_term cs xs - xs ! n + t \<le> eval_term cs xs - xs ! n - eval_ineq p (xs[n := 0])"
      by simp
    also have "\<dots> = c"
      using p' \<open>n < length xs\<close>
      by (auto simp: p ineq_sat_def eval_term_nth_split eval_term_kill eval_ineq_def)
    finally show ?thesis
      using p' \<open>n < length xs\<close>
      by (auto simp: p ineq_sat_def eval_term_nth_split eval_term_kill eval_ineq_def)
  qed

  have 3: "ineq_sat p (xs[n := t])" if "p \<in> set es" for p
  proof -
    obtain cs c where p: "p = ineq cs c"
      by (cases p)
    from assms that have p': "length cs = length xs \<and> cs ! n = 0"
      by (auto simp: p tr)
    have "eval_term cs xs \<le> c"
      using assms that by (force simp: triple_sat_def tr pol_sat_def p ineq_sat_def GZL_product_def)
    also have "eval_term cs xs = eval_term cs (xs[n := t])"
      using p' \<open>n < length xs\<close> by (auto simp: eval_term_nth_split eval_term_kill)
    finally show ?thesis
      using that p p' assms
      by (auto simp: ineq_sat_def eval_term_kill eval_term_nth_split triple_sat_def tr)
  qed

  have "triple_sat tr (xs[n := t])"
    unfolding triple_sat_def using 1 2 3
    by (auto simp: tr pol_sat_def)
  thus ?thesis
    by blast
qed 


text \<open>We give partial credits for the two directions of the main theorem:\<close>
theorem FM_preserves_solution:
  assumes "\<forall>p \<in> set ps. (case p of (ineq cs k) \<Rightarrow> length cs = length xs)"
  assumes "n < length xs" "pol_sat ps (xs[n := t])"
  shows "pol_sat (FM ps n) xs"
proof -
  define xs' where "xs' = xs[n := t]"
  have "pol_sat (FM ps n) (xs'[n := xs ! n])"
  unfolding FM_def
  proof (rule pol_sat_GZL_product_preserves_solution[where n = n], goal_cases)
    case 1
    thus ?case using assms(1,2)
      by (auto simp: GZL_div_def GZL_def pol_div_def ineq_div_def list_div_def
                     G_def Z_def L_def xs'_def split: ineq.splits)
  next
    case 3
    have "case GZL ps n of
      triple ls es gs \<Rightarrow>
        Ball (set ls) (case_ineq (\<lambda>q x. length q = length xs' \<and> 0 < q ! n)) \<and>
        Ball (set gs) (case_ineq (\<lambda>q x. length q = length xs' \<and> q ! n < 0))"
      using assms(1)
      by (auto simp: GZL_def G_def L_def xs'_def split: ineq.splits)
    moreover have "triple_sat (GZL ps n) xs'"
      using assms by (subst triple_sat_GZL) (auto simp: xs'_def)
    ultimately show ?case using \<open>n < length xs\<close>
      by (subst triple_sat_GZL_div) (auto simp: xs'_def)
  qed (use assms in \<open>auto simp: xs'_def\<close>)
  also have "xs'[n := xs ! n] = xs"
    unfolding xs'_def by simp
  finally show ?thesis .
qed

theorem FM_sat_has_solution:
  assumes "\<forall>p \<in> set ps. (case p of (ineq cs k) \<Rightarrow> length cs = length xs)"
  assumes "n < length xs"
  assumes "pol_sat (FM ps n) xs"
  shows "\<exists>t. pol_sat ps (xs[n := t])"
proof -
  from assms have "pol_sat (GZL_product (GZL_div (GZL ps n) n)) xs"
    by (simp add: FM_def)
  have "\<exists>t. triple_sat (GZL_div (GZL ps n) n) (xs[n := t])"
  proof (rule pol_sat_GZL_product_has_solution, goal_cases)
    case 1
    thus ?case
    using assms(1,2)
    by (auto simp: GZL_div_def GZL_def G_def Z_def L_def pol_div_def
                   ineq_div_def list_div_def split: ineq.splits)
  qed (use assms in \<open>auto simp: FM_def\<close>)
  then obtain t where t: "triple_sat (GZL_div (GZL ps n) n) (xs[n := t])"
    by blast
  also have "?this \<longleftrightarrow> triple_sat (GZL ps n) (xs[n := t])"
    by (rule triple_sat_GZL_div)
       (use assms in \<open>auto simp: GZL_def G_def Z_def L_def split: ineq.splits\<close>)
  also have "\<dots> \<longleftrightarrow> pol_sat ps (xs[n := t])"
    by simp
  finally show ?thesis ..
qed

theorem FM_sat_equivalent:
  assumes "\<forall>p \<in> set ps. (case p of (ineq cs k) \<Rightarrow> length cs = length xs)" "n < length xs"
  shows "pol_sat (FM ps n) xs \<longleftrightarrow> (\<exists>t. pol_sat ps (xs[n := t]))"
  using FM_sat_has_solution FM_preserves_solution assms
  by blast

end