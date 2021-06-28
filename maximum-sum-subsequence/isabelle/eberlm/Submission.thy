theory Submission
  imports Defs
begin

text \<open>
  Annoying auxiliary lemma: a maximum over a dependent sum is the same as a
  maximum over the maximum.
\<close>
lemma Max_Sigma:
  fixes g :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: linorder"
  assumes "finite A" "A \<noteq> {}" "\<And>x. x \<in> A \<Longrightarrow> finite (B x)" "\<And>x. x \<in> A \<Longrightarrow> B x \<noteq> {}"
  shows   "Max ((\<lambda>(x,y). g x y) ` Sigma A B) = (MAX x\<in>A. MAX y\<in>B x. g x y)"
proof (intro antisym)
  show "Max ((\<lambda>(x,y). g x y) ` Sigma A B) \<le> (MAX x\<in>A. MAX y\<in>B x. g x y)"
    using assms by (intro Max.boundedI) (auto simp: Max_ge_iff)
next
  show "Max ((\<lambda>(x,y). g x y) ` Sigma A B) \<ge> (MAX x\<in>A. MAX y\<in>B x. g x y)"
  proof (intro Max.boundedI; (safe)?)
    fix a assume a: "a \<in> A"
    thus "Max (g a ` B a) \<le> (MAX (x, y)\<in>Sigma A B. g x y)"
    proof (intro Max.boundedI; (safe)?)
      fix b assume b: "b \<in> B a"
      show "g a b \<le> (MAX (x, y)\<in>Sigma A B. g x y)"
        using a b assms by (subst Max_ge_iff) auto
    qed (use assms in auto)
  qed (use assms in auto)
qed

context 
  fixes a :: "nat \<Rightarrow> int" \<comment> \<open>The input array\<close>
  fixes n :: nat \<comment> \<open>The length of @{term a}\<close>
  assumes n_gt_0: "n > 0"
begin

definition max_sum_subseq where
  "max_sum_subseq = Max {\<Sum>k=i..j. a k | i j. i \<le> j \<and> j < n}"

function f where
  "f i s m = (
    if i \<ge> n then m
    else
    let s' = (if s > 0 then s + a i else a i) in
    f (i + 1) s' (max s' m)
  )
  "
  by auto
termination
  by (relation "measure (\<lambda>(i, _, _). n - i)"; simp)

lemmas [simp del] = f.simps


definition t where "t i j = (\<Sum>k=i..j. a k)"
definition s where "s j = Max ((\<lambda>i. t i j) ` {..j})"

lemma s_0 [simp]: "s 0 = a 0"
  by (simp add: s_def t_def)

lemma t_Suc_right: "i \<le> Suc j \<Longrightarrow> t i (Suc j) = t i j + a (Suc j)"
  by (simp add: t_def)

lemma t_gt [simp]: "i > j \<Longrightarrow> t i j = 0"
  by (simp add: t_def)

lemma s_Suc: "s (Suc j) = max 0 (s j) + a (Suc j)"
proof -
  have "s (Suc j) = (MAX i\<in>{..Suc j}. t i (Suc j))"
    by (simp add: s_def)
  also have "\<dots> = (MAX i\<in>{..Suc j}. t i j + a (Suc j))"
    by (simp add: t_Suc_right)
  also have "\<dots> = (MAX i\<in>{..Suc j}. t i j) + a (Suc j)"
    by (metis Max_add_commute atMost_Suc_eq_insert_0 empty_not_insert finite_atMost)
  also have "{..Suc j} = insert (Suc j) {..j}"
    by auto
  also have "(MAX i\<in>\<dots>. t i j) = max 0 (s j)"
    by (simp add: s_def)
  finally show ?thesis .
qed

lemma f_correct:
  assumes "M = Max (s ` {..<i})"
  assumes "S = s (i - 1)"
  assumes "i > 0" "i \<le> n"
  shows   "f i S M = Max (s ` {..<n})"
  using assms
proof (induction i S M rule: f.induct)
  case (1 i S M)
  show ?case
  proof (cases "i \<ge> n")
    case True
    thus ?thesis using "1.prems"
      by (subst f.simps) auto
  next
    case False
    define S' where "S' = max 0 S + a i"
    obtain i' where i': "i = Suc i'"
      by (metis "1.prems"(3) Suc_pred)
    have S': "S' = s i"
      using "1.prems" False by (auto simp: S'_def s_Suc i')

    have "f i S M = f (i + 1) S' (max S' M)"
      using False by (subst f.simps) (auto simp: S'_def Let_def max_def)
    also have "\<dots> = Max (local.s ` {..<n})"
    proof (rule "1.IH")
      have "{..<i + 1} = insert i {..<i}"
        using \<open>i > 0\<close> by auto
      hence "Max (s ` {..<i + 1}) = Max (insert (s i) (s ` {..<i}))"
        by simp
      also have "\<dots> = max (s i) (Max (s ` {..<i}))"
        using \<open>i > 0\<close> by (subst Max.insert) auto
      also have "Max (s ` {..<i}) = M"
        using "1.prems" by simp
      finally show "max S' M = Max (s ` {..<i + 1})"
        by (simp add: S')
    qed (use "1.prems" False S' in \<open>auto simp: S'_def\<close>)
    finally show ?thesis .
  qed
qed

theorem max_sum_subseq_compute':
  "max_sum_subseq = f 1 (a 0) (a 0)"
proof -
  have "{sum a {i..j} |i j. i \<le> j \<and> j < n} = {t i j |i j. i \<le> j \<and> j < n}"
    by (auto simp: t_def)
  also have "\<dots> = (\<lambda>(j,i). t i j) ` (SIGMA j:{..<n}. {..j})"
    by (force simp: Sigma_def case_prod_unfold image_iff)
  also have "Max \<dots> = (MAX j\<in>{..<n}. MAX i\<in>{..j}. t i j)"
    using \<open>n > 0\<close> by (intro Max_Sigma) auto
  finally show ?thesis
    unfolding max_sum_subseq_def using n_gt_0
    by (subst f_correct) (auto simp: lessThan_Suc s_def t_def)
qed

lemma f_eq:
  "Defs.f a n i x y = Submission.f a n i x y" if "n > 0"
  by (induction i x y rule: f.induct) (simp add: f.simps that)

end

theorem max_sum_subseq_compute:
  "n > 0 \<Longrightarrow> Defs.max_sum_subseq a n = Defs.f a n 1 (a 0) (a 0)"
  using max_sum_subseq_compute' by (simp only: Defs.max_sum_subseq_def max_sum_subseq_def f_eq)

end