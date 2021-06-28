theory Submission
  imports Defs
begin

lemma setcompr_eq_image2:
  "{f x y | x y. P x y} = (\<lambda>(x, y). f x y) ` {(x, y). P x y}" for f
  using setcompr_eq_image[where f = "(\<lambda>(x, y). f x y)" and P = "\<lambda>(x, y). P x y"] by simp

lemma finite_aux1:
  "finite {(x, y). x \<le> y \<and> y < (n :: nat)}"
  by (rule finite_subset[where B = "{(x, y). x < n \<and> y < (n :: nat)}"]) auto

context
  fixes a :: "nat \<Rightarrow> int" \<comment> \<open>The input array\<close>
  fixes n :: nat \<comment> \<open>The length of @{term a}\<close>
  assumes n_gt_0: "n > 0"
begin

definition max_sum_subseq where
  "max_sum_subseq = Max {\<Sum>k=i..j. a k | i j. i \<le> j \<and> j < n}"

definition sum_upto where
  "sum_upto j = Max {\<Sum>k=i..j. a k | i. i \<le> j}"

lemma sum_upto_in:
  "sum_upto j \<in> {\<Sum>k=i..j. a k | i. i \<le> j}"
  unfolding sum_upto_def by (intro Max_in) auto

lemma max_sum_subseq_Max_sum_upto':
  "max_sum_subseq = Max {sum_upto j | j. j < n}" (is "?l = ?r")
proof (rule antisym)
  show "?r \<le> ?l"
    unfolding max_sum_subseq_def
  proof (rule Max_mono)
    show "{sum_upto j | j. j < n} \<subseteq> {\<Sum>k=i..j. a k | i j. i \<le> j \<and> j < n}"
      unfolding sum_upto_def
    proof clarsimp
      fix j :: nat
      assume \<open>j < n\<close>
      have "Max {sum a {i..j} |i. i \<le> j} \<in> {sum a {i..j} |i. i \<le> j}"
        by (rule Max_in) auto
      with \<open>j < n\<close> show \<open>\<exists>i j'.
           Max {sum a {i..j} |i. i \<le> j} = sum a {i..j'} \<and> i \<le> j' \<and> j' < n\<close>
        by auto
    qed
    show \<open>{sum_upto j |j. j < n} \<noteq> {}\<close>
      using n_gt_0 by auto
  next
    show \<open>finite {sum a {i..j} |i j. i \<le> j \<and> j < n}\<close>
      by (subst setcompr_eq_image2, rule finite_imageI, rule finite_aux1)
  qed
  show "?l \<le> ?r"
  proof -
    from n_gt_0 have "max_sum_subseq \<in> {\<Sum>k=i..j. a k | i j. i \<le> j \<and> j < n}"
      unfolding max_sum_subseq_def apply (intro Max_in)
      apply  (subst setcompr_eq_image2, rule finite_imageI, rule finite_aux1)
       apply auto
      done
    then obtain i j where "i \<le> j" "j < n" "max_sum_subseq = (\<Sum>k=i..j. a k)"
      by auto
    then have "max_sum_subseq \<le> sum_upto j"
      unfolding sum_upto_def by (intro Max_ge) auto
    with \<open>j < n\<close> show "max_sum_subseq \<le> ?r"
      by (elim order.trans, intro Max_ge, auto)
  qed
qed

lemma sum_upto_rec':
  "sum_upto (Suc j) = (if sum_upto j > 0 then sum_upto j + a (j + 1) else a (j + 1))" (is "?l = ?r")
proof (rule antisym)
  obtain i0 i1 where
    "sum_upto j = (\<Sum>k=i0..j. a k)" "?l = (\<Sum>k=i1..j + 1. a k)" "i0 \<le> j" "i1 \<le> j + 1"
    using sum_upto_in[of j] sum_upto_in[of "Suc j"] by auto
  from \<open>i0 \<le> j\<close> show "?r \<le> ?l"
    unfolding \<open>sum_upto j = _\<close> unfolding sum_upto_def
    by (intro Max_ge, simp)
       (smt (z3) Suc_eq_plus1 le_imp_less_Suc less_le_not_le mem_Collect_eq not_le
         sum.nat_ivl_Suc' sum.ub_add_nat)
  show "?l \<le> ?r"
  proof (cases "i1 = j + 1")
    case True
    then show ?thesis
      using \<open>?l = _\<close> by auto
  next
    case False
    with \<open>i1 \<le> j + 1\<close> have "i1 \<le> j"
      by auto
    then have "?l = (\<Sum>k=i1..j. a k) + a (j + 1)"
      unfolding \<open>?l = _\<close> by simp
    also from \<open>i1 \<le> j\<close> False have "\<dots> \<le> sum_upto j + a (j + 1)"
      unfolding sum_upto_def by (intro add_right_mono Max_ge) auto
    finally show ?thesis
      by auto
  qed
qed

lemma sum_upto_0:
  "sum_upto 0 = a 0"
  unfolding sum_upto_def by auto

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

definition
  "max_upto i = Max {sum_upto j | j. j < i}"

lemma max_upto_rec:
  "max_upto (Suc i) = max (sum_upto i) (max_upto i)" if "i > 0"
proof -
  have *: "j < Suc i \<longleftrightarrow> (j < i \<or> j = i)" for j
    by auto
  show ?thesis
    using that unfolding max_upto_def
    by (subst Max_insert[symmetric]) (auto simp: * intro: arg_cong[where f= Max])
qed

lemma f_invariant:
  "f i (sum_upto (i - 1)) (max_upto i) = max_upto n" if "0 < i" "i \<le> n"
  using that
proof (induction "n - i" arbitrary: i)
  case 0
  then show ?case
    unfolding max_sum_subseq_Max_sum_upto' by (subst f.simps) simp
next
  case (Suc x)
  from Suc.hyps(1)[of "i + 1"] Suc.hyps(2-) Suc.prems have 1:
    "f (i + 1) (sum_upto i) (max_upto (i + 1)) = max_upto n"
    by simp
  from \<open>i > 0\<close> obtain i' where "i = Suc i'"
    by (metis Suc_pred)
  from Suc.prems have 2:
    "sum_upto i = (if sum_upto (i - 1) > 0 then sum_upto (i - 1) + a i else a i)"
    unfolding \<open>i = _\<close> by (subst sum_upto_rec'; simp)
  from \<open>i > 0\<close> have 3: "max_upto (i + 1) = max (sum_upto i) (max_upto i)"
    by (simp add: max_upto_rec)
  from Suc.prems show ?case
    apply (subst f.simps)
    apply (auto simp: Let_def)
    unfolding 1[symmetric] 2 3
    by simp+
qed

lemma max_sum_subseq_max_upto':
  "max_sum_subseq = max_upto n"
  unfolding max_upto_def max_sum_subseq_Max_sum_upto' ..

lemma max_upto_1:
  "max_upto (Suc 0) = a 0"
  unfolding max_upto_def by (simp add: sum_upto_0)

theorem max_sum_subseq_compute':
  "max_sum_subseq = f 1 (a 0) (a 0)"
  using n_gt_0 unfolding max_sum_subseq_max_upto'
  by (subst f_invariant[symmetric, where i = 1]; simp add: sum_upto_0 max_upto_1)

lemma f_eq:
  "Defs.f a n i x y = Submission.f a n i x y" if "n > 0"
  by (induction i x y rule: f.induct) (simp add: f.simps that)

end

theorem max_sum_subseq_Max_sum_upto:
  "n > 0 \<Longrightarrow> Defs.max_sum_subseq a n = Max {Defs.sum_upto a j | j. j < n}"
  using max_sum_subseq_Max_sum_upto'
  by (simp only: Defs.max_sum_subseq_def Defs.sum_upto_def max_sum_subseq_def sum_upto_def)

theorem sum_upto_rec:
  "(n :: nat) > 0
  \<Longrightarrow> Defs.sum_upto a (Suc j) =
      (if Defs.sum_upto a j > 0 then Defs.sum_upto a j + a (j + 1) else a (j + 1))"
  using sum_upto_rec' by (simp only: Defs.sum_upto_def sum_upto_def)

theorem max_sum_subseq_compute:
  "n > 0 \<Longrightarrow> Defs.max_sum_subseq a n = Defs.f a n 1 (a 0) (a 0)"
  using max_sum_subseq_compute' by (simp only: Defs.max_sum_subseq_def max_sum_subseq_def f_eq)

end