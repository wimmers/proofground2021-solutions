theory Submission
  imports Defs
begin

lemma set_of_altdef_aux: "fold (\<union>) (map set_of_i xs) A  = \<Union> (set_of_i ` set xs) \<union> A"
  unfolding set_of_def
  by (induction xs arbitrary: A) auto

lemma set_of_altdef: "set_of xs = (\<Union>ivl\<in>set xs. set_of_i ivl)"
  unfolding set_of_def by (simp add: set_of_altdef_aux)

lemma set_of_Nil [simp]: "set_of [] = {}"
  by (simp add: set_of_altdef)

lemma set_of_append [simp]: "set_of (xs @ ys) = set_of xs \<union> set_of ys"
  by (simp add: set_of_altdef)

lemma set_of_Cons [simp]: "set_of (x # xs) = set_of_i x \<union> set_of xs"
  by (simp add: set_of_altdef)

fun compl_aux :: "nat \<Rightarrow> intervals \<Rightarrow> intervals" where
  "compl_aux a [] = [[a, \<infinity>)]"
| "compl_aux a ([l, enat u) # ivls) = (if a = l then [] else [[a, enat l)]) @ compl_aux u ivls"
| "compl_aux a [[l, \<infinity>)] = (if a = l then [] else [[a, enat l)])"

lemma inv'_mono:
  assumes "inv' a ivls" "b \<le> a"
  shows   "inv' b ivls"
  using assms
  by (induction a ivls rule: inv'.induct) auto

lemma inv'_subset:
  assumes "inv' u ivls"
  shows   "set_of ivls \<subseteq> {u..}"
  using assms by (induction u ivls rule: inv'.induct) auto

lemma inv'_compl_aux:
  fixes ivls :: intervals
  assumes "inv' a ivls" "\<forall>x\<in>set_of ivls. x \<ge> a"
  shows   "inv' a (compl_aux a ivls)"
  using assms
proof (induction a ivls rule: compl_aux.induct)
  case (2 a l u ivls)
  have IH: "inv' u (compl_aux u ivls)"
    using 2 inv'_mono[of "Suc u" ivls u] inv'_subset
    by (intro "2.IH") auto
  show ?case
    using IH "2.prems" by (auto intro: inv'_mono)
qed (auto simp: atLeast_def)

lemma set_of_compl_aux:
  fixes ivls :: intervals
  assumes "inv' a ivls"
  shows   "set_of (compl_aux a ivls) = {a..} - set_of ivls"
  using assms
proof (induction a ivls rule: compl_aux.induct)
  case (2 a l u ivls)
  have "set_of (compl_aux u ivls) = {u..} - set_of ivls"
    using "2.prems" inv'_mono by (intro "2.IH") force+
  thus ?case using "2.prems"  inv'_subset[of "Suc u" ivls] by force
qed auto


definition compl :: "intervals \<Rightarrow> intervals" where
  "compl x = compl_aux 0 x"

theorem compl_inv:
  assumes "inv ins"
  shows "inv (compl ins)"
  unfolding compl_def inv_def
  using assms by (intro inv'_compl_aux) (auto simp: inv_def)

theorem compl_set_of:
  assumes "inv ins"
  shows "set_of (compl ins) = -set_of ins"
  using assms unfolding compl_def by (subst set_of_compl_aux) (auto simp: inv_def)


text \<open>
  And for good measure: Intersection of interval lists.
\<close>
fun inter :: "intervals \<Rightarrow> intervals \<Rightarrow> intervals" where
  "inter [] ivls2 = []"
| "inter ivls1 [] = []"
| "inter [[l1, \<infinity>)] [[l2, \<infinity>)] = [[max l1 l2, \<infinity>)]"
| "inter ([l1, enat u1) # ivls1) [[l2, \<infinity>)] =
     (if u1 > l2 then [[max l1 l2, u1)] else []) @ inter ivls1 [[l2, \<infinity>)]"
| "inter [[l1, \<infinity>)] ([l2, enat u2) # ivls2) =
     (if u2 > l1 then [[max l1 l2, u2)] else []) @ inter [[l1, \<infinity>)] ivls2"
| "inter ([l1, enat u1) # ivls1) ([l2, enat u2) # ivls2) =
     (if u1 \<le> l2 then inter ivls1 ([l2, u2) # ivls2)
      else if u2 \<le> l1 then inter ([l1, u1) # ivls1) ivls2
      else [max l1 l2, min u1 u2) #
             (if u1 \<le> u2 then inter ivls1 ([l2, u2) # ivls2)
              else inter ([l1, u1) # ivls1) ivls2))"

lemma inv'_inter:
  assumes "inv' a ivls1" "inv' b ivls2" "max a b \<ge> c"
  shows   "inv' c (inter ivls1 ivls2)"
  using assms by (induction ivls1 ivls2 arbitrary: a b c rule: inter.induct) auto

lemma inv_inter:
  assumes "inv ivls1" "inv ivls2"
  shows   "inv (inter ivls1 ivls2)"
  using assms unfolding inv_def by (intro inv'_inter[where a = 0 and b = 0]) auto

lemma set_of_inter_aux:
  assumes "inv' a ivls1" "inv' b ivls2"
  shows   "set_of (inter ivls1 ivls2) = set_of ivls1 \<inter> set_of ivls2"
  using assms
proof (induction ivls1 ivls2 arbitrary: a b rule: inter.induct)
  case (6 l1 u1 ivls1 l2 u2 ivls2 a b)
  show ?case
  proof (cases "u1 \<le> l2")
    case True
    thus ?thesis using "6.prems" inv'_subset
      apply simp
      apply (subst "6.IH"(1)[where a = "Suc u1" and b = b])
         apply force+
      done
  next
    case not_le: False
    show ?thesis
    proof (cases "u2 \<le> l1")
      case True
      thus ?thesis using not_le inv'_subset "6.prems"
        apply simp
        apply (subst "6.IH"(2)[where a = "a" and b = "Suc u2"])
            apply force+
        done
    next
      case not_le': False
      show ?thesis
      proof (cases "u1 \<le> u2")
        case True
        thus ?thesis using not_le not_le' "6.prems" inv'_subset
          apply (simp)
          apply (subst "6.IH"(3)[where a = "Suc u1" and b = b])
               apply force+
          done
      next
        case False
        thus ?thesis using not_le not_le' "6.prems" inv'_subset
          apply (simp)
          apply (subst "6.IH"(4)[where a = a and b = "Suc u2"])
               apply force+
          done
      qed
    qed
  qed
qed auto

lemma set_of_inter:
  assumes "inv ivls1" "inv ivls2"
  shows   "set_of (inter ivls1 ivls2) = set_of ivls1 \<inter> set_of ivls2"
  using assms unfolding inv_def by (intro set_of_inter_aux[where a = 0 and b = 0]) auto

end