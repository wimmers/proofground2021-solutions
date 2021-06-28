theory Submission
  imports Defs
begin


fun compl' :: "intervals \<Rightarrow> intervals" where
  "compl' [[l,\<infinity>)] = []"
| "compl' [[l,r)] = [[r, \<infinity>)]"
| "compl' ([l1,r1)#[l2,r2)#is) = [r1, l2)#compl' ([l2,r2)#is)"
| "compl' [] = []"

fun compl where
  "compl [] = [[0, \<infinity>)]"
| "compl ([l, r)#is) = (if l = 0 then [] else [[0, l)]) @ compl' ([l, r)#is)"
\<comment> \<open>Simon: Needed 15 min for reading & def.\<close>

lemma inv'_anti_mono:
  "inv' k' ins" if "inv' k ins" "k \<ge> k'"
  using that
  apply (induction ins rule: inv'.induct)
     apply auto
  done

lemma inv'_tighten:
  "inv' l ([l, r)#ins)" if "inv' k ([l, r)#ins)"
  using that
  using inv'.elims(3) by fastforce

lemma compl'_inv':
  assumes "inv' k ins"
  shows "inv' (Suc k) (compl' ins)"
  using assms
  apply (induction ins arbitrary: k rule: compl'.induct)
      apply (simp_all add: inv_def)
  apply (auto simp add: inv_def)
  subgoal
    using inv'.elims(2) by fastforce
(*
  subgoal premises prems
    using prems(2-) apply -
    apply (frule prems(1))
    apply (rule inv'_anti_mono, assumption)
    using inv'_anti_mono
    oops
*)
    by (smt (verit) Suc_le_eq compl'.elims interval.inject inv'.elims(3) inv'.simps(3) inv'.simps(4) list.discI list.inject)
  (*  
  by (smt (z3) Suc_le_eq compl'.elims interval.inject inv'.simps(1) inv'.simps(2) inv'.simps(3) inv'.simps(4) list.inject)
*)
(*
    by (smt (z3) Suc_le_eq compl'.elims compl'.simps(1) enat.inject interval.inject inv'.elims(1) inv'.simps(1) inv'.simps(2) inv'.simps(4) list.inject zero_le)
*)

(*
lemma compl'_inv:
  assumes "inv ins"
  shows "inv (compl' ins)"
  using assms compl'_inv' by (simp add: inv_def)
*)

lemma [simp]:
  "set_of [] = {}"
  unfolding set_of_def by simp

lemma [simp]:
  "set_of [i] = set_of_i i"
  unfolding set_of_def by simp

lemma set_of_cons':
  "fold (\<union>) (map set_of_i xs) S = S \<union> fold (\<union>) (map set_of_i xs) {}"
  unfolding set_of_def
  apply (induction xs arbitrary: S)
   apply (simp add: set_of_def)
  by (smt (z3) Un_assoc Un_left_commute fold_simps(2) list.simps(9))

lemma set_of_cons:
  "set_of (a # xs) = set_of_i a \<union> set_of xs"
  unfolding set_of_def
  apply simp
  apply (rule set_of_cons')
  done

lemma Un_Diff_R:
  assumes "A \<inter> C = {}"
  shows "A \<union> B - C = A \<union> (B - C)"
  using assms
  by blast

lemma inv'_inf:
  assumes "inv' k ([l,\<infinity>) # ins)"
  shows "ins = []"
  using assms
  apply (induction "[l,\<infinity>)#ins" arbitrary: l ins rule: inv'.induct)
   apply auto
  done

lemma compl'_lb':
  assumes "inv' k ([l,r)#ins)"
  shows "set_of (compl' ([l,r)#ins)) \<subseteq> {r..}"
  using assms
  apply (induction "[l,r)#ins" arbitrary: k l r ins rule: compl'.induct)
   apply (auto simp add: set_of_def; fail)
  apply (simp add: set_of_cons)
  apply rule
   apply force
  subgoal for l1 r1 l2 r2 "is" k
    apply (cases r2)
     apply simp
     apply force
    apply simp
    apply (auto dest!: inv'_inf simp: set_of_def)
    done
  done

lemma compl'_lb:
  assumes "inv' k ([l,r)#ins)"
  shows "set_of (compl' ([l,r)#ins)) \<subseteq> (case r of \<infinity> \<Rightarrow> {} | enat r \<Rightarrow> {r..})"
  using assms
  apply (cases r)
   apply simp
   apply (rule compl'_lb')
   apply force
  apply simp
  apply (drule inv'_inf)
  apply simp
  done

lemma interval_aux:
  fixes l r1 r2 :: nat
  assumes "l < r1" "r1 < l2"
  shows "{0..<l} \<union> {r1..<l2} = {0..<l2} - {l..<r1}"
  using assms by auto

lemma compl'_correct:
  assumes "inv' k ([l,r)#ins)"
  shows "set_of (compl' ([l,r)#ins)) \<union> {0..<l} = -set_of ([l,r)#ins)"
  using assms
  apply (induction ins arbitrary: k l r)
  subgoal for k l r
   apply (cases "[[l,r)]" rule: compl'.cases)
       apply (auto simp add: set_of_def; fail)
      apply (auto simp add: set_of_def; fail)
     apply (auto simp add: set_of_def; fail)
    apply (auto simp add: set_of_def; fail)
    apply (auto simp add: set_of_def; fail)
    done
  subgoal for a ins k l r
    apply (cases "[l,r) # a # ins" rule: compl'.cases)
        apply (auto simp add: set_of_def; fail)
       apply (auto simp add: set_of_def; fail)
    defer
      apply (auto simp add: set_of_def; fail)
     apply (auto simp add: set_of_def; fail)
    apply simp
    subgoal premises prems for r1 l2 r2

      using prems(1)[of "Suc r1" "l2" "r2"] prems(2-)
      apply simp
      apply (subst set_of_cons)
      apply simp
      apply (subgoal_tac "
  {r1..<l2} \<union> set_of (compl' ([l2,r2) # ins)) \<union> {0..<l} = (set_of (compl' ([l2,r2) # ins)) \<union> {0..<l2}) - {l..<r1}")
      apply simp
       apply (simp add: set_of_cons)
       apply blast
      apply (subgoal_tac "
  {r1..<l2} \<union> {0..<l} = {0..<l2} - {l..<r1}")
       apply (subst Un_commute)
       apply (subst Un_assoc)
       apply (subst Un_Diff_R)
      subgoal
        apply (elim conjE)
        thm compl'_lb
        apply (frule compl'_lb)
        apply (auto split: enat.split_asm)
        done
       apply simp
      apply (subst Un_commute)
      apply (rule interval_aux)
       apply auto
      thm inv'.cases
      apply (cases r2)
       apply simp
      apply simp
      apply (frule inv'_inf)
      apply auto
      done
    done
  done

lemma compl_set_of:
  assumes "inv ins"
  shows "set_of (compl ins) = -set_of ins"
  apply (cases ins rule: compl.cases)
   apply simp
  apply simp
  using assms[unfolded inv_def]
  apply simp
  apply (frule compl'_correct)
  apply (auto simp: set_of_cons)
  done

\<comment> \<open>Simon: Needed ~2h including def.\<close>
theorem compl_inv:
  assumes "inv ins"
  shows "inv (compl ins)"
   apply -
  subgoal
    using assms
    unfolding inv_def
    apply (cases ins rule: compl.cases)
     apply simp
    apply (auto intro: compl'_inv')
    defer
    thm compl'_inv'
    apply (rule compl'_inv')
    thm inv'_tighten
     apply (erule inv'_tighten)
    apply (drule compl'_inv')
    apply (erule inv'_anti_mono)
    apply rule
    done
  done

end