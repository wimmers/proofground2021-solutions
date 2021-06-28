theory Submission
  imports Defs
begin

text \<open>In case you are a unfamiliar with \<open>HOL-Algebra\<close>, here is a very brief primer:
\<^item> Groups are ``structures''. Usually we need to refer to these structures explicitly, i.e.
  @{term "\<one>\<^bsub>H\<^esub>"}, @{term "(\<otimes>\<^bsub>H\<^esub>)"}, \<open>inv\<^bsub>H\<^esub>\<close> are the neutral element, the group operation, and the
  inverse of group \<open>H\<close>, respectively.
\<^item> We fix the group \<open>G\<close> below, so \<open>\<one>\<close>, \<open>\<otimes>\<close>, \<open>inv\<close> will refer to \<open>G\<close> implicitly.
\<^item> The carrier set of a group \<open>G\<close> is denoted @{term "carrier G"}.
\<^item> Don't forget that most existing theorems (e.g. @{thm hom_mult}) will need to be equipped with the
  facts \<open>hom\<close>, \<open>group_G\<close>, \<open>group_H\<close>, \<open>x \<in> carrier G\<close>, \<dots>.
\<close>

text \<open>
  This task was a bit modified from the official one: the official one forgot the carrier
  assumptions of the premise h1. It makes basically no difference for the proof though.
\<close>
theorem solution:
  fixes G (structure) and H (structure) and f
  assumes
    hom: "f \<in> hom G H" and
    group_G: "group G" and
    group_H: "group H" and
    h1: "\<forall>a\<in>carrier G. \<forall>b\<in>carrier G. a \<otimes> b \<otimes> inv a \<otimes> inv b \<in> group.center G" and
    h2: "\<forall>x \<in> group.center G. f x = \<one>\<^bsub>H\<^esub> \<longrightarrow> x = \<one>"
  shows "inj_on f (carrier G)"
proof -
  interpret G: group G by fact
  interpret H: group H by fact
  interpret hom: group_hom G H f
    by unfold_locales fact

  (* Fun fact: sledgehammer can prove this (almost) automatically:

      show ?thesis
        apply (subst hom.inj_on_one_iff)
        using h1 h2 unfolding G.center_def
        apply auto
        by (smt (z3) G.inv_closed G.inv_solve_right' G.inv_unique G.l_inv_ex G.l_one G.m_closed
                     G.one_closed G.r_one h1 h2 hom.hom_mult hom.hom_one)

    But let's do it by hand instead.
  *)

  have "a = \<one>" if a: "a \<in> carrier G" "f a = \<one>\<^bsub>H\<^esub>" for a
  proof -
    have "a \<otimes> b = b \<otimes> a" if b: "b \<in> carrier G" for b
    proof -
      have "\<one>\<^bsub>H\<^esub> = f a \<otimes>\<^bsub>H\<^esub> f b \<otimes>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub> (f a) \<otimes>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub> (f b)"
        using a b by simp
      also have "\<dots> = f (a \<otimes>\<^bsub>G\<^esub> b \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> a \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> b)"
        using a b hom by simp
      finally have "\<dots> = \<one>\<^bsub>H\<^esub>" ..
      moreover have "a \<otimes>\<^bsub>G\<^esub> b \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> a \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> b \<in> group.center G"
        using h1 a b by blast
      ultimately have "a \<otimes>\<^bsub>G\<^esub> b \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> a \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> b = \<one>\<^bsub>G\<^esub>"
        using h2 by blast
      thus "a \<otimes> b = b \<otimes> a"
        using a b by (simp add: G.inv_solve_right')
    qed
    hence "a \<in> group.center G"
      unfolding G.center_def using a by auto
    with a show "a = \<one>" using h2 by auto
  qed
  thus ?thesis
    by (subst hom.inj_on_one_iff) blast
qed

end