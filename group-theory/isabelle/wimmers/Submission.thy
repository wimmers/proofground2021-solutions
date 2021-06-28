theory Submission
  imports Defs
begin

theorem solution:
  fixes G (structure) and H (structure) and f
  assumes
    hom: "f \<in> hom G H" and
    group_G: "group G" and
    group_H: "group H" and
    h1: "\<forall>a b. a \<otimes> b \<otimes> inv a \<otimes> inv b \<in> group.center G" and
    h2: "\<forall>x \<in> group.center G. f x = \<one>\<^bsub>H\<^esub> \<longrightarrow> x = \<one>"
  shows "inj_on f (carrier G)"
proof -
  have "\<forall> a \<in> carrier G. f a = \<one>\<^bsub>H\<^esub> \<longrightarrow> a = \<one>"
  proof safe
    fix a :: 'a
    assume [simp]: \<open>a \<in> carrier G\<close> and [simp]: \<open>f a = \<one>\<^bsub>H\<^esub>\<close>
    then have "a \<in> group.center G"
      unfolding group.center_def[OF group_G]
    proof safe
      fix g :: 'a
      assume [simp]: \<open>g \<in> carrier G\<close>
      note h[simp] = hom_mult[OF hom] hom_one[OF hom]
      note closed[simp] = monoid.m_closed[OF group.is_monoid, OF group_G] hom_in_carrier[OF hom]
      note group[simp] = group_G group_H group.is_monoid
      have "f (a \<otimes> g \<otimes> inv a \<otimes> inv g) = \<one>\<^bsub>H\<^esub>"
      proof -
        have [simp]: "f (inv a) = inv\<^bsub>H\<^esub> (f a)"
          by (metis \<open>a \<in> carrier G\<close> \<open>f a = \<one>\<^bsub>H\<^esub>\<close> group.inv_closed group.l_cancel_one' group.l_inv
                group_G group_H h hom hom_in_carrier)
        have "f (a \<otimes> g \<otimes> inv a \<otimes> inv g) = f a \<otimes>\<^bsub>H\<^esub> f g \<otimes>\<^bsub>H\<^esub> f (inv a) \<otimes>\<^bsub>H\<^esub> f (inv g)"
          by simp
        also have "\<dots> = f g \<otimes>\<^bsub>H\<^esub> f (inv g)"
          by (simp add: monoid.inv_one)
        also have "\<dots> = \<one>\<^bsub>H\<^esub>"
          by (simp flip: h add: group.r_inv)
        finally show ?thesis .
      qed
      with h1 h2 have "a \<otimes> g \<otimes> inv a \<otimes> inv g = \<one>"
        by auto
      then show \<open>a \<otimes> g = g \<otimes> a\<close>
        by (subst group.inv_solve_right'[symmetric]; simp) (subst (asm) group.inv_solve_right'; simp)
    qed
    with h2 \<open>f a = \<one>\<^bsub>H\<^esub>\<close> show \<open>a = \<one>\<close>
      by simp
  qed
  with hom have "f \<in> mon G H"
    unfolding mon_iff_hom_one[OF group_G group_H] by simp
  then show ?thesis \<comment> \<open>Missing \<open>monoid_hom.injective_iff\<close> from Lean here\<close>
    unfolding mon_def by simp
qed

end