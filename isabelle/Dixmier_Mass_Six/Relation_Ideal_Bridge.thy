theory Relation_Ideal_Bridge
  imports "Weyl_Free_Evaluation"
begin

text \<open>This is the least LEFT ideal containing all two-sided multiples
of the relation. Right closure is proved separately, as in the Lean source.\<close>

definition weyl_relation_multiples :: "'k::field weyl_free set" where
  "weyl_relation_multiples = {u * weyl_relation * v |u v. True}"

inductive_set relation_left_span :: "'k::field weyl_free set" where
  multiple: "u * weyl_relation * v \<in> relation_left_span"
| zero: "0 \<in> relation_left_span"
| add: "p \<in> relation_left_span \<Longrightarrow> q \<in> relation_left_span \<Longrightarrow> p+q \<in> relation_left_span"
| left: "p \<in> relation_left_span \<Longrightarrow> u*p \<in> relation_left_span"

lemma relation_left_span_least:
  assumes "weyl_relation_multiples \<subseteq> L" "0 \<in> L"
    "\<And>p q. p \<in> L \<Longrightarrow> q \<in> L \<Longrightarrow> p+q \<in> L"
    "\<And>u p. p \<in> L \<Longrightarrow> u*p \<in> L"
  shows "(relation_left_span :: 'k::field weyl_free set) \<subseteq> L"
proof
  fix p assume "p \<in> (relation_left_span :: 'k weyl_free set)"
  then show "p \<in> L"
    by (induction rule: relation_left_span.induct)
       (use assms in \<open>auto simp: weyl_relation_multiples_def\<close>)
qed

lemma relation_left_span_neg:
  "p \<in> relation_left_span \<Longrightarrow> -p \<in> relation_left_span"
  using relation_left_span.left[of p "-1"] by simp

lemma relation_left_span_right:
  "p \<in> relation_left_span \<Longrightarrow> p*b \<in> relation_left_span"
proof (induction rule: relation_left_span.induct)
  case (multiple u v)
  have "u * weyl_relation * (v*b) \<in> relation_left_span" by (rule relation_left_span.multiple)
  then show ?case by (simp only: mult.assoc)
next
  case zero show ?case by (simp only: mult_zero_left relation_left_span.zero)
next
  case (add p q)
  then show ?case by (simp only: distrib_right) (rule relation_left_span.add)
next
  case (left p u)
  then show ?case by (simp only: mult.assoc) (rule relation_left_span.left)
qed

lemma free_additive_inverse:
  "a_inv (free_ring :: 'k::field weyl_free ring) p = -p"
proof -
  have pick: "(THE y. y = -p \<and> p = -y) = -p"
  proof (rule the_equality)
    show "-p = -p \<and> p = -(-p)"
    proof (rule conjI)
      show "-p = -p" by (rule refl)
      show "p = -(-p)" by (rule minus_minus[symmetric])
    qed
    fix y assume "y = -p \<and> p = -y"
    then show "y = -p" by (rule conjunct1)
  qed
  show ?thesis
    by (simp only: a_inv_def m_inv_def free_ring_def nc_type_ring_def
      ring_record_simps UNIV_I simp_thms add_eq_0_iff pick)
qed

lemma relation_left_span_is_ideal:
  "ideal (relation_left_span :: 'k::field weyl_free set) free_ring"
proof (rule idealI[OF free_ring_is_ring])
  show "subgroup (relation_left_span :: 'k weyl_free set) (add_monoid free_ring)"
  proof (rule subgroup.intro)
    show "(relation_left_span :: 'k weyl_free set) \<subseteq> carrier (add_monoid free_ring)" by simp
    show "\<And>x y. x \<in> (relation_left_span :: 'k weyl_free set) \<Longrightarrow>
      y \<in> relation_left_span \<Longrightarrow>
      monoid.mult (add_monoid free_ring) x y \<in> relation_left_span"
      by (simp only: monoid_record_simps free_ring_simps) (rule relation_left_span.add)
    show "monoid.one (add_monoid (free_ring :: 'k weyl_free ring)) \<in> relation_left_span"
      by (simp only: monoid_record_simps free_ring_simps relation_left_span.zero)
    show "\<And>x. x \<in> (relation_left_span :: 'k weyl_free set) \<Longrightarrow>
      m_inv (add_monoid free_ring) x \<in> relation_left_span"
      by (simp only: a_inv_def[symmetric] free_additive_inverse) (rule relation_left_span_neg)
  qed
  show "\<And>a x. a \<in> (relation_left_span :: 'k weyl_free set) \<Longrightarrow>
    x \<in> carrier free_ring \<Longrightarrow> monoid.mult free_ring x a \<in> relation_left_span"
    by (simp only: free_ring_simps) (rule relation_left_span.left)
  show "\<And>a x. a \<in> (relation_left_span :: 'k weyl_free set) \<Longrightarrow>
    x \<in> carrier free_ring \<Longrightarrow> monoid.mult free_ring a x \<in> relation_left_span"
    by (simp only: free_ring_simps) (rule relation_left_span_right)
qed

lemma relation_left_span_subset_generated:
  "(relation_left_span :: 'k::field weyl_free set) \<subseteq> weyl_relation_ideal"
proof -
  interpret J: ideal "(weyl_relation_ideal :: 'k weyl_free set)" free_ring
    by (rule weyl_relation_ideal_is_ideal)
  show ?thesis
  proof (rule relation_left_span_least)
    show "weyl_relation_multiples \<subseteq> (weyl_relation_ideal :: 'k weyl_free set)"
    proof -
      have multiple: "u * weyl_relation * v \<in> weyl_relation_ideal" for u v :: "'k weyl_free"
      proof -
        have left: "monoid.mult free_ring u weyl_relation \<in> (weyl_relation_ideal :: 'k weyl_free set)"
          by (rule J.I_l_closed[OF weyl_relation_mem_ideal]) simp
        have "monoid.mult free_ring (u * weyl_relation) v \<in> (weyl_relation_ideal :: 'k weyl_free set)"
          by (rule J.I_r_closed) (use left in simp_all)
        then show ?thesis by simp
      qed
      show ?thesis using multiple by (auto simp: weyl_relation_multiples_def)
    qed
    show "0 \<in> (weyl_relation_ideal :: 'k weyl_free set)"
      using additive_subgroup.zero_closed[OF ideal.axioms(1)[OF weyl_relation_ideal_is_ideal]]
      by (simp only: free_ring_simps)
    show "\<And>p q. p \<in> (weyl_relation_ideal :: 'k weyl_free set) \<Longrightarrow>
      q \<in> weyl_relation_ideal \<Longrightarrow> p+q \<in> weyl_relation_ideal"
      using additive_subgroup.a_closed[OF ideal.axioms(1)[OF weyl_relation_ideal_is_ideal]]
      by (simp only: free_ring_simps)
    show "\<And>u p. p \<in> (weyl_relation_ideal :: 'k weyl_free set) \<Longrightarrow> u*p \<in> weyl_relation_ideal"
      using J.I_l_closed by simp
  qed
qed

lemma generated_subset_relation_left_span:
  "(weyl_relation_ideal :: 'k::field weyl_free set) \<subseteq> relation_left_span"
proof -
  have rel: "(weyl_relation :: 'k weyl_free) \<in> relation_left_span"
    using relation_left_span.multiple[of 1 1] by simp
  show ?thesis unfolding weyl_relation_ideal_def
    by (rule ring.genideal_minimal[OF free_ring_is_ring relation_left_span_is_ideal])
       (use rel in auto)
qed

lemma relation_left_span_eq_generated:
  "(relation_left_span :: 'k::field weyl_free set) = weyl_relation_ideal"
  by (rule antisym[OF relation_left_span_subset_generated generated_subset_relation_left_span])

end
