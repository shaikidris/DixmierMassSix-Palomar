theory Abstract_Finite_Coordinates
  imports "Abstract_Normal_Span"
begin

definition abstract_finite_normal_sum :: "(nat \<times> nat) set \<Rightarrow>
    (nat \<times> nat \<Rightarrow> 'k::field) \<Rightarrow> 'k weyl_free set" where
  "abstract_finite_normal_sum S c = central_lcomb abstract_weyl_ring abstract_scalar
    (\<lambda>u. abstract_normal_monomial (fst u) (snd u)) S c"
definition abstract_normal_ordered_sum :: "(nat \<times> nat \<Rightarrow> 'k::field) \<Rightarrow> 'k weyl_free set" where
  "abstract_normal_ordered_sum c = abstract_finite_normal_sum {u. c u \<noteq> 0} c"

fun abstract_normal_list :: "((nat \<times> nat) \<times> 'k::field) list \<Rightarrow> 'k weyl_free set" where
  "abstract_normal_list [] = ring.zero abstract_weyl_ring"
| "abstract_normal_list (t#ts) = ring.add abstract_weyl_ring
    (monoid.mult abstract_weyl_ring (abstract_scalar (snd t))
      (abstract_normal_monomial (fst (fst t)) (snd (fst t)))) (abstract_normal_list ts)"

context abstract_normal_arithmetic
begin

lemma normal_basis_closed:
  "(\<lambda>u. abstract_normal_monomial (fst u) (snd u)) \<in> S \<rightarrow> carrier Q"
  by (auto simp only: Pi_def intro: abstract_normal_monomial_closed)
lemma abstract_normal_sum_closed:
  "abstract_finite_normal_sum S c \<in> carrier Q"
  unfolding abstract_finite_normal_sum_def by (rule W.lcomb_closed[OF normal_basis_closed])
lemma abstract_normal_sum_empty:
  "(abstract_finite_normal_sum {} c :: 'k weyl_free set) = q0"
  by (simp only: abstract_finite_normal_sum_def W.lcomb_empty)
lemma abstract_normal_sum_insert:
  assumes "finite S" "u \<notin> S"
  shows "abstract_finite_normal_sum (insert u S) c =
    qa (qm (abstract_scalar (c u)) (abstract_normal_monomial (fst u) (snd u)))
      (abstract_finite_normal_sum S c)"
  unfolding abstract_finite_normal_sum_def
  by (rule W.lcomb_insert[OF assms normal_basis_closed])
lemma abstract_normal_sum_zero:
  "(abstract_finite_normal_sum S (\<lambda>_. 0) :: 'k weyl_free set) = q0"
  unfolding abstract_finite_normal_sum_def by (rule W.lcomb_zero[OF normal_basis_closed])
lemma abstract_normal_sum_add:
  "abstract_finite_normal_sum S (\<lambda>u. c u+d u) =
    qa (abstract_finite_normal_sum S c) (abstract_finite_normal_sum S d)"
  unfolding abstract_finite_normal_sum_def by (rule W.lcomb_add[OF normal_basis_closed])
lemma abstract_normal_sum_single:
  assumes "finite S" "u \<in> S"
  shows "abstract_finite_normal_sum S (\<lambda>v. if v=u then c else 0) =
    qm (abstract_scalar c) (abstract_normal_monomial (fst u) (snd u))"
  unfolding abstract_finite_normal_sum_def
  by (rule W.lcomb_single[OF assms(2,1) normal_basis_closed])
lemma abstract_normal_sum_restrict:
  assumes "finite S" "{u. c u \<noteq> 0} \<subseteq> S"
  shows "abstract_finite_normal_sum S c = (abstract_normal_ordered_sum c :: 'k weyl_free set)"
  unfolding abstract_finite_normal_sum_def abstract_normal_ordered_sum_def
  by (rule W.lcomb_restrict_support[OF assms(1) normal_basis_closed assms(2)])

lemma abstract_list_closed:
  "abstract_normal_list ts \<in> carrier Q"
  by (induction ts) (auto intro: W.scalar.S.zero_closed W.scalar.S.a_closed
    W.scalar.S.m_closed W.scalar_closed abstract_normal_monomial_closed)
lemma abstract_list_append:
  "abstract_normal_list (ts@us) = qa (abstract_normal_list ts) (abstract_normal_list us)"
  by (induction ts)
     (simp_all add: W.scalar.S.a_assoc abstract_list_closed abstract_normal_monomial_closed W.scalar_closed)
lemma abstract_list_scale:
  "abstract_normal_list (map (\<lambda>t. (fst t, d * snd t)) ts) =
    qm (abstract_scalar d) (abstract_normal_list ts)"
  by (induction ts)
     (simp_all add: abstract_scalar_mult W.scalar.S.r_distr W.scalar.S.m_assoc
       abstract_list_closed abstract_normal_monomial_closed W.scalar_closed)

lemma abstract_span_has_list:
  "z \<in> (abstract_normal_span :: 'k weyl_free set set) \<Longrightarrow> \<exists>ts. abstract_normal_list ts = z"
proof (induction rule: abstract_normal_span.induct)
  case (monomial i j)
  show ?case by (rule exI[of _ "[((i,j),1)]"])
    (simp add: abstract_scalar_one abstract_normal_monomial_closed)
next
  case zero show ?case by (rule exI[of _ "[]"]) (rule abstract_normal_list.simps(1))
next
  case (add z w)
  obtain ts where ts: "abstract_normal_list ts = z" using add.IH(1) by blast
  obtain us where us: "abstract_normal_list us = w" using add.IH(2) by blast
  show ?case by (rule exI[of _ "ts@us"]) (simp only: abstract_list_append ts us)
next
  case (scalar z c)
  obtain ts where ts: "abstract_normal_list ts = z" using scalar.IH by blast
  show ?case by (rule exI[of _ "map (\<lambda>t. (fst t, c * snd t)) ts"])
    (simp only: abstract_list_scale ts)
qed

lemma abstract_list_as_finite_sum:
  assumes fin: "finite S" and keys: "fst ` set ts \<subseteq> S"
  shows "abstract_normal_list ts = (abstract_finite_normal_sum S (normal_list_coeff ts) :: 'k weyl_free set)"
  using keys
proof (induction ts)
  case Nil
  have nil_coeff: "normal_list_coeff [] = (\<lambda>_ :: nat \<times> nat. (0 :: 'k))"
    by (rule ext) (rule normal_list_coeff_Nil)
  show ?case by (simp only: abstract_normal_list.simps nil_coeff abstract_normal_sum_zero)
next
  case (Cons t ts)
  have key: "fst t \<in> S" and tail: "fst ` set ts \<subseteq> S" using Cons.prems by auto
  have coords: "normal_list_coeff (t#ts) =
    (\<lambda>u. (if u=fst t then snd t else 0) + normal_list_coeff ts u)"
    by (rule ext) (simp only: normal_list_coeff_Cons eq_commute)
  show ?case
    by (simp only: coords abstract_normal_sum_add abstract_normal_sum_single[OF fin key]
      abstract_normal_list.simps Cons.IH[OF tail])
qed

lemma abstract_exists_finite_coordinates:
  assumes "z \<in> carrier Q"
  shows "\<exists>c. finite {u. c u \<noteq> 0} \<and> abstract_normal_ordered_sum c = z"
proof -
  have "z \<in> abstract_normal_span" using assms by (simp only: abstract_normal_span_eq_carrier)
  then obtain ts where ts: "abstract_normal_list ts = z" using abstract_span_has_list by blast
  let ?c = "normal_list_coeff ts"
  let ?S = "fst ` set ts"
  have sub: "{u. ?c u \<noteq> 0} \<subseteq> ?S" by (auto dest: normal_list_coeff_outside)
  have fin: "finite {u. ?c u \<noteq> 0}" by (rule finite_subset[OF sub]) simp
  have list_rep: "abstract_normal_list ts = abstract_finite_normal_sum ?S ?c"
    by (rule abstract_list_as_finite_sum) simp_all
  have restriction: "abstract_finite_normal_sum ?S ?c = abstract_normal_ordered_sum ?c"
    by (rule abstract_normal_sum_restrict[OF _ sub]) simp
  have rep: "abstract_normal_ordered_sum ?c = z" using list_rep restriction ts by metis
  show ?thesis by (rule exI[of _ ?c]) (rule conjI[OF fin rep])
qed

end

lemma linear_operator_ring_power:
  "pow (linear_operator_ring :: 'k::field poly_operator ring) T n = (T ^^ n)"
  by (induction n)
     (simp_all only: nat_pow_0 nat_pow_Suc linear_operator_ring_def ring_record_simps
       funpow_0 funpow_Suc_right op_comp_def comp_def id_def)

context abstract_normal_arithmetic
begin

lemma abstract_evaluation_hom_context:
  "ring_hom_ring Q linear_operator_ring abstract_to_concrete"
  by (rule ring_hom_ringI2[OF abstract_weyl_ring_is_ring linear_operator_ring_is_ring
    abstract_to_concrete_ring_hom])
lemma abstract_evaluation_zero:
  "abstract_to_concrete q0 = (0 :: 'k poly_operator)"
  using ring_hom_zero[OF abstract_to_concrete_ring_hom abstract_weyl_ring_is_ring linear_operator_ring_is_ring]
  by (simp only: linear_operator_ring_def ring_record_simps)
lemma abstract_evaluation_add:
  assumes "z \<in> carrier Q" "w \<in> carrier Q"
  shows "abstract_to_concrete (qa z w) = abstract_to_concrete z + abstract_to_concrete w"
  using ring_hom_add[OF abstract_to_concrete_ring_hom assms]
  by (simp only: linear_operator_ring_def ring_record_simps)
lemma abstract_evaluation_scalar_action:
  assumes "z \<in> carrier Q"
  shows "abstract_to_concrete (qm (abstract_scalar c) z) = (\<lambda>p. smult c (abstract_to_concrete z p))"
  using ring_hom_mult[OF abstract_to_concrete_ring_hom quotient_scalar_closed assms]
  by (simp only: linear_operator_ring_def ring_record_simps abstract_to_concrete_scalar op_scalar_def op_comp_def)

lemma abstract_evaluation_normal_monomial:
  "abstract_to_concrete (abstract_normal_monomial i j :: 'k weyl_free set) = normal_monomial i j"
proof -
  have xp: "abstract_to_concrete (qpow qX i) = (x_op ^^ i)"
    using ring_hom_ring.hom_nat_pow[OF abstract_evaluation_hom_context quotient_X_closed, of i]
    by (simp only: abstract_to_concrete_X linear_operator_ring_power)
  have yp: "abstract_to_concrete (qpow qY j) = (y_op ^^ j)"
    using ring_hom_ring.hom_nat_pow[OF abstract_evaluation_hom_context quotient_Y_closed, of j]
    by (simp only: abstract_to_concrete_Y linear_operator_ring_power)
  show ?thesis
    unfolding abstract_normal_monomial_def
    using ring_hom_mult[OF abstract_to_concrete_ring_hom x_power_closed[of i] y_power_closed[of j]]
    by (simp only: xp yp linear_operator_ring_def ring_record_simps normal_monomial_def)
qed

lemma abstract_evaluation_finite_normal_sum:
  assumes "finite S"
  shows "abstract_to_concrete (abstract_finite_normal_sum S c :: 'k weyl_free set) = finite_normal_sum S c"
  using assms
proof (induction S)
  case empty show ?case by (simp only: abstract_normal_sum_empty abstract_evaluation_zero finite_normal_sum_empty)
next
  case (insert u S)
  have term_carrier: "qm (abstract_scalar (c u)) (abstract_normal_monomial (fst u) (snd u)) \<in> carrier Q"
    by (rule W.scalar.S.m_closed[OF W.scalar_closed abstract_normal_monomial_closed])
  show ?case
    by (simp only: abstract_normal_sum_insert[OF insert.hyps]
      abstract_evaluation_add[OF term_carrier abstract_normal_sum_closed]
      abstract_evaluation_scalar_action[OF abstract_normal_monomial_closed]
      abstract_evaluation_normal_monomial insert.IH finite_normal_sum_insert[OF insert.hyps])
qed

lemma abstract_evaluation_normal_ordered_sum:
  assumes "finite {u. c u \<noteq> 0}"
  shows "abstract_to_concrete (abstract_normal_ordered_sum c :: 'k weyl_free set) =
    finite_normal_sum {u. c u \<noteq> 0} c"
  unfolding abstract_normal_ordered_sum_def by (rule abstract_evaluation_finite_normal_sum[OF assms])

end
end
