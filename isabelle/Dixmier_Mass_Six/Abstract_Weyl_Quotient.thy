theory Abstract_Weyl_Quotient
  imports Relation_Ideal_Bridge Ideal_Quotient_Lift
begin

definition abstract_weyl_ring :: "'k::field weyl_free set ring" where
  "abstract_weyl_ring = FactRing free_ring weyl_relation_ideal"
definition abstract_mk :: "'k::field weyl_free \<Rightarrow> 'k weyl_free set" where
  "abstract_mk f = a_r_coset free_ring weyl_relation_ideal f"
definition abstract_X :: "'k::field weyl_free set" where
  "abstract_X = abstract_mk free_X"
definition abstract_Y :: "'k::field weyl_free set" where
  "abstract_Y = abstract_mk free_Y"
definition abstract_scalar :: "'k::field \<Rightarrow> 'k weyl_free set" where
  "abstract_scalar c = abstract_mk (free_scalar c)"
definition abstract_to_concrete :: "'k::field weyl_free set \<Rightarrow> 'k poly_operator" where
  "abstract_to_concrete = ideal_quotient_lift evaluate_weyl_free"

lemma weyl_contained_ideal_quotient:
  "contained_ideal_quotient (free_ring :: 'k::field weyl_free ring)
    linear_operator_ring evaluate_weyl_free weyl_relation_ideal"
  unfolding contained_ideal_quotient_def contained_ideal_quotient_axioms_def
  using evaluate_weyl_free_ring_hom_ring weyl_relation_ideal_is_ideal
    weyl_relation_ideal_subset_kernel by blast

lemma abstract_weyl_ring_is_ring:
  "ring (abstract_weyl_ring :: 'k::field weyl_free set ring)"
  unfolding abstract_weyl_ring_def
  by (rule ideal.quotient_is_ring[OF weyl_relation_ideal_is_ideal])
lemma abstract_mk_ring_hom:
  "abstract_mk \<in> ring_hom (free_ring :: 'k::field weyl_free ring) abstract_weyl_ring"
  unfolding abstract_weyl_ring_def abstract_mk_def[abs_def]
  by (rule ideal.rcos_ring_hom[OF weyl_relation_ideal_is_ideal])
lemma abstract_mk_closed:
  "abstract_mk f \<in> carrier (abstract_weyl_ring :: 'k::field weyl_free set ring)"
  unfolding abstract_mk_def abstract_weyl_ring_def
  by (rule contained_ideal_quotient.quotient_mk_closed[OF weyl_contained_ideal_quotient]) simp
lemma abstract_representative:
  "C \<in> carrier (abstract_weyl_ring :: 'k::field weyl_free set ring) \<Longrightarrow>
    \<exists>f. C = abstract_mk f"
  unfolding abstract_mk_def abstract_weyl_ring_def
  using contained_ideal_quotient.quotient_carrier_rep[OF weyl_contained_ideal_quotient] by blast

lemma abstract_mk_add:
  "abstract_mk (f+g) = ring.add abstract_weyl_ring (abstract_mk f) (abstract_mk g)"
  using ring_hom_add[OF abstract_mk_ring_hom, of f g] by simp
lemma abstract_mk_mult:
  "abstract_mk (f*g) = monoid.mult abstract_weyl_ring (abstract_mk f) (abstract_mk g)"
  using ring_hom_mult[OF abstract_mk_ring_hom, of f g] by simp
lemma abstract_mk_one:
  "abstract_mk 1 = monoid.one (abstract_weyl_ring :: 'k::field weyl_free set ring)"
  using ring_hom_one[OF abstract_mk_ring_hom] by simp
lemma abstract_mk_zero:
  "abstract_mk 0 = ring.zero (abstract_weyl_ring :: 'k::field weyl_free set ring)"
  using ring_hom_zero[OF abstract_mk_ring_hom free_ring_is_ring abstract_weyl_ring_is_ring] by simp
lemma abstract_mk_equality:
  "f-g \<in> (weyl_relation_ideal :: 'k::field weyl_free set) \<longleftrightarrow>
    abstract_mk f = abstract_mk g"
  using ring.quotient_eq_iff_same_a_r_cos[OF free_ring_is_ring weyl_relation_ideal_is_ideal, of f g]
  by (simp add: abstract_mk_def a_minus_def free_additive_inverse)

lemma abstract_X_closed:
  "abstract_X \<in> carrier (abstract_weyl_ring :: 'k::field weyl_free set ring)"
  by (simp add: abstract_X_def abstract_mk_closed)
lemma abstract_Y_closed:
  "abstract_Y \<in> carrier (abstract_weyl_ring :: 'k::field weyl_free set ring)"
  by (simp add: abstract_Y_def abstract_mk_closed)
lemma abstract_scalar_closed:
  "abstract_scalar c \<in> carrier abstract_weyl_ring"
  by (simp add: abstract_scalar_def abstract_mk_closed)

lemma abstract_relation:
  "monoid.mult (abstract_weyl_ring :: 'k::field weyl_free set ring) abstract_Y abstract_X =
   ring.add abstract_weyl_ring (monoid.mult abstract_weyl_ring abstract_X abstract_Y)
     (monoid.one abstract_weyl_ring)"
proof -
  have diff: "(free_Y * free_X :: 'k weyl_free) - (free_X * free_Y + 1) = weyl_relation"
    by (simp add: weyl_relation_def diff_diff_add)
  have "abstract_mk (free_Y * free_X :: 'k weyl_free) = abstract_mk (free_X * free_Y + 1)"
    by (rule abstract_mk_equality[THEN iffD1]) (simp only: diff weyl_relation_mem_ideal)
  then show ?thesis
    by (simp only: abstract_mk_mult abstract_mk_add abstract_mk_one abstract_X_def[symmetric] abstract_Y_def[symmetric])
qed

lemma abstract_scalar_central:
  assumes "C \<in> carrier (abstract_weyl_ring :: 'k::field weyl_free set ring)"
  shows "monoid.mult abstract_weyl_ring (abstract_scalar c) C =
    monoid.mult abstract_weyl_ring C (abstract_scalar c)"
proof -
  obtain f where C: "C = abstract_mk f" using abstract_representative[OF assms] by blast
  show ?thesis
    by (simp only: C abstract_scalar_def abstract_mk_mult[symmetric] free_scalar_central)
qed

lemma abstract_to_concrete_mk:
  "abstract_to_concrete (abstract_mk f) = evaluate_weyl_free f"
  unfolding abstract_to_concrete_def abstract_mk_def
  by (rule contained_ideal_quotient.quotient_lift_mk[OF weyl_contained_ideal_quotient]) simp
lemma abstract_to_concrete_ring_hom:
  "abstract_to_concrete \<in> ring_hom (abstract_weyl_ring :: 'k::field weyl_free set ring)
    linear_operator_ring"
  unfolding abstract_to_concrete_def abstract_weyl_ring_def
  by (rule contained_ideal_quotient.quotient_lift_ring_hom[OF weyl_contained_ideal_quotient])
lemma abstract_to_concrete_X:
  "abstract_to_concrete abstract_X = x_op"
  by (simp add: abstract_X_def abstract_to_concrete_mk)
lemma abstract_to_concrete_Y:
  "abstract_to_concrete abstract_Y = y_op"
  by (simp add: abstract_Y_def abstract_to_concrete_mk)
lemma abstract_to_concrete_scalar:
  "abstract_to_concrete (abstract_scalar c) = op_scalar c"
  by (simp add: abstract_scalar_def abstract_to_concrete_mk)
lemma abstract_to_concrete_in_weyl:
  assumes "C \<in> carrier (abstract_weyl_ring :: 'k::field weyl_free set ring)"
  shows "abstract_to_concrete C \<in> weyl_algebra"
proof -
  obtain f where C: "C = abstract_mk f" using abstract_representative[OF assms] by blast
  show ?thesis by (simp only: C abstract_to_concrete_mk evaluate_weyl_free_in_weyl)
qed

lemma evaluate_weyl_free_surjective_on_weyl:
  assumes "T \<in> (weyl_algebra :: 'k::field poly_operator set)"
  shows "\<exists>f. evaluate_weyl_free f = T"
  using assms unfolding weyl_algebra_def
proof (induction rule: op_adjoin.induct)
  case (generator T)
  have "T = x_op \<or> T = y_op" using generator.hyps by simp
  then show ?case
  proof
    assume T: "T = x_op"
    show ?thesis by (rule exI[of _ free_X]) (simp only: evaluate_weyl_free_X T)
  next
    assume T: "T = y_op"
    show ?thesis by (rule exI[of _ free_Y]) (simp only: evaluate_weyl_free_Y T)
  qed
next
  case (scalar c)
  show ?case by (rule exI[of _ "free_scalar c"]) (rule evaluate_weyl_free_scalar)
next
  case (add T U)
  obtain f g where f: "evaluate_weyl_free f = T" and g: "evaluate_weyl_free g = U"
    using add.IH by blast
  show ?case by (rule exI[of _ "f+g"]) (simp only: evaluate_weyl_free_add f g)
next
  case (diff T U)
  obtain f g where f: "evaluate_weyl_free f = T" and g: "evaluate_weyl_free g = U"
    using diff.IH by blast
  show ?case by (rule exI[of _ "f-g"]) (simp only: evaluate_weyl_free_diff f g)
next
  case (comp T U)
  obtain f g where f: "evaluate_weyl_free f = T" and g: "evaluate_weyl_free g = U"
    using comp.IH by blast
  show ?case by (rule exI[of _ "f*g"]) (simp only: evaluate_weyl_free_mult f g)
qed

lemma abstract_to_concrete_surjective:
  assumes "T \<in> (weyl_algebra :: 'k::field poly_operator set)"
  shows "\<exists>C\<in>carrier abstract_weyl_ring. abstract_to_concrete C = T"
proof -
  obtain f where "evaluate_weyl_free f = T" using evaluate_weyl_free_surjective_on_weyl[OF assms] by blast
  then show ?thesis by (intro bexI[of _ "abstract_mk f"])
    (simp_all only: abstract_to_concrete_mk abstract_mk_closed)
qed

lemma abstract_to_concrete_image:
  "abstract_to_concrete ` carrier (abstract_weyl_ring :: 'k::field weyl_free set ring) = weyl_algebra"
  using abstract_to_concrete_surjective abstract_to_concrete_in_weyl by blast

end
