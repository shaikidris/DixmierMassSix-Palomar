theory Fourier_Free_Lift
  imports "Free_Word_Specializations"
begin

declare id_def [simp del]

definition fourier_generators :: "bool \<Rightarrow> 'k::field poly_operator" where
  "fourier_generators b = (if b then -x_op else y_op)"

lemma fourier_generators_in_weyl:
  "fourier_generators b \<in> (weyl_algebra :: 'k::field poly_operator set)"
proof -
  have neg: "-x_op \<in> (weyl_algebra :: 'k poly_operator set)"
    using op_adjoin.diff[OF op_adjoin_zero weyl_x[unfolded weyl_algebra_def]]
    by (simp add: weyl_algebra_def)
  show ?thesis by (simp add: fourier_generators_def neg)
qed

lemma fourier_free_evaluation:
  "free_word_evaluation (linear_operator_ring :: 'k::field poly_operator ring)
    op_scalar fourier_generators"
proof -
  have lin: "poly_linear (fourier_generators b :: 'k poly_operator)" for b
    by (rule weyl_linear[OF fourier_generators_in_weyl])
  show ?thesis unfolding free_word_evaluation_def free_word_evaluation_axioms_def
    using concrete_central_scalar_ring[where 'k='k] lin
    by (simp add: linear_operator_ring_def)
qed

definition evaluate_fourier_free :: "'k::field weyl_free \<Rightarrow> 'k poly_operator" where
  "evaluate_fourier_free = universal_free_eval linear_operator_ring op_scalar fourier_generators"

lemma evaluate_fourier_free_ring_hom:
  "evaluate_fourier_free \<in> ring_hom (free_ring :: 'k::field weyl_free ring) linear_operator_ring"
  unfolding evaluate_fourier_free_def
  by (rule free_word_evaluation.free_eval_ring_hom[OF fourier_free_evaluation])
lemma evaluate_fourier_free_ring_hom_ring:
  "ring_hom_ring (free_ring :: 'k::field weyl_free ring) linear_operator_ring evaluate_fourier_free"
  unfolding evaluate_fourier_free_def
  by (rule free_word_evaluation.free_eval_ring_hom_ring[OF fourier_free_evaluation])
lemma evaluate_fourier_free_zero [simp]: "evaluate_fourier_free 0 = 0"
  unfolding evaluate_fourier_free_def
  using free_word_evaluation.free_eval_zero[OF fourier_free_evaluation]
  by (simp only: linear_operator_ring_def ring_record_simps)
lemma evaluate_fourier_free_add:
  "evaluate_fourier_free (f+g) = evaluate_fourier_free f + evaluate_fourier_free g"
  unfolding evaluate_fourier_free_def
  using free_word_evaluation.free_eval_add[OF fourier_free_evaluation, of f g]
  by (simp only: linear_operator_ring_def ring_record_simps)
lemma evaluate_fourier_free_mult:
  "evaluate_fourier_free (f*g) = op_comp (evaluate_fourier_free f) (evaluate_fourier_free g)"
  unfolding evaluate_fourier_free_def
  using free_word_evaluation.free_eval_mult[OF fourier_free_evaluation, of f g]
  by (simp only: linear_operator_ring_def ring_record_simps)
lemma evaluate_fourier_free_scalar [simp]: "evaluate_fourier_free (free_scalar c) = op_scalar c"
  unfolding evaluate_fourier_free_def
  by (rule free_word_evaluation.free_eval_scalar[OF fourier_free_evaluation])
lemma evaluate_fourier_free_one [simp]: "evaluate_fourier_free 1 = id"
  using evaluate_fourier_free_scalar[of 1] by simp
lemma evaluate_fourier_free_X [simp]: "evaluate_fourier_free free_X = y_op"
  unfolding evaluate_fourier_free_def
  using free_word_evaluation.free_eval_X[OF fourier_free_evaluation]
  by (simp only: fourier_generators_def if_False)
lemma evaluate_fourier_free_Y [simp]: "evaluate_fourier_free free_Y = -x_op"
  unfolding evaluate_fourier_free_def
  using free_word_evaluation.free_eval_Y[OF fourier_free_evaluation]
  by (simp only: fourier_generators_def if_True)
lemma evaluate_fourier_free_unique:
  assumes hom: "h \<in> ring_hom (free_ring :: 'k::field weyl_free ring) linear_operator_ring"
    and scalars: "\<And>c. h (free_scalar c) = op_scalar c"
    and hx: "h free_X = y_op" and hy: "h free_Y = -x_op"
  shows "h = evaluate_fourier_free"
  unfolding evaluate_fourier_free_def
  by (rule free_word_evaluation.free_eval_unique[OF fourier_free_evaluation hom scalars])
     (simp_all only: fourier_generators_def hx hy if_True if_False)

lemma evaluate_fourier_free_minus:
  "evaluate_fourier_free (-f) = -evaluate_fourier_free f"
proof -
  have "evaluate_fourier_free f + evaluate_fourier_free (-f) = 0"
    using evaluate_fourier_free_add[of f "-f"] by simp
  then show ?thesis by (metis add_eq_0_iff)
qed
lemma evaluate_fourier_free_diff:
  "evaluate_fourier_free (f-g) = evaluate_fourier_free f - evaluate_fourier_free g"
  by (simp only: diff_conv_add_uminus evaluate_fourier_free_add evaluate_fourier_free_minus)

lemma fourier_word_list_in_weyl:
  "universal_word_list linear_operator_ring fourier_generators bs \<in>
    (weyl_algebra :: 'k::field poly_operator set)"
proof (induction bs)
  case Nil show ?case by (simp only: universal_word_list.simps linear_operator_ring_def ring_record_simps weyl_algebra_def op_adjoin_id)
next
  case (Cons b bs)
  have mult: "monoid.mult (linear_operator_ring :: 'k poly_operator ring) = op_comp"
    by (simp only: linear_operator_ring_def ring_record_simps)
  show ?case unfolding universal_word_list.simps mult weyl_algebra_def
    by (rule op_adjoin.comp[OF fourier_generators_in_weyl[unfolded weyl_algebra_def]
          Cons.IH[unfolded weyl_algebra_def]])
qed
lemma fourier_word_in_weyl:
  "universal_word linear_operator_ring fourier_generators w \<in>
    (weyl_algebra :: 'k::field poly_operator set)"
  by (cases w) (simp only: universal_word_def weyl_word.case fourier_word_list_in_weyl)
lemma evaluate_fourier_free_in_weyl:
  "evaluate_fourier_free f \<in> (weyl_algebra :: 'k::field poly_operator set)"
proof (induction f rule: free_induct)
  case zero show ?case by (simp only: evaluate_fourier_free_zero weyl_algebra_def op_adjoin_zero)
next
  case (add f g)
  show ?case unfolding evaluate_fourier_free_add weyl_algebra_def
    by (rule op_adjoin.add[OF add.IH[unfolded weyl_algebra_def]])
next
  case (single w c)
  have eq: "evaluate_fourier_free (Poly_Mapping.single w c) =
    op_comp (op_scalar c) (universal_word linear_operator_ring fourier_generators w)"
    unfolding evaluate_fourier_free_def
    using free_word_evaluation.free_eval_single[OF fourier_free_evaluation, of w c]
    by (simp only: linear_operator_ring_def ring_record_simps)
  show ?case unfolding eq weyl_algebra_def
    by (rule op_adjoin.comp[OF op_adjoin.scalar fourier_word_in_weyl[unfolded weyl_algebra_def]])
qed

lemma evaluateFourierFree_relation:
  "evaluate_fourier_free (weyl_relation :: 'k::field weyl_free) = 0"
  unfolding weyl_relation_def
  by (simp only: evaluate_fourier_free_diff evaluate_fourier_free_mult
      evaluate_fourier_free_X evaluate_fourier_free_Y evaluate_fourier_free_one;
      rule ext; simp add: op_comp_def x_op_def y_op_def pderiv_mult pderiv_pCons pderiv_minus algebra_simps)

lemma fourier_relation_ideal_subset_kernel:
  "(weyl_relation_ideal :: 'k::field weyl_free set) \<subseteq>
    a_kernel free_ring linear_operator_ring evaluate_fourier_free"
proof -
  have ki: "ideal (a_kernel (free_ring :: 'k weyl_free ring) linear_operator_ring evaluate_fourier_free) free_ring"
    by (rule ring_hom_ring.kernel_is_ideal[OF evaluate_fourier_free_ring_hom_ring])
  show ?thesis unfolding weyl_relation_ideal_def
    by (rule ring.genideal_minimal[OF free_ring_is_ring ki])
       (simp add: a_kernel_def' linear_operator_ring_def evaluateFourierFree_relation)
qed
lemma evaluateFourierFree_zero_on_relationIdeal:
  "f \<in> (weyl_relation_ideal :: 'k::field weyl_free set) \<Longrightarrow> evaluate_fourier_free f = 0"
  using fourier_relation_ideal_subset_kernel[where 'k='k]
  by (auto simp: a_kernel_def' linear_operator_ring_def)

definition fourier_abstract_to_concrete :: "'k::field weyl_free set \<Rightarrow> 'k poly_operator" where
  "fourier_abstract_to_concrete = ideal_quotient_lift evaluate_fourier_free"

lemma fourier_contained_ideal_quotient:
  "contained_ideal_quotient (free_ring :: 'k::field weyl_free ring)
    linear_operator_ring evaluate_fourier_free weyl_relation_ideal"
  unfolding contained_ideal_quotient_def contained_ideal_quotient_axioms_def
  using evaluate_fourier_free_ring_hom_ring weyl_relation_ideal_is_ideal
    fourier_relation_ideal_subset_kernel by blast
lemma fourierAbstractToConcrete_mk:
  "fourier_abstract_to_concrete (abstract_mk f) = evaluate_fourier_free f"
  unfolding fourier_abstract_to_concrete_def abstract_mk_def
  by (rule contained_ideal_quotient.quotient_lift_mk[OF fourier_contained_ideal_quotient]) simp
lemma fourier_abstract_to_concrete_ring_hom:
  "fourier_abstract_to_concrete \<in> ring_hom (abstract_weyl_ring :: 'k::field weyl_free set ring) linear_operator_ring"
  unfolding fourier_abstract_to_concrete_def abstract_weyl_ring_def
  by (rule contained_ideal_quotient.quotient_lift_ring_hom[OF fourier_contained_ideal_quotient])
lemma fourierAbstractToConcrete_abstractX:
  "fourier_abstract_to_concrete (abstract_X :: 'k::field weyl_free set) = y_op"
  by (simp add: abstract_X_def fourierAbstractToConcrete_mk)
lemma fourierAbstractToConcrete_abstractY:
  "fourier_abstract_to_concrete (abstract_Y :: 'k::field weyl_free set) = -x_op"
  by (simp add: abstract_Y_def fourierAbstractToConcrete_mk)
lemma fourier_abstract_to_concrete_scalar:
  "fourier_abstract_to_concrete (abstract_scalar c) = op_scalar c"
  by (simp add: abstract_scalar_def fourierAbstractToConcrete_mk)
lemma fourier_abstract_to_concrete_in_weyl:
  "C \<in> carrier (abstract_weyl_ring :: 'k::field weyl_free set ring) \<Longrightarrow>
    fourier_abstract_to_concrete C \<in> weyl_algebra"
  using abstract_representative[of C] evaluate_fourier_free_in_weyl
  by (metis fourierAbstractToConcrete_mk)

lemma fourier_abstract_to_concrete_unique:
  assumes agrees: "\<And>f. g (abstract_mk f) = evaluate_fourier_free f"
    and carrier: "C \<in> carrier (abstract_weyl_ring :: 'k::field weyl_free set ring)"
  shows "g C = fourier_abstract_to_concrete C"
  unfolding fourier_abstract_to_concrete_def
  by (rule contained_ideal_quotient.quotient_lift_unique[OF fourier_contained_ideal_quotient])
     (use agrees carrier in \<open>auto simp: abstract_mk_def abstract_weyl_ring_def\<close>)

end
