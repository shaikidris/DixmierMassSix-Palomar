theory Free_Word_Specializations
  imports Free_Word_Universal Quotient_Scalar_Ring
begin

lemma concrete_scalar_hom:
  "op_scalar \<in> ring_hom (nc_type_ring :: 'k::field ring) linear_operator_ring"
  by (rule ring_hom_memI)
     (simp_all add: nc_type_ring_def linear_operator_ring_def free_op_scalar_add free_op_scalar_mult)

lemma concrete_central_scalar_ring:
  "central_scalar_ring (linear_operator_ring :: 'k::field poly_operator ring) op_scalar"
proof -
  have hom: "ring_hom_ring (nc_type_ring :: 'k ring) linear_operator_ring op_scalar"
    by (rule ring_hom_ringI2[OF nc_type_ring_is_ring linear_operator_ring_is_ring concrete_scalar_hom])
  show ?thesis
  proof (rule central_scalar_ring.intro[OF hom]; rule central_scalar_ring_axioms.intro)
    fix c z
    assume z: "z \<in> carrier (linear_operator_ring :: 'k poly_operator ring)"
    have lin: "poly_linear z" using z by (simp only: linear_operator_ring_def ring_record_simps mem_Collect_eq)
    show "monoid.mult linear_operator_ring (op_scalar c) z = monoid.mult linear_operator_ring z (op_scalar c)"
      by (simp only: linear_operator_ring_def ring_record_simps; rule op_scalar_central[OF lin])
  qed
qed

lemma concrete_free_word_evaluation:
  "free_word_evaluation (linear_operator_ring :: 'k::field poly_operator ring)
    op_scalar (\<lambda>b. if b then y_op else x_op)"
  unfolding free_word_evaluation_def free_word_evaluation_axioms_def
  using concrete_central_scalar_ring[where 'k='k]
  by (simp add: linear_operator_ring_def)

lemma abstract_free_word_evaluation:
  "free_word_evaluation (abstract_weyl_ring :: 'k::field weyl_free set ring)
    abstract_scalar (\<lambda>b. if b then abstract_Y else abstract_X)"
  unfolding free_word_evaluation_def free_word_evaluation_axioms_def
  using abstract_central_scalar_ring[where 'k='k] abstract_X_closed[where 'k='k] abstract_Y_closed[where 'k='k]
  by simp

text \<open>These identifications use the generic uniqueness theorem, rather
than extensional calculation of the finite sums.\<close>

theorem universal_free_eval_concrete:
  "universal_free_eval linear_operator_ring op_scalar (\<lambda>b. if b then y_op else x_op) =
    (evaluate_weyl_free :: 'k::field weyl_free \<Rightarrow> 'k poly_operator)"
proof -
  interpret E: free_word_evaluation "(linear_operator_ring :: 'k poly_operator ring)"
    op_scalar "\<lambda>b. if b then y_op else x_op"
    by (rule concrete_free_word_evaluation)
  show ?thesis
    by (rule sym; rule E.free_eval_unique[OF evaluate_weyl_free_ring_hom]) simp_all
qed

theorem universal_free_eval_abstract:
  "universal_free_eval abstract_weyl_ring abstract_scalar (\<lambda>b. if b then abstract_Y else abstract_X) =
    (abstract_mk :: 'k::field weyl_free \<Rightarrow> 'k weyl_free set)"
proof -
  interpret E: free_word_evaluation "(abstract_weyl_ring :: 'k weyl_free set ring)"
    abstract_scalar "\<lambda>b. if b then abstract_Y else abstract_X"
    by (rule abstract_free_word_evaluation)
  show ?thesis
    by (rule sym; rule E.free_eval_unique[OF abstract_mk_ring_hom])
       (simp_all only: abstract_scalar_def abstract_X_def abstract_Y_def if_True if_False)
qed

corollary concrete_free_universal_property:
  "\<exists>!h :: 'k::field weyl_free \<Rightarrow> 'k poly_operator.
    h \<in> ring_hom free_ring linear_operator_ring \<and> (\<forall>c. h (free_scalar c) = op_scalar c) \<and>
    h free_X = x_op \<and> h free_Y = y_op"
  using free_word_evaluation.free_universal_property[OF concrete_free_word_evaluation[where 'k='k]]
  by (simp only: if_True if_False)

corollary abstract_free_universal_property:
  "\<exists>!h :: 'k::field weyl_free \<Rightarrow> 'k weyl_free set.
    h \<in> ring_hom free_ring abstract_weyl_ring \<and> (\<forall>c. h (free_scalar c) = abstract_scalar c) \<and>
    h free_X = abstract_X \<and> h free_Y = abstract_Y"
  using free_word_evaluation.free_universal_property[OF abstract_free_word_evaluation[where 'k='k]]
  by (simp only: if_True if_False)

end
