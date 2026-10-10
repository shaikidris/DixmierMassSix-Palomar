theory Finite_Cut_Linear_Transport
  imports Finite_Cut_Image_Injection
begin

interpretation ramified_operator_vector: vector_space normal_smult
  by standard (simp_all add: normal_smult_add_scalar normal_smult_add normal_smult_assoc)

lemma finite_cut_aut_add:
  assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l" and U: "U\<in>ramified_operator_algebra l"
  shows "ramified_finite_cut_aut l cuts (T+U)=ramified_finite_cut_aut l cuts T+ramified_finite_cut_aut l cuts U"
proof (induction cuts)
  case Nil show ?case by simp
next
  case (Cons a cuts)
  have Tc: "ramified_finite_cut_aut l cuts T\<in>ramified_operator_algebra l"
    by (rule ramified_finite_cut_aut_carrier[OF l T])
  have Uc: "ramified_finite_cut_aut l cuts U\<in>ramified_operator_algebra l"
    by (rule ramified_finite_cut_aut_carrier[OF l U])
  show ?case by (simp only: ramified_finite_cut_aut.simps Cons.IH ramified_cut_aut_def
    ramified_shear_hom_def ramified_shear_candidate_add[OF l Tc Uc])
qed

lemma finite_cut_aut_smult:
  assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
  shows "ramified_finite_cut_aut l cuts (normal_smult c T)=normal_smult c (ramified_finite_cut_aut l cuts T)"
proof (induction cuts)
  case Nil show ?case by simp
next
  case (Cons a cuts)
  have Tc: "ramified_finite_cut_aut l cuts T\<in>ramified_operator_algebra l"
    by (rule ramified_finite_cut_aut_carrier[OF l T])
  show ?case by (simp only: ramified_finite_cut_aut.simps Cons.IH ramified_cut_aut_def
    ramified_shear_hom_def ramified_shear_candidate_smult[OF l Tc])
qed

lemma finite_cut_aut_sum:
  assumes l: "0<l" and finite: "finite S"
    and carrier: "\<And>d. d\<in>S \<Longrightarrow> T d\<in>ramified_operator_algebra l"
  shows "ramified_finite_cut_aut l cuts (\<Sum>d\<in>S. T d)=(\<Sum>d\<in>S. ramified_finite_cut_aut l cuts (T d))"
  using finite carrier
proof (induction S rule: finite_induct)
  case empty
  show ?case by (simp only: sum.empty finite_cut_aut_zero[OF l])
next
  case (insert d S)
  have d: "T d\<in>ramified_operator_algebra l" using insert.prems by simp
  have all: "\<And>e. e\<in>S \<Longrightarrow> T e\<in>ramified_operator_algebra l" using insert.prems by simp
  have total: "(\<Sum>e\<in>S. T e)\<in>ramified_operator_algebra l"
    by (rule ramified_algebra_sum[OF insert.hyps(1) all])
  have ih: "ramified_finite_cut_aut l cuts (\<Sum>e\<in>S. T e)=(\<Sum>e\<in>S. ramified_finite_cut_aut l cuts (T e))"
    by (rule insert.IH[OF all])
  show ?case by (simp only: sum.insert[OF insert.hyps] finite_cut_aut_add[OF l d total] ih)
qed

lemma finite_cut_image_smult:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
  shows "finite_cut_image l cuts (\<lambda>p. smult c (P p))=normal_smult c (finite_cut_image l cuts P)"
  by (simp only: finite_cut_image_def polynomial_ramified_lift_smult[OF l P]
    finite_cut_aut_smult[OF l polynomial_ramified_lift_carrier])

lemma finite_cut_image_sum:
  assumes l: "0<l" and finite: "finite S"
    and carrier: "\<And>d. d\<in>S \<Longrightarrow> T d\<in>(weyl_algebra::complex poly_operator set)"
  shows "finite_cut_image l cuts (\<Sum>d\<in>S. T d)=(\<Sum>d\<in>S. finite_cut_image l cuts (T d))"
  by (simp only: finite_cut_image_def polynomial_ramified_lift_sum[OF l finite carrier]
    finite_cut_aut_sum[OF l finite polynomial_ramified_lift_carrier])

end
