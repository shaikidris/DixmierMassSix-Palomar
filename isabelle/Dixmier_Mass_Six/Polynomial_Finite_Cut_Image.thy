theory Polynomial_Finite_Cut_Image
  imports Polynomial_Ramified_Lift_Homomorphism
begin

definition finite_cut_image :: "nat \<Rightarrow> ramified_cut_data list \<Rightarrow> complex poly_operator \<Rightarrow> laurent_operator" where
  "finite_cut_image l cuts P=ramified_finite_cut_aut l cuts (polynomial_ramified_lift l P)"

lemma finite_cut_image_carrier:
  assumes l: "0<l"
  shows "finite_cut_image l cuts P\<in>ramified_operator_algebra l"
  unfolding finite_cut_image_def
  by (rule ramified_finite_cut_aut_carrier[OF l polynomial_ramified_lift_carrier])

lemma finiteCutImage_bracket_one:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and bracket: "op_comp Q P-op_comp P Q=id"
  shows "laurent_comp (finite_cut_image l cuts Q) (finite_cut_image l cuts P)-
    laurent_comp (finite_cut_image l cuts P) (finite_cut_image l cuts Q)=id"
  unfolding finite_cut_image_def
  by (rule ramified_finite_cut_aut_exact_pair[OF l polynomial_ramified_lift_carrier
    polynomial_ramified_lift_carrier polynomial_ramified_lift_bracket_one[OF l P Q bracket]])

lemma finite_cut_image_cons:
  "finite_cut_image l (a#cuts) P=
    ramified_cut_aut l (cut_rho a) (cut_sigma a) (cut_root a) (finite_cut_image l cuts P)"
  by (simp only: finite_cut_image_def ramified_finite_cut_aut.simps)

lemma finite_cut_image_exact_pair_nonzero:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and bracket: "op_comp Q P-op_comp P Q=id"
  shows "finite_cut_image l cuts P\<noteq>0 \<and> finite_cut_image l cuts Q\<noteq>0"
proof -
  have exact: "laurent_comp (finite_cut_image l cuts Q) (finite_cut_image l cuts P)-
    laurent_comp (finite_cut_image l cuts P) (finite_cut_image l cuts Q)=id"
    by (rule finiteCutImage_bracket_one[OF l P Q bracket])
  have Plinear: "laurent_linear (finite_cut_image l cuts P)" and Qlinear: "laurent_linear (finite_cut_image l cuts Q)"
    by (rule ramified_operator_algebra_linear[where l=l], rule finite_cut_image_carrier[OF l])+
  have one_nonzero: "(id::laurent_operator)\<noteq>0"
    by (intro notI) (drule fun_cong[where x="1::ramified_laurent"]; simp)
  show ?thesis using exact Plinear Qlinear one_nonzero
    by (auto simp: laurent_comp_zero_left laurent_comp_zero_right)
qed

end
