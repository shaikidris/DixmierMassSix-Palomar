theory One_Sided_Generator_Extraction
  imports One_Sided_Symbol_Face_Adapters
    "Partial_Derivatives"
begin

lemma poisson_coeff_zero:
  fixes p q :: "complex bivariate"
  shows "biv_coeff (biv_poisson p q) 0 0=
    biv_coeff p 0 1*biv_coeff q 1 0-biv_coeff p 1 0*biv_coeff q 0 1"
proof -
  have constant_product: "biv_coeff (a*b) 0 0=biv_coeff a 0 0*biv_coeff b 0 0"
    for a b :: "complex bivariate"
    by (simp add: biv_coeff_def coeff_mult_0)
  show ?thesis by (simp add: biv_poisson_def constant_product biv_dy_coeff biv_dx_coeff)
qed

lemma poisson_first_neg_second:
  "biv_poisson R (-F)=biv_poisson F R"
  for R F :: "complex bivariate"
proof -
  have negative_coefficient: "biv_coeff (-p) i j=-biv_coeff p i j" for p :: "complex bivariate" and i j
    by (simp add: biv_coeff_def)
  have dx_neg: "biv_dx (-p)=-biv_dx p" for p :: "complex bivariate"
    by (rule biv_eqI) (simp only: biv_dx_coeff negative_coefficient; simp)
  have dy_neg: "biv_dy (-p)=-biv_dy p" for p :: "complex bivariate"
    by (rule biv_eqI) (simp only: biv_dy_coeff negative_coefficient; simp)
  show ?thesis by (simp add: biv_poisson_def dx_neg dy_neg algebra_simps)
qed

lemma poisson_eq_one_forces_mate_position_term:
  fixes p q :: "complex bivariate"
  assumes ell: "0<ell"
    and homogeneous: "\<forall>u\<in>biv_support p. pair_weight (int ell) (-int d) u=-int d"
    and bracket: "biv_poisson p q=1"
  shows "(1,0)\<in>biv_support q"
proof -
  have not_x: "(1,0)\<notin>biv_support p"
    using homogeneous ell by (auto simp: pair_weight_def)
  have zero_x: "biv_coeff p 1 0=0" using not_x by (simp add: biv_support_def)
  have constant_coefficient: "biv_coeff (biv_poisson p q) 0 0=1"
    using bracket by (simp add: biv_coeff_def)
  have nonzero_x: "biv_coeff q 1 0\<noteq>0"
    using constant_coefficient by (simp only: poisson_coeff_zero zero_x; auto)
  show ?thesis using nonzero_x by (simp add: biv_support_def)
qed

lemma one_sided_leading_bracket_one_forces_generator:
  fixes P Q :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and side: "\<forall>u\<in>biv_support (pbw_symbol P). pair_grade u\<le>0"
    and bracket: "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=1"
  shows "(0,1)\<in>biv_support (leading_form rho sigma P) \<and>
    (0,1)\<in>biv_support (pbw_symbol P)"
proof -
  have not_x: "(1,0)\<notin>biv_support (leading_form rho sigma P)"
  proof
    assume member: "(1,0)\<in>biv_support (leading_form rho sigma P)"
    have full: "(1,0)\<in>biv_support (pbw_symbol P)"
      using member leading_support_subset[of rho sigma P] by blast
    have "pair_grade (1,0)\<le>0" using side full by blast
    then show False by (simp add: pair_grade_def)
  qed
  have zero_x: "biv_coeff (leading_form rho sigma P) 1 0=0"
    using not_x by (simp add: biv_support_def)
  have constant_coefficient: "biv_coeff (biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)) 0 0=1"
    using bracket by (simp add: biv_coeff_def)
  have nonzero_y: "biv_coeff (leading_form rho sigma P) 0 1\<noteq>0"
    using constant_coefficient by (simp only: poisson_coeff_zero zero_x; auto)
  have y: "(0,1)\<in>biv_support (leading_form rho sigma P)"
    using nonzero_y by (simp add: biv_support_def)
  show ?thesis using y leading_support_subset by blast
qed

end
