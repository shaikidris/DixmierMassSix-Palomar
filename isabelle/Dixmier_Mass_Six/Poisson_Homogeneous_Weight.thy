theory Poisson_Homogeneous_Weight
  imports "Face_Mass_Geometry"
    "Weighted_Product_Components"
    "Poisson_Fixed_Point_Division"
begin

lemma homogeneous_component_eq:
  fixes f :: "complex bivariate"
  assumes "weighted_homogeneous rho sigma m f"
  shows "weighted_component rho sigma m f=f"
proof (rule biv_eqI)
  fix i j
  have nz: "biv_coeff f i j\<noteq>0 \<Longrightarrow> pair_weight rho sigma (i,j)=m"
    using assms by (auto simp: weighted_homogeneous_def biv_support_def)
  show "biv_coeff (weighted_component rho sigma m f) i j=biv_coeff f i j"
    using nz by (auto simp: weighted_component_coeff)
qed

lemma pderiv_weighted_homogeneous_signed:
  fixes f :: "complex bivariate"
  assumes "weighted_homogeneous rho sigma m f"
  shows "weighted_homogeneous rho sigma
    (m-(if is_y then sigma else rho)) (biv_deriv is_y f)"
proof -
  have eq: "weighted_component rho sigma
      (m-(if is_y then sigma else rho)) (biv_deriv is_y f)=biv_deriv is_y f"
    using biv_deriv_component[where is_y=is_y and rho=rho and sigma=sigma and m=m and p=f]
      homogeneous_component_eq[OF assms] by simp
  show ?thesis using weighted_component_homogeneous[of rho sigma
      "m-(if is_y then sigma else rho)" "biv_deriv is_y f"] eq by simp
qed

lemma poisson_weighted_homogeneous_signed:
  fixes f g :: "complex bivariate"
  assumes hf: "weighted_homogeneous rho sigma m f"
    and hg: "weighted_homogeneous rho sigma n g"
  shows "weighted_homogeneous rho sigma (m+n-(rho+sigma)) (biv_poisson f g)"
proof -
  have fb: "\<And>u. u\<in>biv_support f \<Longrightarrow> pair_weight rho sigma u\<le>m"
    using hf by (auto simp: weighted_homogeneous_def)
  have gb: "\<And>u. u\<in>biv_support g \<Longrightarrow> pair_weight rho sigma u\<le>n"
    using hg by (auto simp: weighted_homogeneous_def)
  have eq: "weighted_component rho sigma (m+n-(rho+sigma)) (biv_poisson f g)=biv_poisson f g"
    using poisson_weighted_component_of_bounds[where p=f and q=g, OF fb gb]
      homogeneous_component_eq[OF hf] homogeneous_component_eq[OF hg] by simp
  show ?thesis using weighted_component_homogeneous[of rho sigma
      "m+n-(rho+sigma)" "biv_poisson f g"] eq by simp
qed

end
