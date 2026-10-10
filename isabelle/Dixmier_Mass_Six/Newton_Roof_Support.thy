theory Newton_Roof_Support
  imports "Poisson_Endpoint_Hulls"
    "One_Sided_Symbol_Face_Adapters"
begin

definition integer_positive_newton_roof :: "complex poly_operator \<Rightarrow> (real\<times>real) set" where
  "integer_positive_newton_roof T = {z. \<exists>rho sigma::int. 0<rho+sigma \<and>
    z\<in>convex hull (exponent_point ` biv_support (leading_form rho sigma T))}"

definition positive_scalar_cone :: "(real\<times>real) set \<Rightarrow> (real\<times>real) set" where
  "positive_scalar_cone S = {z. \<exists>r::real. 0\<le>r \<and> (\<exists>q\<in>S. z=scaleR r q)}"

lemma convex_nonpositive_grade_halfspace:
  "convex {z::real\<times>real. fst z\<le>snd z}"
proof (rule convexI)
  fix x y::"real\<times>real" and u v::real
  assume x: "x\<in>{z::real\<times>real. fst z\<le>snd z}"
    and y: "y\<in>{z::real\<times>real. fst z\<le>snd z}"
    and u: "0\<le>u" and v: "0\<le>v" and sum: "u+v=1"
  have ux: "u*fst x\<le>u*snd x" using x mult_left_mono[OF _ u] by auto
  have vy: "v*fst y\<le>v*snd y" using y mult_left_mono[OF _ v] by auto
  show "scaleR u x+scaleR v y\<in>{z::real\<times>real. fst z\<le>snd z}"
    using add_mono[OF ux vy] by simp
qed

lemma exponent_point_grade_nonpositive:
  assumes "pair_grade d\<le>0"
  shows "fst (exponent_point d)\<le>snd (exponent_point d)"
proof -
  have "fst d\<le>snd d" using assms by (simp add: pair_grade_def)
  then show ?thesis by (simp add: exponent_point_def)
qed

lemma integerPositiveNewtonRoof_grade_nonpositive:
  fixes T::"complex poly_operator"
  assumes carrier: "T\<in>weyl_algebra"
    and side: "\<forall>d\<in>biv_support (pbw_symbol T). pair_grade d\<le>0"
  shows "integer_positive_newton_roof T\<subseteq>{z::real\<times>real. fst z\<le>snd z}"
proof
  fix z assume "z\<in>integer_positive_newton_roof T"
  then obtain rho sigma::int where
    z: "z\<in>convex hull (exponent_point ` biv_support (leading_form rho sigma T))"
    by (auto simp: integer_positive_newton_roof_def)
  have subset: "exponent_point ` biv_support (leading_form rho sigma T)\<subseteq>
    {z::real\<times>real. fst z\<le>snd z}"
  proof
    fix y assume "y\<in>exponent_point ` biv_support (leading_form rho sigma T)"
    then obtain d where d: "d\<in>biv_support (leading_form rho sigma T)" and y: "y=exponent_point d" by blast
    have "d\<in>biv_support (pbw_symbol T)"
      using d by (auto simp: leading_form_def weighted_component_support)
    then have "pair_grade d\<le>0" using side by blast
    then show "y\<in>{z::real\<times>real. fst z\<le>snd z}"
      using exponent_point_grade_nonpositive y by auto
  qed
  show "z\<in>{z::real\<times>real. fst z\<le>snd z}"
    using hull_minimal[where S=convex, OF subset convex_nonpositive_grade_halfspace] z by blast
qed

lemma positiveScalarCone_subset_nonpositive_halfspace:
  assumes "S\<subseteq>{z::real\<times>real. fst z\<le>snd z}"
  shows "positive_scalar_cone S\<subseteq>{z::real\<times>real. fst z\<le>snd z}"
proof
  fix z assume "z\<in>positive_scalar_cone S"
  then obtain r q where r: "0\<le>(r::real)" and q: "q\<in>S" and z: "z=scaleR r q"
    by (auto simp: positive_scalar_cone_def)
  have "fst q\<le>snd q" using assms q by blast
  then have "r*fst q\<le>r*snd q" by (rule mult_left_mono[OF _ r])
  then show "z\<in>{z::real\<times>real. fst z\<le>snd z}" by (simp add: z)
qed

lemma integerPositiveNewtonRoof_cone_grade_nonpositive:
  fixes T::"complex poly_operator"
  assumes "T\<in>weyl_algebra"
    and "\<forall>d\<in>biv_support (pbw_symbol T). pair_grade d\<le>0"
  shows "positive_scalar_cone (integer_positive_newton_roof T)\<subseteq>
    {z::real\<times>real. fst z\<le>snd z}"
  by (rule positiveScalarCone_subset_nonpositive_halfspace)
    (rule integerPositiveNewtonRoof_grade_nonpositive[OF assms])

end
