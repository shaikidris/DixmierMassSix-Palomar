theory Ramified_Filtered_Centralizer_Rank
  imports Ramified_Restricted_Weight_Filtration
begin

definition ramified_face_centralization where
  "ramified_face_centralization l rho sigma P T=
    [:of_int (ramified_weight_deg l rho sigma P)/(of_nat l*of_int rho):]*
      ramified_top_face_polynomial l rho sigma P*pderiv (ramified_top_face_polynomial l rho sigma T)-
    [:of_int (ramified_weight_deg l rho sigma T)/(of_nat l*of_int rho):]*
      pderiv (ramified_top_face_polynomial l rho sigma P)*ramified_top_face_polynomial l rho sigma T"

lemma ramified_below_nonzero_component_degree:
  assumes l: "0<l" and rho: "0<rho" and T: "T\<in>ramified_operator_algebra l"
    and below: "T\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1)"
    and component: "ramified_weight_component_polynomial l rho sigma b T\<noteq>0"
  shows "ramified_weight_deg l rho sigma T=b"
proof -
  have rhone: "rho\<noteq>0" using rho by simp
  have exists: "\<exists>i j. ramified_weight l rho sigma (i,j)=b \<and> ramified_pbw_coeff l T i j\<noteq>0"
    using component ramified_weight_component_zero_iff[OF rhone, where l=l and sigma=sigma and b=b and T=T] by blast
  obtain i j where grade: "ramified_weight l rho sigma (i,j)=b" and coeff: "ramified_pbw_coeff l T i j\<noteq>0"
    using exists by blast
  have supported: "(i,j)\<in>ramified_pbw_support l T"
    using coeff ramified_pbw_support_mem_iff[OF l T] by blast
  show ?thesis
  proof (rule ramified_weight_deg_eq_of_attained_upper)
    show "\<exists>p\<in>ramified_pbw_support l T. ramified_weight l rho sigma p=b"
      by (intro bexI[of _ "(i,j)"] grade supported)
    show "\<forall>p\<in>ramified_pbw_support l T. ramified_weight l rho sigma p\<le>b"
    proof (intro ballI)
      fix p assume p: "p\<in>ramified_pbw_support l T"
      obtain i j where pair: "p=(i,j)" by (cases p) auto
      have coeff: "ramified_pbw_coeff l T i j\<noteq>0"
        using p by (simp only: pair ramified_pbw_support_mem_iff[OF l T]; simp)
      have vanishes: "b+1\<le>ramified_weight l rho sigma (i,j) \<Longrightarrow> ramified_pbw_coeff l T i j=0"
        using below by (simp add: ramifiedRestrictedWeightBelow_def)
      have bound: "ramified_weight l rho sigma (i,j)\<le>b"
      proof (rule ccontr)
        assume "\<not>ramified_weight l rho sigma (i,j)\<le>b"
        then have above: "b+1\<le>ramified_weight l rho sigma (i,j)" by arith
        show False using vanishes[OF above] coeff by contradiction
      qed
      show "ramified_weight l rho sigma p\<le>b" by (simp only: pair bound)
    qed
  qed
qed

lemma ramified_filtered_component_centralizes:
  assumes l: "0<l" and rho: "0<rho" and T: "T\<in>ramified_operator_algebra l"
    and below: "T\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1)"
    and central: "ramified_face_centralization l rho sigma P T=0"
  shows "[:of_int (ramified_weight_deg l rho sigma P)/(of_nat l*of_int rho):]*
    ramified_top_face_polynomial l rho sigma P*pderiv (ramified_weight_component_polynomial l rho sigma b T)-
    [:of_int b/(of_nat l*of_int rho):]*pderiv (ramified_top_face_polynomial l rho sigma P)*
      ramified_weight_component_polynomial l rho sigma b T=0"
proof (cases "ramified_weight_component_polynomial l rho sigma b T=0")
  case True then show ?thesis by simp
next
  case False
  have degree: "ramified_weight_deg l rho sigma T=b"
    by (rule ramified_below_nonzero_component_degree[OF l rho T below False])
  have face: "ramified_weight_component_polynomial l rho sigma b T=ramified_top_face_polynomial l rho sigma T"
    using ramified_weight_component_at_degree[where sigma=sigma, OF l rho T] by (simp only: degree)
  show ?thesis using central by (simp only: ramified_face_centralization_def degree face)
qed

lemma ramified_filtered_centralizer_component_representative:
  assumes l: "0<l" and rho: "0<rho" and S: "ramified_operator_vector.subspace S"
    and carrier: "S\<subseteq>ramified_operator_algebra l"
    and P: "P\<in>ramified_operator_algebra l" and Pnz: "P\<noteq>0"
    and m: "ramified_weight_deg l rho sigma P\<noteq>0"
    and central: "\<And>T. T\<in>S \<Longrightarrow> ramified_face_centralization l rho sigma P T=0"
  shows "\<exists>t\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1).
    \<forall>T\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1). \<exists>c.
      ramified_weight_component_polynomial l rho sigma b T=
        smult c (ramified_weight_component_polynomial l rho sigma b t)"
proof (cases "\<exists>t\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1). ramified_weight_component_polynomial l rho sigma b t\<noteq>0")
  case True
  then obtain t where t: "t\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1)"
    and tnz: "ramified_weight_component_polynomial l rho sigma b t\<noteq>0" by blast
  have coefficient: "(of_int (ramified_weight_deg l rho sigma P)/(of_nat l*of_int rho)::complex)\<noteq>0"
    using l rho m by simp
  have Pface: "ramified_top_face_polynomial l rho sigma P\<noteq>0"
    by (rule ramified_top_face_polynomial_ne_zero[OF l P rho Pnz])
  have equation: "[:of_int (ramified_weight_deg l rho sigma P)/(of_nat l*of_int rho):]*
    ramified_top_face_polynomial l rho sigma P*pderiv (ramified_weight_component_polynomial l rho sigma b U)-
    [:of_int b/(of_nat l*of_int rho):]*pderiv (ramified_top_face_polynomial l rho sigma P)*
      ramified_weight_component_polynomial l rho sigma b U=0"
    if member: "U\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1)" for U
  proof -
    have US: "U\<in>S" using member by (simp add: ramifiedRestrictedWeightBelow_def)
    have U: "U\<in>ramified_operator_algebra l" using carrier US by blast
    show ?thesis by (rule ramified_filtered_component_centralizes[OF l rho U member central[OF US]])
  qed
  have ratio: "\<exists>c. ramified_weight_component_polynomial l rho sigma b U=
    smult c (ramified_weight_component_polynomial l rho sigma b t)"
    if U: "U\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1)" for U
  proof -
    obtain c where c: "ramified_weight_component_polynomial l rho sigma b U=
      [:c:]*ramified_weight_component_polynomial l rho sigma b t"
      using weighted_derivative_kernel_scalar_ratio[OF coefficient Pface tnz equation[OF U] equation[OF t]] by blast
    show ?thesis by (intro exI[of _ c]) (use c in \<open>simp\<close>)
  qed
  show ?thesis using t ratio by blast
next
  case False
  have zeroS: "0\<in>S" using S by (simp add: ramified_operator_vector.subspace_def)
  have zero: "0\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1)"
    using zeroS by (simp add: ramifiedRestrictedWeightBelow_def ramified_pbw_coeff_def ramified_pbw_coeffs_zero[OF l])
  have allzero: "ramified_weight_component_polynomial l rho sigma b U=0"
    if "U\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1)" for U
    using False that by blast
  show ?thesis
  proof (intro bexI[of _ 0] zero ballI)
    fix U assume U: "U\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1)"
    show "\<exists>c. ramified_weight_component_polynomial l rho sigma b U=
      smult c (ramified_weight_component_polynomial l rho sigma b 0)"
      by (intro exI[of _ 0]) (simp only: allzero[OF U] smult_0_left)
  qed
qed

lemma ramified_top_centralizer_finrank_le_interval:
  assumes l: "0<l" and rho: "0<rho" and S: "ramified_operator_vector.subspace S"
    and carrier: "S\<subseteq>ramified_operator_algebra l"
    and P: "P\<in>ramified_operator_algebra l" and Pnz: "P\<noteq>0"
    and m: "ramified_weight_deg l rho sigma P\<noteq>0"
    and lower: "\<And>T i j. T\<in>S \<Longrightarrow> ramified_weight l rho sigma (i,j)<b \<Longrightarrow> ramified_pbw_coeff l T i j=0"
    and upper: "\<And>T i j. T\<in>S \<Longrightarrow> b+int N\<le>ramified_weight l rho sigma (i,j) \<Longrightarrow> ramified_pbw_coeff l T i j=0"
    and central: "\<And>T. T\<in>S \<Longrightarrow> ramified_face_centralization l rho sigma P T=0"
  shows "ramified_operator_vector.dim S\<le>N"
proof -
  have rhone: "rho\<noteq>0" using rho by simp
  have bottom: "ramifiedRestrictedWeightBelow l S rho sigma b={0}"
    by (rule ramifiedRestrictedWeightBelow_eq_bot[OF l S carrier lower])
  have top: "ramifiedRestrictedWeightBelow l S rho sigma (b+int N)=S"
    by (rule ramifiedRestrictedWeightBelow_eq_top[OF upper])
  have step: "\<exists>t\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+int k+1).
    \<forall>T\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+int k+1). \<exists>c.
      ramified_weight_component_polynomial l rho sigma (b+int k) T=
        smult c (ramified_weight_component_polynomial l rho sigma (b+int k) t)" for k
    by (rule ramified_filtered_centralizer_component_representative[OF l rho S carrier P Pnz m central])
  show ?thesis using ramified_finite_restricted_filtration_rank_le[OF l rhone S carrier bottom, of N] step
    by (simp only: top)
qed

end
