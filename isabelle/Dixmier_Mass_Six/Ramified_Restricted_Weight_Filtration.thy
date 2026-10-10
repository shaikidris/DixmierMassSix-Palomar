theory Ramified_Restricted_Weight_Filtration
  imports Ramified_Weight_Component
begin

definition ramifiedRestrictedWeightBelow where
  "ramifiedRestrictedWeightBelow l S rho sigma b=
    {T\<in>S. \<forall>i j. b\<le>ramified_weight l rho sigma (i,j) \<longrightarrow> ramified_pbw_coeff l T i j=0}"

lemma ramifiedRestrictedWeightBelow_mono:
  "b\<le>d \<Longrightarrow> ramifiedRestrictedWeightBelow l S rho sigma b\<subseteq>ramifiedRestrictedWeightBelow l S rho sigma d"
  unfolding ramifiedRestrictedWeightBelow_def by auto

lemma ramifiedRestrictedWeightBelow_subspace:
  assumes l: "0<l" and S: "ramified_operator_vector.subspace S"
    and carrier: "S\<subseteq>ramified_operator_algebra l"
  shows "ramified_operator_vector.subspace (ramifiedRestrictedWeightBelow l S rho sigma b)"
proof (unfold ramified_operator_vector.subspace_def, intro conjI)
  have zeroS: "0\<in>S" using S by (simp add: ramified_operator_vector.subspace_def)
  show "0\<in>ramifiedRestrictedWeightBelow l S rho sigma b"
    using zeroS by (simp add: ramifiedRestrictedWeightBelow_def ramified_pbw_coeff_def ramified_pbw_coeffs_zero[OF l])
  show "\<forall>x\<in>ramifiedRestrictedWeightBelow l S rho sigma b. \<forall>y\<in>ramifiedRestrictedWeightBelow l S rho sigma b.
    x+y\<in>ramifiedRestrictedWeightBelow l S rho sigma b"
  proof (intro ballI)
    fix x y assume x: "x\<in>ramifiedRestrictedWeightBelow l S rho sigma b" and y: "y\<in>ramifiedRestrictedWeightBelow l S rho sigma b"
    have xS: "x\<in>S" and yS: "y\<in>S" using x y by (auto simp: ramifiedRestrictedWeightBelow_def)
    have xc: "x\<in>ramified_operator_algebra l" and yc: "y\<in>ramified_operator_algebra l" using carrier xS yS by blast+
    have sumS: "x+y\<in>S" by (rule ramified_operator_vector.subspace_add[OF S xS yS])
    show "x+y\<in>ramifiedRestrictedWeightBelow l S rho sigma b"
      using sumS x y by (auto simp: ramifiedRestrictedWeightBelow_def ramified_pbw_coeff_def ramified_pbw_coeffs_add[OF l xc yc] Poly_Mapping.lookup_add)
  qed
  show "\<forall>c. \<forall>x\<in>ramifiedRestrictedWeightBelow l S rho sigma b.
    normal_smult c x\<in>ramifiedRestrictedWeightBelow l S rho sigma b"
  proof (intro allI ballI)
    fix c x assume x: "x\<in>ramifiedRestrictedWeightBelow l S rho sigma b"
    have xS: "x\<in>S" using x by (simp add: ramifiedRestrictedWeightBelow_def)
    have xc: "x\<in>ramified_operator_algebra l" using carrier xS by blast
    have scaleS: "normal_smult c x\<in>S" by (rule ramified_operator_vector.subspace_scale[OF S xS])
    show "normal_smult c x\<in>ramifiedRestrictedWeightBelow l S rho sigma b"
      using scaleS x by (auto simp: ramifiedRestrictedWeightBelow_def ramified_pbw_coeff_def ramified_pbw_coeffs_smult[OF l xc])
  qed
qed

lemma ramifiedRestrictedWeightComponent_kernel:
  assumes rho: "rho\<noteq>0"
  shows "{T\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1).
    ramified_weight_component_polynomial l rho sigma b T=0}=
    ramifiedRestrictedWeightBelow l S rho sigma b"
proof (rule set_eqI)
  fix T
  show "T\<in>{T\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1).
    ramified_weight_component_polynomial l rho sigma b T=0} \<longleftrightarrow> T\<in>ramifiedRestrictedWeightBelow l S rho sigma b"
  proof
    assume member: "T\<in>{T\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1).
      ramified_weight_component_polynomial l rho sigma b T=0}"
    have TS: "T\<in>S" using member by (simp add: ramifiedRestrictedWeightBelow_def)
    have zero_grade: "\<forall>i j. ramified_weight l rho sigma(i,j)=b \<longrightarrow> ramified_pbw_coeff l T i j=0"
      using member ramified_weight_component_zero_iff[OF rho, where l=l and sigma=sigma and b=b and T=T] by blast
    have upper_zero: "b+1\<le>ramified_weight l rho sigma(i,j) \<Longrightarrow> ramified_pbw_coeff l T i j=0" for i j
      using member by (simp add: ramifiedRestrictedWeightBelow_def)
    have zero: "ramified_pbw_coeff l T i j=0" if bound: "b\<le>ramified_weight l rho sigma(i,j)" for i j
    proof (cases "ramified_weight l rho sigma(i,j)=b")
      case True show ?thesis using zero_grade True by blast
    next
      case False
      have above: "b+1\<le>ramified_weight l rho sigma(i,j)" using bound False by arith
      show ?thesis by (rule upper_zero[OF above])
    qed
    show "T\<in>ramifiedRestrictedWeightBelow l S rho sigma b" using TS zero by (simp add: ramifiedRestrictedWeightBelow_def)
  next
    assume member: "T\<in>ramifiedRestrictedWeightBelow l S rho sigma b"
    have upper: "T\<in>ramifiedRestrictedWeightBelow l S rho sigma(b+1)"
      by (rule subsetD[OF ramifiedRestrictedWeightBelow_mono member]) simp
    have zero_grade: "\<forall>i j. ramified_weight l rho sigma(i,j)=b \<longrightarrow> ramified_pbw_coeff l T i j=0"
      using member by (auto simp: ramifiedRestrictedWeightBelow_def)
    have zero: "ramified_weight_component_polynomial l rho sigma b T=0"
      using ramified_weight_component_zero_iff[OF rho, where l=l and sigma=sigma and b=b and T=T] zero_grade by blast
    show "T\<in>{T\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1).
      ramified_weight_component_polynomial l rho sigma b T=0}" using upper zero by simp
  qed
qed

lemma ramifiedRestrictedWeightBelow_eq_bot:
  assumes l: "0<l" and S: "ramified_operator_vector.subspace S"
    and carrier: "S\<subseteq>ramified_operator_algebra l"
    and lower: "\<And>T i j. T\<in>S \<Longrightarrow> ramified_weight l rho sigma (i,j)<b \<Longrightarrow> ramified_pbw_coeff l T i j=0"
  shows "ramifiedRestrictedWeightBelow l S rho sigma b={0}"
proof (rule set_eqI)
  fix T
  have zero: "T=0" if member: "T\<in>ramifiedRestrictedWeightBelow l S rho sigma b"
  proof -
    have TS: "T\<in>S" using member by (simp add: ramifiedRestrictedWeightBelow_def)
    have Tc: "T\<in>ramified_operator_algebra l" using carrier TS by blast
    have zc: "(0::laurent_operator)\<in>ramified_operator_algebra l"
      unfolding ramified_operator_algebra_def by (rule laurent_adjoin_zero)
    show ?thesis
    proof (rule ramifiedOperator_eq_of_pbwCoeff[OF l Tc zc])
      fix i j
      have coeffzero: "ramified_pbw_coeff l T i j=0"
      proof (cases "ramified_weight l rho sigma (i,j)<b")
        case True show ?thesis by (rule lower[OF TS True])
      next
        case False show ?thesis using member False by (simp add: ramifiedRestrictedWeightBelow_def)
      qed
      show "ramified_pbw_coeff l T i j=ramified_pbw_coeff l 0 i j"
        by (simp only: coeffzero; simp only: ramified_pbw_coeff_def ramified_pbw_coeffs_zero[OF l] Poly_Mapping.lookup_zero)
    qed
  qed
  have zeroS: "0\<in>S" using S by (simp add: ramified_operator_vector.subspace_def)
  have memberzero: "0\<in>ramifiedRestrictedWeightBelow l S rho sigma b"
    using zeroS by (simp add: ramifiedRestrictedWeightBelow_def ramified_pbw_coeff_def ramified_pbw_coeffs_zero[OF l])
  show "T\<in>ramifiedRestrictedWeightBelow l S rho sigma b \<longleftrightarrow> T\<in>{0}"
    using zero memberzero by blast
qed

lemma ramifiedRestrictedWeightBelow_eq_top:
  assumes upper: "\<And>T i j. T\<in>S \<Longrightarrow> b\<le>ramified_weight l rho sigma (i,j) \<Longrightarrow> ramified_pbw_coeff l T i j=0"
  shows "ramifiedRestrictedWeightBelow l S rho sigma b=S"
  using upper unfolding ramifiedRestrictedWeightBelow_def by auto

lemma ramified_restricted_component_span_extension:
  assumes l: "0<l" and rho: "rho\<noteq>0" and S: "ramified_operator_vector.subspace S"
    and carrier: "S\<subseteq>ramified_operator_algebra l"
    and lower: "ramifiedRestrictedWeightBelow l S rho sigma b\<subseteq>ramified_operator_vector.span A"
    and t: "t\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1)"
    and image: "\<And>T. T\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1) \<Longrightarrow>
      \<exists>c. ramified_weight_component_polynomial l rho sigma b T=
        smult c (ramified_weight_component_polynomial l rho sigma b t)"
  shows "ramifiedRestrictedWeightBelow l S rho sigma (b+1)\<subseteq>ramified_operator_vector.span (insert t A)"
proof
  fix T assume T: "T\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1)"
  obtain c where c: "ramified_weight_component_polynomial l rho sigma b T=
    smult c (ramified_weight_component_polynomial l rho sigma b t)" using image[OF T] by blast
  let ?d = "T-normal_smult c t"
  have subspace: "ramified_operator_vector.subspace (ramifiedRestrictedWeightBelow l S rho sigma (b+1))"
    by (rule ramifiedRestrictedWeightBelow_subspace[OF l S carrier])
  have upper: "?d\<in>ramifiedRestrictedWeightBelow l S rho sigma (b+1)"
    by (intro ramified_operator_vector.subspace_diff[OF subspace] T ramified_operator_vector.subspace_scale[OF subspace t])
  have TS: "T\<in>S" and tS: "t\<in>S" using T t by (auto simp: ramifiedRestrictedWeightBelow_def)
  have Tc: "T\<in>ramified_operator_algebra l" and tc: "t\<in>ramified_operator_algebra l" using carrier TS tS by blast+
  have scaled: "normal_smult c t\<in>ramified_operator_algebra l" by (rule ramified_algebra_smult[OF tc])
  have zero: "ramified_weight_component_polynomial l rho sigma b ?d=0"
  proof (rule poly_eqI)
    fix j
    have ce: "coeff (ramified_weight_component_polynomial l rho sigma b T) j=
      coeff (smult c (ramified_weight_component_polynomial l rho sigma b t)) j"
      by (rule arg_cong[OF c])
    show "coeff (ramified_weight_component_polynomial l rho sigma b ?d) j=coeff (0::complex poly) j"
      using ce by (simp add: ramified_weight_component_coeff ramified_pbw_coeff_def
        ramified_pbw_coeffs_diff[OF l Tc scaled] ramified_pbw_coeffs_smult[OF l tc] Poly_Mapping.lookup_minus split: if_splits)
  qed
  have d: "?d\<in>ramifiedRestrictedWeightBelow l S rho sigma b"
    using upper zero ramifiedRestrictedWeightComponent_kernel[OF rho, where S=S and l=l and sigma=sigma and b=b] by blast
  have ds: "?d\<in>ramified_operator_vector.span (insert t A)"
    using lower d ramified_operator_vector.span_mono[of A "insert t A"] by blast
  have ts: "normal_smult c t\<in>ramified_operator_vector.span (insert t A)"
    by (intro ramified_operator_vector.span_scale ramified_operator_vector.span_base) simp
  have "?d+normal_smult c t\<in>ramified_operator_vector.span (insert t A)"
    by (rule ramified_operator_vector.span_add[OF ds ts])
  then show "T\<in>ramified_operator_vector.span (insert t A)" by simp
qed

lemma ramified_finite_restricted_filtration_spanning:
  fixes S :: "laurent_operator set"
  assumes l: "0<l" and rho: "rho\<noteq>0" and S: "ramified_operator_vector.subspace S"
    and carrier: "S\<subseteq>ramified_operator_algebra l"
    and bottom: "ramifiedRestrictedWeightBelow l S rho sigma a={0}"
    and step: "\<And>k. k<n \<Longrightarrow> \<exists>t\<in>ramifiedRestrictedWeightBelow l S rho sigma (a+int k+1).
      \<forall>p\<in>ramifiedRestrictedWeightBelow l S rho sigma (a+int k+1). \<exists>c.
        ramified_weight_component_polynomial l rho sigma (a+int k) p=
          smult c (ramified_weight_component_polynomial l rho sigma (a+int k) t)"
  shows "\<exists>A. finite A \<and> card A\<le>n \<and>
    ramifiedRestrictedWeightBelow l S rho sigma (a+int n)\<subseteq>ramified_operator_vector.span A"
  using step
proof (induction n)
  case 0
  show ?case by (intro exI[of _ "{}"])
    (simp add: bottom ramified_operator_vector.span_zero)
next
  case (Suc n)
  obtain A where A: "finite A" "card A\<le>n"
    "ramifiedRestrictedWeightBelow l S rho sigma (a+int n)\<subseteq>ramified_operator_vector.span A"
    using Suc.IH Suc.prems by force
  obtain t where t: "t\<in>ramifiedRestrictedWeightBelow l S rho sigma (a+int n+1)"
    and image: "\<forall>p\<in>ramifiedRestrictedWeightBelow l S rho sigma (a+int n+1). \<exists>c.
      ramified_weight_component_polynomial l rho sigma (a+int n) p=
        smult c (ramified_weight_component_polynomial l rho sigma (a+int n) t)"
    using Suc.prems[of n] by auto
  have subset: "ramifiedRestrictedWeightBelow l S rho sigma (a+int (Suc n))\<subseteq>
      ramified_operator_vector.span (insert t A)"
    using ramified_restricted_component_span_extension[OF l rho S carrier A(3) t] image
    by (simp add: algebra_simps)
  have card: "card (insert t A)\<le>Suc n" using A(1,2) by (simp add: card_insert_if)
  show ?case by (intro exI[of _ "insert t A"]) (use A card subset in auto)
qed

lemma ramified_finite_restricted_filtration_rank_le:
  fixes S :: "laurent_operator set"
  assumes l: "0<l" and rho: "rho\<noteq>0" and S: "ramified_operator_vector.subspace S"
    and carrier: "S\<subseteq>ramified_operator_algebra l"
    and bottom: "ramifiedRestrictedWeightBelow l S rho sigma a={0}"
    and step: "\<And>k. k<n \<Longrightarrow> \<exists>t\<in>ramifiedRestrictedWeightBelow l S rho sigma (a+int k+1).
      \<forall>p\<in>ramifiedRestrictedWeightBelow l S rho sigma (a+int k+1). \<exists>c.
        ramified_weight_component_polynomial l rho sigma (a+int k) p=
          smult c (ramified_weight_component_polynomial l rho sigma (a+int k) t)"
  shows "ramified_operator_vector.dim (ramifiedRestrictedWeightBelow l S rho sigma (a+int n))\<le>n"
proof -
  obtain A where A: "finite A" "card A\<le>n"
    "ramifiedRestrictedWeightBelow l S rho sigma (a+int n)\<subseteq>ramified_operator_vector.span A"
    using ramified_finite_restricted_filtration_spanning[OF l rho S carrier bottom step] by blast
  show ?thesis using ramified_operator_vector.dim_le_card[OF A(3) A(1)] A(2) by arith
qed

end
