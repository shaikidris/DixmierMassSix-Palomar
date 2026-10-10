theory GGV_Companion_Proved
 imports "Proper_Power_Descent"
   "GGV_Joseph_Proved"
   "Poisson_Power_Cancellation"
begin

definition GGVProperPowerInput::bool where
 "GGVProperPowerInput \<longleftrightarrow>
 (\<forall>P Q::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
 (\<forall>rho sigma::int. is_direction rho sigma \<longrightarrow>
 (\<exists>mu::complex. \<exists>k::nat. \<exists>R::complex bivariate. \<exists>m::int.
 mu\<noteq>0 \<and> 2\<le>k \<and> R\<noteq>0 \<and> weighted_homogeneous rho sigma m R \<and>
 leading_form rho sigma P=[:[:mu:]:]*R^k)))"

definition GGVPreliminaryCompanionInput::bool where
 "GGVPreliminaryCompanionInput \<longleftrightarrow>
 (\<forall>P Q::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
 (\<forall>rho sigma::int. is_direction rho sigma \<longrightarrow>
 (\<exists>F::complex bivariate. weighted_homogeneous rho sigma (rho+sigma) F \<and>
 biv_poisson(leading_form rho sigma P) F=leading_form rho sigma P)))"

lemma native_homogeneous_scalar_multiple:
 fixes F::"complex bivariate" and c::complex
 assumes hom: "weighted_homogeneous rho sigma m F"
 shows "weighted_homogeneous rho sigma m ([:[:c:]:]*F)"
 unfolding weighted_homogeneous_def
proof (intro ballI)
 fix e assume member: "e\<in>biv_support([:[:c:]:]*F)"
 have raw: "e\<in>biv_support F" using member by (auto simp: biv_support_def biv_coeff_def)
 show "pair_weight rho sigma e=m" using hom raw unfolding weighted_homogeneous_def by blast
qed

lemma ggv_companion_of_source_inputs:
 assumes power: "GGVProperPowerInput" and preliminary: "GGVPreliminaryCompanionInput"
 shows "\<forall>P Q::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
 (\<forall>rho sigma::int. is_direction rho sigma \<longrightarrow>
 (\<exists>mu::complex. \<exists>k::nat. \<exists>R F::complex bivariate. \<exists>m::int.
 mu\<noteq>0 \<and> 2\<le>k \<and> R\<noteq>0 \<and> weighted_homogeneous rho sigma m R \<and>
 weighted_homogeneous rho sigma (rho+sigma) F \<and>
 leading_form rho sigma P=[:[:mu:]:]*R^k \<and> biv_poisson R F=R))"
proof (intro allI impI)
 fix P Q::"complex poly_operator" and rho sigma::int
 assume pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 obtain mu k R m where mu: "mu\<noteq>0" and k: "2\<le>k" and R: "R\<noteq>0"
 and Rhom: "weighted_homogeneous rho sigma m R"
 and shape: "leading_form rho sigma P=[:[:mu:]:]*R^k"
   using power pair direction unfolding GGVProperPowerInput_def by blast
 obtain F where Fhom: "weighted_homogeneous rho sigma (rho+sigma) F"
 and bracket: "biv_poisson(leading_form rho sigma P) F=leading_form rho sigma P"
   using preliminary pair direction unfolding GGVPreliminaryCompanionInput_def by blast
 let ?F="[:[:of_nat k:]:]*F"
 have hom: "weighted_homogeneous rho sigma (rho+sigma) ?F"
   by (rule native_homogeneous_scalar_multiple[OF Fhom])
 have positive: "0<k" using k by arith
 have power_bracket: "biv_poisson([:[:mu:]:]*R^k) F=[:[:mu:]:]*R^k"
   using bracket by (simp only: shape)
 have companion: "biv_poisson R ?F=R"
   by (rule poisson_power_companion_cancel[OF mu positive R power_bracket])
 show "\<exists>mu::complex. \<exists>k::nat. \<exists>R F::complex bivariate. \<exists>m::int.
 mu\<noteq>0 \<and> 2\<le>k \<and> R\<noteq>0 \<and> weighted_homogeneous rho sigma m R \<and>
 weighted_homogeneous rho sigma (rho+sigma) F \<and>
 leading_form rho sigma P=[:[:mu:]:]*R^k \<and> biv_poisson R F=R"
   by (intro exI[of _ mu] exI[of _ k] exI[of _ R] exI[of _ ?F] exI[of _ m])
      (use mu k R Rhom hom shape companion in blast)
qed

lemma ggv_companion_proved:
 "\<forall>P Q::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
 (\<forall>rho sigma::int. is_direction rho sigma \<longrightarrow>
 (\<exists>mu::complex. \<exists>k::nat. \<exists>R F::complex bivariate. \<exists>m::int.
 mu\<noteq>0 \<and> 2\<le>k \<and> R\<noteq>0 \<and> weighted_homogeneous rho sigma m R \<and>
 weighted_homogeneous rho sigma (rho+sigma) F \<and>
 leading_form rho sigma P=[:[:mu:]:]*R^k \<and> biv_poisson R F=R))"
proof -
 have power: "GGVProperPowerInput"
   using ggv_proper_power_input_proved by (simp only: GGVProperPowerInput_def)
 have preliminary: "GGVPreliminaryCompanionInput"
   using ggv_preliminary_companion_proved by (simp only: GGVPreliminaryCompanionInput_def)
 show ?thesis by (rule ggv_companion_of_source_inputs[OF power preliminary])
qed

end
