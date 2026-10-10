theory GGV_Inputs
 imports "Weyl_Statement_Interfaces"
   "Fourier_Generation"
   "Face_Mass_Geometry"
begin

text \<open>The source Prop-valued structure has no data fields. Its exact
native semantics is the conjunction of its six universally quantified
propositions; no structural field is registered as an axiom.\<close>

definition GGVGradesInput::bool where
 "GGVGradesInput \<longleftrightarrow> (\<forall>P Q::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
 (\<exists>e\<in>biv_support(pbw_symbol P). 0<pair_grade e) \<and> (\<exists>e\<in>biv_support(pbw_symbol P). pair_grade e<0))"

definition GGVCompanionInput::bool where
 "GGVCompanionInput \<longleftrightarrow> (\<forall>P Q::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
 (\<forall>rho sigma::int. is_direction rho sigma \<longrightarrow>
 (\<exists>mu::complex. \<exists>k::nat. \<exists>R F::complex bivariate. \<exists>m::int.
 mu\<noteq>0 \<and> 2\<le>k \<and> R\<noteq>0 \<and> weighted_homogeneous rho sigma m R \<and>
 weighted_homogeneous rho sigma (rho+sigma) F \<and>
 leading_form rho sigma P=[:[:mu:]:]*R^k \<and> biv_poisson R F=R)))"

definition GGVCaseSplitInput::bool where
 "GGVCaseSplitInput \<longleftrightarrow> (\<forall>P Q::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
 case_alternative P \<or> case_alternative(fourier_alg_hom P))"

definition GGVDegreeBoundInput::bool where
 "GGVDegreeBoundInput \<longleftrightarrow> (\<forall>P Q::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
 15<gcd(total_degree P)(total_degree Q))"

definition GGVCutCornerInput::bool where
 "GGVCutCornerInput \<longleftrightarrow> (\<forall>P Q::complex poly_operator. \<forall>rho sigma::int. \<forall>u v n d h::nat.
 is_counterexample_pair P Q \<longrightarrow> is_direction rho sigma \<longrightarrow> 0<rho \<longrightarrow> sigma\<le>0 \<longrightarrow>
 in_direction rho sigma P \<longrightarrow> in_direction rho sigma Q \<longrightarrow>
 0<v_degree rho sigma P \<longrightarrow> 0<v_degree rho sigma Q \<longrightarrow>
 rho+sigma<v_degree rho sigma P+v_degree rho sigma Q \<longrightarrow>
 \<not>v_degree rho sigma P dvd v_degree rho sigma Q \<longrightarrow> \<not>v_degree rho sigma Q dvd v_degree rho sigma P \<longrightarrow>
 (\<exists>e\<in>biv_support(leading_form rho sigma P). pair_grade e<0) \<longrightarrow>
 (\<exists>e\<in>biv_support(leading_form rho sigma Q). pair_grade e<0) \<longrightarrow>
 (u,v)\<in>biv_support(leading_form rho sigma P) \<longrightarrow>
 (\<forall>e\<in>biv_support(leading_form rho sigma P). pair_grade e\<le>pair_grade(u,v)) \<longrightarrow>
 v_degree rho sigma Q*int d=v_degree rho sigma P*int n \<longrightarrow>
 1<n \<longrightarrow> 1<d \<longrightarrow> coprime n d \<longrightarrow> 2\<le>h \<longrightarrow>
 \<not>(((of_nat u+((of_nat v::rat)-of_nat(max_root_mult(cut_poly rho sigma P)))*of_int sigma/of_int rho)/of_nat d=
 of_nat h-1/of_int rho) \<and> (of_nat(max_root_mult(cut_poly rho sigma P))::rat)/of_nat d=of_nat h))"

definition GGVPolynomialCornerInput::bool where
 "GGVPolynomialCornerInput \<longleftrightarrow> (\<forall>P Q::complex poly_operator. \<forall>rho sigma::int. \<forall>a b n d h::nat.
 is_counterexample_pair P Q \<longrightarrow> is_direction rho sigma \<longrightarrow> sigma\<le>0 \<longrightarrow>
 in_direction rho sigma P \<longrightarrow> in_direction rho sigma Q \<longrightarrow>
 0<v_degree rho sigma P \<longrightarrow> 0<v_degree rho sigma Q \<longrightarrow>
 \<not>v_degree rho sigma P dvd v_degree rho sigma Q \<longrightarrow> \<not>v_degree rho sigma Q dvd v_degree rho sigma P \<longrightarrow>
 (a,b)\<in>biv_support(leading_form rho sigma P) \<longrightarrow>
 (\<forall>e\<in>biv_support(leading_form rho sigma P). pair_grade(a,b)\<le>pair_grade e) \<longrightarrow>
 v_degree rho sigma Q*int d=v_degree rho sigma P*int n \<longrightarrow>
 1<n \<longrightarrow> 1<d \<longrightarrow> coprime n d \<longrightarrow> 2\<le>h \<longrightarrow>
 \<not>((of_nat a::rat)/of_nat d=of_nat h-1 \<and> (of_nat b::rat)/of_nat d=of_nat h))"

definition GGVInputs::bool where
 "GGVInputs \<longleftrightarrow> GGVGradesInput \<and> GGVCompanionInput \<and> GGVCaseSplitInput \<and>
 GGVDegreeBoundInput \<and> GGVCutCornerInput \<and> GGVPolynomialCornerInput"

lemma GGVInputs_grades_opposite: "GGVInputs \<Longrightarrow> GGVGradesInput"
 by (simp add: GGVInputs_def)
lemma GGVInputs_companion: "GGVInputs \<Longrightarrow> GGVCompanionInput"
 by (simp add: GGVInputs_def)
lemma GGVInputs_caseSplit: "GGVInputs \<Longrightarrow> GGVCaseSplitInput"
 by (simp add: GGVInputs_def)
lemma GGVInputs_degreeBound: "GGVInputs \<Longrightarrow> GGVDegreeBoundInput"
 by (simp add: GGVInputs_def)
lemma GGVInputs_cutCorner: "GGVInputs \<Longrightarrow> GGVCutCornerInput"
 by (simp add: GGVInputs_def)
lemma GGVInputs_corner: "GGVInputs \<Longrightarrow> GGVPolynomialCornerInput"
 by (simp add: GGVInputs_def)

end
