theory GGV_Case_Field_Adapter
 imports "GGV_Companion_Proved"
begin

text \<open>Source: 61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff,
GGVCaseFieldAdapter.lean.\<close>

lemma uniform_degree_bound_of_degree_gcd:
 fixes P Q::"complex poly_operator"
 assumes degree_bound: "\<And>P Q::complex poly_operator. is_counterexample_pair P Q \<Longrightarrow>
   15<gcd (total_degree P) (total_degree Q)"
   and pair: "is_counterexample_pair P Q"
 shows "16\<le>total_degree P"
proof -
 have direction: "is_direction 1 1" by (simp add: is_direction_def)
 have positive: "0<v_degree 1 1 P"
   by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 let ?S="biv_support (pbw_symbol P)"
 let ?W="pair_weight 1 1 ` ?S"
 have nonempty: "?S\<noteq>{}"
   using positive by (auto simp: v_degree_def weighted_degree_def)
 have max_positive: "0<Max ?W"
   using positive nonempty by (simp add: v_degree_def weighted_degree_def)
 have attained: "Max ?W\<in>?W"
   by (rule Max_in) (use nonempty in auto)
 obtain u where image_eq: "Max ?W=pair_weight 1 1 u" and member: "u\<in>?S"
   using attained by (rule imageE)
 have weight: "pair_weight 1 1 u=Max ?W" by (rule sym[OF image_eq])
 have positive_integer: "0<int(fst u+snd u)"
   using max_positive weight by (simp only: pair_weight_def mult_1_right of_nat_add; linarith)
 have positive_sum: "0<fst u+snd u"
   using positive_integer by (simp only: of_nat_0_less_iff)
 have image_member: "(\<lambda>u. fst u+snd u) u\<in>(\<lambda>u. fst u+snd u) ` ?S"
   by (rule imageI[OF member])
 have bound: "fst u+snd u\<le>total_degree P"
   unfolding total_degree_def by (rule Max_ge) (simp, rule insertI2[OF image_member])
 have nonzero: "total_degree P\<noteq>0" using positive_sum bound by arith
 have gcd_bound: "gcd (total_degree P) (total_degree Q)\<le>total_degree P"
   by (rule gcd_le1_nat[OF nonzero])
 have lower: "15<gcd (total_degree P) (total_degree Q)"
   by (rule degree_bound[OF pair])
 show ?thesis using lower gcd_bound by arith
qed

lemma preliminary_companion_of_power_companion_field:
 assumes companion: "\<forall>P Q::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
 (\<forall>rho sigma::int. is_direction rho sigma \<longrightarrow>
 (\<exists>mu::complex. \<exists>k::nat. \<exists>R F::complex bivariate. \<exists>m::int.
 mu\<noteq>0 \<and> 2\<le>k \<and> R\<noteq>0 \<and> weighted_homogeneous rho sigma m R \<and>
 weighted_homogeneous rho sigma (rho+sigma) F \<and>
 leading_form rho sigma P=[:[:mu:]:]*R^k \<and> biv_poisson R F=R))"
 shows "GGVPreliminaryCompanionInput"
 unfolding GGVPreliminaryCompanionInput_def
proof (intro allI impI)
 fix P Q::"complex poly_operator" and rho sigma::int
 assume pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 obtain mu k R F m where k: "2\<le>k"
   and homogeneous: "weighted_homogeneous rho sigma (rho+sigma) F"
   and face: "leading_form rho sigma P=[:[:mu:]:]*R^k"
   and bracket: "biv_poisson R F=R"
   using companion pair direction by blast
 let ?G="[:[:inverse(of_nat k::complex):]:]*F"
 have Ghom: "weighted_homogeneous rho sigma (rho+sigma) ?G"
   by (rule native_homogeneous_scalar_multiple[OF homogeneous])
 have positive: "0<k" using k by arith
 have scalar_nonzero: "(of_nat k::complex)\<noteq>0" using positive by simp
 have exponent: "Suc(k-1)=k" using positive by arith
 have power: "R^(k-1)*R=R^k"
   using power_Suc2[of R "k-1"] by (simp only: exponent)
 have scalar_inverse: "[:[:inverse(of_nat k::complex):]:]*(of_nat k::complex bivariate)=1"
   using scalar_nonzero by (simp add: of_nat_poly one_pCons)
 have Gbracket: "biv_poisson (leading_form rho sigma P) ?G=leading_form rho sigma P"
 proof -
   have "biv_poisson (leading_form rho sigma P) ?G =
     [:[:mu:]:]*([:[:inverse(of_nat k::complex):]:]*(of_nat k*R^(k-1)*R))"
     by (simp only: face; subst biv_poisson_const_left; subst biv_poisson_const_right;
       subst poisson_power_left; subst bracket; rule refl)
   also have "...=[:[:mu:]:]*(
     ([:[:inverse(of_nat k::complex):]:] * (of_nat k::complex bivariate))*(R^(k-1)*R))"
     by (simp only: mult.assoc)
   also have "...=[:[:mu:]:]*R^k" by (simp only: scalar_inverse power mult_1_left)
   also have "...=leading_form rho sigma P" by (rule face[symmetric])
   finally show ?thesis .
 qed
 show "\<exists>F::complex bivariate. weighted_homogeneous rho sigma (rho+sigma) F \<and>
   biv_poisson (leading_form rho sigma P) F=leading_form rho sigma P"
   by (intro exI[of _ ?G] conjI) (rule Ghom, rule Gbracket)
qed

lemma preliminary_companion_from_actual_GGV_companion:
 "GGVPreliminaryCompanionInput"
 by (rule preliminary_companion_of_power_companion_field[OF ggv_companion_proved])

end
