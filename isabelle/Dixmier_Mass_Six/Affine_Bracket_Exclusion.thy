theory Affine_Bracket_Exclusion
 imports Affine_Degree_One
   "Counterexample_Positive_Weight"
   "Leading_Mate"
begin

lemma affine_linear_neg_image:
 "poly_linear T \<Longrightarrow> T (-p)=-T p" for T :: "complex poly_operator"
proof -
 assume linear: "poly_linear T"
 have "T (smult (-1) p)=smult (-1) (T p)" using linear unfolding poly_linear_def by blast
 then show ?thesis by simp
qed

lemma isCounterexamplePair_swap_neg:
 fixes P Q :: "complex poly_operator"
 assumes pair: "is_counterexample_pair P Q"
 shows "is_counterexample_pair Q (-P)"
proof -
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
   and exact: "op_comp Q P-op_comp P Q=id"
   and nongeneration: "op_adjoin {P,Q}\<noteq>weyl_algebra"
   using pair by (auto simp: is_counterexample_pair_def)
 have zero: "(0::complex poly_operator)\<in>weyl_algebra"
   unfolding weyl_algebra_def by (rule op_adjoin_zero)
 have negP: "-P\<in>weyl_algebra"
   using P zero weyl_subalgebra by (auto simp: op_subalgebra_def)
 have swapped_exact: "op_comp (-P) Q-op_comp Q (-P)=id"
 proof (rule ext)
   fix p
   have original: "Q(P p)-P(Q p)=p"
     using fun_cong[OF exact, of p] by (simp add: op_comp_def)
   show "(op_comp (-P) Q-op_comp Q (-P)) p=id p"
     using original by (simp add: op_comp_def
       affine_linear_neg_image[OF weyl_linear[OF Q]] algebra_simps)
 qed
 have closed_original: "op_subalgebra (op_adjoin {P,Q})"
   by (rule op_adjoin_subalgebra) (use P Q in \<open>auto intro: weyl_linear\<close>)
 have closed_swapped: "op_subalgebra (op_adjoin {Q,-P})"
   by (rule op_adjoin_subalgebra) (use Q negP in \<open>auto intro: weyl_linear\<close>)
 have P_original: "P\<in>op_adjoin {P,Q}" and Q_original: "Q\<in>op_adjoin {P,Q}"
   and negP_swapped: "-P\<in>op_adjoin {Q,-P}" and Q_swapped: "Q\<in>op_adjoin {Q,-P}"
   by (auto intro: op_adjoin.generator)
 have negP_original: "-P\<in>op_adjoin {P,Q}"
   using op_adjoin.diff[OF op_adjoin_zero P_original] by simp
 have P_swapped: "P\<in>op_adjoin {Q,-P}"
   using op_adjoin.diff[OF op_adjoin_zero negP_swapped] by simp
 have equal: "op_adjoin {Q,-P}= op_adjoin {P,Q}"
   by (rule equalityI;
       rule op_adjoin_least)
      (use Q_original negP_original closed_original Q_swapped P_swapped closed_swapped in auto)
 show ?thesis using Q negP swapped_exact nongeneration
   by (simp add: is_counterexample_pair_def equal)
qed

lemma leading_weights_sum_of_bracket_one:
 fixes P Q :: "complex poly_operator"
 assumes direction: "is_direction rho sigma" and pair: "is_counterexample_pair P Q"
   and bracket: "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=1"
 shows "v_degree rho sigma P+v_degree rho sigma Q=rho+sigma"
proof -
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
   and exact: "op_comp Q P-op_comp P Q=id"
   using pair by (auto simp: is_counterexample_pair_def)
 have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have zero: "v_degree rho sigma Q+v_degree rho sigma P-(rho+sigma)=0"
   by (rule exactPair_target_eq_zero_of_leadingPoisson_eq_one[OF P Q sum exact bracket])
 show ?thesis using zero by arith
qed

lemma leading_weights_one_of_bracket_one_sum_two:
 fixes P Q :: "complex poly_operator"
 assumes direction: "is_direction rho sigma" and sum_two: "rho+sigma=2"
   and pair: "is_counterexample_pair P Q"
   and bracket: "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=1"
 shows "v_degree rho sigma P=1\<and>v_degree rho sigma Q=1"
proof -
 have P_positive: "0<v_degree rho sigma P"
   by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have Q_positive: "0<v_degree rho sigma Q"
   by (rule counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF pair] direction])
 have weights: "v_degree rho sigma P+v_degree rho sigma Q=rho+sigma"
   by (rule leading_weights_sum_of_bracket_one[OF direction pair bracket])
 show ?thesis using P_positive Q_positive weights sum_two by arith
qed

lemma total_degree_one_of_vDeg_one:
 assumes degree: "v_degree 1 1 (T::complex poly_operator)=1"
 shows "total_degree T=1"
proof -
 let ?S = "biv_support (pbw_symbol T)"
 let ?W = "pair_weight 1 1 ` ?S"
 have nonempty: "?S\<noteq>{}"
   using degree by (auto simp: v_degree_def weighted_degree_def)
 have weight_max: "Max ?W=1"
   using degree nonempty by (simp add: v_degree_def weighted_degree_def)
 have total_weight: "pair_weight 1 1 u=int(fst u+snd u)" for u
   by (simp add: pair_weight_def)
 have upper: "fst u+snd u\<le>1" if member: "u\<in>?S" for u
 proof -
   have weight_member: "pair_weight 1 1 u\<in>?W" by (rule imageI[OF member])
   have bound: "pair_weight 1 1 u\<le>Max ?W"
     by (rule Max_ge) (simp, rule weight_member)
   have cast_bound: "int(fst u+snd u)\<le>(1::int)"
     using bound by (simp only: total_weight weight_max)
   show ?thesis using cast_bound by simp
 qed
 have max_member: "Max ?W\<in>?W" by (rule Max_in) (use nonempty in auto)
 obtain u where member: "u\<in>?S" and weight: "pair_weight 1 1 u=1"
   using max_member weight_max by auto
 have sum_one: "fst u+snd u=1" using weight by (simp only: total_weight; simp)
 have image_member: "(\<lambda>u. fst u+snd u) u\<in>(\<lambda>u. fst u+snd u) ` ?S"
   by (rule imageI[OF member])
 have one_image: "1\<in>(\<lambda>u. fst u+snd u) ` ?S"
   using image_member by (simp only: sum_one)
 have one_member: "1\<in>insert 0 ((\<lambda>u. fst u+snd u) ` ?S)"
   by (rule insertI2[OF one_image])
 have finite_set: "finite (insert 0 ((\<lambda>u. fst u+snd u) ` ?S))" by simp
 have bounded: "y\<le>1" if y: "y\<in>insert 0 ((\<lambda>u. fst u+snd u) ` ?S)" for y
 proof (cases "y=0")
   case True then show ?thesis by simp
 next
   case False
   have image: "y\<in>(\<lambda>u. fst u+snd u) ` ?S" using y False by simp
   obtain e where e: "e\<in>?S" and image_value: "y=fst e+snd e" using image by blast
   show ?thesis using upper[OF e] by (simp only: image_value)
 qed
 show ?thesis unfolding total_degree_def
   by (rule Max_eqI[OF finite_set bounded one_member])
qed

lemma bracket_one_diagonal_forces_totalDeg_one:
 fixes P Q :: "complex poly_operator"
 assumes pair: "is_counterexample_pair P Q"
   and bracket: "biv_poisson (leading_form 1 1 Q) (leading_form 1 1 P)=1"
 shows "total_degree P=1\<and>total_degree Q=1"
proof -
 have direction: "is_direction 1 1" by (simp add: is_direction_def)
 have weights: "v_degree 1 1 P=1\<and>v_degree 1 1 Q=1"
   by (rule leading_weights_one_of_bracket_one_sum_two[OF direction _ pair bracket]) simp
 show ?thesis using weights total_degree_one_of_vDeg_one by blast
qed

lemma bracket_one_diagonal_impossible:
 fixes P Q :: "complex poly_operator"
 assumes pair: "is_counterexample_pair P Q"
 shows "biv_poisson (leading_form 1 1 Q) (leading_form 1 1 P)\<noteq>1"
proof
 assume bracket: "biv_poisson (leading_form 1 1 Q) (leading_form 1 1 P)=1"
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
   and nongeneration: "op_adjoin {P,Q}\<noteq>weyl_algebra"
   using pair by (auto simp: is_counterexample_pair_def)
 have direction: "is_direction 1 1" by (simp add: is_direction_def)
 have weights: "v_degree 1 1 P=1\<and>v_degree 1 1 Q=1"
   by (rule leading_weights_one_of_bracket_one_sum_two[OF direction _ pair bracket]) simp
 have total: "total_degree P=1\<and>total_degree Q=1"
   by (rule bracket_one_diagonal_forces_totalDeg_one[OF pair bracket])
 have determinant: "pbw_coeff Q 0 1*pbw_coeff P 1 0-pbw_coeff Q 1 0*pbw_coeff P 0 1=1"
   by (rule affine_determinant_one_of_diagonal_bracket_one[OF P Q conjunct1[OF weights] conjunct2[OF weights] bracket])
 have generated: "op_adjoin {P,Q}=weyl_algebra"
   by (rule affine_pair_generates_of_unit_determinant[OF P Q
      affine_reconstruction_of_totalDeg_one[OF P conjunct1[OF total]]
      affine_reconstruction_of_totalDeg_one[OF Q conjunct2[OF total]] determinant])
 show False using generated nongeneration by contradiction
qed


lemma bracket_one_impossible_of_nonpositive_sigma:
 fixes P Q :: "complex poly_operator"
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
   and rho: "0<rho" and sigma: "sigma\<le>0"
 shows "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)\<noteq>1"
proof
 assume bracket: "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=1"
 have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have P_lower: "rho\<le>v_degree rho sigma P"
   by (rule counterexample_vDeg_ge_rho_of_positive_grade[OF pair rho sum])
 have Q_positive: "0<v_degree rho sigma Q"
   by (rule counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF pair] direction])
 have weights: "v_degree rho sigma P+v_degree rho sigma Q=rho+sigma"
   by (rule leading_weights_sum_of_bracket_one[OF direction pair bracket])
 show False using P_lower Q_positive weights sigma by arith
qed

lemma bracket_one_impossible_of_nonpositive_rho:
 fixes P Q :: "complex poly_operator"
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
   and rho: "rho\<le>0" and sigma: "0<sigma"
 shows "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)\<noteq>1"
proof
 assume bracket: "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=1"
 have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have P_lower: "sigma\<le>v_degree rho sigma P"
   by (rule counterexample_vDeg_ge_sigma_of_negative_grade[OF pair sigma sum])
 have Q_positive: "0<v_degree rho sigma Q"
   by (rule counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF pair] direction])
 have weights: "v_degree rho sigma P+v_degree rho sigma Q=rho+sigma"
   by (rule leading_weights_sum_of_bracket_one[OF direction pair bracket])
 show False using P_lower Q_positive weights rho by arith
qed

lemma bracket_one_impossible_positive_quadrant:
 fixes P Q :: "complex poly_operator"
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
   and rho: "0<rho" and sigma: "0<sigma"
 shows "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)\<noteq>1"
proof
 assume bracket: "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=1"
 have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have swapped: "is_counterexample_pair Q (-P)" by (rule isCounterexamplePair_swap_neg[OF pair])
 have P_rho: "rho\<le>v_degree rho sigma P"
   by (rule counterexample_vDeg_ge_rho_of_positive_grade[OF pair rho sum])
 have P_sigma: "sigma\<le>v_degree rho sigma P"
   by (rule counterexample_vDeg_ge_sigma_of_negative_grade[OF pair sigma sum])
 have Q_rho: "rho\<le>v_degree rho sigma Q"
   by (rule counterexample_vDeg_ge_rho_of_positive_grade[OF swapped rho sum])
 have Q_sigma: "sigma\<le>v_degree rho sigma Q"
   by (rule counterexample_vDeg_ge_sigma_of_negative_grade[OF swapped sigma sum])
 have weights: "v_degree rho sigma P+v_degree rho sigma Q=rho+sigma"
   by (rule leading_weights_sum_of_bracket_one[OF direction pair bracket])
 have equal: "rho=sigma" using weights P_rho P_sigma Q_rho Q_sigma by arith
 have primitive: "gcd (nat(abs rho)) (nat(abs sigma))=1"
   using direction by (simp only: is_direction_def; blast)
 have absolute_nat: "nat (abs rho)=1"
   using primitive by (simp only: equal[symmetric] gcd_self; simp)
 have absolute: "abs rho=1"
   using arg_cong[OF absolute_nat, of int] by simp
 have rho_one: "rho=1" using absolute rho by simp
 have sigma_one: "sigma=1" using rho_one equal by simp
 show False using bracket bracket_one_diagonal_impossible[OF pair]
   by (simp only: rho_one sigma_one)
qed

lemma ggv_bracket_one_input_proved:
 fixes P Q :: "complex poly_operator"
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 shows "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)\<noteq>1"
proof (cases "rho\<le>0")
 case True
 have sigma: "0<sigma" using direction True by (simp add: is_direction_def; arith)
 show ?thesis by (rule bracket_one_impossible_of_nonpositive_rho[OF pair direction True sigma])
next
 case False
 have rho: "0<rho" using False by arith
 show ?thesis
 proof (cases "sigma\<le>0")
   case True
   show ?thesis by (rule bracket_one_impossible_of_nonpositive_sigma[OF pair direction rho True])
 next
   case False
   have sigma: "0<sigma" using False by arith
   show ?thesis by (rule bracket_one_impossible_positive_quadrant[OF pair direction rho sigma])
 qed
qed

lemma counterexample_leadingPoisson_zero_all_directions:
 fixes P Q :: "complex poly_operator"
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 shows "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=0"
proof -
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
   and exact: "op_comp Q P-op_comp P Q=id"
   using pair by (auto simp: is_counterexample_pair_def)
 have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have alternatives: "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=0\<or>
   biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=1"
   by (rule exactPair_leadingPoisson_zero_or_one[OF P Q sum exact])
 show ?thesis using alternatives ggv_bracket_one_input_proved[OF pair direction] by blast
qed

end
