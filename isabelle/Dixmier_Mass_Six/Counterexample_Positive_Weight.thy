theory Counterexample_Positive_Weight
 imports "One_Sided_Global_Generation"
begin

lemma positive_grade_weight_ge_rho:
 assumes rho: "0<rho" and sum: "0<rho+sigma" and grade: "0<pair_grade a"
 shows "rho\<le>pair_weight rho sigma a"
proof -
 have gap: "1\<le>int(fst a)-int(snd a)" using grade by (simp add: pair_grade_def)
 have first: "rho\<le>rho*(int(fst a)-int(snd a))"
   using mult_left_mono[OF gap, of rho] rho by simp
 have rest: "0\<le>(rho+sigma)*int(snd a)" using sum by simp
 have expand: "pair_weight rho sigma a=rho*(int(fst a)-int(snd a))+(rho+sigma)*int(snd a)"
   by (simp add: pair_weight_def algebra_simps)
 show ?thesis using first rest by (simp only: expand; arith)
qed

lemma negative_grade_weight_ge_sigma:
 assumes sigma: "0<sigma" and sum: "0<rho+sigma" and grade: "pair_grade a<0"
 shows "sigma\<le>pair_weight rho sigma a"
proof -
 have gap: "1\<le>int(snd a)-int(fst a)" using grade by (simp add: pair_grade_def)
 have first: "sigma\<le>sigma*(int(snd a)-int(fst a))"
   using mult_left_mono[OF gap, of sigma] sigma by simp
 have rest: "0\<le>(rho+sigma)*int(fst a)" using sum by simp
 have expand: "pair_weight rho sigma a=sigma*(int(snd a)-int(fst a))+(rho+sigma)*int(fst a)"
   by (simp add: pair_weight_def algebra_simps)
 show ?thesis using first rest by (simp only: expand; arith)
qed

lemma counterexample_vDeg_ge_rho_of_positive_grade:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q" and rho: "0<rho" and sum: "0<rho+sigma"
 shows "rho\<le>v_degree rho sigma P"
proof -
 obtain a where a: "a\<in>biv_support(pbw_symbol P)" and grade: "0<pair_grade a"
   using ggv_grades_opposite_proved pair by blast
 have lower: "rho\<le>pair_weight rho sigma a"
   by (rule positive_grade_weight_ge_rho[OF rho sum grade])
 show ?thesis using lower symbol_weight_le_v_degree[OF a, of rho sigma] by arith
qed

lemma counterexample_vDeg_ge_sigma_of_negative_grade:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q" and sigma: "0<sigma" and sum: "0<rho+sigma"
 shows "sigma\<le>v_degree rho sigma P"
proof -
 obtain a where a: "a\<in>biv_support(pbw_symbol P)" and grade: "pair_grade a<0"
   using ggv_grades_opposite_proved pair by blast
 have lower: "sigma\<le>pair_weight rho sigma a"
   by (rule negative_grade_weight_ge_sigma[OF sigma sum grade])
 show ?thesis using lower symbol_weight_le_v_degree[OF a, of rho sigma] by arith
qed

lemma counterexample_vDeg_pos_all_directions:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 shows "0<v_degree rho sigma P"
proof (cases "0<rho")
 case True
 have "rho\<le>v_degree rho sigma P"
   by (rule counterexample_vDeg_ge_rho_of_positive_grade[OF pair True])
      (use direction in \<open>simp add: is_direction_def\<close>)
 then show ?thesis using True by arith
next
 case False
 have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have sigma: "0<sigma" using sum False by arith
 have "sigma\<le>v_degree rho sigma P"
   by (rule counterexample_vDeg_ge_sigma_of_negative_grade[OF pair sigma sum])
 then show ?thesis using sigma by arith
qed

end
