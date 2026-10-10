theory Ramified_Companion_Diagonal_Start
 imports Ramified_Companion_Root_Budget
begin

lemma ramified_no_diagonal_start_of_source_leading_bracket:
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Fnz: "F\<noteq>0"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and m: "0<m" and point: "(int l*int m,m)\<in>ramified_pbw_support l P"
 and top: "ramified_weight l rho sigma (int l*int m,m)=ramified_weight_deg l rho sigma P"
 and minimum: "\<And>j. j\<in>polynomial_support(ramified_top_face_polynomial l rho sigma P) \<Longrightarrow> m\<le>j"
 shows False
proof -
 let ?g="ramified_top_face_polynomial l rho sigma P"
 let ?f="ramified_top_face_polynomial l rho sigma (-F)"
 let ?D="ramified_weight_deg l rho sigma P"
 let ?A="ramified_weight_deg l rho sigma (-F)"
 let ?den="of_nat l*of_int rho::complex"
 have first: "coeff ?g m\<noteq>0"
   using point ramified_top_face_coeff_of_weight[OF l P rho top]
   by (simp only: ramified_pbw_support_mem_iff[OF l P] not_False_eq_True)
 have low: "coeff ?g j=0" if "j<m" for j
 proof (rule ccontr)
   assume nonzero: "coeff ?g j\<noteq>0"
   have membership: "j\<in>polynomial_support ?g" using nonzero
     by (simp only: polynomial_support_def mem_Collect_eq not_False_eq_True)
   have bound: "m\<le>j" by (rule minimum[OF membership])
   show False using bound that by arith
 qed
 have expression: "?D=rho*(int l*int m)+int l*sigma*int m"
   using top by (simp add: ramified_weight_def)
 have integer: "?D=?A*int m"
   by (simp only: expression ramifiedWeightDeg_neg[OF l F] Fweight; algebra)
 have cast_nat: "(of_int(int m)::complex)=of_nat m" by simp
 have cast: "(of_int ?D::complex)=of_int ?A*of_nat m"
   by (simp only: integer of_int_mult cast_nat)
 have diagonal: "of_int ?D/?den=(of_int ?A/?den)*of_nat m"
   by (simp only: cast divide_inverse; algebra)
 have integer_sum_nonzero: "rho+sigma\<noteq>0" using sum by arith
 have complex_sum_nonzero: "(of_int rho+of_int sigma::complex)\<noteq>0"
   using integer_sum_nonzero by (simp only: of_int_add[symmetric] of_int_eq_0_iff not_False_eq_True)
 have beta: "(of_int ?A/?den::complex)\<noteq>0"
   using l rho complex_sum_nonzero by (simp add: ramifiedWeightDeg_neg[OF l F] Fweight)
 have scalar: "[:of_int ?D/?den:]*(pderiv ?f*?g)-[:of_int ?A/?den:]*(?f*pderiv ?g)=?g"
   by (rule native_ramified_source_bracket_scalar[OF l rho sum P F Pnz Fnz degree face Fweight])
 have impossible: "[:of_int ?D/?den:]*pderiv ?f*?g-[:of_int ?A/?den:]*?f*pderiv ?g\<noteq>?g"
   by (rule diagonal_lowest_order_bracket_ne[OF m beta first low diagonal])
 have transported: "[:of_int ?D/?den:]*pderiv ?f*?g-[:of_int ?A/?den:]*?f*pderiv ?g=?g"
   using scalar by (simp only: mult.assoc)
 show False by (rule notE[OF impossible transported])
qed

end
