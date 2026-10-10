theory Ramified_Companion_Root_Budget
 imports Ramified_Companion_Bracket_Order
   "Derivative_Bracket_Roots"
   "Complex_Root_Budget"
begin

lemma ramified_source_companion_top_face_root_count:
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Fnz: "F\<noteq>0"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=
   ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=
   ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 shows "card(set_mset(proots(ramified_top_face_polynomial l rho sigma P)))\<le>
   degree(ramified_top_face_polynomial l rho sigma (-F))"
proof -
 let ?g="ramified_top_face_polynomial l rho sigma P"
 let ?f="ramified_top_face_polynomial l rho sigma (-F)"
 let ?A="of_int(ramified_weight_deg l rho sigma P)/(of_nat l*of_int rho)::complex"
 let ?B="of_int(ramified_weight_deg l rho sigma (-F))/(of_nat l*of_int rho)::complex"
 have scalar: "[:?A:]*(pderiv ?f*?g)-[:?B:]*(?f*pderiv ?g)=?g"
   by (rule native_ramified_source_bracket_scalar[OF l rho sum P F Pnz Fnz degree face Fweight])
 have g: "?g\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l P rho Pnz])
 have sum_nz: "rho+sigma\<noteq>0" using sum by arith
 have weight_nz: "ramified_weight_deg l rho sigma (-F)\<noteq>0"
   using l sum_nz by (simp only: ramifiedWeightDeg_neg[OF l F] Fweight) simp
 have B: "?B\<noteq>0" using weight_nz l rho by simp
 have "card {z. poly ?g z=0}\<le>degree ?f"
   by (rule derivative_bracket_root_count[OF g B scalar])
 then show ?thesis by (simp only: set_count_proots[OF g])
qed

lemma ramified_source_companion_cut_maxRoot_budget:
 assumes l: "0<l" and rho: "0<rho" and div: "rho dvd int l" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Fnz: "F\<noteq>0"
 and weight: "ramified_weight_deg l rho sigma P=rho*r"
 and upper: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l rho sigma p\<le>ramified_weight_deg l rho sigma P"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=
   ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=
   ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 shows "degree(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma))\<le>
   degree(ramified_top_face_polynomial l rho sigma (-F))*
   max_root_mult(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma))"
proof -
 have equal: "ramified_top_face_polynomial l rho sigma P=
   ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)"
   by (rule ramified_top_face_polynomial_eq_cut_face[OF l P rho div weight upper])
 have bound: "card(set_mset(proots(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma))))\<le>
   degree(ramified_top_face_polynomial l rho sigma (-F))"
   using ramified_source_companion_top_face_root_count[OF l rho sum P F Pnz Fnz degree face Fweight]
   by (simp only: equal)
 show ?thesis by (rule complex_polynomial_companion_root_budget[OF bound])
qed

lemma ramified_cut_endpoint_grade_nonpositive_of_companion:
 fixes rho sigma r::int and l N M m::nat
 assumes l: "0<l" and rho: "0<rho" and div: "rho dvd int l" and sum: "0<rho+sigma"
 and M: "0<M"
 and companion: "r*int M=(int l+ramified_cut_exponent l rho sigma)*int N"
 and roots: "N\<le>M*m"
 shows "r-(ramified_cut_exponent l rho sigma+int l)*int m\<le>0"
proof -
 have positive: "0<int l+ramified_cut_exponent l rho sigma"
   using ramified_cut_exponent_gt_neg_index[OF l rho div sum] by arith
 have cast_roots: "int N\<le>int M*int m" using roots by (simp only: of_nat_mult[symmetric] of_nat_le_iff)
 have product: "(int l+ramified_cut_exponent l rho sigma)*int N\<le>
   (int l+ramified_cut_exponent l rho sigma)*(int M*int m)"
   by (rule mult_left_mono[OF cast_roots]) (use positive in arith)
 have factor: "(r-(ramified_cut_exponent l rho sigma+int l)*int m)*int M\<le>0"
   using product by (simp only: companion[symmetric]; simp add: algebra_simps)
 have Mpos: "0<int M" using M by simp
 show ?thesis using factor Mpos by (simp only: mult_le_0_iff) auto
qed

lemma ramified_source_companion_endpoint_degree_identity:
 assumes l: "0<l" and rho: "0<rho" and div: "rho dvd int l" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Fnz: "F\<noteq>0"
 and weight: "ramified_weight_deg l rho sigma P=rho*r"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and Pdegree: "0<degree(ramified_top_face_polynomial l rho sigma P)"
 and Fdegree: "2\<le>degree(ramified_top_face_polynomial l rho sigma (-F))"
 shows "r*int(degree(ramified_top_face_polynomial l rho sigma (-F)))=
   (int l+ramified_cut_exponent l rho sigma)*int(degree(ramified_top_face_polynomial l rho sigma P))"
proof -
 let ?g="ramified_top_face_polynomial l rho sigma P"
 let ?f="ramified_top_face_polynomial l rho sigma (-F)"
 let ?den="of_nat l*of_int rho::complex"
 let ?A="of_int(ramified_weight_deg l rho sigma P)/?den"
 let ?B="of_int(ramified_weight_deg l rho sigma (-F))/?den"
 have scalar: "[:?A:]*(pderiv ?f*?g)-[:?B:]*(?f*pderiv ?g)=?g"
   by (rule native_ramified_source_bracket_scalar[OF l rho sum P F Pnz Fnz degree face Fweight])
 have balance: "?A*of_nat(degree ?f)=?B*of_nat(degree ?g)"
   by (rule derivative_bracket_top_degree_balance[OF Pdegree Fdegree scalar])
 have den: "?den\<noteq>0" using l rho by simp
 have scaled: "(?A*of_nat(degree ?f))*?den=(?B*of_nat(degree ?g))*?den"
   by (rule arg_cong[OF balance])
 have raw: "(of_int(ramified_weight_deg l rho sigma P)::complex)*of_nat(degree ?f)=
   of_int(ramified_weight_deg l rho sigma (-F))*of_nat(degree ?g)"
   using scaled den by (simp add: divide_inverse mult_ac)
 have cast_nat: "(of_int(int n)::complex)=of_nat n" for n by simp
 have grouped: "(of_int(ramified_weight_deg l rho sigma P*int(degree ?f))::complex)=
   of_int(ramified_weight_deg l rho sigma (-F)*int(degree ?g))"
   using raw by (simp only: of_int_mult cast_nat)
 have integers: "ramified_weight_deg l rho sigma P*int(degree ?f)=
   ramified_weight_deg l rho sigma (-F)*int(degree ?g)"
   using grouped by (simp only: of_int_eq_iff)
 have cut: "rho*ramified_cut_exponent l rho sigma=int l*sigma"
   using ramified_cut_weight_factor[OF div, where i=0 and j=1 and sigma=sigma]
   by (simp add: ramified_weight_def)
 have factor_weight: "rho*(int l+ramified_cut_exponent l rho sigma)=int l*(rho+sigma)"
 proof -
   have "rho*(int l+ramified_cut_exponent l rho sigma)=rho*int l+rho*ramified_cut_exponent l rho sigma" by algebra
   also have "...=rho*int l+int l*sigma" by (simp only: cut)
   also have "...=int l*(rho+sigma)" by algebra
   finally show ?thesis .
 qed
 have raw_integer: "(rho*r)*int(degree ?f)=(int l*(rho+sigma))*int(degree ?g)"
   using integers by (simp only: weight ramifiedWeightDeg_neg[OF l F] Fweight)
 have expanded: "rho*(r*int(degree ?f))=rho*((int l+ramified_cut_exponent l rho sigma)*int(degree ?g))"
 proof -
   have "rho*(r*int(degree ?f))=(rho*r)*int(degree ?f)" by algebra
   also have "...=(int l*(rho+sigma))*int(degree ?g)" by (rule raw_integer)
   also have "...=(rho*(int l+ramified_cut_exponent l rho sigma))*int(degree ?g)"
     by (simp only: factor_weight)
   also have "...=rho*((int l+ramified_cut_exponent l rho sigma)*int(degree ?g))" by algebra
   finally show ?thesis .
 qed
 have rho_ne: "rho\<noteq>0" using rho by arith
 show ?thesis using expanded by (simp only: mult_left_cancel[OF rho_ne])
qed

lemma ramified_source_companion_top_face_degree_pos:
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Fnz: "F\<noteq>0"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and Pdegree: "0<degree(ramified_top_face_polynomial l rho sigma P)"
 shows "0<degree(ramified_top_face_polynomial l rho sigma (-F))"
proof -
 let ?g="ramified_top_face_polynomial l rho sigma P"
 have roots_nonempty: "proots ?g\<noteq>{#}"
   using size_proots_complex[of ?g] Pdegree by auto
 have roots_positive: "0<card(set_mset(proots ?g))" using roots_nonempty by (auto simp: card_gt_0_iff)
 have bound: "card(set_mset(proots ?g))\<le>degree(ramified_top_face_polynomial l rho sigma (-F))"
   by (rule ramified_source_companion_top_face_root_count[OF l rho sum P F Pnz Fnz degree face Fweight])
 show ?thesis using roots_positive bound by arith
qed

lemma ramified_source_companion_cut_grade_nonpositive:
 assumes l: "0<l" and rho: "0<rho" and div: "rho dvd int l" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Fnz: "F\<noteq>0"
 and weight: "ramified_weight_deg l rho sigma P=rho*r"
 and upper: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l rho sigma p\<le>ramified_weight_deg l rho sigma P"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and Pdegree: "0<degree(ramified_top_face_polynomial l rho sigma P)"
 and Fdegree: "2\<le>degree(ramified_top_face_polynomial l rho sigma (-F))"
 shows "r-(ramified_cut_exponent l rho sigma+int l)*
   int(max_root_mult(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)))\<le>0"
proof -
 have equal: "ramified_top_face_polynomial l rho sigma P=ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)"
   by (rule ramified_top_face_polynomial_eq_cut_face[OF l P rho div weight upper])
 have budget: "degree(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma))\<le>
   degree(ramified_top_face_polynomial l rho sigma (-F))*max_root_mult(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma))"
   by (rule ramified_source_companion_cut_maxRoot_budget[OF l rho div sum P F Pnz Fnz weight upper degree face Fweight])
 have identity: "r*int(degree(ramified_top_face_polynomial l rho sigma (-F)))=
   (int l+ramified_cut_exponent l rho sigma)*int(degree(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)))"
   using ramified_source_companion_endpoint_degree_identity[OF l rho div sum P F Pnz Fnz weight degree face Fweight Pdegree Fdegree]
   by (simp only: equal)
 have positive: "0<degree(ramified_top_face_polynomial l rho sigma (-F))" using Fdegree by arith
 show ?thesis by (rule ramified_cut_endpoint_grade_nonpositive_of_companion[OF l rho div sum positive identity budget])
qed

lemma ramified_source_companion_linear_cut_grade_negative:
 assumes l: "0<l" and rho: "0<rho" and div: "rho dvd int l" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Fnz: "F\<noteq>0"
 and weight: "ramified_weight_deg l rho sigma P=rho*r"
 and upper: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l rho sigma p\<le>ramified_weight_deg l rho sigma P"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and linear: "degree(ramified_top_face_polynomial l rho sigma (-F))=1"
 and old_end: "r-(ramified_cut_exponent l rho sigma+int l)*int(degree(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)))<0"
 shows "r-(ramified_cut_exponent l rho sigma+int l)*int(max_root_mult(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)))<0"
proof -
 let ?p="ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)"
 have budget: "degree ?p\<le>max_root_mult ?p"
   using ramified_source_companion_cut_maxRoot_budget[OF l rho div sum P F Pnz Fnz weight upper degree face Fweight]
   by (simp only: linear mult_1_left)
 have cast_budget: "int(degree ?p)\<le>int(max_root_mult ?p)" using budget by simp
 have positive: "0<ramified_cut_exponent l rho sigma+int l"
   using ramified_cut_exponent_gt_neg_index[OF l rho div sum] by arith
 have product: "(ramified_cut_exponent l rho sigma+int l)*int(degree ?p)\<le>
   (ramified_cut_exponent l rho sigma+int l)*int(max_root_mult ?p)"
   by (rule mult_left_mono[OF cast_budget]) (use positive in arith)
 show ?thesis using old_end product by arith
qed

lemma ramified_source_companion_cut_grade_nonpositive_of_old_end:
 assumes l: "0<l" and rho: "0<rho" and div: "rho dvd int l" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Fnz: "F\<noteq>0"
 and weight: "ramified_weight_deg l rho sigma P=rho*r"
 and upper: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l rho sigma p\<le>ramified_weight_deg l rho sigma P"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and Pdegree: "0<degree(ramified_top_face_polynomial l rho sigma P)"
 and old_end: "r-(ramified_cut_exponent l rho sigma+int l)*int(degree(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)))<0"
 shows "r-(ramified_cut_exponent l rho sigma+int l)*int(max_root_mult(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)))\<le>0"
proof (cases "degree(ramified_top_face_polynomial l rho sigma (-F))=1")
 case True
 have strict: "r-(ramified_cut_exponent l rho sigma+int l)*int(max_root_mult(ramified_face_polynomial l P r (ramified_cut_exponent l rho sigma)))<0"
   by (rule ramified_source_companion_linear_cut_grade_negative[OF l rho div sum P F Pnz Fnz weight upper degree face Fweight True old_end])
 show ?thesis using strict by arith
next
 case False
 have positive: "0<degree(ramified_top_face_polynomial l rho sigma (-F))"
   by (rule ramified_source_companion_top_face_degree_pos[OF l rho sum P F Pnz Fnz degree face Fweight Pdegree])
 have two: "2\<le>degree(ramified_top_face_polynomial l rho sigma (-F))" using positive False by arith
 show ?thesis by (rule ramified_source_companion_cut_grade_nonpositive[OF l rho div sum P F Pnz Fnz weight upper degree face Fweight Pdegree two])
qed

end
