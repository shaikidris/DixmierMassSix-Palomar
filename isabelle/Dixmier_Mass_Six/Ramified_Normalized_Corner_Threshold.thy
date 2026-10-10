theory Ramified_Normalized_Corner_Threshold
 imports Ramified_Leading_Poisson_Constant Ramified_Corner_Parallel_Rigidity
begin

lemma ramified_positive_order_zero_face_weight_ge_rho:
 assumes l: "0<l" and rho: "0<rho" and P: "P\<in>ramified_operator_algebra l"
 and positive: "0<ramified_weight_deg l rho sigma P"
 and zero: "0\<in>polynomial_support(ramified_top_face_polynomial l rho sigma P)"
 shows "rho\<le>ramified_weight_deg l rho sigma P"
proof -
 have weight: "rho*ramified_pbw_top_laurent l P 0=ramified_weight_deg l rho sigma P"
   using zero by (simp add: ramified_top_face_polynomial_mem_support_iff)
 have coordinatepos: "0<ramified_pbw_top_laurent l P 0" using positive rho
   by (simp only: weight[symmetric] zero_less_mult_iff; arith)
 have coordinate: "1\<le>ramified_pbw_top_laurent l P 0" using coordinatepos by arith
 have "rho*1\<le>rho*ramified_pbw_top_laurent l P 0"
   by (rule mult_left_mono[OF coordinate]) (use rho in arith)
 then show ?thesis by (simp only: mult_1_right weight)
qed

lemma ramified_exact_pair_normalized_corners_positive_threshold:
 fixes d n h::nat
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0"
 and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and d: "0<d" and n: "0<n" and h: "2\<le>h"
 and Apos: "0<ramified_weight_deg l rho sigma P"
 and Dpos: "0<ramified_weight_deg l rho sigma Q"
 and Ptop: "ramified_weight l rho sigma (int d*(int l*int h-1),d*h)=ramified_weight_deg l rho sigma P"
 and Qtop: "ramified_weight l rho sigma (int n*(int l*int h-1),n*h)=ramified_weight_deg l rho sigma Q"
 shows "0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
proof -
 let ?A="ramified_weight_deg l rho sigma P"
 let ?D="ramified_weight_deg l rho sigma Q"
 let ?w="int l*int h*(rho+sigma)-rho"
 have A: "?A=int d*?w" using Ptop by (simp only: ramified_weight_def fst_conv snd_conv of_nat_mult; simp only: algebra_simps; linarith)
 have D: "?D=int n*?w" using Qtop by (simp only: ramified_weight_def fst_conv snd_conv of_nat_mult; simp only: algebra_simps; linarith)
 have dZ: "1\<le>int d" using d by simp
 have nZ: "1\<le>int n" using n by simp
 have hZ: "2\<le>int h" using h by simp
 have wpos: "0<?w" using dZ Apos by (simp only: A zero_less_mult_iff; arith)
 have wA: "?w\<le>?A"
 proof -
   have "1*?w\<le>int d*?w" by (rule mult_right_mono[OF dZ]) (use wpos in arith)
   then show ?thesis by (simp only: mult_1_left A)
 qed
 have wD: "?w\<le>?D"
 proof -
   have "1*?w\<le>int n*?w" by (rule mult_right_mono[OF nZ]) (use wpos in arith)
   then show ?thesis by (simp only: mult_1_left D)
 qed
 have lower: "int l*(rho+sigma)\<le>?D+?A"
   by (rule ramified_exact_pair_weightDeg_sum_lower[OF l rho sum Q P exact])
 show ?thesis
 proof (rule ccontr)
   assume bad: "\<not>0<?A+?D-int l*(rho+sigma)"
   have threshold: "?D+?A-int l*(rho+sigma)=0" using bad lower by arith
   have scaledthreshold: "int h*(?D+?A-int l*(rho+sigma))=int h*0" by (rule arg_cong[OF threshold])
   have relation: "rho=int h*(?A+?D)-?w" using scaledthreshold by (simp only: algebra_simps; linarith)
   have total: "0<?A+?D" using Apos Dpos by arith
   have large: "2*(?A+?D)\<le>int h*(?A+?D)"
     by (rule mult_right_mono[OF hZ]) (use total in arith)
   have lowerA: "2*(?A+?D)-?D\<le>rho"
   proof -
     have "2*(?A+?D)-?D\<le>int h*(?A+?D)-?w" by (rule diff_mono[OF large wD])
     also have "...=rho" by (rule relation[symmetric])
     finally show ?thesis .
   qed
   have lowerD: "2*(?A+?D)-?A\<le>rho"
   proof -
     have "2*(?A+?D)-?A\<le>int h*(?A+?D)-?w" by (rule diff_mono[OF large wA])
     also have "...=rho" by (rule relation[symmetric])
     finally show ?thesis .
   qed
   have expandedA: "2*(?A+?D)-?D=?A+?A+?D" by algebra
   have normalizedA: "?A+?A+?D\<le>rho" using lowerA by (simp only: expandedA)
   have expandedD: "2*(?A+?D)-?A=?D+?D+?A" by algebra
   have normalizedD: "?D+?D+?A\<le>rho" using lowerD by (simp only: expandedD)
   have Arho: "?A<rho" using normalizedA Apos Dpos by arith
   have Drho: "?D<rho" using normalizedD Apos Dpos by arith
   have starts: "0\<in>polynomial_support(ramified_top_face_polynomial l rho sigma Q) \<or>
     0\<in>polynomial_support(ramified_top_face_polynomial l rho sigma P)"
     by (rule ramified_exact_pair_threshold_zero_has_top_order_zero[OF l rho sum Q P Qnz Pnz exact threshold])
   then show False
   proof
     assume "0\<in>polynomial_support(ramified_top_face_polynomial l rho sigma Q)"
     then have "rho\<le>?D" by (rule ramified_positive_order_zero_face_weight_ge_rho[OF l rho Q Dpos])
     then show False using Drho by arith
   next
     assume "0\<in>polynomial_support(ramified_top_face_polynomial l rho sigma P)"
     then have "rho\<le>?A" by (rule ramified_positive_order_zero_face_weight_ge_rho[OF l rho P Apos])
     then show False using Arho by arith
   qed
 qed
qed

end
