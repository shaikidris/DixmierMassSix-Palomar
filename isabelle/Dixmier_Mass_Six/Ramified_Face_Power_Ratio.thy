theory Ramified_Face_Power_Ratio
 imports "Ramified_Leading_Poisson_Zero"
   "Wronskian_Ratio"
begin

lemma polynomial_power_ratio_of_weighted_derivative_zero:
  fixes f g :: "complex poly"
  assumes "0<A" "0<D" "f\<noteq>0" "g\<noteq>0"
    "[:of_nat D:]*(pderiv f*g)-[:of_nat A:]*(f*pderiv g)=0"
  shows "\<exists>c. c\<noteq>0 \<and> f^D=[:c:]*g^A"
proof -
  obtain a where A: "A=Suc a" using assms(1) by (cases A) auto
  obtain d where D: "D=Suc d" using assms(2) by (cases D) auto
  have br: "[:of_nat (Suc d):]*(pderiv f*g)-[:of_nat (Suc a):]*(f*pderiv g)=0"
    using assms(5) by (simp only: A D)
  have df: "pderiv (f^D) = smult (of_nat (Suc d)) (f^d) * pderiv f"
    by (simp only: D pderiv_power_Suc)
  have dg: "pderiv (g^A) = smult (of_nat (Suc a)) (g^a) * pderiv g"
    by (simp only: A pderiv_power_Suc)
  have smult_const: "smult c h = [:c:]*h" for c and h :: "complex poly" by simp
  have identity: "polynomial_wronskian (f^D) (g^A)=
    -(f^d*g^a)*([:of_nat (Suc d):]*(pderiv f*g)-[:of_nat (Suc a):]*(f*pderiv g))"
    by (simp only: polynomial_wronskian_def df dg; simp only: A D smult_const power_Suc;
      simp only: algebra_simps mult_minus_left mult_minus_right; simp only: add_uminus_conv_diff diff_self)
  have W: "polynomial_wronskian (f^D) (g^A)=0" using identity br by simp
  obtain c where ratio: "f^D=[:c:]*g^A"
    using polynomial_wronskian_zero_scalar_ratio[OF power_not_zero[OF assms(4)] W] by blast
  have "c\<noteq>0" using ratio assms(3) by auto
  then show ?thesis using ratio by blast
qed

lemma polynomial_weighted_derivative_clear_denominator:
  fixes f g :: "complex poly" and A D den :: complex
  assumes "den\<noteq>0" "[:D/den:]*(pderiv f*g)-[:A/den:]*(f*pderiv g)=0"
  shows "[:D:]*(pderiv f*g)-[:A:]*(f*pderiv g)=0"
proof -
  have mult: "[:den:]*([:D/den:]*(pderiv f*g)-[:A/den:]*(f*pderiv g))=0"
    using assms(2) by simp
  have cd: "[:den:]*[:D/den:]=[:D:]" using assms(1) by simp
  have ca: "[:den:]*[:A/den:]=[:A:]" using assms(1) by simp
  show ?thesis using mult by (simp only: right_diff_distrib mult.assoc[symmetric] cd ca)
qed

lemma ramified_exact_pair_top_face_power_ratio:
  assumes "0<l" "0<rho" "0<rho+sigma"
    "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "P\<noteq>0" "Q\<noteq>0" "laurent_comp P Q-laurent_comp Q P=id"
    "0<ramified_weight_deg l rho sigma P" "0<ramified_weight_deg l rho sigma Q"
    "0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
  shows "\<exists>c. c\<noteq>0 \<and>
    ramified_top_face_polynomial l rho sigma P ^ nat (ramified_weight_deg l rho sigma Q)=
    [:c:] * ramified_top_face_polynomial l rho sigma Q ^ nat (ramified_weight_deg l rho sigma P)"
proof -
  let ?f="ramified_top_face_polynomial l rho sigma P"
  let ?g="ramified_top_face_polynomial l rho sigma Q"
  let ?A="ramified_weight_deg l rho sigma P"
  let ?D="ramified_weight_deg l rho sigma Q"
  let ?den="of_nat l*of_int rho::complex"
  have fnz: "?f\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF assms(1,4,2,6)])
  have gnz: "?g\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF assms(1,5,2,7)])
  have den: "?den\<noteq>0" using assms(1,2) by simp
  have br: "[:of_int ?D/?den:]*(pderiv ?f*?g)-[:of_int ?A/?den:]*(?f*pderiv ?g)=0"
    by (rule ramified_exact_pair_top_face_bracket_eq_zero[OF assms(1,2,3,4,5,6,7,8,11)])
  have clear: "[:of_int ?D:]*(pderiv ?f*?g)-[:of_int ?A:]*(?f*pderiv ?g)=0"
    by (rule polynomial_weighted_derivative_clear_denominator[OF den br])
  have Acast: "of_nat (nat ?A)=(of_int ?A::complex)" using assms(9) by simp
  have Dcast: "of_nat (nat ?D)=(of_int ?D::complex)" using assms(10) by simp
  have natbr: "[:of_nat (nat ?D):]*(pderiv ?f*?g)-[:of_nat (nat ?A):]*(?f*pderiv ?g)=0"
    using clear by (simp only: Acast Dcast)
  show ?thesis by (rule polynomial_power_ratio_of_weighted_derivative_zero[OF _ _ fnz gnz natbr])
    (use assms(9,10) in auto)
qed
end
