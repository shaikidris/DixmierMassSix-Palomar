theory Ramified_Contraction_Weight_All
  imports Ramified_First_Coefficient_All
begin
lemma ramified_pbw_coeffs_atom_product_upper:
  assumes "0<l" "laurent_upper f B" "laurent_upper g C"
  shows "laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m))) (r+m))
    (B+C-int l*(int n-int r))"
proof -
  have bound: "laurent_upper (f*Poly_Mapping.lookup (ramified_derivative_pbw_power l g n) r)
    (B+(C-int l*(int n-int r)))"
    by (rule laurent_upper_mul[OF assms(2) ramified_derivative_pbw_power_upper[OF assms(3)]])
  show ?thesis using bound by (simp only: ramified_pbw_coeffs_atom_product_all[OF assms(1)];
    simp add: algebra_simps)
qed

lemma ramified_pbw_coeffs_atom_product_weight_upper:
  assumes "0<l" "0<rho" "laurent_upper f B" "laurent_upper g C"
    "v\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l
      (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m))) (r+m))"
  shows "ramified_weight l rho sigma (v,r+m)\<le>
    rho*(B+C)+int l*sigma*(int n+int m)-int l*(rho+sigma)*(int n-int r)"
proof -
  have bound: "v\<le>B+C-int l*(int n-int r)"
    using ramified_pbw_coeffs_atom_product_upper[OF assms(1,3,4), where n=n and m=m and r=r] assms(5)
    by (auto simp: laurent_upper_def)
  have scaled: "rho*v\<le>rho*(B+C-int l*(int n-int r))"
    by (rule mult_left_mono[OF bound]) (use assms(2) in arith)
  show ?thesis using scaled by (simp add: ramified_weight_def algebra_simps)
qed

lemma ramified_pbw_coeffs_atom_product_below_first_of_defect:
  assumes "0<l" "0<rho" "0<rho+sigma" "laurent_upper f B" "laurent_upper g C"
    "r+1\<le>n" "rho*B+int l*sigma*int n\<le>A" "rho*C+int l*sigma*int m\<le>D"
    "rho*B+int l*sigma*int n<A \<or> rho*C+int l*sigma*int m<D \<or> r+2\<le>n"
    "v\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l
      (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m))) (r+m))"
  shows "ramified_weight l rho sigma (v,r+m)<A+D-int l*(rho+sigma)"
proof -
  let ?s = "int l*(rho+sigma)"
  let ?p = "rho*B+int l*sigma*int n"
  let ?q = "rho*C+int l*sigma*int m"
  have positive: "0<?s" using assms(1,3) by (intro mult_pos_pos) simp_all
  have gap: "1\<le>int n-int r" using assms(6) by presburger
  have step: "?s\<le>?s*(int n-int r)"
    using mult_left_mono[OF gap, of ?s] positive by simp
  have weight: "ramified_weight l rho sigma (v,r+m)\<le>?p+?q-?s*(int n-int r)"
    using ramified_pbw_coeffs_atom_product_weight_upper[OF assms(1,2,4,5,10), where sigma=sigma]
    by (simp add: algebra_simps)
  consider "?p<A" | "?q<D" | "r+2\<le>n" using assms(9) by blast
  then show ?thesis
  proof cases
    case 1 show ?thesis using weight step 1 assms(8) by arith
  next
    case 2 show ?thesis using weight step 2 assms(7) by arith
  next
    case 3
    have gap2: "2\<le>int n-int r" using 3 by presburger
    have step2: "?s*2\<le>?s*(int n-int r)"
      by (rule mult_left_mono[OF gap2]) (use positive in arith)
    show ?thesis using weight step2 positive assms(7,8) by arith
  qed
qed

lemma ramified_monomial_higher_contraction_below_first:
  assumes "0<l" "0<rho" "0<rho+sigma" "j+2\<le>n"
    "v\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_derivative_pbw_power l (laurent_T u) n) j)"
  shows "ramified_weight l rho sigma (i+v,j+k)<
    ramified_weight l rho sigma (i+u,n+k)-int l*(rho+sigma)"
proof -
  have bound: "v\<le>u-int l*(int n-int j)"
    by (rule ramified_derivative_pbw_power_monomial_exponent_upper[OF assms(5)])
  have scaled: "rho*v\<le>rho*(u-int l*(int n-int j))"
    by (rule mult_left_mono[OF bound]) (use assms(2) in arith)
  have weight: "ramified_weight l rho sigma (i+v,j+k)\<le>
    ramified_weight l rho sigma (i+u,n+k)-int l*(rho+sigma)*(int n-int j)"
    using scaled by (simp add: ramified_weight_def algebra_simps)
  have positive: "0<int l*(rho+sigma)" using assms(1,3) by (intro mult_pos_pos) simp_all
  have gap: "2\<le>int n-int j" using assms(4) by presburger
  have step: "int l*(rho+sigma)*2\<le>int l*(rho+sigma)*(int n-int j)"
    by (rule mult_left_mono[OF gap]) (use positive in arith)
  show ?thesis using weight positive step by arith
qed
end
