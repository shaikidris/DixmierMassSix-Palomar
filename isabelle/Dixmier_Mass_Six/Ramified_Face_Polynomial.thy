theory Ramified_Face_Polynomial
  imports Ramified_Cut_Edge_Coeff
begin
definition ramified_face_polynomial ::
  "nat \<Rightarrow> laurent_operator \<Rightarrow> int \<Rightarrow> int \<Rightarrow> complex poly" where
  "ramified_face_polynomial l T r k =
    (\<Sum>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
      monom (ramified_pbw_coeff l T (r-k*int j) j) j)"

lemma ramified_face_polynomial_coeff:
  "coeff (ramified_face_polynomial l T r k) j = ramified_pbw_coeff l T (r-k*int j) j"
  by (cases "j \<in> Poly_Mapping.keys (ramified_pbw_coeffs l T)")
     (simp_all add: ramified_face_polynomial_def coeff_sum ramified_pbw_coeff_def Poly_Mapping.in_keys_iff)

lemma ramified_face_polynomial_ne_zero_of_coeff:
  "ramified_pbw_coeff l T (r-k*int j) j \<noteq> 0 \<Longrightarrow> ramified_face_polynomial l T r k \<noteq> 0"
  by (metis ramified_face_polynomial_coeff coeff_0)

lemma ramified_cut_weight_point_index:
  assumes "0<rho" "rho dvd int l" "ramified_weight l rho sigma (i,j) = rho*r"
  shows "i = r-ramified_cut_exponent l rho sigma*int j"
proof -
  have "rho*(i+ramified_cut_exponent l rho sigma*int j) = ramified_weight l rho sigma (i,j)"
    by (simp only: ramified_weight_def fst_conv snd_conv distrib_left mult.assoc[symmetric]
        ramified_cut_exponent_weight[OF assms(2)])
  then have "i+ramified_cut_exponent l rho sigma*int j=r"
    using assms(1,3) by simp
  then show ?thesis by arith
qed

lemma ramified_face_polynomial_ne_zero_of_weight_point:
  assumes "0<l" "T\<in>ramified_operator_algebra l" "0<rho" "rho dvd int l"
    "(i,j)\<in>ramified_pbw_support l T" "ramified_weight l rho sigma (i,j)=rho*r"
  shows "ramified_face_polynomial l T r (ramified_cut_exponent l rho sigma) \<noteq> 0"
  using ramified_pbw_support_mem_iff[OF assms(1,2), of i j] assms(5)
    ramified_cut_weight_point_index[OF assms(3,4,6)]
  by (intro ramified_face_polynomial_ne_zero_of_coeff[where j=j]) simp

lemma polynomial_translate_inverse:
  "pcompose (pcompose p [:c,1:]) [:-c,1:] = (p::complex poly)"
  by (simp only: pcompose_assoc[symmetric]) (simp add: pcompose_pCons algebra_simps)

lemma ramified_face_polynomial_translate_ne_zero:
  "ramified_face_polynomial l T r k \<noteq> 0 \<Longrightarrow>
    pcompose (ramified_face_polynomial l T r k) [:c,1:] \<noteq> 0"
  using polynomial_translate_inverse[of "ramified_face_polynomial l T r k" c]
  by (metis pcompose_0)

lemma ramified_cut_face_translate_ne_zero_of_weight_point:
  "0<l \<Longrightarrow> T\<in>ramified_operator_algebra l \<Longrightarrow> 0<rho \<Longrightarrow> rho dvd int l \<Longrightarrow>
   (i,j)\<in>ramified_pbw_support l T \<Longrightarrow> ramified_weight l rho sigma (i,j)=rho*r \<Longrightarrow>
   pcompose (ramified_face_polynomial l T r (ramified_cut_exponent l rho sigma)) [:c,1:] \<noteq> 0"
  by (intro ramified_face_polynomial_translate_ne_zero
      ramified_face_polynomial_ne_zero_of_weight_point) assumption+
end
