theory Ramified_Top_Face_Polynomial
  imports Ramified_Canonical_Face_Max
begin
definition ramified_top_face_polynomial ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> laurent_operator \<Rightarrow> complex poly" where
  "ramified_top_face_polynomial l rho sigma T =
    (\<Sum>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
      monom (if rho*ramified_pbw_top_laurent l T j+int l*sigma*int j=ramified_weight_deg l rho sigma T
        then ramified_pbw_coeff l T (ramified_pbw_top_laurent l T j) j else 0) j)"

lemma ramified_top_face_polynomial_coeff:
  "coeff (ramified_top_face_polynomial l rho sigma T) j =
    (if j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T) then
     if rho*ramified_pbw_top_laurent l T j+int l*sigma*int j=ramified_weight_deg l rho sigma T
     then ramified_pbw_coeff l T (ramified_pbw_top_laurent l T j) j else 0 else 0)"
  by (simp add: ramified_top_face_polynomial_def coeff_sum)

lemma ramified_top_face_polynomial_mem_support_iff:
  "j\<in>polynomial_support (ramified_top_face_polynomial l rho sigma T) \<longleftrightarrow>
    j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T) \<and>
    rho*ramified_pbw_top_laurent l T j+int l*sigma*int j=ramified_weight_deg l rho sigma T"
  using ramified_pbw_top_laurent_mem[of j l T]
  by (auto simp: polynomial_support_def ramified_top_face_polynomial_coeff
      ramified_pbw_coeff_def Poly_Mapping.in_keys_iff)

lemma ramified_top_face_polynomial_support:
  "polynomial_support (ramified_top_face_polynomial l rho sigma T) =
    {j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
     rho*ramified_pbw_top_laurent l T j+int l*sigma*int j=ramified_weight_deg l rho sigma T}"
  by (auto simp: ramified_top_face_polynomial_mem_support_iff)

lemma ramified_top_face_polynomial_coeff_of_mem_support:
  "j\<in>polynomial_support (ramified_top_face_polynomial l rho sigma T) \<Longrightarrow>
   coeff (ramified_top_face_polynomial l rho sigma T) j =
   ramified_pbw_coeff l T (ramified_pbw_top_laurent l T j) j"
  by (simp add: ramified_top_face_polynomial_mem_support_iff ramified_top_face_polynomial_coeff)

lemma ramified_top_face_polynomial_ne_zero:
  assumes "0<l" "T\<in>ramified_operator_algebra l" "0<rho" "T\<noteq>0"
  shows "ramified_top_face_polynomial l rho sigma T\<noteq>0"
proof -
  obtain A N where N: "N\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T)"
    "rho*ramified_pbw_top_laurent l T N+int l*sigma*int N=A"
    "ramified_weight_deg l rho sigma T=A"
    using exists_ramified_canonical_face_endpoint[OF assms(3)
      ramified_pbw_support_nonempty_of_ne_zero[OF assms(1,2,4)], of sigma] by blast
  have "N\<in>polynomial_support (ramified_top_face_polynomial l rho sigma T)"
    using N by (simp add: ramified_top_face_polynomial_mem_support_iff)
  then show ?thesis by (auto simp: polynomial_support_def)
qed

lemma ramified_top_face_polynomial_nat_degree_of_endpoint:
  assumes "N\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T)"
    "rho*ramified_pbw_top_laurent l T N+int l*sigma*int N=ramified_weight_deg l rho sigma T"
    "\<forall>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
      rho*ramified_pbw_top_laurent l T j+int l*sigma*int j=ramified_weight_deg l rho sigma T \<longrightarrow> j\<le>N"
  shows "degree (ramified_top_face_polynomial l rho sigma T)=N"
proof (rule antisym)
  show "degree (ramified_top_face_polynomial l rho sigma T)\<le>N"
  proof (rule degree_le, intro allI impI)
    fix j assume "N<j"
    then have "j\<notin>polynomial_support (ramified_top_face_polynomial l rho sigma T)"
      using assms(3) by (auto simp: ramified_top_face_polynomial_mem_support_iff)
    then show "coeff (ramified_top_face_polynomial l rho sigma T) j=0"
      by (simp add: polynomial_support_def)
  qed
  have "coeff (ramified_top_face_polynomial l rho sigma T) N\<noteq>0"
    using ramified_top_face_polynomial_mem_support_iff[of N l rho sigma T] assms(1,2)
    by (simp only: polynomial_support_def mem_Collect_eq)
  then show "N\<le>degree (ramified_top_face_polynomial l rho sigma T)" by (rule le_degree)
qed
end
