theory Ramified_Shear_PBW_Support
  imports Ramified_Shear_PBW_Sum
begin
lemma ramified_cut_weight_factor:
  "rho dvd int l \<Longrightarrow> ramified_weight l rho sigma (i,j) =
    rho*(i+ramified_cut_exponent l rho sigma*int j)"
  by (simp only: ramified_weight_def fst_conv snd_conv distrib_left mult.assoc[symmetric]
      ramified_cut_exponent_weight)

lemma ramified_cut_upper_of_weight_upper:
  assumes "0<l" "T\<in>ramified_operator_algebra l" "0<rho" "rho dvd int l"
    and weight: "\<And>i j. (i,j)\<in>ramified_pbw_support l T \<Longrightarrow>
      ramified_weight l rho sigma (i,j)\<le>rho*r"
  shows "laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n)
    (r-ramified_cut_exponent l rho sigma*int n)"
proof (unfold laurent_upper_def, intro ballI)
  fix i assume "i\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n)"
  then have member: "(i,n)\<in>ramified_pbw_support l T"
    by (simp add: ramified_pbw_support_mem_iff[OF assms(1,2)]
      ramified_pbw_coeff_def Poly_Mapping.in_keys_iff)
  have "rho*(i+ramified_cut_exponent l rho sigma*int n)\<le>rho*r"
    using weight[OF member] by (simp only: ramified_cut_weight_factor[OF assms(4)])
  then have "i+ramified_cut_exponent l rho sigma*int n\<le>r" using assms(3) by simp
  then show "i\<le>r-ramified_cut_exponent l rho sigma*int n" by arith
qed

lemma ramified_cut_aut_laurent_upper:
  assumes "0<l" "T\<in>ramified_operator_algebra l" "0<rho" "rho dvd int l" "0<rho+sigma"
    and upper: "\<And>n. laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n)
      (r-ramified_cut_exponent l rho sigma*int n)"
  shows "laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l (ramified_cut_aut l rho sigma c T)) j)
    (r-ramified_cut_exponent l rho sigma*int j)"
proof -
  let ?k = "ramified_cut_exponent l rho sigma"
  have atom: "laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n *
    Poly_Mapping.lookup (ramified_shift_pbw_power l (ramified_cut_shift l rho sigma c) n) j)
    (r-?k*int j)" for n
    using laurent_upper_mul[OF upper[of n]
      ramified_cut_power_upper[OF assms(1,3,4,5), of c n j]]
    by (simp add: algebra_simps)
  show ?thesis
    by (simp only: ramified_cut_aut_pbw_coeffs_sum[OF assms(1,2)] ramified_shear_pbw_sum_def
      Poly_Mapping.lookup_sum ramified_coeff_left_linear_apply)
       (rule laurent_upper_finset_sum; simp add: atom)
qed

lemma ramified_cut_aut_weight_upper:
  assumes "0<l" "T\<in>ramified_operator_algebra l" "0<rho" "rho dvd int l" "0<rho+sigma"
    and weight: "\<And>u n. (u,n)\<in>ramified_pbw_support l T \<Longrightarrow>
      ramified_weight l rho sigma (u,n)\<le>rho*r"
    and member: "(i,j)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c T)"
  shows "ramified_weight l rho sigma (i,j)\<le>rho*r"
proof -
  have upper: "laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l (ramified_cut_aut l rho sigma c T)) j)
    (r-ramified_cut_exponent l rho sigma*int j)"
    by (rule ramified_cut_aut_laurent_upper[OF assms(1,2,3,4,5)])
       (rule ramified_cut_upper_of_weight_upper[OF assms(1,2,3,4) weight])
  have nonzero: "Poly_Mapping.lookup
    (Poly_Mapping.lookup (ramified_pbw_coeffs l (ramified_cut_aut l rho sigma c T)) j) i\<noteq>0"
    using member by (simp add: ramified_pbw_support_mem_iff[OF assms(1)
      ramified_cut_aut_mem[OF assms(1,2)]] ramified_pbw_coeff_def)
  have bound: "i\<le>r-ramified_cut_exponent l rho sigma*int j"
    using upper nonzero unfolding laurent_upper_def by (simp add: Poly_Mapping.in_keys_iff)
  then have "i+ramified_cut_exponent l rho sigma*int j\<le>r" by arith
  then have "rho*(i+ramified_cut_exponent l rho sigma*int j)\<le>rho*r"
    by (rule mult_left_mono) (use assms(3) in simp)
  then show ?thesis by (simp only: ramified_cut_weight_factor[OF assms(4)])
qed

lemma ramified_cut_aut_face_eq_translate_of_weight_upper:
  "0<l \<Longrightarrow> T\<in>ramified_operator_algebra l \<Longrightarrow> 0<rho \<Longrightarrow> rho dvd int l \<Longrightarrow>
   0<rho+sigma \<Longrightarrow>
   (\<And>i j. (i,j)\<in>ramified_pbw_support l T \<Longrightarrow> ramified_weight l rho sigma (i,j)\<le>rho*r) \<Longrightarrow>
   ramified_face_polynomial l (ramified_cut_aut l rho sigma c T) r (ramified_cut_exponent l rho sigma) =
   pcompose (ramified_face_polynomial l T r (ramified_cut_exponent l rho sigma)) [:c,1:]"
  by (intro ramified_cut_aut_face_polynomial_eq_translate ramified_cut_upper_of_weight_upper) assumption+

lemma ramified_cut_aut_face_nonempty_of_weight_point:
  assumes "0<l" "T\<in>ramified_operator_algebra l" "0<rho" "rho dvd int l" "0<rho+sigma"
    and member: "(i,j)\<in>ramified_pbw_support l T"
    and top: "ramified_weight l rho sigma (i,j)=rho*r"
    and weight: "\<And>u n. (u,n)\<in>ramified_pbw_support l T \<Longrightarrow>
      ramified_weight l rho sigma (u,n)\<le>rho*r"
  shows "\<exists>u n. (u,n)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c T) \<and>
    ramified_weight l rho sigma (u,n)=rho*r"
proof -
  let ?U = "ramified_cut_aut l rho sigma c T"
  let ?k = "ramified_cut_exponent l rho sigma"
  have nonzero: "ramified_face_polynomial l ?U r ?k\<noteq>0"
    by (simp only: ramified_cut_aut_face_eq_translate_of_weight_upper[OF assms(1,2,3,4,5) weight])
       (rule ramified_cut_face_translate_ne_zero_of_weight_point[OF assms(1,2,3,4) member top])
  then obtain n where occupied: "coeff (ramified_face_polynomial l ?U r ?k) n\<noteq>0"
    by (metis poly_eqI coeff_0)
  have support: "(r-?k*int n,n)\<in>ramified_pbw_support l ?U"
    using occupied by (simp add: ramified_face_polynomial_coeff
      ramified_pbw_support_mem_iff[OF assms(1) ramified_cut_aut_mem[OF assms(1,2)]])
  have eq: "ramified_weight l rho sigma (r-?k*int n,n)=rho*r"
    by (simp only: ramified_cut_weight_factor[OF assms(4)]) simp
  show ?thesis using support eq by blast
qed

lemma ramified_cut_aut_preserves_max_weight_data:
  assumes "0<l" "T\<in>ramified_operator_algebra l" "0<rho" "rho dvd int l" "0<rho+sigma"
    "(i,j)\<in>ramified_pbw_support l T" "ramified_weight l rho sigma (i,j)=rho*r"
    and weight: "\<And>u n. (u,n)\<in>ramified_pbw_support l T \<Longrightarrow>
      ramified_weight l rho sigma (u,n)\<le>rho*r"
  shows "(\<exists>u n. (u,n)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c T) \<and>
    ramified_weight l rho sigma (u,n)=rho*r) \<and>
    (\<forall>u n. (u,n)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c T) \<longrightarrow>
      ramified_weight l rho sigma (u,n)\<le>rho*r)"
  using ramified_cut_aut_face_nonempty_of_weight_point[OF assms(1,2,3,4,5,6,7) weight]
    ramified_cut_aut_weight_upper[OF assms(1,2,3,4,5) weight]
  by blast
end
