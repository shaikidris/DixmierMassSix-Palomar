theory Ramified_Canonical_Face_Max
  imports "Ramified_Shear_PBW_Support"
begin

definition laurent_top_exponent :: "ramified_laurent \<Rightarrow> int" where
  "laurent_top_exponent f = (if Poly_Mapping.keys f={} then 0 else Max (Poly_Mapping.keys f))"

lemma laurent_top_exponent_upper:
  "i\<in>Poly_Mapping.keys f \<Longrightarrow> i\<le>laurent_top_exponent f"
  by (auto simp: laurent_top_exponent_def intro: Max_ge)

lemma laurent_top_exponent_mem:
  "f\<noteq>0 \<Longrightarrow> laurent_top_exponent f\<in>Poly_Mapping.keys f"
  by (simp add: laurent_top_exponent_def Poly_Mapping.keys_eq_empty Max_in)

definition ramified_pbw_top_laurent ::
  "nat \<Rightarrow> laurent_operator \<Rightarrow> nat \<Rightarrow> int" where
  "ramified_pbw_top_laurent l T j = laurent_top_exponent (Poly_Mapping.lookup (ramified_pbw_coeffs l T) j)"

lemma ramified_pbw_top_laurent_upper:
  "laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l T) j) (ramified_pbw_top_laurent l T j)"
  by (simp add: laurent_upper_def ramified_pbw_top_laurent_def laurent_top_exponent_upper)

lemma ramified_pbw_top_laurent_mem:
  "j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T) \<Longrightarrow>
   ramified_pbw_top_laurent l T j\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l T) j)"
  by (unfold ramified_pbw_top_laurent_def; rule laurent_top_exponent_mem)
     (simp add: Poly_Mapping.in_keys_iff)

lemma ramified_pbw_top_laurent_support:
  "j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T) \<Longrightarrow>
   (ramified_pbw_top_laurent l T j,j)\<in>ramified_pbw_support l T"
  by (auto simp: ramified_pbw_support_def intro!: bexI[where x=j] image_eqI[where x="ramified_pbw_top_laurent l T j"] ramified_pbw_top_laurent_mem)

lemma ramified_pbw_support_nonempty_of_ne_zero:
  assumes "0<l" "T\<in>ramified_operator_algebra l" "T\<noteq>0"
  shows "ramified_pbw_support l T\<noteq>{}"
proof
  assume empty: "ramified_pbw_support l T={}"
  have "Poly_Mapping.keys (ramified_pbw_coeffs l T)={}"
    using ramified_pbw_top_laurent_support[of _ l T] empty by blast
  then have "ramified_pbw_coeffs l T=0" by simp
  then have "T=0" using ramified_pbw_coeffs_eval[OF assms(1,2)] by simp
  then show False using assms(3) by contradiction
qed

lemma ramified_exact_pair_support_nonempty:
  assumes "0<l" "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "laurent_comp P Q-laurent_comp Q P=id"
  shows "ramified_pbw_support l P\<noteq>{} \<and> ramified_pbw_support l Q\<noteq>{}"
proof -
  have nzid: "(id::laurent_operator)\<noteq>0"
    by (metis id_apply zero_fun_def zero_neq_one)
  have linP: "laurent_linear P" by (rule ramified_operator_algebra_linear[OF assms(2)])
  have linQ: "laurent_linear Q" by (rule ramified_operator_algebra_linear[OF assms(3)])
  have P: "P\<noteq>0" using assms(4) nzid linQ
    by (auto simp: laurent_comp_zero_left laurent_comp_zero_right)
  have Q: "Q\<noteq>0" using assms(4) nzid linP
    by (auto simp: laurent_comp_zero_left laurent_comp_zero_right)
  show ?thesis by (intro conjI ramified_pbw_support_nonempty_of_ne_zero[OF assms(1)])
    (rule assms(2) assms(3) P Q)+
qed

lemma exists_ramified_pbw_support_max_weight:
  assumes "ramified_pbw_support l T\<noteq>{}"
  shows "\<exists>A. (\<exists>p\<in>ramified_pbw_support l T. ramified_weight l rho sigma p=A) \<and>
    (\<forall>p\<in>ramified_pbw_support l T. ramified_weight l rho sigma p\<le>A)"
proof -
  let ?W = "image (ramified_weight l rho sigma) (ramified_pbw_support l T)"
  have fin: "finite ?W" by (simp add: ramified_pbw_support_finite)
  have ne: "?W\<noteq>{}" using assms by simp
  have "Max ?W\<in>?W" by (rule Max_in[OF fin ne])
  moreover have "\<And>p. p\<in>ramified_pbw_support l T \<Longrightarrow> ramified_weight l rho sigma p\<le>Max ?W"
    by (rule Max_ge[OF fin]) auto
  ultimately show ?thesis
    by (intro exI[where x="Max ?W"] conjI) (auto simp: image_iff)
qed

lemma ramified_weight_deg_eq_of_attained_upper:
  assumes "\<exists>p\<in>ramified_pbw_support l T. ramified_weight l rho sigma p=A"
    "\<forall>p\<in>ramified_pbw_support l T. ramified_weight l rho sigma p\<le>A"
  shows "ramified_weight_deg l rho sigma T=A"
proof -
  let ?W = "image (ramified_weight l rho sigma) (ramified_pbw_support l T)"
  have fin: "finite ?W" by (simp add: ramified_pbw_support_finite)
  have mem: "A\<in>?W" using assms(1) by blast
  have eq: "Max ?W=A"
    by (intro antisym Max.boundedI[OF fin] Max.coboundedI[OF fin mem])
       (use assms(2) mem in auto)
  show ?thesis using assms(1) eq by (auto simp: ramified_weight_deg_def)
qed

lemma exists_ramified_canonical_face_endpoint:
  assumes "0<rho" "ramified_pbw_support l T\<noteq>{}"
  shows "\<exists>A N. N\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T) \<and>
    (\<forall>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
      rho*ramified_pbw_top_laurent l T j+int l*sigma*int j\<le>A) \<and>
    rho*ramified_pbw_top_laurent l T N+int l*sigma*int N=A \<and>
    (\<forall>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
      rho*ramified_pbw_top_laurent l T j+int l*sigma*int j=A \<longrightarrow> j\<le>N) \<and>
    ramified_pbw_top_laurent l T N\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l T) N) \<and>
    ramified_weight_deg l rho sigma T=A"
proof -
  obtain A p where p: "p\<in>ramified_pbw_support l T" "ramified_weight l rho sigma p=A"
    and upper: "\<forall>q\<in>ramified_pbw_support l T. ramified_weight l rho sigma q\<le>A"
    using exists_ramified_pbw_support_max_weight[OF assms(2), of rho sigma] by blast
  let ?F = "{q\<in>ramified_pbw_support l T. ramified_weight l rho sigma q=A}"
  let ?O = "image snd ?F"
  have fin: "finite ?O" by (simp add: ramified_pbw_support_finite)
  have ne: "?O\<noteq>{}" using p by blast
  obtain q where q: "q\<in>?F" "snd q=Max ?O"
    using Max_in[OF fin ne] by (elim imageE) auto
  let ?N = "snd q"
  have key: "?N\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T)"
    using q(1) by (auto simp: ramified_pbw_support_def)
  have qi: "fst q\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l T) ?N)"
    using q(1) by (auto simp: ramified_pbw_support_def)
  have low: "fst q\<le>ramified_pbw_top_laurent l T ?N"
    using laurent_top_exponent_upper[OF qi] by (simp add: ramified_pbw_top_laurent_def)
  have top: "(ramified_pbw_top_laurent l T ?N,?N)\<in>ramified_pbw_support l T"
    by (rule ramified_pbw_top_laurent_support[OF key])
  have high: "rho*ramified_pbw_top_laurent l T ?N\<le>rho*fst q"
    using upper top q(1) by (auto simp: ramified_weight_def)
  have equal: "ramified_pbw_top_laurent l T ?N=fst q"
    using high low assms(1) by simp
  have topA: "rho*ramified_pbw_top_laurent l T ?N+int l*sigma*int ?N=A"
    using q(1) by (simp add: equal ramified_weight_def)
  have allupper: "\<forall>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
    rho*ramified_pbw_top_laurent l T j+int l*sigma*int j\<le>A"
  proof (intro ballI)
    fix j assume "j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T)"
    then have "(ramified_pbw_top_laurent l T j,j)\<in>ramified_pbw_support l T"
      by (rule ramified_pbw_top_laurent_support)
    then show "rho*ramified_pbw_top_laurent l T j+int l*sigma*int j\<le>A"
      using upper by (auto simp: ramified_weight_def)
  qed
  have maxN: "\<forall>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
    rho*ramified_pbw_top_laurent l T j+int l*sigma*int j=A \<longrightarrow> j\<le>?N"
  proof (intro ballI impI)
    fix j assume j: "j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T)"
      "rho*ramified_pbw_top_laurent l T j+int l*sigma*int j=A"
    have "j\<in>?O" using ramified_pbw_top_laurent_support[OF j(1)] j(2)
      by (force simp: ramified_weight_def)
    then show "j\<le>?N" using Max_ge[OF fin] q(2) by metis
  qed
  have degree: "ramified_weight_deg l rho sigma T=A"
    by (rule ramified_weight_deg_eq_of_attained_upper) (use p upper in blast)+
  show ?thesis
    by (intro exI[where x=A] exI[where x="?N"] conjI)
       (rule key allupper topA maxN ramified_pbw_top_laurent_mem[OF key] degree)+
qed
end
