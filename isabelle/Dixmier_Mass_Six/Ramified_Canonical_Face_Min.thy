theory Ramified_Canonical_Face_Min
  imports Ramified_Exact_Weight_Lower
begin

lemma exists_ramified_canonical_face_start:
  assumes "0<l" "T\<in>ramified_operator_algebra l" "0<rho" "ramified_pbw_support l T\<noteq>{}"
  shows "\<exists>A N. N\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T) \<and>
    (\<forall>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
      rho*ramified_pbw_top_laurent l T j+int l*sigma*int j\<le>A) \<and>
    rho*ramified_pbw_top_laurent l T N+int l*sigma*int N=A \<and>
    (\<forall>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
      rho*ramified_pbw_top_laurent l T j+int l*sigma*int j=A \<longrightarrow> N\<le>j) \<and>
    ramified_pbw_top_laurent l T N\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l T) N) \<and>
    ramified_weight_deg l rho sigma T=A"
proof -
  obtain A p where p: "p\<in>ramified_pbw_support l T" "ramified_weight l rho sigma p=A"
    and upper: "\<forall>q\<in>ramified_pbw_support l T. ramified_weight l rho sigma q\<le>A"
    using exists_ramified_pbw_support_max_weight[OF assms(4), of rho sigma] by blast
  let ?F = "{q\<in>ramified_pbw_support l T. ramified_weight l rho sigma q=A}"
  let ?O = "image snd ?F"
  have fin: "finite ?O" by (simp add: ramified_pbw_support_finite)
  have ne: "?O\<noteq>{}" using p by blast
  obtain q where q: "q\<in>?F" "snd q=Min ?O"
    using Min_in[OF fin ne] by (elim imageE) auto
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
    using high low assms(3) by simp
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
  have minN: "\<forall>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
    rho*ramified_pbw_top_laurent l T j+int l*sigma*int j=A \<longrightarrow> ?N\<le>j"
  proof (intro ballI impI)
    fix j assume j: "j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T)"
      "rho*ramified_pbw_top_laurent l T j+int l*sigma*int j=A"
    have "j\<in>?O" using ramified_pbw_top_laurent_support[OF j(1)] j(2)
      by (force simp: ramified_weight_def)
    then show "?N\<le>j" using Min_le[OF fin] q(2) by metis
  qed
  have degree: "ramified_weight_deg l rho sigma T=A"
    by (rule ramified_weight_deg_eq_of_attained_upper) (use p upper in blast)+
  show ?thesis
    by (rule exI[where x=A], rule exI[where x="?N"], intro conjI)
       (rule key allupper topA minN ramified_pbw_top_laurent_mem[OF key] degree)+
qed
end
