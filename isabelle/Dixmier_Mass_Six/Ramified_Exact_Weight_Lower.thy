theory Ramified_Exact_Weight_Lower
  imports Ramified_Common_Integral_Face
begin

lemma ramified_exact_pair_weight_sum_lower:
  assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
    and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
    and exact: "laurent_comp P Q-laurent_comp Q P=id"
    and BP: "\<And>n. n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P) \<Longrightarrow>
      laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) (B n)"
    and CQ: "\<And>m. m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q) \<Longrightarrow>
      laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) (C m)"
    and Pupper: "\<And>n. n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P) \<Longrightarrow> rho*B n+int l*sigma*int n\<le>A"
    and Qupper: "\<And>m. m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q) \<Longrightarrow> rho*C m+int l*sigma*int m\<le>D"
  shows "int l*(rho+sigma)\<le>A+D"
proof (rule ccontr)
  assume bad: "\<not>int l*(rho+sigma)\<le>A+D"
  let ?A = "int l*(rho+sigma)-D"
  have enlarged: "\<And>n. n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P) \<Longrightarrow> rho*B n+int l*sigma*int n\<le>?A"
  proof -
    fix n assume member: "n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P)"
    show "rho*B n+int l*sigma*int n\<le>?A" using Pupper[OF member] bad by arith
  qed
  have weight: "?A+D-int l*(rho+sigma)\<le>ramified_weight l rho sigma (0,0)"
    by (simp add: ramified_weight_def)
  have nonzero: "Poly_Mapping.lookup (Poly_Mapping.lookup
    (ramified_pbw_coeffs l (laurent_comp P Q-laurent_comp Q P)) 0) 0\<noteq>0"
    by (simp only: exact ramified_pbw_coeffs_one_coeff_at_origin[OF l]; simp)
  obtain n m where n: "n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P)"
    and equality: "rho*B n+int l*sigma*int n=?A"
    using ramified_pbw_coeffs_commutator_first_weight_survivor[
      OF l rho positive P Q BP CQ enlarged Qupper weight nonzero] by blast
  show False using equality Pupper[OF n] bad by arith
qed

lemma ramified_exact_pair_weightDeg_sum_lower:
  assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
    and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
    and exact: "laurent_comp P Q-laurent_comp Q P=id"
  shows "int l*(rho+sigma)\<le>ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q"
proof -
  have Pupper: "\<And>n. n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P) \<Longrightarrow>
    rho*ramified_pbw_top_laurent l P n+int l*sigma*int n\<le>ramified_weight_deg l rho sigma P"
    using ramified_weight_deg_upper[OF ramified_pbw_top_laurent_support]
    by (simp add: ramified_weight_def)
  have Qupper: "\<And>m. m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q) \<Longrightarrow>
    rho*ramified_pbw_top_laurent l Q m+int l*sigma*int m\<le>ramified_weight_deg l rho sigma Q"
    using ramified_weight_deg_upper[OF ramified_pbw_top_laurent_support]
    by (simp add: ramified_weight_def)
  show ?thesis by (rule ramified_exact_pair_weight_sum_lower[
    OF l rho positive P Q exact ramified_pbw_top_laurent_upper ramified_pbw_top_laurent_upper Pupper Qupper])
qed

lemma ramified_exact_pair_parallel_new_weight_nonzero:
  assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
    and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
    and exact: "laurent_comp Q P-laurent_comp P Q=id"
    and Eorder: "0<snd E"
    and parallel: "int(snd E)*fst F=int(snd F)*fst E"
    and Etop: "ramified_weight l rho sigma E=ramified_weight_deg l rho sigma P"
    and Ftop: "ramified_weight l rho sigma F=ramified_weight_deg l rho sigma Q"
  shows "ramified_weight l rho sigma E\<noteq>0"
proof
  assume zero: "ramified_weight l rho sigma E=0"
  have scaled: "rho*(int(snd E)*fst F)=rho*(int(snd F)*fst E)"
    by (rule arg_cong[OF parallel])
  have ratio: "int(snd E)*ramified_weight l rho sigma F=int(snd F)*ramified_weight l rho sigma E"
    using scaled by (simp add: ramified_weight_def algebra_simps)
  have Fzero: "ramified_weight l rho sigma F=0" using ratio Eorder zero by simp
  have lower: "int l*(rho+sigma)\<le>ramified_weight_deg l rho sigma Q+ramified_weight_deg l rho sigma P"
    by (rule ramified_exact_pair_weightDeg_sum_lower[OF l rho positive Q P exact])
  have step: "0<int l*(rho+sigma)" using l positive by simp
  show False using lower step by (simp only: Etop[symmetric] Ftop[symmetric] zero Fzero; arith)
qed

end
