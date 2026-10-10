theory Ramified_Shear_Candidate
  imports Ramified_Shear_Base
begin

definition ramified_shift_eval ::
  "nat \<Rightarrow> ramified_laurent \<Rightarrow> ramified_pbw_coefficients \<Rightarrow> laurent_operator" where
  "ramified_shift_eval l h a = (\<Sum>j\<in>Poly_Mapping.keys a.
    laurent_comp (ramified_coeff_mul (Poly_Mapping.lookup a j)) (ramified_shifted_Y l h ^^ j))"

lemma ramified_shifted_Y_mem:
  "ramified_shifted_Y l h \<in> ramified_operator_algebra l"
  by (simp add: ramified_shifted_Y_def ramified_algebra_add
      derivative_mem_ramified_operator_algebra coeff_mem_ramified_operator_algebra)

lemma ramified_algebra_sum:
  "finite S \<Longrightarrow> (\<And>j. j \<in> S \<Longrightarrow> F j \<in> ramified_operator_algebra l) \<Longrightarrow>
   (\<Sum>j\<in>S. F j) \<in> ramified_operator_algebra l"
  by (induction S rule: finite_induct)
     (auto simp: ramified_operator_algebra_def intro: laurent_adjoin.add)

lemma ramified_shift_eval_mem:
  "ramified_shift_eval l h a \<in> ramified_operator_algebra l"
  unfolding ramified_shift_eval_def
  by (intro ramified_algebra_sum Poly_Mapping.finite_keys ramified_algebra_comp
      coeff_mem_ramified_operator_algebra)
     (unfold ramified_operator_algebra_def,
      rule laurent_adjoin_iterate,
      rule ramified_shifted_Y_mem[unfolded ramified_operator_algebra_def])

lemma ramified_shift_eval_carrier:
  "laurent_linear (ramified_shift_eval l h a)"
  by (rule ramified_operator_algebra_linear[OF ramified_shift_eval_mem])

definition ramified_shear_candidate ::
  "nat \<Rightarrow> ramified_laurent \<Rightarrow> laurent_operator \<Rightarrow> laurent_operator" where
  "ramified_shear_candidate l h T = ramified_shift_eval l h (ramified_pbw_coeffs l T)"

lemma ramified_shear_candidate_mem:
  "ramified_shear_candidate l h T \<in> ramified_operator_algebra l"
  by (simp add: ramified_shear_candidate_def ramified_shift_eval_mem)

lemma ramified_shift_eval_zero [simp]: "ramified_shift_eval l h 0 = 0"
  by (simp add: ramified_shift_eval_def)

lemma ramified_shift_eval_single:
  "ramified_shift_eval l h (Poly_Mapping.single j f) =
   laurent_comp (ramified_coeff_mul f) (ramified_shifted_Y l h ^^ j)"
  by (cases "f = 0")
     (simp_all add: ramified_shift_eval_def ramified_coeff_mul_def laurent_comp_def fun_eq_iff)

definition ramified_coeff_gen :: "nat \<Rightarrow> ramified_laurent \<Rightarrow> laurent_operator" where
  "ramified_coeff_gen l f = ramified_coeff_mul f"

definition ramified_Y_gen :: "nat \<Rightarrow> laurent_operator" where
  "ramified_Y_gen l = ramified_derivative l"

lemma ramified_coeff_gen_carrier:
  "ramified_coeff_gen l f \<in> ramified_operator_algebra l"
  by (simp add: ramified_coeff_gen_def coeff_mem_ramified_operator_algebra)

lemma ramified_Y_gen_carrier:
  "ramified_Y_gen l \<in> ramified_operator_algebra l"
  by (simp add: ramified_Y_gen_def derivative_mem_ramified_operator_algebra)

lemma ramified_pbw_coeffs_coeff_gen:
  "0 < l \<Longrightarrow> ramified_pbw_coeffs l (ramified_coeff_gen l f) = Poly_Mapping.single 0 f"
  by (simp add: ramified_coeff_gen_def ramified_pbw_coeffs_coeff_mul)

lemma ramified_pbw_coeffs_Y_gen:
  "0 < l \<Longrightarrow> ramified_pbw_coeffs l (ramified_Y_gen l) = Poly_Mapping.single 1 1"
  by (simp add: ramified_Y_gen_def ramified_pbw_coeffs_derivative)

lemma ramified_shear_candidate_coeff_gen:
  "0 < l \<Longrightarrow> ramified_shear_candidate l h (ramified_coeff_gen l f) = ramified_coeff_gen l f"
  by (simp add: ramified_shear_candidate_def ramified_pbw_coeffs_coeff_gen
      ramified_shift_eval_single ramified_coeff_gen_def ramified_pbw_coeffs_coeff_mul)

lemma ramified_shear_candidate_Y_gen:
  "0 < l \<Longrightarrow> ramified_shear_candidate l h (ramified_Y_gen l) = ramified_shifted_Y l h"
  by (simp add: ramified_shear_candidate_def ramified_pbw_coeffs_Y_gen
      ramified_shift_eval_single ramified_coeff_mul_one)

lemma ramified_shifted_Y_zero:
  "ramified_shifted_Y l 0 = ramified_derivative l"
  by (simp add: ramified_shifted_Y_def ramified_coeff_mul_def fun_eq_iff)

lemma ramified_shear_candidate_zero:
  "0 < l \<Longrightarrow> T \<in> ramified_operator_algebra l \<Longrightarrow>
   ramified_shear_candidate l 0 T = T"
  by (simp add: ramified_shear_candidate_def ramified_shift_eval_def
      ramified_shifted_Y_zero ramified_normal_eval_def[symmetric] ramified_pbw_coeffs_eval)

definition ramified_shift_eval_linear ::
  "nat \<Rightarrow> ramified_laurent \<Rightarrow> ramified_pbw_coefficients \<Rightarrow> laurent_operator" where
  "ramified_shift_eval_linear l h = ramified_shift_eval l h"

lemma ramified_shift_eval_linear_apply:
  "ramified_shift_eval_linear l h a = ramified_shift_eval l h a"
  by (simp add: ramified_shift_eval_linear_def)

lemma ramified_shift_eval_add:
  "ramified_shift_eval l h (a+b) = ramified_shift_eval l h a + ramified_shift_eval l h b"
  unfolding ramified_shift_eval_def
  by (rule Poly_Mapping.setsum_keys_plus_distrib)
     (simp_all add: ramified_coeff_mul_def laurent_comp_def fun_eq_iff algebra_simps)

lemma ramified_shift_eval_apply:
  "ramified_shift_eval l h a g = (\<Sum>j\<in>Poly_Mapping.keys a.
    Poly_Mapping.lookup a j * (ramified_shifted_Y l h ^^ j) g)"
proof -
  have "(\<Sum>j\<in>S. laurent_comp (ramified_coeff_mul (Poly_Mapping.lookup a j))
      (ramified_shifted_Y l h ^^ j)) g =
    (\<Sum>j\<in>S. Poly_Mapping.lookup a j * (ramified_shifted_Y l h ^^ j) g)"
    if "finite S" for S
    using that by (induction S rule: finite_induct)
      (simp_all add: laurent_comp_def ramified_coeff_mul_def)
  then show ?thesis by (simp add: ramified_shift_eval_def)
qed

lemma ramified_shift_eval_expand:
  "finite S \<Longrightarrow> Poly_Mapping.keys a \<subseteq> S \<Longrightarrow>
   ramified_shift_eval l h a g =
    (\<Sum>j\<in>S. Poly_Mapping.lookup a j * (ramified_shifted_Y l h ^^ j) g)"
  unfolding ramified_shift_eval_apply
  by (rule sum.mono_neutral_cong_left)
     (auto simp: Poly_Mapping.in_keys_iff)

lemma ramified_shift_eval_smult:
  "ramified_shift_eval l h (ramified_pbw_smult c a) = normal_smult c (ramified_shift_eval l h a)"
proof (rule ext)
  fix g
  have "ramified_shift_eval l h (ramified_pbw_smult c a) g =
      (\<Sum>j\<in>Poly_Mapping.keys a.
        laurent_smult c (Poly_Mapping.lookup a j) * (ramified_shifted_Y l h ^^ j) g)"
    using ramified_shift_eval_expand[where S="Poly_Mapping.keys a"
      and a="ramified_pbw_smult c a" and l=l and h=h and g=g]
      ramified_pbw_smult_keys[of c a] by simp
  also have "\<dots> = laurent_smult c (\<Sum>j\<in>Poly_Mapping.keys a.
      Poly_Mapping.lookup a j * (ramified_shifted_Y l h ^^ j) g)"
    by (simp add: laurent_smult_as_multiplication sum_distrib_left mult.assoc)
  also have "\<dots> = normal_smult c (ramified_shift_eval l h a) g"
    by (simp only: normal_smult_def ramified_shift_eval_apply)
  finally show "ramified_shift_eval l h (ramified_pbw_smult c a) g =
      normal_smult c (ramified_shift_eval l h a) g" .
qed

lemma ramified_pbw_coeffs_add:
  assumes "0 < l" "T \<in> ramified_operator_algebra l" "U \<in> ramified_operator_algebra l"
  shows "ramified_pbw_coeffs l (T+U) = ramified_pbw_coeffs l T + ramified_pbw_coeffs l U"
  by (rule ramified_pbw_coeffs_eq_of_eval)
     (simp_all add: assms ramified_algebra_add ramified_normal_eval_add ramified_pbw_coeffs_eval)

lemma ramified_pbw_coeffs_smult:
  assumes "0 < l" "T \<in> ramified_operator_algebra l"
  shows "ramified_pbw_coeffs l (normal_smult c T) = ramified_pbw_smult c (ramified_pbw_coeffs l T)"
  by (rule ramified_pbw_coeffs_eq_of_eval)
     (simp_all add: assms ramified_algebra_smult ramified_normal_eval_smult ramified_pbw_coeffs_eval)

lemma ramified_shear_candidate_add:
  "0 < l \<Longrightarrow> T \<in> ramified_operator_algebra l \<Longrightarrow> U \<in> ramified_operator_algebra l \<Longrightarrow>
   ramified_shear_candidate l h (T+U) = ramified_shear_candidate l h T + ramified_shear_candidate l h U"
  by (simp add: ramified_shear_candidate_def ramified_pbw_coeffs_add ramified_shift_eval_add)

lemma ramified_shear_candidate_smult:
  "0 < l \<Longrightarrow> T \<in> ramified_operator_algebra l \<Longrightarrow>
   ramified_shear_candidate l h (normal_smult c T) = normal_smult c (ramified_shear_candidate l h T)"
  by (simp add: ramified_shear_candidate_def ramified_pbw_coeffs_smult ramified_shift_eval_smult)

definition ramified_shear_linear ::
  "nat \<Rightarrow> ramified_laurent \<Rightarrow> laurent_operator \<Rightarrow> laurent_operator" where
  "ramified_shear_linear l h = ramified_shear_candidate l h"

lemma ramified_shear_linear_carrier:
  "ramified_shear_linear l h T \<in> ramified_operator_algebra l"
  by (simp add: ramified_shear_linear_def ramified_shear_candidate_mem)

lemma ramified_shear_linear_add:
  "0 < l \<Longrightarrow> T \<in> ramified_operator_algebra l \<Longrightarrow> U \<in> ramified_operator_algebra l \<Longrightarrow>
   ramified_shear_linear l h (T+U) = ramified_shear_linear l h T + ramified_shear_linear l h U"
  by (simp add: ramified_shear_linear_def ramified_shear_candidate_add)

lemma ramified_shear_linear_smult:
  "0 < l \<Longrightarrow> T \<in> ramified_operator_algebra l \<Longrightarrow>
   ramified_shear_linear l h (normal_smult c T) = normal_smult c (ramified_shear_linear l h T)"
  by (simp add: ramified_shear_linear_def ramified_shear_candidate_smult)
end
