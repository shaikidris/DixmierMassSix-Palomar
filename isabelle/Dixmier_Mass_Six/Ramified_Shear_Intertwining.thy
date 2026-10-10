theory Ramified_Shear_Intertwining
  imports Ramified_Shear_Candidate
begin

lemma ramified_normal_eval_sum:
  "finite S \<Longrightarrow> ramified_normal_eval l (\<Sum>j\<in>S. A j) =
   (\<Sum>j\<in>S. ramified_normal_eval l (A j))"
  by (induction S rule: finite_induct) (simp_all add: ramified_normal_eval_add)

lemma ramified_shift_eval_sum:
  "finite S \<Longrightarrow> ramified_shift_eval l h (\<Sum>j\<in>S. A j) =
   (\<Sum>j\<in>S. ramified_shift_eval l h (A j))"
  by (induction S rule: finite_induct) (simp_all add: ramified_shift_eval_add)

lemma laurent_comp_sum_left:
  "finite S \<Longrightarrow> laurent_comp (\<Sum>j\<in>S. A j) T =
   (\<Sum>j\<in>S. laurent_comp (A j) T)"
proof (induction S rule: finite_induct)
  case empty
  show ?case by (simp only: sum.empty laurent_comp_zero_left)
next
  case (insert j S)
  show ?case
    by (simp only: sum.insert[OF insert.hyps] laurent_comp_add_left insert.IH)
qed

lemma laurent_comp_sum_right:
  "finite S \<Longrightarrow> laurent_linear T \<Longrightarrow>
   laurent_comp T (\<Sum>j\<in>S. A j) = (\<Sum>j\<in>S. laurent_comp T (A j))"
  by (induction S rule: finite_induct)
     (simp_all add: laurent_comp_add_right laurent_comp_zero_right)

lemma ramified_pbw_smult_single:
  "ramified_pbw_smult c (Poly_Mapping.single j f) = Poly_Mapping.single j (laurent_smult c f)"
  by (rule poly_mapping_eqI)
     (simp add: Poly_Mapping.lookup_single when_def laurent_smult_as_multiplication)

lemma ramified_pbw_smult_sum:
  "ramified_pbw_smult c (\<Sum>j\<in>S. A j) = (\<Sum>j\<in>S. ramified_pbw_smult c (A j))"
  by (rule poly_mapping_eqI)
     (simp add: Poly_Mapping.lookup_sum laurent_smult_as_multiplication sum_distrib_left)

lemma ramified_pbw_smult_add:
  "ramified_pbw_smult c (a+b) = ramified_pbw_smult c a + ramified_pbw_smult c b"
  by (rule poly_mapping_eqI)
     (simp add: Poly_Mapping.lookup_add laurent_smult_as_multiplication algebra_simps)

lemma ramified_derivative_smult_law:
  "ramified_derivative l (laurent_smult c f) = laurent_smult c (ramified_derivative l f)"
  using ramified_derivative_linear[of l] unfolding laurent_linear_def by blast

lemma pbw_column_sum_expand:
  assumes "finite S" "Poly_Mapping.keys a \<subseteq> S"
    "\<And>j. F j 0 = 0"
  shows "(\<Sum>j\<in>Poly_Mapping.keys a. F j (Poly_Mapping.lookup a j)) =
    (\<Sum>j\<in>S. F j (Poly_Mapping.lookup a j))"
  by (rule sum.mono_neutral_cong_left)
     (use assms in \<open>auto simp: Poly_Mapping.in_keys_iff\<close>)

lemma pbw_column_sum_smult:
  fixes F :: "nat \<Rightarrow> ramified_laurent \<Rightarrow> ramified_pbw_coefficients"
  assumes zero: "\<And>j. F j 0 = 0"
    and scalar: "\<And>j f. F j (laurent_smult c f) = ramified_pbw_smult c (F j f)"
  shows "(\<Sum>j\<in>Poly_Mapping.keys (ramified_pbw_smult c a).
      F j (Poly_Mapping.lookup (ramified_pbw_smult c a) j)) =
    ramified_pbw_smult c (\<Sum>j\<in>Poly_Mapping.keys a. F j (Poly_Mapping.lookup a j))"
proof -
  have "(\<Sum>j\<in>Poly_Mapping.keys (ramified_pbw_smult c a).
      F j (Poly_Mapping.lookup (ramified_pbw_smult c a) j)) =
    (\<Sum>j\<in>Poly_Mapping.keys a. F j (laurent_smult c (Poly_Mapping.lookup a j)))"
    using pbw_column_sum_expand[where S="Poly_Mapping.keys a"
      and a="ramified_pbw_smult c a" and F=F]
      ramified_pbw_smult_keys[of c a] zero by simp
  then show ?thesis by (simp add: scalar ramified_pbw_smult_sum)
qed

definition ramified_coeff_left_linear ::
  "ramified_laurent \<Rightarrow> ramified_pbw_coefficients \<Rightarrow> ramified_pbw_coefficients" where
  "ramified_coeff_left_linear f a =
    (\<Sum>j\<in>Poly_Mapping.keys a. Poly_Mapping.single j (f * Poly_Mapping.lookup a j))"

lemma ramified_coeff_left_linear_single:
  "ramified_coeff_left_linear f (Poly_Mapping.single j g) = Poly_Mapping.single j (f*g)"
  by (cases "g = 0") (simp_all add: ramified_coeff_left_linear_def)

lemma ramified_coeff_left_linear_add:
  "ramified_coeff_left_linear f (a+b) = ramified_coeff_left_linear f a + ramified_coeff_left_linear f b"
  unfolding ramified_coeff_left_linear_def
  by (rule Poly_Mapping.setsum_keys_plus_distrib)
     (simp_all add: algebra_simps Poly_Mapping.single_add)

lemma ramified_coeff_left_linear_smult:
  "ramified_coeff_left_linear f (ramified_pbw_smult c a) =
   ramified_pbw_smult c (ramified_coeff_left_linear f a)"
  unfolding ramified_coeff_left_linear_def
  by (rule pbw_column_sum_smult)
     (simp_all add: ramified_pbw_smult_single laurent_smult_as_multiplication algebra_simps)

lemma ramified_coeff_mul_mul:
  "ramified_coeff_mul (f*g) = laurent_comp (ramified_coeff_mul f) (ramified_coeff_mul g)"
  by (rule ext) (simp add: ramified_coeff_mul_def laurent_comp_def mult.assoc)

lemma ramified_normal_eval_coeff_left:
  "ramified_normal_eval l (ramified_coeff_left_linear f a) =
   laurent_comp (ramified_coeff_mul f) (ramified_normal_eval l a)"
proof -
  have expanded: "ramified_normal_eval l (ramified_coeff_left_linear f a) =
    (\<Sum>j\<in>Poly_Mapping.keys a.
      laurent_comp (ramified_coeff_mul (f * Poly_Mapping.lookup a j)) (ramified_derivative l ^^ j))"
    unfolding ramified_coeff_left_linear_def
    by (simp only: ramified_normal_eval_sum[OF Poly_Mapping.finite_keys] ramified_normal_eval_single)
  have "ramified_normal_eval l (ramified_coeff_left_linear f a) =
    (\<Sum>j\<in>Poly_Mapping.keys a.
      laurent_comp (ramified_coeff_mul (f * Poly_Mapping.lookup a j)) (ramified_derivative l ^^ j))"
    by (rule expanded)
  also have "\<dots> = laurent_comp (ramified_coeff_mul f) (ramified_normal_eval l a)"
    by (simp only: ramified_normal_eval_def
        laurent_comp_sum_right[OF Poly_Mapping.finite_keys ramified_coeff_mul_linear]
        ramified_coeff_mul_mul laurent_comp_assoc)
  finally show ?thesis .
qed

lemma ramified_shift_eval_coeff_left:
  "ramified_shift_eval l h (ramified_coeff_left_linear f a) =
   laurent_comp (ramified_coeff_mul f) (ramified_shift_eval l h a)"
proof -
  have expanded: "ramified_shift_eval l h (ramified_coeff_left_linear f a) =
    (\<Sum>j\<in>Poly_Mapping.keys a.
      laurent_comp (ramified_coeff_mul (f * Poly_Mapping.lookup a j)) (ramified_shifted_Y l h ^^ j))"
    unfolding ramified_coeff_left_linear_def
    by (simp only: ramified_shift_eval_sum[OF Poly_Mapping.finite_keys] ramified_shift_eval_single)
  have "ramified_shift_eval l h (ramified_coeff_left_linear f a) =
    (\<Sum>j\<in>Poly_Mapping.keys a.
      laurent_comp (ramified_coeff_mul (f * Poly_Mapping.lookup a j)) (ramified_shifted_Y l h ^^ j))"
    by (rule expanded)
  also have "\<dots> = laurent_comp (ramified_coeff_mul f) (ramified_shift_eval l h a)"
    by (simp only: ramified_shift_eval_def
        laurent_comp_sum_right[OF Poly_Mapping.finite_keys ramified_coeff_mul_linear]
        ramified_coeff_mul_mul laurent_comp_assoc)
  finally show ?thesis .
qed

lemma ramified_pbw_coeffs_coeff_left:
  "0 < l \<Longrightarrow> T \<in> ramified_operator_algebra l \<Longrightarrow>
   ramified_pbw_coeffs l (laurent_comp (ramified_coeff_gen l f) T) =
   ramified_coeff_left_linear f (ramified_pbw_coeffs l T)"
  by (rule ramified_pbw_coeffs_eq_of_eval)
     (simp_all add: ramified_coeff_gen_def ramified_algebra_comp
       coeff_mem_ramified_operator_algebra ramified_normal_eval_coeff_left ramified_pbw_coeffs_eval)

lemma ramified_shear_candidate_coeff_left:
  "0 < l \<Longrightarrow> T \<in> ramified_operator_algebra l \<Longrightarrow>
   ramified_shear_candidate l h (laurent_comp (ramified_coeff_gen l f) T) =
   laurent_comp (ramified_coeff_gen l f) (ramified_shear_candidate l h T)"
  by (simp add: ramified_shear_candidate_def ramified_pbw_coeffs_coeff_left
      ramified_shift_eval_coeff_left ramified_coeff_gen_def
      ramified_pbw_coeffs_coeff_left[unfolded ramified_coeff_gen_def])

definition ramified_derivative_left_linear ::
  "nat \<Rightarrow> ramified_pbw_coefficients \<Rightarrow> ramified_pbw_coefficients" where
  "ramified_derivative_left_linear l a =
   (\<Sum>j\<in>Poly_Mapping.keys a.
     Poly_Mapping.single (j+1) (Poly_Mapping.lookup a j) +
     Poly_Mapping.single j (ramified_derivative l (Poly_Mapping.lookup a j)))"

lemma ramified_derivative_left_linear_single:
  "ramified_derivative_left_linear l (Poly_Mapping.single j f) =
   Poly_Mapping.single (j+1) f + Poly_Mapping.single j (ramified_derivative l f)"
  by (cases "f = 0") (simp_all add: ramified_derivative_left_linear_def
      laurent_linear_zero_apply ramified_derivative_linear)

lemma ramified_derivative_left_linear_add:
  "ramified_derivative_left_linear l (a+b) =
   ramified_derivative_left_linear l a + ramified_derivative_left_linear l b"
  unfolding ramified_derivative_left_linear_def
  by (rule Poly_Mapping.setsum_keys_plus_distrib)
     (simp_all add: ramified_derivative_linear[unfolded laurent_linear_def]
       laurent_linear_zero_apply ramified_derivative_linear Poly_Mapping.single_add algebra_simps)

lemma ramified_derivative_left_linear_smult:
  "ramified_derivative_left_linear l (ramified_pbw_smult c a) =
   ramified_pbw_smult c (ramified_derivative_left_linear l a)"
  unfolding ramified_derivative_left_linear_def
  by (rule pbw_column_sum_smult)
     (simp_all add: ramified_pbw_smult_add ramified_pbw_smult_single
       ramified_derivative_smult_law laurent_linear_zero_apply ramified_derivative_linear)

lemma laurent_comp_funpow_Suc:
  "laurent_comp T (T ^^ j) = (T ^^ (j+1))"
  by (simp add: laurent_comp_def funpow.simps comp_def)

lemma ramified_normal_eval_derivative_left:
  "ramified_normal_eval l (ramified_derivative_left_linear l a) =
   laurent_comp (ramified_derivative l) (ramified_normal_eval l a)"
proof -
  have atom: "laurent_comp (ramified_derivative l)
      (laurent_comp (ramified_coeff_mul f) (ramified_derivative l ^^ j)) =
    laurent_comp (ramified_coeff_mul f) (ramified_derivative l ^^ (j+1)) +
      laurent_comp (ramified_coeff_mul (ramified_derivative l f)) (ramified_derivative l ^^ j)"
    for f j
    by (simp only: laurent_comp_assoc[symmetric] ramified_normal_order laurent_comp_add_left;
        simp only: laurent_comp_assoc laurent_comp_funpow_Suc)
  have expanded: "ramified_normal_eval l (ramified_derivative_left_linear l a) =
    (\<Sum>j\<in>Poly_Mapping.keys a.
      laurent_comp (ramified_coeff_mul (Poly_Mapping.lookup a j)) (ramified_derivative l ^^ (j+1)) +
      laurent_comp (ramified_coeff_mul (ramified_derivative l (Poly_Mapping.lookup a j))) (ramified_derivative l ^^ j))"
    unfolding ramified_derivative_left_linear_def
    by (simp only: ramified_normal_eval_sum[OF Poly_Mapping.finite_keys]
        ramified_normal_eval_add ramified_normal_eval_single)
  have "ramified_normal_eval l (ramified_derivative_left_linear l a) =
    (\<Sum>j\<in>Poly_Mapping.keys a.
      laurent_comp (ramified_coeff_mul (Poly_Mapping.lookup a j)) (ramified_derivative l ^^ (j+1)) +
      laurent_comp (ramified_coeff_mul (ramified_derivative l (Poly_Mapping.lookup a j))) (ramified_derivative l ^^ j))"
    by (rule expanded)
  also have "\<dots> = laurent_comp (ramified_derivative l) (ramified_normal_eval l a)"
    by (simp only: ramified_normal_eval_def
        laurent_comp_sum_right[OF Poly_Mapping.finite_keys ramified_derivative_linear] atom)
  finally show ?thesis .
qed

lemma ramified_shift_eval_derivative_left:
  "ramified_shift_eval l h (ramified_derivative_left_linear l a) =
   laurent_comp (ramified_shifted_Y l h) (ramified_shift_eval l h a)"
proof -
  have atom: "laurent_comp (ramified_shifted_Y l h)
      (laurent_comp (ramified_coeff_mul f) (ramified_shifted_Y l h ^^ j)) =
    laurent_comp (ramified_coeff_mul f) (ramified_shifted_Y l h ^^ (j+1)) +
      laurent_comp (ramified_coeff_mul (ramified_derivative l f)) (ramified_shifted_Y l h ^^ j)"
    for f j
    by (simp only: laurent_comp_assoc[symmetric] ramified_shifted_Y_normal_order laurent_comp_add_left;
        simp only: laurent_comp_assoc laurent_comp_funpow_Suc)
  have expanded: "ramified_shift_eval l h (ramified_derivative_left_linear l a) =
    (\<Sum>j\<in>Poly_Mapping.keys a.
      laurent_comp (ramified_coeff_mul (Poly_Mapping.lookup a j)) (ramified_shifted_Y l h ^^ (j+1)) +
      laurent_comp (ramified_coeff_mul (ramified_derivative l (Poly_Mapping.lookup a j))) (ramified_shifted_Y l h ^^ j))"
    unfolding ramified_derivative_left_linear_def
    by (simp only: ramified_shift_eval_sum[OF Poly_Mapping.finite_keys]
        ramified_shift_eval_add ramified_shift_eval_single)
  have "ramified_shift_eval l h (ramified_derivative_left_linear l a) =
    (\<Sum>j\<in>Poly_Mapping.keys a.
      laurent_comp (ramified_coeff_mul (Poly_Mapping.lookup a j)) (ramified_shifted_Y l h ^^ (j+1)) +
      laurent_comp (ramified_coeff_mul (ramified_derivative l (Poly_Mapping.lookup a j))) (ramified_shifted_Y l h ^^ j))"
    by (rule expanded)
  also have "\<dots> = laurent_comp (ramified_shifted_Y l h) (ramified_shift_eval l h a)"
    by (simp only: ramified_shift_eval_def
        laurent_comp_sum_right[OF Poly_Mapping.finite_keys ramified_shifted_Y_linear] atom)
  finally show ?thesis .
qed

lemma ramified_pbw_coeffs_derivative_left:
  "0 < l \<Longrightarrow> T \<in> ramified_operator_algebra l \<Longrightarrow>
   ramified_pbw_coeffs l (laurent_comp (ramified_Y_gen l) T) =
   ramified_derivative_left_linear l (ramified_pbw_coeffs l T)"
  by (rule ramified_pbw_coeffs_eq_of_eval)
     (simp_all add: ramified_Y_gen_def ramified_algebra_comp
       derivative_mem_ramified_operator_algebra ramified_normal_eval_derivative_left ramified_pbw_coeffs_eval)

lemma ramified_shear_candidate_derivative_left:
  "0 < l \<Longrightarrow> T \<in> ramified_operator_algebra l \<Longrightarrow>
   ramified_shear_candidate l h (laurent_comp (ramified_Y_gen l) T) =
   laurent_comp (ramified_shifted_Y l h) (ramified_shear_candidate l h T)"
  by (simp add: ramified_shear_candidate_def ramified_pbw_coeffs_derivative_left
      ramified_shift_eval_derivative_left)
end
