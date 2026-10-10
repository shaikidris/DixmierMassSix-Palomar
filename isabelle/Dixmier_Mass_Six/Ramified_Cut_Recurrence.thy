theory Ramified_Cut_Recurrence
  imports Ramified_Cut_Setup
begin
definition ramified_shift_pbw_step ::
  "nat \<Rightarrow> ramified_laurent \<Rightarrow> (nat,ramified_laurent) poly_mapping \<Rightarrow>
    (nat,ramified_laurent) poly_mapping" where
  "ramified_shift_pbw_step l h a = ramified_derivative_left_linear l a + ramified_coeff_left_linear h a"
lemma ramified_normal_eval_shift_step:
  "ramified_normal_eval l (ramified_shift_pbw_step l h a) =
    laurent_comp (ramified_shifted_Y l h) (ramified_normal_eval l a)"
  by (simp add: ramified_shift_pbw_step_def ramified_normal_eval_add
      ramified_normal_eval_derivative_left ramified_normal_eval_coeff_left
      ramified_shifted_Y_def laurent_comp_add_left)
primrec ramified_shift_pbw_power ::
  "nat \<Rightarrow> ramified_laurent \<Rightarrow> nat \<Rightarrow> (nat,ramified_laurent) poly_mapping" where
  "ramified_shift_pbw_power l h 0 = Poly_Mapping.single 0 1"
| "ramified_shift_pbw_power l h (Suc n) = ramified_shift_pbw_step l h (ramified_shift_pbw_power l h n)"
lemma ramified_shift_pbw_power_eval:
  "ramified_normal_eval l (ramified_shift_pbw_power l h n) = (ramified_shifted_Y l h ^^ n)"
proof (induction n)
  case 0
  show ?case by (simp only: ramified_shift_pbw_power.simps ramified_normal_eval_single
      ramified_coeff_mul_one funpow.simps(1) laurent_comp_id)
next
  case (Suc n)
  have step: "laurent_comp (ramified_shifted_Y l h) (ramified_shifted_Y l h ^^ n) =
    (ramified_shifted_Y l h ^^ Suc n)"
    using laurent_comp_funpow_Suc[of "ramified_shifted_Y l h" n] by simp
  show ?case
    by (simp only: ramified_shift_pbw_power.simps ramified_normal_eval_shift_step Suc.IH step)
qed
lemma ramified_shift_pbw_power_carrier:
  "(ramified_shifted_Y_gen l h ^^ n) \<in> ramified_operator_algebra l"
proof (induction n)
  case 0
  show ?case by (simp only: funpow.simps(1))
      (simp only: ramified_operator_algebra_def laurent_adjoin_id)
next
  case (Suc n)
  have "laurent_comp (ramified_shifted_Y_gen l h) (ramified_shifted_Y_gen l h ^^ n)
      \<in> ramified_operator_algebra l"
    by (rule ramified_algebra_comp[OF ramified_shifted_Y_gen_carrier Suc.IH])
  then show ?case by (simp only: funpow.simps laurent_comp_def comp_def)
qed
lemma ramified_shift_pbw_power_canonical:
  "0 < l \<Longrightarrow> ramified_pbw_coeffs l (ramified_shifted_Y_gen l h ^^ n) =
    ramified_shift_pbw_power l h n"
  by (rule ramified_pbw_coeffs_eq_of_eval)
     (assumption, rule ramified_shift_pbw_power_carrier,
       simp only: ramified_shift_pbw_power_eval ramified_shifted_Y_gen_def)
end
