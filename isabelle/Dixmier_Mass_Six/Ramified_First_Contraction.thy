theory Ramified_First_Contraction
  imports "Ramified_Shear_Top_Face"
begin
primrec ramified_derivative_pbw_power ::
  "nat \<Rightarrow> ramified_laurent \<Rightarrow> nat \<Rightarrow> ramified_pbw_coefficients" where
  "ramified_derivative_pbw_power l f 0=Poly_Mapping.single 0 f"
| "ramified_derivative_pbw_power l f (Suc n)=ramified_derivative_left_linear l (ramified_derivative_pbw_power l f n)"

lemma ramified_derivative_pbw_power_eval:
  "ramified_normal_eval l (ramified_derivative_pbw_power l f n)=
    laurent_comp (ramified_derivative l ^^ n) (ramified_coeff_mul f)"
proof (induction n)
  case 0
  show ?case by (simp only: ramified_derivative_pbw_power.simps ramified_normal_eval_single
    funpow.simps(1) laurent_comp_id)
next
  case (Suc n)
  show ?case by (simp only: ramified_derivative_pbw_power.simps ramified_normal_eval_derivative_left
    Suc.IH laurent_comp_assoc[symmetric] laurent_comp_funpow_Suc) (simp add: comp_def)
qed

lemma ramified_derivative_pbw_power_zero_above:
  "n<j \<Longrightarrow> Poly_Mapping.lookup (ramified_derivative_pbw_power l f n) j=0"
proof (induction n arbitrary: j)
  case 0
  then show ?case by (simp add: ramified_derivative_pbw_power.simps Poly_Mapping.lookup_single when_def)
next
  case (Suc n)
  have "j\<noteq>0" "n<j-1" "n<j" using Suc.prems by presburger+
  then show ?case by (simp add: ramified_derivative_pbw_power.simps
    ramified_derivative_left_linear_apply Suc.IH
    laurent_linear_zero_apply[OF ramified_derivative_linear])
qed

lemma ramified_derivative_pbw_power_top:
  "Poly_Mapping.lookup (ramified_derivative_pbw_power l f n) n=f"
  by (induction n) (simp_all add: ramified_derivative_pbw_power.simps
      ramified_derivative_left_linear_apply ramified_derivative_pbw_power_zero_above
      Poly_Mapping.lookup_single when_def)

lemma ramified_derivative_pbw_power_next:
  "Poly_Mapping.lookup (ramified_derivative_pbw_power l f (Suc n)) n=
    laurent_smult (of_nat (Suc n)) (ramified_derivative l f)"
proof (induction n)
  case 0
  show ?case by (rule poly_mapping_eqI)
    (simp add: ramified_derivative_pbw_power.simps ramified_derivative_left_linear_apply
    Poly_Mapping.lookup_single when_def laurent_smult_lookup)
next
  case (Suc n)
  have rec: "Poly_Mapping.lookup (ramified_derivative_pbw_power l f (Suc (Suc n))) (Suc n)=
    laurent_smult (of_nat (Suc n)) (ramified_derivative l f)+ramified_derivative l f"
    by (subst ramified_derivative_pbw_power.simps(2))
      (simp only: ramified_derivative_left_linear_apply
      Suc_not_Zero if_False diff_Suc_1 Suc.IH ramified_derivative_pbw_power_top)
  show ?case unfolding rec
    by (rule poly_mapping_eqI) (simp add: Poly_Mapping.lookup_add laurent_smult_lookup algebra_simps)
qed

lemma ramified_derivative_power_coeff_carrier:
  "laurent_comp (ramified_derivative l ^^ n) (ramified_coeff_mul f)\<in>ramified_operator_algebra l"
proof -
  have coeffzero: "ramified_coeff_mul 0=0" by (rule ext) (simp add: ramified_coeff_mul_def)
  have power: "(ramified_derivative l ^^ n)\<in>ramified_operator_algebra l"
    using ramified_shift_pbw_power_carrier[where l=l and h=0 and n=n]
    by (simp add: ramified_shifted_Y_gen_def ramified_shifted_Y_def coeffzero)
  show ?thesis by (rule ramified_algebra_comp[OF power coeff_mem_ramified_operator_algebra])
qed

lemma ramified_pbw_coeffs_derivative_pow_coeff:
  "0<l \<Longrightarrow> ramified_pbw_coeffs l (laurent_comp (ramified_derivative l ^^ n) (ramified_coeff_mul f))=
    ramified_derivative_pbw_power l f n"
  by (intro ramified_pbw_coeffs_eq_of_eval ramified_derivative_power_coeff_carrier
      ramified_derivative_pbw_power_eval) assumption

lemma ramified_pbw_coeffs_derivative_pow_top:
  "0<l \<Longrightarrow>
   Poly_Mapping.lookup (ramified_pbw_coeffs l (laurent_comp (ramified_derivative l ^^ n) (ramified_coeff_mul f))) n=f"
  by (simp only: ramified_pbw_coeffs_derivative_pow_coeff ramified_derivative_pbw_power_top)

lemma ramified_pbw_coeffs_derivative_pow_next:
  "0<l \<Longrightarrow>
   Poly_Mapping.lookup (ramified_pbw_coeffs l (laurent_comp (ramified_derivative l ^^ Suc n) (ramified_coeff_mul f))) n=
   laurent_smult (of_nat (Suc n)) (ramified_derivative l f)"
  by (simp only: ramified_pbw_coeffs_derivative_pow_coeff ramified_derivative_pbw_power_next)
end
