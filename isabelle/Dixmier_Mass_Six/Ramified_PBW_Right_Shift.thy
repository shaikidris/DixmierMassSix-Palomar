theory Ramified_PBW_Right_Shift
  imports "Ramified_Endpoint_Coefficient"
begin
definition ramified_pbw_right_shift ::
  "ramified_pbw_coefficients \<Rightarrow> nat \<Rightarrow> ramified_pbw_coefficients" where
  "ramified_pbw_right_shift a k=(\<Sum>j\<in>Poly_Mapping.keys a. Poly_Mapping.single (j+k) (Poly_Mapping.lookup a j))"

lemma ramified_pbw_right_shift_lookup:
  "Poly_Mapping.lookup (ramified_pbw_right_shift a k) j =
    (if j<k then 0 else Poly_Mapping.lookup a (j-k))"
proof -
  have index: "\<And>u. u+k=j \<longleftrightarrow> k\<le>j \<and> u=j-k" by presburger
  show ?thesis by (cases "j<k"; cases "j-k\<in>Poly_Mapping.keys a")
    (simp_all add: ramified_pbw_right_shift_def Poly_Mapping.lookup_sum
      Poly_Mapping.lookup_single when_def index not_less Poly_Mapping.in_keys_iff)
qed

lemma ramified_pbw_right_shift_apply:
  "Poly_Mapping.lookup (ramified_pbw_right_shift a k) (j+k)=Poly_Mapping.lookup a j"
  by (simp add: ramified_pbw_right_shift_lookup)

lemma laurent_comp_funpow_add:
  "laurent_comp (D ^^ n) (D ^^ m) = (D::laurent_operator) ^^ (n+m)"
  by (rule ext) (simp add: laurent_comp_def funpow_add)

lemma ramified_normal_eval_right_shift:
  "ramified_normal_eval l (ramified_pbw_right_shift a k)=
    laurent_comp (ramified_normal_eval l a) (ramified_derivative l ^^ k)"
proof -
  have expanded: "ramified_normal_eval l (ramified_pbw_right_shift a k)=
    (\<Sum>j\<in>Poly_Mapping.keys a. laurent_comp (ramified_coeff_mul (Poly_Mapping.lookup a j))
       (ramified_derivative l ^^ (j+k)))"
    by (simp only: ramified_pbw_right_shift_def ramified_normal_eval_sum[OF Poly_Mapping.finite_keys]
      ramified_normal_eval_single)
  show ?thesis unfolding expanded by (simp only: ramified_normal_eval_def
    laurent_comp_sum_left[OF Poly_Mapping.finite_keys] laurent_comp_assoc laurent_comp_funpow_add)
qed

lemma ramified_derivative_power_carrier:
  "(ramified_derivative l ^^ n)\<in>ramified_operator_algebra l"
proof -
  have coeffzero: "ramified_coeff_mul 0=0" by (rule ext) (simp add: ramified_coeff_mul_def)
  show ?thesis using ramified_shift_pbw_power_carrier[where l=l and h=0 and n=n]
    by (simp add: ramified_shifted_Y_gen_def ramified_shifted_Y_def coeffzero)
qed

lemma ramified_pbw_coeffs_right_shift:
  assumes "0<l" "T\<in>ramified_operator_algebra l"
  shows "ramified_pbw_coeffs l (laurent_comp T (ramified_derivative l ^^ k))=
    ramified_pbw_right_shift (ramified_pbw_coeffs l T) k"
  by (intro ramified_pbw_coeffs_eq_of_eval[OF assms(1)]
      ramified_algebra_comp[OF assms(2) ramified_derivative_power_carrier])
     (simp only: ramified_normal_eval_right_shift ramified_pbw_coeffs_eval[OF assms])

definition ramified_pbw_atom ::
  "nat \<Rightarrow> ramified_laurent \<Rightarrow> nat \<Rightarrow> laurent_operator" where
  "ramified_pbw_atom l f n=laurent_comp (ramified_coeff_mul f) (ramified_derivative l ^^ n)"

lemma ramified_pbw_atom_carrier:
  "ramified_pbw_atom l f n\<in>ramified_operator_algebra l"
  by (unfold ramified_pbw_atom_def; intro ramified_algebra_comp
    coeff_mem_ramified_operator_algebra ramified_derivative_power_carrier)

lemma ramified_pbw_coeffs_atom_product_all:
  assumes "0<l"
  shows "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m))) (r+m)=
    f*Poly_Mapping.lookup (ramified_derivative_pbw_power l g n) r"
proof -
  let ?A = "laurent_comp (ramified_derivative l ^^ n) (ramified_coeff_mul g)"
  have A: "?A\<in>ramified_operator_algebra l" by (rule ramified_derivative_power_coeff_carrier)
  have B: "laurent_comp ?A (ramified_derivative l ^^ m)\<in>ramified_operator_algebra l"
    by (rule ramified_algebra_comp[OF A ramified_derivative_power_carrier])
  have shape: "laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m)=
    laurent_comp (ramified_coeff_mul f) (laurent_comp ?A (ramified_derivative l ^^ m))"
    by (simp only: ramified_pbw_atom_def laurent_comp_assoc)
  show ?thesis by (simp only: shape ramified_pbw_coeffs_coeff_left[OF assms B, unfolded ramified_coeff_gen_def]
    ramified_pbw_coeffs_right_shift[OF assms A] ramified_coeff_left_linear_apply
    ramified_pbw_right_shift_apply ramified_pbw_coeffs_derivative_pow_coeff[OF assms])
qed

lemma ramified_pbw_coeffs_atom_product_next:
  assumes "0<l"
  shows "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f (Suc j)) (ramified_pbw_atom l g (Suc k)))) (j+k+1)=
    f*laurent_smult (of_nat (Suc j)) (ramified_derivative l g)"
proof -
  have index: "j+k+1=j+Suc k" by presburger
  show ?thesis by (simp only: index ramified_pbw_coeffs_atom_product_all[OF assms]
    ramified_derivative_pbw_power_next)
qed

lemmas ramified_pbw_coeffs_sub = ramified_pbw_coeffs_diff

lemma ramified_pbw_coeffs_atom_commutator_top_zero:
  assumes "0<l"
  shows "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m)-
     laurent_comp (ramified_pbw_atom l g m) (ramified_pbw_atom l f n))) (n+m)=0"
proof -
  have first: "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m))) (n+m)=f*g"
    by (simp only: ramified_pbw_coeffs_atom_product_all[OF assms] ramified_derivative_pbw_power_top)
  have index: "n+m=m+n" by simp
  have second: "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l g m) (ramified_pbw_atom l f n))) (n+m)=g*f"
    by (subst index) (simp only: ramified_pbw_coeffs_atom_product_all[OF assms] ramified_derivative_pbw_power_top)
  show ?thesis by (simp only: ramified_pbw_coeffs_sub[OF assms
    ramified_algebra_comp[OF ramified_pbw_atom_carrier ramified_pbw_atom_carrier]
    ramified_algebra_comp[OF ramified_pbw_atom_carrier ramified_pbw_atom_carrier]]
    Poly_Mapping.lookup_minus first second) (simp add: mult.commute)
qed

lemma ramified_pbw_coeffs_atom_commutator_next:
  assumes "0<l"
  shows "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f (Suc j)) (ramified_pbw_atom l g (Suc k))-
     laurent_comp (ramified_pbw_atom l g (Suc k)) (ramified_pbw_atom l f (Suc j)))) (j+k+1)=
    f*laurent_smult (of_nat (Suc j)) (ramified_derivative l g)-
    g*laurent_smult (of_nat (Suc k)) (ramified_derivative l f)"
proof -
  have first: "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f (Suc j)) (ramified_pbw_atom l g (Suc k)))) (j+k+1)=
    f*laurent_smult (of_nat (Suc j)) (ramified_derivative l g)"
    by (rule ramified_pbw_coeffs_atom_product_next[OF assms])
  have index: "j+k+1=k+j+1" by simp
  have second: "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l g (Suc k)) (ramified_pbw_atom l f (Suc j)))) (j+k+1)=
    g*laurent_smult (of_nat (Suc k)) (ramified_derivative l f)"
    by (subst index) (rule ramified_pbw_coeffs_atom_product_next[OF assms])
  show ?thesis by (simp only: ramified_pbw_coeffs_sub[OF assms
    ramified_algebra_comp[OF ramified_pbw_atom_carrier ramified_pbw_atom_carrier]
    ramified_algebra_comp[OF ramified_pbw_atom_carrier ramified_pbw_atom_carrier]]
    Poly_Mapping.lookup_minus first second)
qed

lemma ramified_pbw_coeffs_monomial_commutator_next:
  assumes "0<l"
  shows "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l (laurent_T i) (Suc j)) (ramified_pbw_atom l (laurent_T u) (Suc k))-
     laurent_comp (ramified_pbw_atom l (laurent_T u) (Suc k)) (ramified_pbw_atom l (laurent_T i) (Suc j)))) (j+k+1)=
    laurent_smult ((of_nat (Suc j)*of_int u-of_nat (Suc k)*of_int i)/of_nat l::complex)
      (laurent_T (i+u-int l))"
  by (subst ramified_pbw_coeffs_atom_commutator_next[OF assms]; simp only: ramified_derivative_T; rule poly_mapping_eqI)
     (simp add: ramified_derivative_T laurent_T_def laurent_smult_single Poly_Mapping.mult_single
       Poly_Mapping.lookup_minus Poly_Mapping.lookup_single when_def algebra_simps diff_divide_distrib)
end
