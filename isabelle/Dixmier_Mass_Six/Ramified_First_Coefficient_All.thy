theory Ramified_First_Coefficient_All
  imports "Ramified_PBW_Reconstruction"
begin
lemma ramified_pbw_coeffs_right_shift_zero_below:
  assumes "0<l" "T\<in>ramified_operator_algebra l" "j<m"
  shows "Poly_Mapping.lookup (ramified_pbw_coeffs l (laurent_comp T (ramified_derivative l ^^ m))) j=0"
  by (simp only: ramified_pbw_coeffs_right_shift[OF assms(1,2)] ramified_pbw_right_shift_lookup
    assms(3) if_True)

lemma ramified_pbw_coeffs_atom_product_zero_above:
  assumes "0<l" "n+m<j"
  shows "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m))) j=0"
proof (cases "j<m")
  case True
  have shape: "laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m)=
    laurent_comp (laurent_comp (ramified_pbw_atom l f n) (ramified_coeff_mul g)) (ramified_derivative l ^^ m)"
    by (simp only: ramified_pbw_atom_def laurent_comp_assoc)
  show ?thesis unfolding shape by (rule ramified_pbw_coeffs_right_shift_zero_below[OF assms(1)
    ramified_algebra_comp[OF ramified_pbw_atom_carrier coeff_mem_ramified_operator_algebra] True])
next
  case False
  have index: "j=(j-m)+m" using False by presburger
  have order: "n<j-m" using assms(2) False by presburger
  show ?thesis by (subst index)
    (simp only: ramified_pbw_coeffs_atom_product_all[OF assms(1)]
      ramified_derivative_pbw_power_zero_above[OF order] mult_zero_right)
qed

lemma ramified_pbw_coeffs_atom_commutator_zero_at_or_above:
  assumes "0<l" "n+m\<le>j"
  shows "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m)-
     laurent_comp (ramified_pbw_atom l g m) (ramified_pbw_atom l f n))) j=0"
proof (cases "n+m=j")
  case True
  then show ?thesis using ramified_pbw_coeffs_atom_commutator_top_zero[OF assms(1), of f n g m] by simp
next
  case False
  have orders: "n+m<j" "m+n<j" using assms(2) False by presburger+
  show ?thesis by (simp only: ramified_pbw_coeffs_sub[OF assms(1)
    ramified_algebra_comp[OF ramified_pbw_atom_carrier ramified_pbw_atom_carrier]
    ramified_algebra_comp[OF ramified_pbw_atom_carrier ramified_pbw_atom_carrier]]
    Poly_Mapping.lookup_minus ramified_pbw_coeffs_atom_product_zero_above[OF assms(1) orders(1)]
    ramified_pbw_coeffs_atom_product_zero_above[OF assms(1) orders(2)] diff_self)
qed

lemma ramified_pbw_key_order_bound:
  "n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P) \<Longrightarrow> n\<le>ramified_pbw_order l P"
  unfolding ramified_pbw_order_def by (intro Max_ge) auto

lemma ramified_pbw_coeffs_commutator_zero_at_or_above_orders:
  assumes "0<l" "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "ramified_pbw_order l P+ramified_pbw_order l Q\<le>j"
  shows "Poly_Mapping.lookup (ramified_pbw_coeffs l (laurent_comp P Q-laurent_comp Q P)) j=0"
unfolding ramified_pbw_coeffs_commutator_double_sum[OF assms(1,2,3)]
proof (intro sum.neutral ballI)
  fix n m assume n: "n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P)"
    and m: "m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q)"
  have "n+m\<le>j" using ramified_pbw_key_order_bound[OF n] ramified_pbw_key_order_bound[OF m]
    assms(4) by arith
  then show "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) n)
      (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) m)-
     laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) m)
      (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) n))) j=0"
    by (rule ramified_pbw_coeffs_atom_commutator_zero_at_or_above[OF assms(1)])
qed

lemma ramified_pbw_atom_zero:
  "ramified_pbw_atom l f 0=ramified_coeff_mul f"
  by (simp only: ramified_pbw_atom_def funpow.simps(1) laurent_comp_id)

lemma ramified_pbw_coeffs_coeff_atom:
  assumes "0<l"
  shows "ramified_pbw_coeffs l (ramified_pbw_atom l f n)=ramified_pbw_right_shift (Poly_Mapping.single 0 f) n"
  by (rule ramified_pbw_coeffs_eq_of_eval[OF assms ramified_pbw_atom_carrier])
    (simp only: ramified_normal_eval_right_shift ramified_normal_eval_single funpow.simps(1)
      laurent_comp_id ramified_pbw_atom_def)

lemma ramified_pbw_right_shift_single_zero_below:
  "j<n \<Longrightarrow> Poly_Mapping.lookup (ramified_pbw_right_shift (Poly_Mapping.single 0 f) n) j=0"
  by (simp only: ramified_pbw_right_shift_lookup if_True)

lemma ramified_pbw_coeffs_coeff_atom_zero_below:
  "0<l \<Longrightarrow> j<n \<Longrightarrow> Poly_Mapping.lookup (ramified_pbw_coeffs l (ramified_pbw_atom l f n)) j=0"
  by (simp only: ramified_pbw_coeffs_coeff_atom ramified_pbw_right_shift_single_zero_below)

lemma ramified_pbw_coeffs_positive_zero_product_next:
  assumes "0<l"
  shows "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f (Suc n)) (ramified_pbw_atom l g 0))) n=
    f*laurent_smult (of_nat (Suc n)) (ramified_derivative l g)"
  using ramified_pbw_coeffs_atom_product_all[OF assms, where f=f and g=g and n="Suc n" and m=0 and r=n]
  by (simp only: add_0_right ramified_derivative_pbw_power_next)

lemma ramified_pbw_coeffs_zero_positive_product_next:
  assumes "0<l"
  shows "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l g 0) (ramified_pbw_atom l f (Suc n)))) n=0"
  by (simp only: ramified_pbw_atom_zero
    ramified_pbw_coeffs_coeff_left[OF assms ramified_pbw_atom_carrier, unfolded ramified_coeff_gen_def]
    ramified_coeff_left_linear_apply ramified_pbw_coeffs_coeff_atom_zero_below[OF assms lessI]
    mult_zero_right)

lemma ramified_pbw_coeffs_positive_zero_commutator_next:
  assumes "0<l"
  shows "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f (Suc n)) (ramified_pbw_atom l g 0)-
     laurent_comp (ramified_pbw_atom l g 0) (ramified_pbw_atom l f (Suc n)))) n=
    f*laurent_smult (of_nat (Suc n)) (ramified_derivative l g)"
  by (simp only: ramified_pbw_coeffs_sub[OF assms
    ramified_algebra_comp[OF ramified_pbw_atom_carrier ramified_pbw_atom_carrier]
    ramified_algebra_comp[OF ramified_pbw_atom_carrier ramified_pbw_atom_carrier]]
    Poly_Mapping.lookup_minus ramified_pbw_coeffs_positive_zero_product_next[OF assms]
    ramified_pbw_coeffs_zero_positive_product_next[OF assms] diff_zero)

lemma laurent_smult_zero_scalar:
  "laurent_smult 0 f=0"
  by (rule poly_mapping_eqI) (simp add: laurent_smult_lookup)

lemma ramified_pbw_coeffs_atom_commutator_first_any_second:
  assumes "0<l"
  shows "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f (Suc n)) (ramified_pbw_atom l g m)-
     laurent_comp (ramified_pbw_atom l g m) (ramified_pbw_atom l f (Suc n)))) (n+m)=
    f*laurent_smult (of_nat (Suc n)) (ramified_derivative l g)-
    g*laurent_smult (of_nat m) (ramified_derivative l f)"
proof (cases m)
  case 0
  show ?thesis by (simp only: 0 add_0_right of_nat_0 laurent_smult_zero_scalar
    mult_zero_right diff_zero ramified_pbw_coeffs_positive_zero_commutator_next[OF assms])
next
  case (Suc k)
  have index: "n+Suc k=n+k+1" by presburger
  show ?thesis by (simp only: Suc index ramified_pbw_coeffs_atom_commutator_next[OF assms])
qed

lemma ramified_pbw_coeffs_atom_commutator_first_extremal:
  assumes "0<l" "laurent_upper f i" "laurent_upper g u"
    "i\<in>Poly_Mapping.keys f" "u\<in>Poly_Mapping.keys g"
  shows "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f (Suc n)) (ramified_pbw_atom l g m)-
     laurent_comp (ramified_pbw_atom l g m) (ramified_pbw_atom l f (Suc n)))) (n+m)) (i+u-int l)=
    ((of_nat (Suc n)*of_int u-of_nat m*of_int i)/of_nat l::complex)*
    Poly_Mapping.lookup f i*Poly_Mapping.lookup g u"
  by (simp only: ramified_pbw_coeffs_atom_commutator_first_any_second[OF assms(1)]
    ramified_first_contraction_extremal_coeff[OF assms(2,3,4,5)])

lemma ramified_pbw_coeffs_positive_zero_monomial_next:
  assumes "0<l"
  shows "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l (laurent_T i) (Suc j)) (ramified_pbw_atom l (laurent_T u) 0)-
     laurent_comp (ramified_pbw_atom l (laurent_T u) 0) (ramified_pbw_atom l (laurent_T i) (Suc j)))) j=
    laurent_smult ((of_nat (Suc j)*of_int u)/of_nat l::complex) (laurent_T (i+u-int l))"
  by (subst ramified_pbw_coeffs_positive_zero_commutator_next[OF assms];
      simp only: ramified_derivative_T; rule poly_mapping_eqI)
     (simp add: laurent_T_def laurent_smult_single Poly_Mapping.mult_single
       Poly_Mapping.lookup_single when_def algebra_simps)

lemma ramified_coeff_gen_commute:
  "laurent_comp (ramified_coeff_mul f) (ramified_coeff_mul g)-
   laurent_comp (ramified_coeff_mul g) (ramified_coeff_mul f)=0"
  by (rule ext) (simp add: laurent_comp_def ramified_coeff_mul_def mult.left_commute)

end
