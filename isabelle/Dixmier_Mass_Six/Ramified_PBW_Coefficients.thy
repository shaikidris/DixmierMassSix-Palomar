theory Ramified_PBW_Coefficients
  imports "Ramified_Normal_Form"
begin

text \<open>R1A uses finite sequences indexed by derivative order, with actual
complex Laurent polynomial coefficients and arbitrary integer exponents.
This is not the pair-indexed witness carrier of the normal-span parent.
Operator multiplication is explicit composition and operator powers are
function iteration. The evaluation always belongs to the exact complex-linear
endomorphism carrier, with no restriction on the input sequence or parameter.\<close>

type_synonym ramified_pbw_coefficients = "(nat, ramified_laurent) poly_mapping"

text \<open>This first source root reuses the already accepted exact proof.\<close>
lemma ramified_derivative_X:
  "0 < l \<Longrightarrow> ramified_derivative l (laurent_T (int l)) = 1"
  by (rule ramified_derivative_X_unit)

lemma ramified_derivative_one [simp]:
  "ramified_derivative l 1 = 0"
  using ramified_derivative_single_coefficient[of l 0 1] by simp

lemma ramified_derivative_X_pow:
  assumes "0 < l"
  shows "ramified_derivative l (laurent_T (int l) ^ k) =
    laurent_smult (of_nat k) (laurent_T (int l) ^ (k - 1))"
proof (induction k)
  case 0
  show ?case by (simp add: laurent_smult_as_multiplication)
next
  case (Suc k)
  then show ?case
    by (cases k)
       (simp_all add: power_Suc ramified_derivative_mul
         ramified_derivative_X[OF assms] laurent_smult_as_multiplication
         of_nat_Suc Poly_Mapping.single_add algebra_simps)
qed

lemma ramified_iterate_smult:
  "(ramified_derivative l ^^ n) (laurent_smult c f) =
    laurent_smult c ((ramified_derivative l ^^ n) f)"
  using laurent_iterate_linear[OF ramified_derivative_linear, of n]
  unfolding laurent_linear_def by blast

lemma ramified_iterate_zero [simp]:
  "(ramified_derivative l ^^ n) 0 = 0"
  by (rule laurent_linear_zero_apply)
     (intro laurent_iterate_linear ramified_derivative_linear)

lemma ramified_derivative_pow_X_pow_diag:
  assumes "0 < l"
  shows "(ramified_derivative l ^^ k) (laurent_T (int l) ^ k) =
    laurent_smult (of_nat (fact k :: nat)) 1"
proof (induction k)
  case 0
  show ?case by (simp add: laurent_smult_as_multiplication)
next
  case (Suc k)
  have "(ramified_derivative l ^^ Suc k) (laurent_T (int l) ^ Suc k) =
    laurent_smult (of_nat (Suc k))
      ((ramified_derivative l ^^ k) (laurent_T (int l) ^ k))"
    by (simp only: funpow_Suc_right comp_apply ramified_derivative_X_pow[OF assms]
        diff_Suc_1 ramified_iterate_smult)
  also have "\<dots> = laurent_smult (of_nat (fact (Suc k) :: nat)) 1"
    by (simp add: Suc.IH laurent_smult_as_multiplication
        mult.assoc[symmetric] Poly_Mapping.mult_single algebra_simps)
  finally show ?case .
qed

lemma ramified_derivative_pow_X_pow_zero:
  assumes "0 < l" "k < j"
  shows "(ramified_derivative l ^^ j) (laurent_T (int l) ^ k) = 0"
  using assms(2)
proof (induction k arbitrary: j)
  case 0
  then obtain r where "j = Suc r" by (cases j) auto
  then show ?case
    by (simp only: funpow_Suc_right comp_apply power_0 ramified_derivative_one
        ramified_iterate_zero)
next
  case (Suc k)
  then obtain r where r: "j = Suc r" "k < r" by (cases j) auto
  show ?case
    unfolding r(1)
    by (simp only: funpow_Suc_right comp_apply ramified_derivative_X_pow[OF assms(1)]
        diff_Suc_1 ramified_iterate_smult Suc.IH[OF r(2)])
       (simp add: laurent_smult_as_multiplication)
qed

definition ramified_normal_eval ::
  "nat \<Rightarrow> ramified_pbw_coefficients \<Rightarrow> laurent_operator" where
  "ramified_normal_eval l a = (\<Sum>j\<in>Poly_Mapping.keys a.
    laurent_comp (ramified_coeff_mul (Poly_Mapping.lookup a j))
      (ramified_derivative l ^^ j))"

lemma ramified_normal_eval_apply:
  "ramified_normal_eval l a g = (\<Sum>j\<in>Poly_Mapping.keys a.
    Poly_Mapping.lookup a j * (ramified_derivative l ^^ j) g)"
proof -
  have eval_sum:
    "(\<Sum>j\<in>S. laurent_comp (ramified_coeff_mul (Poly_Mapping.lookup a j))
       (ramified_derivative l ^^ j)) g =
     (\<Sum>j\<in>S. Poly_Mapping.lookup a j * (ramified_derivative l ^^ j) g)"
    if "finite S" for S
    using that by (induction S rule: finite_induct)
      (simp_all add: laurent_comp_def ramified_coeff_mul_def)
  show ?thesis unfolding ramified_normal_eval_def by (rule eval_sum) simp
qed

lemma laurent_linear_finite_sum:
  assumes "finite S" "\<And>j. j \<in> S \<Longrightarrow> laurent_linear (F j)"
  shows "laurent_linear (\<Sum>j\<in>S. F j)"
  using assms by (induction S rule: finite_induct)
    (auto intro: laurent_linear_zero laurent_linear_add)

lemma ramified_normal_eval_linear:
  "laurent_linear (ramified_normal_eval l a)"
  unfolding ramified_normal_eval_def
  by (intro laurent_linear_finite_sum Poly_Mapping.finite_keys
      laurent_linear_comp ramified_coeff_mul_linear
      laurent_iterate_linear ramified_derivative_linear)

lemma ramified_normal_eval_zero [simp]: "ramified_normal_eval l 0 = 0"
  by (simp add: ramified_normal_eval_def)

lemma ramified_normal_eval_single:
  "ramified_normal_eval l (Poly_Mapping.single n f) =
    laurent_comp (ramified_coeff_mul f) (ramified_derivative l ^^ n)"
  by (cases "f = 0")
     (simp_all add: ramified_normal_eval_def ramified_coeff_mul_def laurent_comp_def fun_eq_iff)

lemma ramified_normal_eval_zero_coeff:
  assumes "0 < l" "ramified_normal_eval l a = 0"
  shows "Poly_Mapping.lookup a k = 0"
proof (induction k rule: less_induct)
  case (less k)
  have sum_zero:
    "(\<Sum>j\<in>Poly_Mapping.keys a. Poly_Mapping.lookup a j *
      (ramified_derivative l ^^ j) (laurent_T (int l) ^ k)) = 0"
    using fun_cong[OF assms(2), of "laurent_T (int l) ^ k"]
    by (simp add: ramified_normal_eval_apply)
  have off_diagonal:
    "Poly_Mapping.lookup a j *
      (ramified_derivative l ^^ j) (laurent_T (int l) ^ k) = 0" if "j \<noteq> k" for j
  proof -
    from that consider "j < k" | "k < j" by arith
    then show ?thesis
      by cases (simp_all add: less.IH ramified_derivative_pow_X_pow_zero[OF assms(1)])
  qed
  have sum_single:
    "(\<Sum>j\<in>Poly_Mapping.keys a. Poly_Mapping.lookup a j *
      (ramified_derivative l ^^ j) (laurent_T (int l) ^ k)) =
      Poly_Mapping.lookup a k * (ramified_derivative l ^^ k) (laurent_T (int l) ^ k)"
  proof -
    have "(\<Sum>j\<in>Poly_Mapping.keys a. Poly_Mapping.lookup a j *
      (ramified_derivative l ^^ j) (laurent_T (int l) ^ k)) =
      (\<Sum>j\<in>{k}. Poly_Mapping.lookup a j *
        (ramified_derivative l ^^ j) (laurent_T (int l) ^ k))"
      by (rule sum.mono_neutral_cong)
         (auto simp: Poly_Mapping.in_keys_iff off_diagonal)
    then show ?thesis by simp
  qed
  have product_zero:
    "Poly_Mapping.lookup a k * laurent_smult (of_nat (fact k :: nat)) 1 = 0"
    using sum_zero sum_single ramified_derivative_pow_X_pow_diag[OF assms(1), of k]
    by simp
  have scalar_nonzero:
    "(Poly_Mapping.single 0 (of_nat (fact k :: nat)) :: ramified_laurent) \<noteq> 0"
  proof
    assume z: "(Poly_Mapping.single 0 (of_nat (fact k :: nat)) :: ramified_laurent) = 0"
    have "Poly_Mapping.lookup (Poly_Mapping.single 0 (of_nat (fact k :: nat))
        :: ramified_laurent) 0 = 0"
      using z by simp
    then show False by simp
  qed
  show ?case using product_zero scalar_nonzero
    by (simp add: laurent_smult_as_multiplication)
qed

lemma ramified_coeff_mul_sub:
  "ramified_coeff_mul (f - g) = ramified_coeff_mul f - ramified_coeff_mul g"
  by (rule ext) (simp add: ramified_coeff_mul_def algebra_simps)

lemma ramified_normal_eval_add:
  "ramified_normal_eval l (a + b) = ramified_normal_eval l a + ramified_normal_eval l b"
  unfolding ramified_normal_eval_def
  by (rule Poly_Mapping.setsum_keys_plus_distrib)
     (simp_all add: ramified_coeff_mul_def laurent_comp_def fun_eq_iff algebra_simps)

lemma ramified_normal_eval_sub:
  "ramified_normal_eval l (a - b) = ramified_normal_eval l a - ramified_normal_eval l b"
proof -
  have "ramified_normal_eval l (a - b) + ramified_normal_eval l b = ramified_normal_eval l a"
    using ramified_normal_eval_add[of l "a - b" b] by simp
  then show ?thesis by (simp add: eq_diff_eq)
qed

lemma ramified_normal_eval_injective:
  assumes "0 < l"
  shows "inj (ramified_normal_eval l)"
proof (rule injI)
  fix a b assume eq: "ramified_normal_eval l a = ramified_normal_eval l b"
  have z: "ramified_normal_eval l (a - b) = 0"
    by (simp add: ramified_normal_eval_sub eq)
  show "a = b"
  proof (rule poly_mapping_eqI)
    fix k
    have "Poly_Mapping.lookup (a - b) k = 0"
      by (rule ramified_normal_eval_zero_coeff[OF assms z])
    then show "Poly_Mapping.lookup a k = Poly_Mapping.lookup b k"
      by (simp add: Poly_Mapping.lookup_minus)
  qed
qed

end
