theory Exact_Normal_Order
  imports Polynomial_Leibniz "PBW_Finite_Coordinates"
begin

lemma operator_sum_apply:
  fixes f :: "'i \<Rightarrow> 'x \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>i\<in>S. f i) x = (\<Sum>i\<in>S. f i x)"
  by (induction S rule: infinite_finite_induct) simp_all

lemma nat_desc_factorial_cast_falling_coeff:
  "(of_nat (nat_desc_factorial n k) :: 'a::field) = falling_coeff n k"
proof -
  have h: "smult (of_nat (nat_desc_factorial n k)) ([:0, 1:] ^ (n-k) :: 'a poly) =
      smult (falling_coeff n k) ([:0, 1:] ^ (n-k))"
  proof -
    have "smult (of_nat (nat_desc_factorial n k)) ([:0, 1:] ^ (n-k) :: 'a poly) =
        (pderiv ^^ k) ([:0, 1:] ^ n)"
      by (rule derivative_X_power_desc_factorial[symmetric])
    also have "\<dots> = smult (falling_coeff n k) ([:0, 1:] ^ (n-k))"
      by (rule derivative_X_power_falling)
    finally show ?thesis .
  qed
  from arg_cong[OF h, of "\<lambda>p. coeff p (n-k)"]
  show ?thesis by (simp add: coeff_X_power_local)
qed

lemma y_power_comp_x_power:
  "op_comp (y_op ^^ j) (x_op ^^ i) =
    (\<Sum>k\<le>min i j. (\<lambda>p. smult (of_nat ((j choose k) * nat_desc_factorial i k))
      (normal_monomial (i-k) (j-k) p)))"
  by (rule ext)
     (simp add: op_comp_def y_op_def x_op_power_apply normal_monomial_apply higher_pderiv_mul_X_power operator_sum_apply)


lemma normal_monomial_mul:
  "op_comp (normal_monomial a b) (normal_monomial c d) =
    (\<Sum>k\<le>min c b. (\<lambda>p. smult (of_nat ((b choose k) * nat_desc_factorial c k))
      (normal_monomial (a+c-k) (b+d-k) p)))"
proof (rule ext)
  fix p :: "'a poly"
  have step_term: "[:0, 1:] ^ a *
      smult (of_nat ((b choose k) * nat_desc_factorial c k))
        ([:0, 1:] ^ (c-k) * (pderiv ^^ (b-k)) ((pderiv ^^ d) p)) =
      smult (of_nat ((b choose k) * nat_desc_factorial c k))
        ([:0, 1:] ^ (a+c-k) * (pderiv ^^ (b+d-k)) p)"
    if "k \<le> min c b" for k
  proof -
    have ex: "a + (c-k) = a+c-k" and ey: "(b-k)+d = b+d-k"
      using that by arith+
    have deriv: "(pderiv ^^ (b-k)) ((pderiv ^^ d) p) = (pderiv ^^ (b+d-k)) p"
    proof -
      have "(pderiv ^^ (b-k)) ((pderiv ^^ d) p) = (pderiv ^^ ((b-k)+d)) p"
        by (simp only: funpow_add comp_apply)
      then show ?thesis by (simp only: ey)
    qed
    show ?thesis
      by (simp only: deriv normal_monomial_apply mult_smult_right mult.assoc[symmetric]
          power_add[symmetric] ex)
  qed
  show "op_comp (normal_monomial a b) (normal_monomial c d) p =
      (\<Sum>k\<le>min c b. (\<lambda>p. smult (of_nat ((b choose k) * nat_desc_factorial c k))
        (normal_monomial (a+c-k) (b+d-k) p))) p"
    by (simp only: op_comp_def normal_monomial_apply higher_pderiv_mul_X_power
          sum_distrib_left operator_sum_apply)
       (intro sum.cong refl; rule step_term; simp)
qed

lemma normal_monomial_mul_apply:
  "normal_monomial a b (normal_monomial c d p) =
    (\<Sum>k\<le>min c b. smult (of_nat ((b choose k) * nat_desc_factorial c k))
      (normal_monomial (a+c-k) (b+d-k) p))"
proof -
  note h = normal_monomial_mul[of a b c d]
  have "op_comp (normal_monomial a b) (normal_monomial c d) p =
    (\<Sum>k\<le>min c b. (\<lambda>p. smult (of_nat ((b choose k) * nat_desc_factorial c k))
      (normal_monomial (a+c-k) (b+d-k) p))) p"
    by (rule fun_cong[OF h])
  then show ?thesis by (simp only: op_comp_def operator_sum_apply)
qed

lemma smult_polynomial_sum:
  "smult c (\<Sum>i\<in>S. f i) = (\<Sum>i\<in>S. smult c (f i))"
  by (induction S rule: infinite_finite_induct) (simp_all add: smult_add_right)

lemma normal_monomial_sum:
  "normal_monomial a b (\<Sum>i\<in>S. f i) = (\<Sum>i\<in>S. normal_monomial a b (f i))"
  by (rule poly_linear_sum[OF normal_monomial_linear])

lemma normal_monomial_smult:
  "normal_monomial a b (smult c p) = smult c (normal_monomial a b p)"
  using normal_monomial_linear unfolding poly_linear_def by blast

lemma finite_normal_sum_mul:
  assumes "finite S" "finite T"
  shows "op_comp (finite_normal_sum S c) (finite_normal_sum T d) =
    (\<Sum>u\<in>S. \<Sum>v\<in>T. \<Sum>k\<le>min (fst v) (snd u).
      (\<lambda>p. smult (c u * d v * of_nat ((snd u choose k) * nat_desc_factorial (fst v) k))
        (normal_monomial (fst u+fst v-k) (snd u+snd v-k) p)))"
  by (rule ext)
     (simp only: finite_normal_sum_def op_comp_def operator_sum_apply normal_monomial_sum
        normal_monomial_smult smult_polynomial_sum normal_monomial_mul_apply smult_smult mult.assoc)

end
