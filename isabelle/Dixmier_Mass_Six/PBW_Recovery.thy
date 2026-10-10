theory PBW_Recovery
  imports "Normal_Order_Span" "PBW_Extraction"
begin

definition falling_coeff :: "nat \<Rightarrow> nat \<Rightarrow> 'a::field" where
  "falling_coeff n m = (if m \<le> n then pochhammer (of_nat (Suc (n - m))) m else 0)"
lemma derivative_monomial_falling:
  "(pderiv ^^ b) (monom c k) = monom (falling_coeff k b * c) (k - b)"
  by (cases "b \<le> k")
     (simp_all add: falling_coeff_def y_op_def[symmetric] y_op_power_monom y_op_power_monom_zero)
lemma derivative_X_power_falling:
  "(pderiv ^^ b) ([:0, 1:] ^ k) = smult (falling_coeff k b) ([:0, 1:] ^ (k - b))"
  using derivative_monomial_falling[of b 1 k]
  by (simp add: monom_altdef)
lemma higher_derivative_translate:
  "(pderiv ^^ b) (pcompose p [:c, 1:]) = pcompose ((pderiv ^^ b) p) [:c, 1:]"
  by (induction b) (simp_all add: pderiv_pcompose pderiv_pCons)
lemma pcompose_power_local:
  "pcompose (p ^ n) q = pcompose p q ^ n"
  by (induction n) (simp_all add: pcompose_1 pcompose_mult)
lemma coeff_X_power_local:
  "coeff ([:0, 1:] ^ j) b = (if b = j then 1 else 0 :: 'a::field)"
proof -
  have "([:0, 1:] :: 'a poly) ^ j = monom 1 j" by (simp add: monom_altdef)
  then show ?thesis by (simp add: coeff_monom)
qed
lemma pochhammer_one_factorial_cast:
  "pochhammer (1::'a::field) b = of_nat (fact b)"
  by (induction b) (simp_all add: pochhammer_Suc fact_Suc of_nat_mult of_nat_Suc algebra_simps)
lemma derivative_shift_power_at_one:
  "poly ((pderiv ^^ b) ([:-1, 1:] ^ j)) 1 = (if j = b then of_nat (fact j) else 0 :: 'a::field)"
proof -
  have shift: "[:-1, 1:] ^ j = pcompose ([:0, 1:] ^ j) [:-1, 1:]"
    by (simp add: pcompose_power_local pcompose_pCons)
  show ?thesis
    unfolding shift higher_derivative_translate
    by (simp add: poly_pcompose poly_0_coeff_0 coeff_higher_pderiv
      coeff_X_power_local pochhammer_one_factorial_cast)
qed
lemma binomial_shift_power:
  "([:-1, 1:] :: 'a::field poly) ^ j =
    (\<Sum>k\<in>{..<Suc j}. smult ((-1) ^ (j - k) * of_nat (j choose k)) ([:0, 1:] ^ k))"
proof -
  have shift: "([:-1, 1:] :: 'a poly) = [:0, 1:] + (-1)" by (rule poly_eqI) (simp add: coeff_pCons split: nat.split)
  show ?thesis unfolding shift binomial_ring
    by (simp add: lessThan_Suc_atMost of_nat_poly one_pCons poly_const_pow algebra_simps)
qed
lemma alternating_binomial_falling:
  "(\<Sum>k\<in>{..<Suc j}. (-1) ^ (j - k) * of_nat (j choose k) * falling_coeff k b) =
    (if j = b then of_nat (fact j) else 0 :: 'a::field)"
proof -
  have eq: "poly ((pderiv ^^ b) (([:-1, 1:] :: 'a poly) ^ j)) 1 =
    (\<Sum>k\<in>{..<Suc j}. (-1) ^ (j - k) * of_nat (j choose k) * falling_coeff k b)"
    by (subst binomial_shift_power)
       (simp only: higher_pderiv_sum higher_pderiv_smult derivative_X_power_falling
         poly_sum poly_smult poly_power; simp)
  show ?thesis using eq[symmetric] by (simp only: derivative_shift_power_at_one)
qed

lemma normal_monomial_X_power:
  "normal_monomial a b ([:0, 1:] ^ k) =
    smult (falling_coeff k b) ([:0, 1:] ^ a * [:0, 1:] ^ (k - b))"
  by (simp add: normal_monomial_apply derivative_X_power_falling)
lemma normal_coefficient_term:
  assumes "k \<le> j"
  shows "smult ((-1) ^ (j-k) * of_nat (j choose k))
      ([:0, 1:] ^ (j-k) * normal_monomial a b ([:0, 1:] ^ k)) =
    smult ((-1) ^ (j-k) * of_nat (j choose k) * falling_coeff k b)
      ([:0, 1:] ^ (a+j-b))"
proof (cases "b \<le> k")
  case True
  have ex: "(j-k) + (a + (k-b)) = a+j-b" using assms True by arith
  show ?thesis
    by (simp add: normal_monomial_X_power smult_smult power_add[symmetric] ex)
next
  case False then show ?thesis by (simp add: normal_monomial_X_power falling_coeff_def)
qed
lemma coeff_poly_normal_monomial:
  "coeff_poly (normal_monomial a b :: 'a::field_char_0 poly_operator) j =
    (if j = b then [:0, 1:] ^ a else 0)"
proof -
  have terms: "(\<Sum>k\<in>{..<Suc j}. smult ((-1) ^ (j-k) * of_nat (j choose k))
      ([:0, 1:] ^ (j-k) * normal_monomial a b ([:0, 1:] ^ k))) =
    smult (\<Sum>k\<in>{..<Suc j}. (-1) ^ (j-k) * of_nat (j choose k) * falling_coeff k b)
      ([:0, 1:] ^ (a+j-b))"
    unfolding smult_sum
    by (intro sum.cong refl normal_coefficient_term) auto
  show ?thesis
    unfolding coeff_poly_def terms alternating_binomial_falling
    by (cases "j = b") (simp_all add: smult_smult)
qed
lemma pbw_coeff_normal_monomial:
  "pbw_coeff (normal_monomial a b :: 'a::field_char_0 poly_operator) i j =
    (if i = a \<and> j = b then 1 else 0)"
  by (simp add: pbw_coeff_def coeff_poly_normal_monomial coeff_X_power_local)

end
