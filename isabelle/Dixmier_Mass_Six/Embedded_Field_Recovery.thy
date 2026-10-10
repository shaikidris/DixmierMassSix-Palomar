theory Embedded_Field_Recovery
  imports "Typed_Field_Descent" "PBW_Finite_Coordinates"
begin

text \<open>The target coefficient type remains merely a field. Its needed
factorial nonvanishing is derived from a characteristic-zero source embedding,
not installed as an extra type-class assumption.\<close>

lemma coeff_poly_normal_monomial_factorial_nonzero:
  assumes fnz: "of_nat (fact j) \<noteq> (0 :: 'a::field)"
  shows "coeff_poly (normal_monomial a b :: 'a poly_operator) j =
    (if j = b then [:0, 1:] ^ a else 0)"
proof -
  have terms: "(\<Sum>k\<in>{..<Suc j}. smult ((-1) ^ (j-k) * of_nat (j choose k))
      ([:0, 1:] ^ (j-k) * normal_monomial a b ([:0, 1:] ^ k))) =
    smult (\<Sum>k\<in>{..<Suc j}. (-1) ^ (j-k) * of_nat (j choose k) * falling_coeff k b)
      ([:0, 1:] ^ (a+j-b))"
    unfolding smult_sum
    by (intro sum.cong refl normal_coefficient_term) auto
  show ?thesis
    using fnz
    unfolding coeff_poly_def terms alternating_binomial_falling
    by (cases "j = b") (simp_all add: smult_smult fnz)
qed

locale dixmier_char_zero_embedding = dixmier_field_embedding i
  for i :: "'k::field_char_0 \<Rightarrow> 'l::field"
begin

interpretation embedding_additive: additive i
  by standard (rule map_add)

lemma map_zero [simp]: "i 0 = 0"
  by (rule embedding_additive.zero)

lemma map_of_nat [simp]: "i (of_nat n) = of_nat n"
  by (induction n) (simp_all add: of_nat_Suc map_add map_one)

lemma target_of_nat_eq_zero:
  "(of_nat n :: 'l) = 0 \<longleftrightarrow> n = 0"
proof
  assume h: "(of_nat n :: 'l) = 0"
  have "i (of_nat n) = i 0" using h by simp
  then have "(of_nat n :: 'k) = 0" by (rule injD[OF injective])
  then show "n = 0" by simp
next
  assume "n = 0" then show "(of_nat n :: 'l) = 0" by simp
qed

lemma target_factorial_nonzero:
  "of_nat (fact j) \<noteq> (0 :: 'l)"
  by (simp add: target_of_nat_eq_zero)

lemma target_coeff_poly_normal_monomial:
  "coeff_poly (normal_monomial a b :: 'l poly_operator) j =
    (if j = b then [:0, 1:] ^ a else 0)"
  by (rule coeff_poly_normal_monomial_factorial_nonzero[OF target_factorial_nonzero])

lemma target_pbw_coeff_normal_monomial:
  "pbw_coeff (normal_monomial a b :: 'l poly_operator) u v =
    (if u = a \<and> v = b then 1 else 0)"
  by (simp add: pbw_coeff_def target_coeff_poly_normal_monomial coeff_X_power_local)

lemma target_pbw_coeff_finite_normal_sum:
  assumes "finite S"
  shows "pbw_coeff (finite_normal_sum S c :: 'l poly_operator) a b =
    (if (a,b) \<in> S then c (a,b) else 0)"
  using assms
proof (induction S)
  case empty show ?case by (simp add: pbw_coeff_def zero_fun_def[symmetric])
next
  case (insert u S)
  show ?case
    unfolding finite_normal_sum_insert[OF insert.hyps]
    by (simp only: pbw_coeff_add pbw_coeff_smult target_pbw_coeff_normal_monomial insert.IH;
      use insert.hyps in \<open>auto simp: prod_eq_iff split: if_splits\<close>)
qed

lemma target_pbw_coeff_finite_coordinates:
  assumes "finite {u. c u \<noteq> 0}"
  shows "pbw_coeff (finite_normal_sum {u. c u \<noteq> 0} c :: 'l poly_operator) a b = c (a,b)"
  by (simp add: target_pbw_coeff_finite_normal_sum[OF assms])

lemma target_weyl_pbw_injective:
  assumes "T \<in> (weyl_algebra :: 'l poly_operator set)" "U \<in> weyl_algebra"
    "\<And>a b. pbw_coeff T a b = pbw_coeff U a b"
  shows "T = U"
proof -
  obtain c where cf: "finite {u. c u \<noteq> 0}" and cT: "finite_normal_sum {u. c u \<noteq> 0} c = T"
    using weyl_exists_finite_coordinates[OF assms(1)] by blast
  obtain d where df: "finite {u. d u \<noteq> 0}" and dU: "finite_normal_sum {u. d u \<noteq> 0} d = U"
    using weyl_exists_finite_coordinates[OF assms(2)] by blast
  have cd: "c = d"
  proof (rule ext)
    fix u
    have "c u = pbw_coeff T (fst u) (snd u)"
      using target_pbw_coeff_finite_coordinates[OF cf, of "fst u" "snd u"] cT by simp
    also have "\<dots> = pbw_coeff U (fst u) (snd u)" by (rule assms(3))
    also have "\<dots> = d u"
      using target_pbw_coeff_finite_coordinates[OF df, of "fst u" "snd u"] dU by simp
    finally show "c u = d u" .
  qed
  show ?thesis using cT dU cd by simp
qed

end
end
