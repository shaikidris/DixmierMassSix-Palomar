theory Fourier_Monomial_Symbols
  imports "PBW_Symbol"
    "Exact_Normal_Order"
begin

declare id_def [simp del]

lemma fourier_pbw_coeff_sum:
  fixes f :: "'b \<Rightarrow> 'a::field poly_operator"
  shows "pbw_coeff (\<Sum>u\<in>S. f u) i j = (\<Sum>u\<in>S. pbw_coeff (f u) i j)"
proof -
  have z: "pbw_coeff (0::'a::field poly_operator) i j = 0" for i j
    by (simp add: pbw_coeff_def coeff_poly_def)
  show ?thesis
  proof (induction S rule: infinite_finite_induct)
    case (infinite A)
    show ?case by (simp only: sum.infinite[OF infinite] z)
  next
    case empty
    show ?case by (simp only: sum.empty z)
  next
    case (insert x F)
    show ?case by (simp only: sum.insert[OF insert.hyps] pbw_coeff_add insert.IH)
  qed
qed

lemma symbol_concreteNormalMonomial:
  "pbw_symbol (op_comp (x_op ^^ i) (y_op ^^ j) :: 'a::field_char_0 poly_operator) =
    biv_monom 1 i j"
  by (simp only: normal_monomial_def[symmetric] pbw_symbol_normal_monomial)

lemma fourier_antinormal_in_weyl:
  "op_comp (y_op ^^ i) (x_op ^^ j) \<in> (weyl_algebra :: 'a::field poly_operator set)"
  unfolding weyl_algebra_def
  by (intro op_adjoin.comp op_adjoin_power) (simp_all add: weyl_algebra_def[symmetric])

lemma symbol_concreteAntiNormalMonomial:
  "pbw_symbol (op_comp (y_op ^^ i) (x_op ^^ j) :: 'a::field_char_0 poly_operator) =
    (\<Sum>k\<le>min j i. biv_monom (of_nat ((i choose k) * nat_desc_factorial j k)) (j-k) (i-k))"
proof (rule biv_eqI)
  fix a b
  show "biv_coeff (pbw_symbol (op_comp (y_op ^^ i) (x_op ^^ j) :: 'a poly_operator)) a b =
    biv_coeff (\<Sum>k\<le>min j i. biv_monom (of_nat ((i choose k) * nat_desc_factorial j k)) (j-k) (i-k)) a b"
    by (subst weyl_symbol_coeff[OF fourier_antinormal_in_weyl];
        simp only: y_power_comp_x_power fourier_pbw_coeff_sum pbw_coeff_smult
        pbw_coeff_normal_monomial biv_coeff_sum biv_coeff_monom)
       (intro sum.cong refl; auto)
qed

lemma grade_symbol_concreteAntiNormalMonomial:
  assumes "e \<in> biv_support (pbw_symbol (op_comp (y_op ^^ i) (x_op ^^ j) :: 'a::field_char_0 poly_operator))"
  shows "pair_grade e = int j - int i"
proof -
  have nz: "(\<Sum>k\<le>min j i. biv_coeff
      (biv_monom (of_nat ((i choose k) * nat_desc_factorial j k)::'a) (j-k) (i-k)) (fst e) (snd e)) \<noteq> 0"
    using assms by (simp add: biv_support_def symbol_concreteAntiNormalMonomial biv_coeff_sum)
  obtain k where hk: "k \<le> min j i" and hn:
    "biv_coeff (biv_monom (of_nat ((i choose k) * nat_desc_factorial j k)::'a) (j-k) (i-k)) (fst e) (snd e) \<noteq> 0"
    using sum.not_neutral_contains_not_neutral[OF nz] by auto
  have ij: "fst e = j-k" "snd e = i-k" using hn by (auto split: if_splits)
  have kj: "k \<le> j" and ki: "k \<le> i" using hk by auto
  show ?thesis by (simp add: pair_grade_def ij of_nat_diff[OF kj] of_nat_diff[OF ki])
qed

end
