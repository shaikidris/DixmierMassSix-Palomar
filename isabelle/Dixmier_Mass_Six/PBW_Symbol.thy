theory PBW_Symbol
  imports Bivariate_Polynomial
begin

definition pbw_pair_support :: "'a::field poly_operator \<Rightarrow> (nat \<times> nat) set" where
  "pbw_pair_support T = {u. pbw_coeff T (fst u) (snd u) \<noteq> 0}"
definition pbw_symbol :: "'a::field poly_operator \<Rightarrow> 'a bivariate" where
  "pbw_symbol T = (if finite (pbw_pair_support T) then
    (\<Sum>u\<in>pbw_pair_support T. biv_monom (pbw_coeff T (fst u) (snd u)) (fst u) (snd u)) else 0)"
definition pair_grade :: "nat \<times> nat \<Rightarrow> int" where
  "pair_grade u = int (fst u) - int (snd u)"
definition exponent_grade :: "(bool \<Rightarrow> nat) \<Rightarrow> int" where
  "exponent_grade e = int (e False) - int (e True)"
lemma exponent_grade_pair [simp]: "exponent_grade (pair_exponent u) = pair_grade u"
  by (simp add: exponent_grade_def pair_exponent_def pair_grade_def)
definition weyl_mass :: "'a::field poly_operator \<Rightarrow> nat" where
  "weyl_mass T = card (pair_grade ` biv_support (pbw_symbol T))"

lemma weyl_mass_exponent_form:
  "weyl_mass T = card (exponent_grade ` (pair_exponent ` biv_support (pbw_symbol T)))"
  by (simp add: weyl_mass_def image_image comp_def)

lemma pbw_symbol_infinite_support:
  "\<not> finite (pbw_pair_support T) \<Longrightarrow> pbw_symbol T = 0"
  by (simp add: pbw_symbol_def)
lemma pbw_symbol_coeff_finite:
  "finite (pbw_pair_support T) \<Longrightarrow> biv_coeff (pbw_symbol T) i j = pbw_coeff T i j"
  by (simp add: pbw_symbol_def biv_sum_monom_coeff pbw_pair_support_def)
lemma pbw_symbol_support_finite:
  "finite (pbw_pair_support T) \<Longrightarrow> biv_support (pbw_symbol T) = pbw_pair_support T"
  by (auto simp: biv_support_def pbw_symbol_coeff_finite pbw_pair_support_def)
lemma weyl_finite_pbw_pair_support:
  "T \<in> (weyl_algebra :: 'a::field_char_0 poly_operator set) \<Longrightarrow> finite (pbw_pair_support T)"
  unfolding pbw_pair_support_def by (rule weyl_pbw_finite_support)
lemma weyl_symbol_coeff:
  "T \<in> (weyl_algebra :: 'a::field_char_0 poly_operator set) \<Longrightarrow>
    biv_coeff (pbw_symbol T) i j = pbw_coeff T i j"
  by (intro pbw_symbol_coeff_finite weyl_finite_pbw_pair_support)
lemma weyl_symbol_support:
  "T \<in> (weyl_algebra :: 'a::field_char_0 poly_operator set) \<Longrightarrow>
    biv_support (pbw_symbol T) = pbw_pair_support T"
  by (intro pbw_symbol_support_finite weyl_finite_pbw_pair_support)
lemma weyl_mass_grade_support:
  "T \<in> (weyl_algebra :: 'a::field_char_0 poly_operator set) \<Longrightarrow>
    weyl_mass T = card ((\<lambda>u. int (fst u) - int (snd u)) ` pbw_pair_support T)"
  by (simp add: weyl_mass_def weyl_symbol_support pair_grade_def)
lemma weyl_symbol_injective:
  assumes "T \<in> (weyl_algebra :: 'a::field_char_0 poly_operator set)" "U \<in> weyl_algebra"
    "pbw_symbol T = pbw_symbol U"
  shows "T = U"
proof (rule weyl_pbw_injective[OF assms(1,2)])
  fix i j
  show "pbw_coeff T i j = pbw_coeff U i j"
    using weyl_symbol_coeff[OF assms(1), of i j] weyl_symbol_coeff[OF assms(2), of i j] assms(3) by simp
qed
lemma pbw_symbol_zero [simp]: "pbw_symbol 0 = 0"
  by (simp add: pbw_symbol_def pbw_pair_support_def pbw_coeff_def coeff_poly_def)
lemma weyl_mass_zero [simp]: "weyl_mass 0 = 0"
  by (simp add: weyl_mass_def)
lemma pbw_symbol_normal_monomial:
  "pbw_symbol (normal_monomial a b :: 'a::field_char_0 poly_operator) = biv_monom 1 a b"
proof -
  have supp: "pbw_pair_support (normal_monomial a b :: 'a poly_operator) = {(a,b)}"
    by (auto simp: pbw_pair_support_def pbw_coeff_normal_monomial prod_eq_iff)
  show ?thesis by (simp add: pbw_symbol_def supp pbw_coeff_normal_monomial)
qed
lemma weyl_mass_normal_monomial:
  "weyl_mass (normal_monomial a b :: 'a::field_char_0 poly_operator) = 1"
proof -
  have supp: "biv_support (biv_monom (1::'a) a b) = {(a,b)}"
    by (auto simp: biv_support_def prod_eq_iff)
  show ?thesis by (simp add: weyl_mass_def pbw_symbol_normal_monomial supp)
qed

lemma pbw_symbol_finite_normal_sum:
  assumes "finite S"
  shows "pbw_symbol (finite_normal_sum S c :: 'a::field_char_0 poly_operator) =
    (\<Sum>u\<in>S. biv_monom (c u) (fst u) (snd u))"
  by (rule biv_eqI)
     (simp only: weyl_symbol_coeff[OF finite_normal_sum_in_weyl[OF assms]]
       pbw_coeff_finite_normal_sum[OF assms] biv_sum_monom_coeff[OF assms])
lemma symbol_finite_normal_expansion:
  assumes "T \<in> (weyl_algebra :: 'a::field_char_0 poly_operator set)"
  shows "\<exists>c. finite {u. c u \<noteq> 0} \<and> finite_normal_sum {u. c u \<noteq> 0} c = T \<and>
    pbw_symbol T = (\<Sum>u\<in>{u. c u \<noteq> 0}. biv_monom (c u) (fst u) (snd u))"
proof -
  obtain c where fin: "finite {u. c u \<noteq> 0}" and rep: "finite_normal_sum {u. c u \<noteq> 0} c = T"
    using weyl_exists_finite_coordinates[OF assms] by blast
  show ?thesis by (rule exI[of _ c]) (use fin rep pbw_symbol_finite_normal_sum[OF fin, of c] in auto)
qed
lemma mass_finite_normal_expansion:
  assumes "T \<in> (weyl_algebra :: 'a::field_char_0 poly_operator set)"
  shows "\<exists>c. finite {u. c u \<noteq> 0} \<and> finite_normal_sum {u. c u \<noteq> 0} c = T \<and>
    weyl_mass T = card (pair_grade ` {u. c u \<noteq> 0})"
proof -
  obtain c where fin: "finite {u. c u \<noteq> 0}" and rep: "finite_normal_sum {u. c u \<noteq> 0} c = T"
    using weyl_exists_finite_coordinates[OF assms] by blast
  have supp: "biv_support (pbw_symbol T) = {u. c u \<noteq> 0}"
    using pbw_symbol_finite_normal_sum[OF fin, of c] rep
    by (simp add: biv_support_sum_monom[OF fin])
  show ?thesis by (rule exI[of _ c]) (use fin rep supp in \<open>simp add: weyl_mass_def\<close>)
qed

lemma pbw_coeff_diff:
  "pbw_coeff (T-U) i j = pbw_coeff T i j - pbw_coeff U i j"
  by (simp add: pbw_coeff_def coeff_poly_def smult_diff_right algebra_simps sum_subtractf)
lemma weyl_symbol_add:
  assumes "T \<in> (weyl_algebra :: 'a::field_char_0 poly_operator set)" "U \<in> weyl_algebra"
  shows "pbw_symbol (T+U) = pbw_symbol T + pbw_symbol U"
proof -
  have mem: "T+U \<in> weyl_algebra" using assms unfolding weyl_algebra_def by (rule op_adjoin.add)
  show ?thesis by (rule biv_eqI)
    (simp only: weyl_symbol_coeff[OF mem] biv_coeff_add weyl_symbol_coeff[OF assms(1)]
      weyl_symbol_coeff[OF assms(2)] pbw_coeff_add)
qed
lemma weyl_symbol_smult:
  assumes "T \<in> (weyl_algebra :: 'a::field_char_0 poly_operator set)"
  shows "pbw_symbol (\<lambda>p. smult c (T p)) = smult [:c:] (pbw_symbol T)"
proof -
  have mem: "(\<lambda>p. smult c (T p)) \<in> weyl_algebra"
    using assms unfolding weyl_algebra_def by (rule op_adjoin_smult)
  show ?thesis by (rule biv_eqI)
    (simp only: weyl_symbol_coeff[OF mem] biv_coeff_smult weyl_symbol_coeff[OF assms] pbw_coeff_smult)
qed
lemma weyl_symbol_sub:
  assumes "T \<in> (weyl_algebra :: 'a::field_char_0 poly_operator set)" "U \<in> weyl_algebra"
  shows "pbw_symbol (T-U) = pbw_symbol T - pbw_symbol U"
proof -
  have mem: "T-U \<in> weyl_algebra" using assms unfolding weyl_algebra_def by (rule op_adjoin.diff)
  show ?thesis by (rule biv_eqI)
    (simp only: weyl_symbol_coeff[OF mem] biv_coeff_diff weyl_symbol_coeff[OF assms(1)]
      weyl_symbol_coeff[OF assms(2)] pbw_coeff_diff)
qed
lemma sum_neg_one_pow_choose:
  "(\<Sum>k\<in>{..<Suc j}. (-1) ^ (j-k) * of_nat (j choose k)) =
    (if j = 0 then 1 else 0 :: 'a::field)"
  using alternating_binomial_falling[of j 0, where 'a='a]
  by (simp add: falling_coeff_def)
lemma coeff_poly_zero_derivative_monomial:
  "coeff_poly (normal_monomial a 0 :: 'a::field poly_operator) j =
    (if j = 0 then [:0, 1:] ^ a else 0)"
proof -
  have terms: "(\<Sum>k\<in>{..<Suc j}. smult ((-1) ^ (j-k) * of_nat (j choose k))
      ([:0, 1:] ^ (j-k) * normal_monomial a 0 ([:0, 1:] ^ k))) =
    smult (\<Sum>k\<in>{..<Suc j}. (-1) ^ (j-k) * of_nat (j choose k) * falling_coeff k 0)
      ([:0, 1:] ^ (a+j))"
    unfolding smult_sum
  proof (rule sum.cong[OF refl])
    fix k assume "k \<in> {..<Suc j}"
    then have kle: "k \<le> j" by simp
    show "smult ((-1) ^ (j-k) * of_nat (j choose k))
      ([:0, 1:] ^ (j-k) * normal_monomial a 0 ([:0, 1:] ^ k)) =
      smult ((-1) ^ (j-k) * of_nat (j choose k) * falling_coeff k 0) ([:0, 1:] ^ (a+j))"
      using normal_coefficient_term[OF kle, of a 0] by simp
  qed
  show ?thesis unfolding coeff_poly_def terms alternating_binomial_falling
    by (cases "j = 0") (simp_all add: smult_smult)
qed
lemma coeff_poly_x_op:
  "coeff_poly (x_op :: 'a::field poly_operator) j = (if j = 0 then [:0, 1:] else 0)"
  using coeff_poly_zero_derivative_monomial[of 1 j, where 'a='a]
  by (simp add: normal_monomial_def)
lemma pbw_coeff_x_op:
  "pbw_coeff (x_op :: 'a::field poly_operator) i j = (if i = 1 \<and> j = 0 then 1 else 0)"
  by (auto simp: pbw_coeff_def coeff_poly_x_op coeff_pCons split: nat.split)
lemma symbol_x_op:
  "pbw_symbol (x_op :: 'a::field poly_operator) = biv_monom 1 1 0"
proof -
  have supp: "pbw_pair_support (x_op :: 'a poly_operator) = {(1,0)}"
    by (auto simp: pbw_pair_support_def pbw_coeff_x_op prod_eq_iff)
  show ?thesis by (simp add: pbw_symbol_def supp pbw_coeff_x_op)
qed
lemma mass_x_op: "weyl_mass (x_op :: 'a::field poly_operator) = 1"
proof -
  have supp: "biv_support (biv_monom (1::'a) 1 0) = {(1,0)}"
    by (auto simp: biv_support_def prod_eq_iff)
  show ?thesis by (simp only: weyl_mass_def symbol_x_op supp; simp)
qed

lemma symbol_support_finite_expansion:
  assumes "T \<in> (weyl_algebra :: 'a::field_char_0 poly_operator set)"
  shows "\<exists>c. finite {u. c u \<noteq> 0} \<and> finite_normal_sum {u. c u \<noteq> 0} c = T \<and>
    biv_support (pbw_symbol T) = {u. c u \<noteq> 0}"
proof -
  obtain c where fin: "finite {u. c u \<noteq> 0}" and rep: "finite_normal_sum {u. c u \<noteq> 0} c = T"
    and sym: "pbw_symbol T = (\<Sum>u\<in>{u. c u \<noteq> 0}. biv_monom (c u) (fst u) (snd u))"
    using symbol_finite_normal_expansion[OF assms] by blast
  show ?thesis by (rule exI[of _ c])
    (simp add: fin rep sym biv_support_sum_monom[OF fin])
qed

lemma symbol_support_finite_sum:
  assumes "finite S"
  shows "biv_support (pbw_symbol (finite_normal_sum S c :: 'a::field_char_0 poly_operator)) =
    {u\<in>S. c u \<noteq> 0}"
  by (simp only: pbw_symbol_finite_normal_sum[OF assms] biv_support_sum_monom[OF assms])
lemma mass_finite_sum_grade:
  assumes "finite S"
  shows "weyl_mass (finite_normal_sum S c :: 'a::field_char_0 poly_operator) =
    card (pair_grade ` {u\<in>S. c u \<noteq> 0})"
  by (simp only: weyl_mass_def symbol_support_finite_sum[OF assms])

end
