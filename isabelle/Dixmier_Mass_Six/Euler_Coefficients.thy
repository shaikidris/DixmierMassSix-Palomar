theory Euler_Coefficients
  imports Sparse_Support
begin

definition euler :: "'a::field poly \<Rightarrow> 'a poly" where
  "euler p = monom 1 1 * pderiv p"

lemma coeff_euler:
  "coeff (euler p) n = of_nat n * coeff p n"
  by (cases n) (simp_all add: euler_def coeff_monom_mult coeff_pderiv)

lemma coeff_euler_iterate:
  "coeff ((euler ^^ k) p) n = of_nat n ^ k * coeff p n"
  by (induction k) (simp_all add: funpow_Suc_right coeff_euler power_Suc mult.assoc)

lemma sparse_support_euler_iterate:
  "sparse_support ((euler ^^ k) p) \<subseteq> sparse_support p"
  by (auto simp: coeff_euler_iterate)

end
