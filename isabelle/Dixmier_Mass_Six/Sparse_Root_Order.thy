theory Sparse_Root_Order
  imports Sparse_Power_Divisibility
begin

text \<open>The bridge is restricted to nonzero polynomials. No convention for order of zero is used.\<close>
lemma nonzero_root_multiplicity_bridge:
  fixes S :: "'a::field poly"
  assumes "S \<noteq> 0"
  shows "([:0,1:] - [:a:]) ^ m dvd S \<longleftrightarrow> m \<le> Polynomial.order a S"
  using assms by (simp add: Polynomial.order_divides)

lemma rootMultiplicity_lt_termCount:
  fixes S :: "'a::field_char_0 poly"
  assumes "S \<noteq> 0" "a \<noteq> 0"
  shows "Polynomial.order a S < termCount S"
  by (rule pow_dvd_imp_lt_termCount[OF assms])
    (simp add: Polynomial.order_divides assms)

end
