theory Support_Test_Polynomial
  imports Sparse_Support
begin

text \<open>The finite-set adapter for the source test polynomial.  Natural
  casts need be injective only for the final nonvanishing lemma.\<close>

definition testPoly :: "nat set \<Rightarrow> 'a::field poly" where
  "testPoly T = (\<Prod>m\<in>T. ([:0, 1:] - [:of_nat m:]))"

lemma natDegree_testPoly_le:
  fixes T :: "nat set"
  assumes "finite T"
  shows "degree (testPoly T :: 'a::field poly) \<le> card T"
proof -
  have "degree (testPoly T :: 'a poly) \<le>
      (\<Sum>m\<in>T. degree ([:0, 1:] - [:of_nat m:] :: 'a poly))"
    unfolding testPoly_def
    using degree_prod_sum_le[OF assms,
      of "\<lambda>m. ([:0, 1:] - [:of_nat m:] :: 'a poly)"]
    by simp
  also have "... = card T" by simp
  finally show ?thesis .
qed

lemma eval_testPoly:
  fixes T :: "nat set"
  assumes "finite T"
  shows "poly (testPoly T :: 'a::field poly) (of_nat n) =
    (\<Prod>m\<in>T. (of_nat n - of_nat m))"
  by (simp add: testPoly_def poly_prod)

lemma eval_testPoly_eq_zero:
  fixes T :: "nat set"
  assumes "finite T" "n \<in> T"
  shows "poly (testPoly T :: 'a::field poly) (of_nat n) = 0"
  using assms by (auto simp: eval_testPoly)

lemma eval_testPoly_ne_zero:
  fixes T :: "nat set"
  assumes "finite T" "n \<notin> T"
  shows "poly (testPoly T :: 'a::field_char_0 poly) (of_nat n) \<noteq> 0"
  using assms by (auto simp: eval_testPoly)

end
