theory Finite_Difference
  imports "HOL-Computational_Algebra.Polynomial"
begin

text \<open>Exact ten-item port of Scalar/FiniteDifference.lean at commit
61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff.\<close>

definition fallingFactorialPoly :: "nat \<Rightarrow> 'a::field poly" where
  "fallingFactorialPoly k = (\<Prod>i<k. [:- of_nat (i + 1),1:])"

lemma fallingFactorialPoly_natDegree:
  "degree (fallingFactorialPoly k :: 'a::field poly) = k"
  unfolding fallingFactorialPoly_def
  by (subst degree_prod_sum_eq) simp_all

lemma fallingFactorialPoly_ne_zero:
  assumes hk: "0 < k"
  shows "(fallingFactorialPoly k :: 'a::field poly) \<noteq> 0"
  using hk fallingFactorialPoly_natDegree[where k=k and 'a='a] by auto

lemma polynomial_shift_difference_eq_one_is_linear:
  fixes F :: "'a::field_char_0 poly"
  assumes hF: "pcompose F [:1,1:] - F = 1"
  shows "F = [:0,1:] + [:poly F 0:]"
proof -
  have step: "poly F (1 + of_nat n) = poly F (of_nat n) + 1" for n :: nat
  proof -
    have "poly (pcompose F [:1,1:] - F) (of_nat n) = poly 1 (of_nat n)"
      using hF by simp
    then have "poly F (1 + of_nat n) - poly F (of_nat n) = 1"
      by (simp add: poly_pcompose add.commute)
    then show ?thesis by (simp add: diff_eq_eq add.commute)
  qed
  have eval_nat: "poly F (of_nat n) = poly F 0 + of_nat n" for n :: nat
    by (induction n) (simp_all add: of_nat_Suc step add_ac)
  let ?D = "F - ([:0,1:] + [:poly F 0:])"
  have subset: "range (of_nat :: nat \<Rightarrow> 'a) \<subseteq> {x. poly ?D x = 0}"
    by (auto simp: eval_nat add.commute)
  have inf: "infinite (range (of_nat :: nat \<Rightarrow> 'a))"
    by (rule range_inj_infinite) (simp add: inj_on_def)
  have "?D = 0"
  proof (rule ccontr)
    assume "?D \<noteq> 0"
    then have "finite {x. poly ?D x = 0}" by (rule poly_roots_finite)
    with subset have "finite (range (of_nat :: nat \<Rightarrow> 'a))"
      by (rule finite_subset)
    with inf show False by contradiction
  qed
  then show ?thesis by simp
qed

lemma natDegree_eq_one_of_shift_difference_eq_one:
  fixes F :: "'a::field_char_0 poly"
  assumes hF: "pcompose F [:1,1:] - F = 1"
  shows "degree F = 1"
  by (subst polynomial_shift_difference_eq_one_is_linear[OF hF]) simp

lemma natDegree_eq_one_of_shift_difference_eq_one_step:
  fixes F :: "'a::field_char_0 poly" and a :: 'a
  assumes ha: "a \<noteq> 0"
    and hF: "pcompose F [:a,1:] - F = 1"
  shows "degree F = 1"
proof -
  let ?G = "pcompose F [:0,a:]"
  have scaled: "pcompose (pcompose F [:a,1:]) [:0,a:] - ?G = 1"
    using arg_cong[OF hF, of "\<lambda>H. pcompose H [:0,a:]"]
    by (simp add: pcompose_diff pcompose_1)
  have inner: "pcompose [:0,a:] [:1,1:] = pcompose [:a,1:] [:0,a:]"
    by (simp add: pcompose_pCons)
  have Gcomp: "pcompose ?G [:1,1:] = pcompose (pcompose F [:a,1:]) [:0,a:]"
    by (simp only: pcompose_assoc[symmetric] inner)
  have "pcompose ?G [:1,1:] - ?G = 1"
    by (simp only: Gcomp scaled)
  then have "degree ?G = 1"
    by (rule natDegree_eq_one_of_shift_difference_eq_one)
  with ha show ?thesis by (simp add: degree_pcompose)
qed

lemma natDegree_eq_one_of_reverse_shift_difference_eq_one_step:
  fixes F :: "'a::field_char_0 poly" and a :: 'a
  assumes ha: "a \<noteq> 0"
    and hF: "F - pcompose F [:a,1:] = 1"
  shows "degree F = 1"
proof -
  have "pcompose (-F) [:a,1:] - (-F) = 1"
    using hF by (simp add: pcompose_uminus)
  from natDegree_eq_one_of_shift_difference_eq_one_step[OF ha this]
  show ?thesis by simp
qed

lemma product_reverse_shift_difference_forces_unit_factor_degree:
  fixes f A g :: "'a::field_char_0 poly" and k :: nat
  assumes hk: "0 < k" and hf: "f \<noteq> 0" and hA: "A \<noteq> 0"
    and hg: "g \<noteq> 0" and hAdeg: "degree A = k"
    and h: "f * A * g - pcompose (f * A * g) [:of_nat k,1:] = 1"
  shows "degree f = 0 \<and> k = 1 \<and> degree g = 0"
proof -
  have step: "(of_nat k :: 'a) \<noteq> 0" using hk by simp
  have "degree (f * A * g) = 1"
    by (rule natDegree_eq_one_of_reverse_shift_difference_eq_one_step[OF step h])
  then have "degree f + k + degree g = 1"
    using hf hA hg by (simp add: degree_mult_eq hAdeg)
  with hk show ?thesis by arith
qed

lemma fallingFactorial_shift_difference_forces_generator_case:
  fixes f g :: "'a::field_char_0 poly" and k :: nat
  assumes hk: "0 < k" and hf: "f \<noteq> 0" and hg: "g \<noteq> 0"
    and h: "f * fallingFactorialPoly k * g -
      pcompose (f * fallingFactorialPoly k * g) [:of_nat k,1:] = 1"
  shows "degree f = 0 \<and> k = 1 \<and> degree g = 0"
  by (rule product_reverse_shift_difference_forces_unit_factor_degree[OF
      hk hf fallingFactorialPoly_ne_zero[OF hk] hg fallingFactorialPoly_natDegree h])

lemma shiftProduct_eq_one_forces_constant_factors:
  fixes f g :: "'a::field_char_0 poly"
  assumes hf: "f \<noteq> 0" and hg: "g \<noteq> 0"
    and h: "pcompose ([:0,1:] * f * pcompose g [:1,1:]) [:1,1:] -
      ([:0,1:] * f * pcompose g [:1,1:]) = 1"
  shows "degree f = 0 \<and> degree g = 0"
proof -
  have deg: "degree ([:0,1:] * f * pcompose g [:1,1:]) = 1"
    by (rule natDegree_eq_one_of_shift_difference_eq_one[OF h])
  have shiftne: "pcompose g [:1,1:] \<noteq> 0"
    using hg by (simp add: pcompose_eq_0_iff)
  have "1 + degree f + degree g = 1"
    using deg hf shiftne by (simp add: degree_mult_eq degree_pcompose)
  then show ?thesis by arith
qed

end
