theory Sparse_Support
  imports "HOL-Computational_Algebra.Polynomial"
begin

text \<open>Finite coefficient support, matching Lean Polynomial.support extensionally.\<close>
definition sparse_support :: "'a::zero poly \<Rightarrow> nat set" where
  "sparse_support p = {n. coeff p n \<noteq> 0}"

definition termCount :: "'a::semiring_0 poly \<Rightarrow> nat" where
  "termCount p = card (sparse_support p)"

lemma mem_sparse_support [simp]: "n \<in> sparse_support p \<longleftrightarrow> coeff p n \<noteq> 0"
  by (simp add: sparse_support_def)

lemma sparse_support_subset: "sparse_support p \<subseteq> {..degree p}"
  by (auto intro: le_degree)

lemma finite_sparse_support [simp]: "finite (sparse_support p)"
  by (rule finite_subset[OF sparse_support_subset]) simp

lemma sparse_support_empty_iff [simp]: "sparse_support p = {} \<longleftrightarrow> p = 0"
  by (auto simp: sparse_support_def intro: poly_eqI)

lemma termCount_zero [simp]: "termCount (0 :: 'a::semiring_0 poly) = 0"
  by (simp add: termCount_def sparse_support_def)

lemma termCount_pos: "p \<noteq> 0 \<Longrightarrow> 0 < termCount p"
  by (simp add: termCount_def card_gt_0_iff)

lemma sparse_support_monom:
  "sparse_support (monom a n) = (if a = 0 then {} else {n})"
  by (auto simp: sparse_support_def)

lemma termCount_monom [simp]:
  "a \<noteq> 0 \<Longrightarrow> termCount (monom a n) = 1"
  by (simp add: termCount_def sparse_support_monom)

lemma poly_sparse_support:
  fixes p :: "'a::comm_semiring_1 poly"
  shows "poly p a = (\<Sum>n\<in>sparse_support p. coeff p n * a ^ n)"
proof -
  have "(\<Sum>n\<in>{..degree p}. coeff p n * a ^ n) =
      (\<Sum>n\<in>sparse_support p. coeff p n * a ^ n)"
    by (rule sum.mono_neutral_right) (auto simp: sparse_support_def intro: le_degree)
  then show ?thesis by (simp add: poly_altdef)
qed

end
