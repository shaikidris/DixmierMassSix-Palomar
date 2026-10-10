theory Sparse_Power_Divisibility
  imports Vanishing_Moments Support_Test_Polynomial
begin

lemma pow_dvd_imp_lt_termCount:
  fixes S :: "'a::field_char_0 poly"
  assumes hS: "S \<noteq> 0" and ha: "a \<noteq> 0"
    and hdvd: "([:0,1:] - [:a:]) ^ m dvd S"
  shows "m < termCount S"
proof (rule ccontr)
  assume "\<not> m < termCount S"
  then have le: "termCount S \<le> m" by simp
  obtain n0 where hn: "n0 \<in> sparse_support S"
    using hS sparse_support_empty_iff by blast
  let ?T = "sparse_support S - {n0}"
  let ?g = "testPoly ?T :: 'a poly"
  have fin: "finite ?T" by simp
  have cardlt: "card ?T < termCount S"
    using hn termCount_pos[OF hS]
    by (simp add: termCount_def card_Diff_singleton_if)
  have hg: "degree ?g < m"
    using natDegree_testPoly_le[OF fin, where 'a='a] cardlt le by linarith
  have mom: "(\<Sum>n\<in>sparse_support S. coeff S n * a ^ n * poly ?g (of_nat n)) = 0"
    by (rule moment_eq_zero[OF hdvd hg])
  have single: "(\<Sum>n\<in>sparse_support S. coeff S n * a ^ n * poly ?g (of_nat n)) =
    coeff S n0 * a ^ n0 * poly ?g (of_nat n0)"
    proof -
    have "(\<Sum>n\<in>sparse_support S. coeff S n * a ^ n * poly ?g (of_nat n)) =
      (\<Sum>n\<in>{n0}. coeff S n * a ^ n * poly ?g (of_nat n))"
      by (rule sum.mono_neutral_right)
        (use hn fin in \<open>auto simp: eval_testPoly_eq_zero\<close>)
    then show ?thesis by simp
  qed
  have nonzero: "coeff S n0 * a ^ n0 * poly ?g (of_nat n0) \<noteq> 0"
    using hn ha eval_testPoly_ne_zero[OF fin, of n0] by simp
  show False using mom single nonzero by simp
qed

end
