theory Vanishing_Moments
  imports Euler_Divisibility
begin

lemma poly_euler_iterate_support:
  "poly ((euler ^^ k) S) a =
    (\<Sum>n\<in>sparse_support S. coeff S n * a ^ n * of_nat n ^ k)"
proof -
  have "(\<Sum>n\<in>sparse_support S. coeff ((euler ^^ k) S) n * a ^ n) =
    (\<Sum>n\<in>sparse_support ((euler ^^ k) S). coeff ((euler ^^ k) S) n * a ^ n)"
    by (rule sum.mono_neutral_right)
      (auto intro: sparse_support_euler_iterate[THEN subsetD])
  then show ?thesis
    by (simp add: poly_sparse_support coeff_euler_iterate algebra_simps)
qed

lemma sum_coeff_pow_mul_eq_zero:
  fixes S :: "'a::field poly"
  assumes h: "([:0,1:] - [:a:]) ^ m dvd S" and hk: "k < m"
  shows "(\<Sum>n\<in>sparse_support S. coeff S n * a ^ n * of_nat n ^ k) = 0"
proof -
  have d: "([:0,1:] - [:a:]) ^ (m-k) dvd (euler ^^ k) S"
    by (rule pow_dvd_euler_iterate[OF h])
  obtain q where q: "(euler ^^ k) S = ([:0,1:] - [:a:]) ^ (m-k) * q"
    using d by (elim dvdE)
  have "poly ((euler ^^ k) S) a = 0"
    using hk by (simp add: q poly_mult poly_power)
  then show ?thesis by (simp add: poly_euler_iterate_support)
qed

lemma moment_eq_zero:
  fixes S g :: "'a::field poly"
  assumes h: "([:0,1:] - [:a:]) ^ m dvd S" and hg: "degree g < m"
  shows "(\<Sum>n\<in>sparse_support S. coeff S n * a ^ n * poly g (of_nat n)) = 0"
proof -
  have "(\<Sum>n\<in>sparse_support S. coeff S n * a ^ n * poly g (of_nat n)) =
    (\<Sum>k\<le>degree g. coeff g k *
      (\<Sum>n\<in>sparse_support S. coeff S n * a ^ n * of_nat n ^ k))"
    unfolding poly_altdef
    by (simp only: sum_distrib_left, subst sum.swap)
      (simp add: sum_distrib_left mult_ac)
  also have "... = 0"
    by (rule sum.neutral) (use hg in \<open>auto simp: sum_coeff_pow_mul_eq_zero[OF h]\<close>)
  finally show ?thesis .
qed

end
