theory Alternating_Square_Support
  imports "Sparse_Support"
begin

text \<open>Local finite-convolution adapter; no additional source declaration credit.\<close>
lemma alternating_square_support:
  fixes p :: "complex poly" and y :: "nat \<Rightarrow> real"
  assumes coeffs: "\<And>k. coeff p k = of_real (y k)"
    and sign: "\<And>k. k\<le>e \<Longrightarrow> 0 < (-1)^k * y k"
    and tail: "\<And>k. e<k \<Longrightarrow> y k=0"
  shows "2*e+1 \<le> termCount (p^2)"
proof -
  have nonneg: "0\<le>(-1)^k*y k" for k
  proof (cases "k\<le>e")
    case True show ?thesis by (rule less_imp_le[OF sign[OF True]])
  next
    case False then have "y k=0" by (intro tail) arith
    then show ?thesis by simp
  qed
  have nz: "coeff (p^2) n \<noteq> 0" if hn: "n\<le>2*e" for n
  proof -
    have fac: "(-1::real)^n*(y k*y(n-k)) = ((-1)^k*y k)*((-1)^(n-k)*y(n-k))"
      if "k\<le>n" for k
    proof -
      have pow: "(-1::real)^n = (-1)^k * (-1)^(n-k)"
        using power_add[of "-1::real" k "n-k"] that by simp
      show ?thesis by (simp only: pow; algebra)
    qed
    have left: "min n e\<le>e" by simp
    have right: "n-min n e\<le>e" using hn by arith
    have kn: "min n e\<le>n" by simp
    have positive: "0 < (-1::real)^n*(y(min n e)*y(n-min n e))"
      by (subst fac[OF kn]) (rule mult_pos_pos[OF sign[OF left] sign[OF right]])
    have pos: "0 < (\<Sum>k\<le>n. (-1::real)^n*(y k*y(n-k)))"
    proof (rule sum_pos2[where i="min n e"])
      show "finite {..n}" by simp
      show "min n e \<in> {..n}" by simp
      show "0 < (-1::real)^n*(y(min n e)*y(n-min n e))" by (rule positive)
      fix k assume "k\<in>{..n}"
      then have bound: "k\<le>n" by simp
      show "0\<le>(-1::real)^n*(y k*y(n-k))"
        by (simp only: fac[OF bound]; rule mult_nonneg_nonneg[OF nonneg nonneg])
    qed
    have sum: "coeff (p^2) n = of_real (\<Sum>k\<le>n. y k*y(n-k))"
      by (simp add: power2_eq_square coeff_mult coeffs)
    show ?thesis
    proof
      assume "coeff (p^2) n=0"
      then have "(\<Sum>k\<le>n. y k*y(n-k))=0" by (simp only: sum of_real_eq_0_iff)
      with pos show False by (simp add: sum_distrib_left[symmetric])
    qed
  qed
  have "{..<2*e+1} \<subseteq> sparse_support (p^2)" using nz by auto
  then have "card {..<2*e+1} \<le> card (sparse_support (p^2))"
    by (rule card_mono[OF finite_sparse_support])
  then show ?thesis by (simp add: termCount_def)
qed
end
