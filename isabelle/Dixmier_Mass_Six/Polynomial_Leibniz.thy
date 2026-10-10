theory Polynomial_Leibniz
  imports "Normal_Order_Span"
begin

text \<open>The recursion is the pinned Mathlib Nat.descFactorial definition:
n falling 0 = 1 and n falling (k+1) = (n-k) * (n falling k).
All factors and binomial coefficients are computed in nat before casting.\<close>

fun nat_desc_factorial :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nat_desc_factorial n 0 = 1"
| "nat_desc_factorial n (Suc k) = (n - k) * nat_desc_factorial n k"

lemma nat_desc_factorial_eq_product:
  "nat_desc_factorial n k = (\<Prod>r<k. n-r)"
  by (induction k) (simp_all add: mult.commute)

lemma nat_desc_factorial_overflow:
  "n < k \<Longrightarrow> nat_desc_factorial n k = 0"
  by (auto simp: nat_desc_factorial_eq_product prod_zero_iff intro!: bexI[of _ n])

lemma derivative_X_power_desc_factorial:
  "(pderiv ^^ k) ([:0, 1:] ^ n :: 'a::field poly) =
    smult (of_nat (nat_desc_factorial n k)) ([:0, 1:] ^ (n-k))"
  by (induction k)
     (simp_all add: pderiv_smult pderiv_power pderiv_pCons of_nat_mult mult.commute)

lemma binomial_step_weighted_sum:
  fixes F :: "nat \<Rightarrow> 'a::comm_semiring_1"
  shows "(\<Sum>k\<le>Suc n. of_nat (Suc n choose k) * F k) =
    (\<Sum>k\<le>n. of_nat (n choose k) * F k) +
    (\<Sum>k\<le>n. of_nat (n choose k) * F (Suc k))"
proof -
  have shift: "(\<Sum>k\<le>n. of_nat (n choose k) * F k) =
    F 0 + (\<Sum>k\<le>n. of_nat (n choose Suc k) * F (Suc k))"
  proof -
    have "(\<Sum>k\<le>Suc n. of_nat (n choose k) * F k) =
      F 0 + (\<Sum>k\<le>n. of_nat (n choose Suc k) * F (Suc k))"
      by (subst sum.atMost_Suc_shift) simp
    then show ?thesis by (simp add: binomial_eq_0)
  qed
  show ?thesis
    by (subst sum.atMost_Suc_shift)
       (simp only: binomial_n_0 binomial_Suc_Suc of_nat_1 mult_1_left of_nat_add
          distrib_right sum.distrib; simp only: shift add.assoc add.commute add.left_commute)
qed

lemma pderiv_finite_sum:
  "pderiv (\<Sum>i\<in>A. f i) = (\<Sum>i\<in>A. pderiv (f i))"
  using higher_pderiv_sum[of 1 f A] by simp

lemma higher_pderiv_leibniz:
  fixes p q :: "'a::field poly"
  shows "(pderiv ^^ n) (p * q) =
    (\<Sum>k\<le>n. of_nat (n choose k) * (pderiv ^^ k) p * (pderiv ^^ (n-k)) q)"
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  let ?F = "\<lambda>k. (pderiv ^^ k) p * (pderiv ^^ (Suc n-k)) q"
  have step_term: "pderiv (of_nat (n choose k) * (pderiv ^^ k) p * (pderiv ^^ (n-k)) q) =
    of_nat (n choose k) * ?F k + of_nat (n choose k) * ?F (Suc k)"
    if "k \<le> n" for k
  proof -
    have diff: "Suc n - k = Suc (n-k)" using that by arith
    show ?thesis
      by (simp add: diff of_nat_poly pderiv_mult pderiv_smult pderiv_pCons smult_add_right algebra_simps)
  qed
  have "(pderiv ^^ Suc n) (p*q) =
      pderiv (\<Sum>k\<le>n. of_nat (n choose k) * (pderiv ^^ k) p * (pderiv ^^ (n-k)) q)"
    by (simp only: funpow.simps comp_apply Suc.IH)
  also have "\<dots> = (\<Sum>k\<le>n. of_nat (n choose k) * ?F k + of_nat (n choose k) * ?F (Suc k))"
    by (simp only: pderiv_finite_sum) (intro sum.cong refl step_term; simp)
  also have "\<dots> = (\<Sum>k\<le>n. of_nat (n choose k) * ?F k) +
      (\<Sum>k\<le>n. of_nat (n choose k) * ?F (Suc k))"
    by (rule sum.distrib)
  also have "\<dots> = (\<Sum>k\<le>Suc n. of_nat (Suc n choose k) * ?F k)"
    by (rule binomial_step_weighted_sum[symmetric])
  finally show ?case by (simp only: mult.assoc)
qed

lemma higher_pderiv_mul_X_power:
  fixes p :: "'a::field poly"
  shows "(pderiv ^^ j) ([:0, 1:] ^ i * p) =
    (\<Sum>k\<le>min i j. smult (of_nat ((j choose k) * nat_desc_factorial i k))
       ([:0, 1:] ^ (i-k) * (pderiv ^^ (j-k)) p))"
proof -
  let ?F = "\<lambda>k. smult (of_nat ((j choose k) * nat_desc_factorial i k))
    ([:0, 1:] ^ (i-k) * (pderiv ^^ (j-k)) p)"
  have "(pderiv ^^ j) ([:0, 1:] ^ i * p) = (\<Sum>k\<le>j. ?F k)"
    by (subst higher_pderiv_leibniz)
       (simp add: derivative_X_power_desc_factorial of_nat_poly of_nat_mult mult.commute)
  also have "\<dots> = (\<Sum>k\<le>min i j. ?F k)"
  proof (rule sum.mono_neutral_right)
    show "finite {..j}" by simp
    show "{..min i j} \<subseteq> {..j}" by auto
    show "\<forall>k\<in>{..j} - {..min i j}. ?F k = 0"
      by (auto simp: nat_desc_factorial_overflow)
  qed
  finally show ?thesis .
qed

end
