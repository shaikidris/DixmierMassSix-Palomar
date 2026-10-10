theory Semiring_Polynomial_Product
  imports "Sparse_Support"
begin

text \<open>Isabelle's standard polynomial product has commutative coefficients.
This finite convolution adapter preserves Lean's arbitrary Semiring domain,
including noncommutative and trivial semirings. No multiplicative unit is used.\<close>

definition semiring_poly_mult :: "'a::semiring_0 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "semiring_poly_mult p q = Poly (map
    (\<lambda>k. \<Sum>i\<le>k. coeff p i * coeff q (k-i)) [0..<Suc (degree p + degree q)])"

lemma coeff_semiring_poly_mult:
  "coeff (semiring_poly_mult p q) k = (\<Sum>i\<le>k. coeff p i * coeff q (k-i))"
proof (cases "k \<le> degree p + degree q")
  case True
  then show ?thesis by (simp add: semiring_poly_mult_def nth_default_def del: upt_Suc)
next
  case False
  have vanishes: "(\<Sum>i\<le>k. coeff p i * coeff q (k-i)) = 0"
  proof (rule sum.neutral, clarify)
    fix i assume "i \<le> k"
    show "coeff p i * coeff q (k-i) = 0"
    proof (cases "degree p < i")
      case True then show ?thesis by (simp add: coeff_eq_0)
    next
      case False
      with \<open>\<not> k \<le> degree p + degree q\<close> have "degree q < k-i" by arith
      then show ?thesis by (simp add: coeff_eq_0)
    qed
  qed
  from False show ?thesis by (simp add: semiring_poly_mult_def nth_default_def vanishes)
qed

lemma semiring_poly_mult_eq_mult:
  fixes p q :: "'a::comm_semiring_0 poly"
  shows "semiring_poly_mult p q = p * q"
  by (rule poly_eqI) (simp only: coeff_semiring_poly_mult coeff_mult)

lemma coeff_mul_of_natDegree_le':
  fixes p q :: "'a::semiring_0 poly"
  assumes hp: "degree p \<le> m" and hq: "degree q \<le> n"
  shows "coeff (semiring_poly_mult p q) (m+n) = coeff p m * coeff q n"
proof -
  have summand: "coeff p i * coeff q (m+n-i) =
      (if i=m then coeff p m * coeff q n else 0)" for i
  proof (cases "i=m")
    case True then show ?thesis by simp
  next
    case False
    note ine = False
    show ?thesis
    proof (cases "i < m")
      case True
      with hq have "degree q < m+n-i" by arith
      then show ?thesis using ine by (simp add: coeff_eq_0)
    next
      case False
      with hp ine have "degree p < i" by arith
      then show ?thesis using ine by (simp add: coeff_eq_0)
    qed
  qed
  show ?thesis by (simp add: coeff_semiring_poly_mult summand)
qed

lemma coeff_mult_of_degree_le:
  fixes p q :: "'a::comm_semiring_0 poly"
  assumes "degree p \<le> m" "degree q \<le> n"
  shows "coeff (p*q) (m+n) = coeff p m * coeff q n"
  using coeff_mul_of_natDegree_le'[OF assms]
  by (simp only: semiring_poly_mult_eq_mult)

end
