theory Polynomial_Endomorphisms
  imports "HOL-Computational_Algebra.Polynomial" "HOL-Library.Function_Algebras"
begin

text \<open>Operators are functions with an explicit linearity carrier predicate.
Their multiplication is composition, not the pointwise multiplication on functions.\<close>

type_synonym 'a poly_operator = "'a poly \<Rightarrow> 'a poly"

definition poly_linear :: "('a::field poly_operator) \<Rightarrow> bool" where
  "poly_linear T \<longleftrightarrow>
    (\<forall>p q. T (p + q) = T p + T q) \<and>
    (\<forall>c p. T (smult c p) = smult c (T p))"

definition op_comp :: "'a poly_operator \<Rightarrow> 'a poly_operator \<Rightarrow> 'a poly_operator" where
  "op_comp T U = (\<lambda>p. T (U p))"
definition op_scalar :: "'a::field \<Rightarrow> 'a poly_operator" where
  "op_scalar c = smult c"
definition x_op :: "'a::field poly_operator" where
  "x_op p = [:0, 1:] * p"
definition y_op :: "'a::field poly_operator" where
  "y_op = pderiv"

lemma poly_linear_zero [simp]: "poly_linear 0"
  by (simp add: poly_linear_def)
lemma poly_linear_id [simp]: "poly_linear id"
  by (simp add: poly_linear_def)
lemma poly_linear_scalar [simp]: "poly_linear (op_scalar c)"
  by (simp add: poly_linear_def op_scalar_def smult_add_right smult_smult mult.commute)
lemma poly_linear_add:
  "poly_linear T \<Longrightarrow> poly_linear U \<Longrightarrow> poly_linear (T + U)"
  by (auto simp: poly_linear_def smult_add_right algebra_simps)
lemma poly_linear_diff:
  "poly_linear T \<Longrightarrow> poly_linear U \<Longrightarrow> poly_linear (T - U)"
  by (auto simp: poly_linear_def smult_diff_right algebra_simps)
lemma poly_linear_comp:
  "poly_linear T \<Longrightarrow> poly_linear U \<Longrightarrow> poly_linear (op_comp T U)"
  by (auto simp: poly_linear_def op_comp_def)
lemma poly_linear_smult:
  "poly_linear T \<Longrightarrow> poly_linear (\<lambda>p. smult c (T p))"
  by (auto simp: poly_linear_def smult_add_right smult_smult mult.commute)
lemma poly_linear_zero_image:
  "poly_linear T \<Longrightarrow> T 0 = 0"
  by (metis poly_linear_def smult_0_left)
lemma poly_linear_sum:
  "poly_linear T \<Longrightarrow> T (\<Sum>i\<in>A. f i) = (\<Sum>i\<in>A. T (f i))"
  by (induction A rule: infinite_finite_induct)
     (auto simp: poly_linear_zero_image poly_linear_def)

lemma op_comp_assoc:
  "op_comp (op_comp T U) V = op_comp T (op_comp U V)"
  by (simp add: op_comp_def)
lemma op_comp_id [simp]: "op_comp id T = T" "op_comp T id = T"
  by (simp_all add: op_comp_def)
lemma op_comp_add_left:
  "op_comp (T + U) V = op_comp T V + op_comp U V"
  by (simp add: op_comp_def fun_eq_iff)
lemma op_comp_add_right:
  "poly_linear T \<Longrightarrow> op_comp T (U + V) = op_comp T U + op_comp T V"
  by (auto simp: op_comp_def fun_eq_iff poly_linear_def)
lemma op_scalar_central:
  "poly_linear T \<Longrightarrow> op_comp (op_scalar c) T = op_comp T (op_scalar c)"
  by (auto simp: poly_linear_def op_comp_def op_scalar_def fun_eq_iff)
lemma poly_linear_power:
  "poly_linear T \<Longrightarrow> poly_linear (T ^^ n)"
  by (induction n) (auto simp: poly_linear_def)

lemma poly_linear_x [simp]: "poly_linear x_op"
  by (simp add: poly_linear_def x_op_def algebra_simps)
lemma poly_linear_y [simp]: "poly_linear y_op"
  by (simp add: poly_linear_def y_op_def pderiv_add pderiv_smult)
lemma yx_commutator:
  "op_comp y_op x_op - op_comp x_op y_op = (id :: 'a::field poly_operator)"
  by (rule ext) (simp add: op_comp_def x_op_def y_op_def pderiv_mult pderiv_pCons)
lemma x_op_monom:
  "x_op (monom c n) = monom c (Suc n)"
  by (simp add: x_op_def monom_altdef power_Suc algebra_simps)
lemma y_op_monom:
  "y_op (monom c n) = monom (of_nat n * c) (n - 1)"
  by (simp add: y_op_def pderiv_monom)
lemma y_op_power_coeff:
  "coeff ((y_op ^^ m) p) n = pochhammer (of_nat (Suc n)) m * coeff p (n + m)"
  by (simp add: y_op_def coeff_higher_pderiv)

lemma x_op_power_apply:
  "(x_op ^^ n) p = [:0, 1:] ^ n * p"
  by (induction n) (simp_all add: x_op_def mult.assoc)
lemma y_op_power_monom_zero:
  assumes "n < m"
  shows "(y_op ^^ m) (monom c n) = 0"
proof (rule poly_eqI)
  fix k
  have "k + m \<noteq> n" using assms by arith
  then show "coeff ((y_op ^^ m) (monom c n)) k = coeff 0 k"
    by (simp add: y_op_power_coeff coeff_monom)
qed
lemma y_op_power_monom:
  assumes "m \<le> n"
  shows "(y_op ^^ m) (monom c n) =
    monom (pochhammer (of_nat (Suc (n - m))) m * c) (n - m)"
proof (rule poly_eqI)
  fix k
  have "k + m = n \<longleftrightarrow> k = n - m" using assms by arith
  then show "coeff ((y_op ^^ m) (monom c n)) k =
    coeff (monom (pochhammer (of_nat (Suc (n - m))) m * c) (n - m)) k"
    by (auto simp: y_op_power_coeff coeff_monom)
qed

end
