theory Ramified_Laurent_Commutator
  imports "Ramified_Laurent_Leibniz"
    "HOL-Library.Function_Algebras"
begin

text \<open>The explicit linearity carrier gives the exact complex-linear
endomorphisms. Multiplication of operators below is named composition, never
the pointwise multiplication of the ambient function type.\<close>

definition laurent_comp :: "laurent_operator \<Rightarrow> laurent_operator \<Rightarrow> laurent_operator" where
  "laurent_comp F G = (\<lambda>f. F (G f))"

definition ramified_X :: "nat \<Rightarrow> laurent_operator" where
  "ramified_X l f = laurent_T (int l) * f"

lemma laurent_smult_diff:
  "laurent_smult c (f - g) = laurent_smult c f - laurent_smult c g"
  by (simp add: laurent_smult_as_multiplication algebra_simps)

lemma laurent_linear_id: "laurent_linear id"
  by (simp add: laurent_linear_def)

lemma laurent_linear_comp:
  "laurent_linear F \<Longrightarrow> laurent_linear G \<Longrightarrow> laurent_linear (laurent_comp F G)"
  by (auto simp: laurent_linear_def laurent_comp_def)

lemma laurent_linear_diff:
  "laurent_linear F \<Longrightarrow> laurent_linear G \<Longrightarrow> laurent_linear (F - G)"
  by (auto simp: laurent_linear_def laurent_smult_diff algebra_simps)

lemma ramified_X_linear:
  "laurent_linear (ramified_X l)"
  by (simp add: laurent_linear_def ramified_X_def laurent_smult_as_multiplication algebra_simps)

lemma ramified_derivative_X_unit:
  assumes "0 < l"
  shows "ramified_derivative l (laurent_T (int l)) = 1"
proof -
  have nz: "(of_nat l :: complex) \<noteq> 0" using assms by simp
  show ?thesis
    by (subst ramified_derivative_T)
       (simp add: laurent_smult_as_multiplication laurent_T_def nz assms)
qed

lemma ramified_derivative_X_comm_all:
  assumes "0 < l"
  shows "ramified_derivative l (laurent_T (int l) * f) -
    laurent_T (int l) * ramified_derivative l f = f"
  by (simp add: ramified_derivative_mul ramified_derivative_X_unit[OF assms])

lemma ramified_derivative_X_comm:
  assumes "0 < l"
  shows "ramified_derivative l (laurent_T (int l) * laurent_T n) -
    laurent_T (int l) * ramified_derivative l (laurent_T n) = laurent_T n"
  by (rule ramified_derivative_X_comm_all[OF assms])

lemma ramified_end_comm:
  assumes "0 < l"
  shows "laurent_comp (ramified_derivative l) (ramified_X l) -
    laurent_comp (ramified_X l) (ramified_derivative l) = id"
  by (rule ext)
     (simp add: laurent_comp_def ramified_X_def ramified_derivative_X_comm_all[OF assms])

lemma ramified_end_comm_linear:
  "laurent_linear (laurent_comp (ramified_derivative l) (ramified_X l) -
    laurent_comp (ramified_X l) (ramified_derivative l))"
  by (intro laurent_linear_diff laurent_linear_comp
      ramified_derivative_linear ramified_X_linear)

end
