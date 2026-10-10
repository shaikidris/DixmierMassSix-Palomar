theory Complex_Norm_Square_Bridge
  imports "Six_Node_Moment_Kernel"
begin

text \<open>Lean Complex.normSq is represented by norm squared.\<close>
lemma norm_sq_Re_Im:
  "norm z ^ 2 = Re z ^ 2 + Im z ^ 2"
  by (simp add: norm_complex_def)

lemma norm_sq_mult:
  "norm (z * w :: complex) ^ 2 = norm z ^ 2 * norm w ^ 2"
  by (simp add: norm_mult power_mult_distrib)

lemma norm_sq_power:
  "norm (z ^ n :: complex) ^ 2 = (norm z ^ 2) ^ n"
  by (simp add: norm_power power_mult[symmetric] mult.commute)

lemma cnj_eq_self_iff_Im_zero:
  "cnj z = z \<longleftrightarrow> Im z = 0"
  by (simp add: complex_eq_iff)

lemma real_Re_of_cnj_fixed:
  "cnj z = z \<Longrightarrow> of_real (Re z) = z"
  by (simp add: cnj_eq_self_iff_Im_zero complex_eq_iff)

lemma norm_sq_affine:
  fixes a :: real and B :: complex and n :: nat
  shows "norm (of_real a + B * of_nat n) ^ 2 =
    a ^ 2 + 2 * a * Re B * of_nat n + (Re B ^ 2 + Im B ^ 2) * (of_nat n :: real) ^ 2"
  by (simp add: norm_sq_Re_Im; algebra)

end
