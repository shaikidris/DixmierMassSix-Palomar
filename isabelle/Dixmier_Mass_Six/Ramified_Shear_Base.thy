theory Ramified_Shear_Base
  imports "Ramified_PBW_Data"
begin

lemma ramified_algebra_add:
  "T \<in> ramified_operator_algebra l \<Longrightarrow> U \<in> ramified_operator_algebra l \<Longrightarrow>
   T + U \<in> ramified_operator_algebra l"
  by (simp add: ramified_operator_algebra_def laurent_adjoin.add)

lemma ramified_algebra_diff:
  "T \<in> ramified_operator_algebra l \<Longrightarrow> U \<in> ramified_operator_algebra l \<Longrightarrow>
   T - U \<in> ramified_operator_algebra l"
  by (simp add: ramified_operator_algebra_def laurent_adjoin.diff)

lemma ramified_algebra_comp:
  "T \<in> ramified_operator_algebra l \<Longrightarrow> U \<in> ramified_operator_algebra l \<Longrightarrow>
   laurent_comp T U \<in> ramified_operator_algebra l"
  by (simp add: ramified_operator_algebra_def laurent_adjoin.comp)

lemma ramified_algebra_smult:
  "T \<in> ramified_operator_algebra l \<Longrightarrow> normal_smult c T \<in> ramified_operator_algebra l"
  by (simp add: ramified_operator_algebra_def normal_smult_def laurent_adjoin_smult)

definition ramified_shifted_Y :: "nat \<Rightarrow> ramified_laurent \<Rightarrow> laurent_operator" where
  "ramified_shifted_Y l h = ramified_derivative l + ramified_coeff_mul h"

lemma ramified_shifted_Y_linear:
  "laurent_linear (ramified_shifted_Y l h)"
  by (simp add: ramified_shifted_Y_def laurent_linear_add
      ramified_derivative_linear ramified_coeff_mul_linear)

lemma ramified_shifted_Y_normal_order:
  "laurent_comp (ramified_shifted_Y l h) (ramified_coeff_mul f) =
   laurent_comp (ramified_coeff_mul f) (ramified_shifted_Y l h) +
     ramified_coeff_mul (ramified_derivative l f)"
  by (rule ext)
     (simp add: ramified_shifted_Y_def laurent_comp_def ramified_coeff_mul_def
       ramified_derivative_mul algebra_simps)

definition ramified_shifted_algebra ::
  "nat \<Rightarrow> ramified_laurent \<Rightarrow> laurent_operator set" where
  "ramified_shifted_algebra l h =
   laurent_adjoin (range ramified_coeff_mul \<union> {ramified_shifted_Y l h})"

lemma ramified_shifted_algebra_eq:
  "ramified_shifted_algebra l h = ramified_operator_algebra l"
proof (rule equalityI)
  show "ramified_shifted_algebra l h \<subseteq> ramified_operator_algebra l"
    unfolding ramified_shifted_algebra_def
    by (rule laurent_adjoin_least[OF _ ramified_operator_algebra_subalgebra])
       (auto simp: ramified_shifted_Y_def intro: coeff_mem_ramified_operator_algebra
         derivative_mem_ramified_operator_algebra ramified_algebra_add)
  have sub: "laurent_subalgebra (ramified_shifted_algebra l h)"
    unfolding ramified_shifted_algebra_def
    by (rule laurent_adjoin_subalgebra)
       (auto intro: ramified_coeff_mul_linear ramified_shifted_Y_linear)
  have coeff: "ramified_coeff_mul f \<in> ramified_shifted_algebra l h" for f
    by (auto simp: ramified_shifted_algebra_def intro: laurent_adjoin.generator)
  have shift: "ramified_shifted_Y l h \<in> ramified_shifted_algebra l h"
    by (auto simp: ramified_shifted_algebra_def intro: laurent_adjoin.generator)
  have deriv: "ramified_derivative l \<in> ramified_shifted_algebra l h"
  proof -
    have "ramified_shifted_Y l h - ramified_coeff_mul h \<in> ramified_shifted_algebra l h"
      using sub coeff[of h] shift by (auto simp: laurent_subalgebra_def)
    then show ?thesis by (simp add: ramified_shifted_Y_def)
  qed
  show "ramified_operator_algebra l \<subseteq> ramified_shifted_algebra l h"
    by (rule ramified_operator_algebra_least[OF sub coeff deriv])
qed

lemma ramified_shifted_Y_X_comm:
  "0 < l \<Longrightarrow>
   laurent_comp (ramified_shifted_Y l h) (ramified_X l) -
   laurent_comp (ramified_X l) (ramified_shifted_Y l h) = id"
  by (rule ext)
     (simp add: ramified_shifted_Y_def laurent_comp_def ramified_X_def
       ramified_coeff_mul_def ramified_derivative_mul ramified_derivative_X
       algebra_simps)
end
