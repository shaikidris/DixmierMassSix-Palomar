theory Ramified_Derivation
  imports "Ramified_Laurent_Commutator"
begin

text \<open>The exact carrier of complex-linear Laurent derivations. The
named package below has the existing derivative as its underlying map.\<close>

definition laurent_derivation :: "laurent_operator \<Rightarrow> bool" where
  "laurent_derivation D \<longleftrightarrow> laurent_linear D \<and>
    (\<forall>f g. D (f * g) = D f * g + f * D g)"

definition ramified_derivation :: "nat \<Rightarrow> laurent_operator" where
  "ramified_derivation l = ramified_derivative l"

lemma ramified_derivation_carrier:
  "laurent_derivation (ramified_derivation l)"
  by (simp add: laurent_derivation_def ramified_derivation_def
      ramified_derivative_linear ramified_derivative_mul)

lemma ramified_derivation_apply:
  "ramified_derivation l f = ramified_derivative l f"
  by (simp add: ramified_derivation_def)

definition ramified_coeff_mul :: "ramified_laurent \<Rightarrow> laurent_operator" where
  "ramified_coeff_mul f g = f * g"

lemma ramified_coeff_mul_linear:
  "laurent_linear (ramified_coeff_mul f)"
  by (simp add: laurent_linear_def ramified_coeff_mul_def
      laurent_smult_as_multiplication algebra_simps)

lemma ramified_derivative_coeff_comm:
  "laurent_comp (ramified_derivative l) (ramified_coeff_mul f) -
    laurent_comp (ramified_coeff_mul f) (ramified_derivative l) =
    ramified_coeff_mul (ramified_derivative l f)"
  by (rule ext)
     (simp add: laurent_comp_def ramified_coeff_mul_def ramified_derivative_mul)

end
