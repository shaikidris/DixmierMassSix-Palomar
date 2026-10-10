theory Ramified_Operator
  imports Ramified_Derivation
begin

text \<open>The scalar embedding sends a complex number to its scalar
identity map. The generated subalgebra lives inside the explicit linear
carrier. Its multiplication is named composition throughout.\<close>

definition laurent_scalar :: "complex \<Rightarrow> laurent_operator" where
  "laurent_scalar c f = laurent_smult c f"

lemma laurent_smult_add:
  "laurent_smult c (f + g) = laurent_smult c f + laurent_smult c g"
  by (simp add: laurent_smult_as_multiplication algebra_simps)

lemma laurent_linear_add:
  "laurent_linear F \<Longrightarrow> laurent_linear G \<Longrightarrow> laurent_linear (F + G)"
  by (auto simp: laurent_linear_def laurent_smult_add algebra_simps)

lemma laurent_linear_scalar:
  "laurent_linear (laurent_scalar c)"
  by (simp add: laurent_linear_def laurent_scalar_def
      laurent_smult_as_multiplication algebra_simps)

lemma laurent_scalar_zero: "laurent_scalar 0 = 0"
  by (rule ext) (simp add: laurent_scalar_def laurent_smult_as_multiplication)

lemma laurent_scalar_one: "laurent_scalar 1 = id"
  by (rule ext) (simp add: laurent_scalar_def laurent_smult_as_multiplication)

inductive_set laurent_adjoin :: "laurent_operator set \<Rightarrow> laurent_operator set"
  for G where
  generator: "T \<in> G \<Longrightarrow> T \<in> laurent_adjoin G"
| scalar: "laurent_scalar c \<in> laurent_adjoin G"
| add: "T \<in> laurent_adjoin G \<Longrightarrow> U \<in> laurent_adjoin G \<Longrightarrow> T + U \<in> laurent_adjoin G"
| diff: "T \<in> laurent_adjoin G \<Longrightarrow> U \<in> laurent_adjoin G \<Longrightarrow> T - U \<in> laurent_adjoin G"
| comp: "T \<in> laurent_adjoin G \<Longrightarrow> U \<in> laurent_adjoin G \<Longrightarrow> laurent_comp T U \<in> laurent_adjoin G"

definition laurent_subalgebra :: "laurent_operator set \<Rightarrow> bool" where
  "laurent_subalgebra A \<longleftrightarrow>
    (\<forall>T\<in>A. laurent_linear T) \<and>
    (\<forall>c. laurent_scalar c \<in> A) \<and>
    (\<forall>T\<in>A. \<forall>U\<in>A. T + U \<in> A \<and> T - U \<in> A \<and> laurent_comp T U \<in> A)"

lemma laurent_adjoin_linear:
  assumes "\<And>T. T \<in> G \<Longrightarrow> laurent_linear T" "T \<in> laurent_adjoin G"
  shows "laurent_linear T"
  using assms(2) by (induction rule: laurent_adjoin.induct)
    (blast intro: assms(1) laurent_linear_scalar laurent_linear_add laurent_linear_diff laurent_linear_comp)+

lemma laurent_adjoin_subalgebra:
  "(\<And>T. T \<in> G \<Longrightarrow> laurent_linear T) \<Longrightarrow> laurent_subalgebra (laurent_adjoin G)"
  by (auto simp: laurent_subalgebra_def intro: laurent_adjoin_linear laurent_adjoin.intros)

lemma laurent_adjoin_least:
  assumes "G \<subseteq> A" "laurent_subalgebra A"
  shows "laurent_adjoin G \<subseteq> A"
proof
  fix T assume "T \<in> laurent_adjoin G"
  then show "T \<in> A"
    by (induction rule: laurent_adjoin.induct)
       (use assms in \<open>unfold laurent_subalgebra_def; blast\<close>)+
qed

lemma laurent_adjoin_zero [simp]: "0 \<in> laurent_adjoin G"
  using laurent_adjoin.scalar[of 0 G] by (simp add: laurent_scalar_zero)

lemma laurent_adjoin_id [simp]: "id \<in> laurent_adjoin G"
  using laurent_adjoin.scalar[of 1 G] by (simp add: laurent_scalar_one)

lemma laurent_adjoin_smult:
  assumes "T \<in> laurent_adjoin G"
  shows "(\<lambda>f. laurent_smult c (T f)) \<in> laurent_adjoin G"
  using laurent_adjoin.comp[OF laurent_adjoin.scalar assms, of c]
  by (simp add: laurent_comp_def laurent_scalar_def)

definition ramified_operator_algebra :: "nat \<Rightarrow> laurent_operator set" where
  "ramified_operator_algebra l =
    laurent_adjoin (range ramified_coeff_mul \<union> {ramified_derivative l})"

lemma ramified_operator_algebra_linear:
  "T \<in> ramified_operator_algebra l \<Longrightarrow> laurent_linear T"
  unfolding ramified_operator_algebra_def
  by (rule laurent_adjoin_linear)
     (auto intro: ramified_coeff_mul_linear ramified_derivative_linear)

lemma ramified_operator_algebra_subalgebra:
  "laurent_subalgebra (ramified_operator_algebra l)"
  unfolding ramified_operator_algebra_def
  by (rule laurent_adjoin_subalgebra)
     (auto intro: ramified_coeff_mul_linear ramified_derivative_linear)

lemma ramified_operator_algebra_least:
  assumes "laurent_subalgebra A"
    and "\<And>f. ramified_coeff_mul f \<in> A"
    and "ramified_derivative l \<in> A"
  shows "ramified_operator_algebra l \<subseteq> A"
  unfolding ramified_operator_algebra_def
  by (rule laurent_adjoin_least) (use assms in auto)

lemma coeff_mem_ramified_operator_algebra:
  "ramified_coeff_mul f \<in> ramified_operator_algebra l"
  by (auto simp: ramified_operator_algebra_def intro: laurent_adjoin.generator)

lemma derivative_mem_ramified_operator_algebra:
  "ramified_derivative l \<in> ramified_operator_algebra l"
  by (auto simp: ramified_operator_algebra_def intro: laurent_adjoin.generator)

lemma ramified_normal_order:
  "laurent_comp (ramified_derivative l) (ramified_coeff_mul f) =
    laurent_comp (ramified_coeff_mul f) (ramified_derivative l) +
      ramified_coeff_mul (ramified_derivative l f)"
  by (rule ext)
     (simp add: laurent_comp_def ramified_coeff_mul_def ramified_derivative_mul add.commute)

lemma ramified_X_mem:
  "ramified_X l \<in> ramified_operator_algebra l"
proof -
  have "ramified_X l = ramified_coeff_mul (laurent_T (int l))"
    by (rule ext) (simp add: ramified_X_def ramified_coeff_mul_def)
  then show ?thesis using coeff_mem_ramified_operator_algebra by simp
qed

end
