theory Ramified_Normal_Form
  imports "Ramified_Operator"
begin

text \<open>The source RamEnd is exactly the complex-linear carrier in the
existing ambient operator function type. No pointwise operator multiplication
or function-type algebraic power is used for composition or iteration.\<close>

abbreviation ram_end :: "laurent_operator set" where
  "ram_end \<equiv> {T. laurent_linear T}"

lemma ram_end_carrier: "T \<in> ram_end \<longleftrightarrow> laurent_linear T"
  by simp

definition normal_smult :: "complex \<Rightarrow> laurent_operator \<Rightarrow> laurent_operator" where
  "normal_smult c T = (\<lambda>f. laurent_smult c (T f))"

lemma normal_smult_zero [simp]: "normal_smult 0 T = 0" "normal_smult c 0 = 0"
  by (rule ext; simp add: normal_smult_def laurent_smult_as_multiplication)+

lemma normal_smult_one [simp]: "normal_smult 1 T = T"
  by (rule ext) (simp add: normal_smult_def laurent_smult_as_multiplication)

lemma normal_smult_add_scalar:
  "normal_smult (a + b) T = normal_smult a T + normal_smult b T"
  by (rule ext)
     (simp add: normal_smult_def laurent_smult_as_multiplication
       Poly_Mapping.single_add algebra_simps)

lemma normal_smult_add:
  "normal_smult c (T + U) = normal_smult c T + normal_smult c U"
  by (rule ext) (simp add: normal_smult_def laurent_smult_add)

lemma normal_smult_assoc:
  "normal_smult c (normal_smult d T) = normal_smult (c * d) T"
  by (rule ext)
     (simp add: normal_smult_def laurent_smult_as_multiplication
       mult.assoc[symmetric] Poly_Mapping.mult_single)

lemma normal_smult_minus_one:
  "normal_smult (-1) T = - T"
  by (rule ext)
     (simp add: normal_smult_def laurent_smult_as_multiplication Poly_Mapping.single_uminus)

lemma normal_smult_sum:
  "normal_smult c (\<Sum>p\<in>S. F p) = (\<Sum>p\<in>S. normal_smult c (F p))"
proof (cases "finite S")
  case True
  then show ?thesis
  proof (induction S rule: finite_induct)
    case empty
    show ?case by (simp only: sum.empty normal_smult_zero)
  next
    case (insert x A)
    have sum_F: "(\<Sum>p\<in>insert x A. F p) = F x + (\<Sum>p\<in>A. F p)"
      by (rule sum.insert[OF insert.hyps(1) insert.hyps(2)])
    have sum_scaled:
      "(\<Sum>p\<in>insert x A. normal_smult c (F p)) =
        normal_smult c (F x) + (\<Sum>p\<in>A. normal_smult c (F p))"
      by (rule sum.insert[OF insert.hyps(1) insert.hyps(2)])
    show ?case by (simp only: sum_F sum_scaled normal_smult_add insert.IH)
  qed
next
  case False
  have sum_F: "(\<Sum>p\<in>S. F p) = 0" by (rule sum.infinite[OF False])
  have sum_scaled: "(\<Sum>p\<in>S. normal_smult c (F p)) = 0"
    by (rule sum.infinite[OF False])
  show ?thesis by (simp only: sum_F sum_scaled normal_smult_zero)
qed

lemma normal_smult_linear:
  assumes "laurent_linear T"
  shows "laurent_linear (normal_smult c T)"
proof -
  have "laurent_linear (laurent_comp (laurent_scalar c) T)"
    by (intro laurent_linear_comp laurent_linear_scalar assms)
  then show ?thesis by (simp add: normal_smult_def laurent_comp_def laurent_scalar_def)
qed

lemma laurent_linear_zero: "laurent_linear 0"
  using laurent_linear_scalar[of 0] by (simp add: laurent_scalar_zero)

lemma laurent_linear_zero_apply:
  assumes "laurent_linear T"
  shows "T 0 = 0"
proof -
  have "T (laurent_smult 0 0) = laurent_smult 0 (T 0)"
    using assms unfolding laurent_linear_def by blast
  then show ?thesis by (simp add: laurent_smult_as_multiplication)
qed

lemma laurent_comp_assoc:
  "laurent_comp (laurent_comp T U) V = laurent_comp T (laurent_comp U V)"
  by (simp add: laurent_comp_def)

lemma laurent_comp_id [simp]: "laurent_comp id T = T" "laurent_comp T id = T"
  by (simp_all add: laurent_comp_def)

lemma laurent_comp_zero_left [simp]: "laurent_comp 0 T = 0"
  by (rule ext) (simp add: laurent_comp_def)

lemma laurent_comp_zero_right:
  "laurent_linear T \<Longrightarrow> laurent_comp T 0 = 0"
  by (rule ext) (simp add: laurent_comp_def laurent_linear_zero_apply)

lemma laurent_comp_add_left:
  "laurent_comp (T + U) V = laurent_comp T V + laurent_comp U V"
  by (rule ext) (simp add: laurent_comp_def)

lemma laurent_comp_add_right:
  "laurent_linear T \<Longrightarrow> laurent_comp T (U + V) = laurent_comp T U + laurent_comp T V"
  by (rule ext) (simp add: laurent_comp_def laurent_linear_def)

lemma laurent_comp_smult_left:
  "laurent_comp (normal_smult c T) U = normal_smult c (laurent_comp T U)"
  by (simp add: laurent_comp_def normal_smult_def)

lemma laurent_comp_smult_right:
  "laurent_linear T \<Longrightarrow> laurent_comp T (normal_smult c U) = normal_smult c (laurent_comp T U)"
  by (rule ext) (simp add: laurent_comp_def normal_smult_def laurent_linear_def)

lemma laurent_iterate_linear:
  "laurent_linear T \<Longrightarrow> laurent_linear (T ^^ n)"
proof (induction n)
  case 0
  then show ?case by (simp only: funpow.simps(1) laurent_linear_id)
next
  case (Suc n)
  have "laurent_linear (laurent_comp T (T ^^ n))"
    by (intro laurent_linear_comp Suc)
  then show ?case by (simp add: laurent_comp_def comp_def)
qed

lemma ramified_coeff_mul_mul:
  "laurent_comp (ramified_coeff_mul f) (ramified_coeff_mul g) = ramified_coeff_mul (f * g)"
  by (rule ext) (simp add: laurent_comp_def ramified_coeff_mul_def mult.assoc)

inductive_set laurent_span :: "laurent_operator set \<Rightarrow> laurent_operator set"
  for G where
  generator: "T \<in> G \<Longrightarrow> T \<in> laurent_span G"
| zero: "0 \<in> laurent_span G"
| add: "T \<in> laurent_span G \<Longrightarrow> U \<in> laurent_span G \<Longrightarrow> T + U \<in> laurent_span G"
| smult: "T \<in> laurent_span G \<Longrightarrow> normal_smult c T \<in> laurent_span G"

definition laurent_submodule :: "laurent_operator set \<Rightarrow> bool" where
  "laurent_submodule A \<longleftrightarrow>
    (\<forall>T\<in>A. laurent_linear T) \<and> 0 \<in> A \<and>
    (\<forall>T\<in>A. \<forall>U\<in>A. T + U \<in> A) \<and>
    (\<forall>c T. T \<in> A \<longrightarrow> normal_smult c T \<in> A)"

lemma laurent_span_linear:
  assumes "\<And>T. T \<in> G \<Longrightarrow> laurent_linear T" "T \<in> laurent_span G"
  shows "laurent_linear T"
  using assms(2) by (induction rule: laurent_span.induct)
    (blast intro: assms(1) laurent_linear_zero laurent_linear_add normal_smult_linear)+

lemma laurent_span_submodule:
  "(\<And>T. T \<in> G \<Longrightarrow> laurent_linear T) \<Longrightarrow> laurent_submodule (laurent_span G)"
  by (auto simp: laurent_submodule_def intro: laurent_span_linear laurent_span.intros)

lemma laurent_span_least:
  assumes "G \<subseteq> A" "laurent_submodule A"
  shows "laurent_span G \<subseteq> A"
proof
  fix T assume "T \<in> laurent_span G"
  then show "T \<in> A"
    by (induction rule: laurent_span.induct)
       (use assms in \<open>unfold laurent_submodule_def; blast\<close>)+
qed

lemma laurent_span_diff:
  assumes "T \<in> laurent_span G" "U \<in> laurent_span G"
  shows "T - U \<in> laurent_span G"
proof -
  have "T + normal_smult (-1) U \<in> laurent_span G"
    by (intro laurent_span.add laurent_span.smult assms)
  then show ?thesis by (simp add: normal_smult_minus_one)
qed

definition normal_atom :: "nat \<Rightarrow> (ramified_laurent \<times> nat) \<Rightarrow> laurent_operator" where
  "normal_atom l p = laurent_comp (ramified_coeff_mul (fst p)) (ramified_derivative l ^^ snd p)"

definition normal_span :: "nat \<Rightarrow> laurent_operator set" where
  "normal_span l = laurent_span (range (normal_atom l))"

lemma normal_atom_linear: "laurent_linear (normal_atom l p)"
  unfolding normal_atom_def
  by (intro laurent_linear_comp ramified_coeff_mul_linear laurent_iterate_linear ramified_derivative_linear)

lemma normal_span_linear: "T \<in> normal_span l \<Longrightarrow> laurent_linear T"
  unfolding normal_span_def
  by (rule laurent_span_linear) (auto intro: normal_atom_linear)

lemma normal_span_submodule: "laurent_submodule (normal_span l)"
  unfolding normal_span_def
  by (rule laurent_span_submodule) (auto intro: normal_atom_linear)

lemma normal_span_least:
  "range (normal_atom l) \<subseteq> A \<Longrightarrow> laurent_submodule A \<Longrightarrow> normal_span l \<subseteq> A"
  unfolding normal_span_def by (rule laurent_span_least)

lemma normal_atom_mem:
  "laurent_comp (ramified_coeff_mul f) (ramified_derivative l ^^ n) \<in> normal_span l"
  unfolding normal_span_def
  by (rule laurent_span.generator) (auto simp: normal_atom_def intro!: image_eqI[where x="(f,n)"])

lemma normal_span_coeff_left:
  assumes "T \<in> normal_span l"
  shows "laurent_comp (ramified_coeff_mul f) T \<in> normal_span l"
  using assms unfolding normal_span_def
proof (induction rule: laurent_span.induct)
  case (generator T)
  then obtain g n where "T = normal_atom l (g,n)" by auto
  then have "laurent_comp (ramified_coeff_mul f) T = normal_atom l (f * g,n)"
    by (simp add: normal_atom_def laurent_comp_assoc[symmetric] ramified_coeff_mul_mul)
  then show ?case by (auto intro: laurent_span.generator)
next
  case zero
  show ?case
    unfolding laurent_comp_zero_right[OF ramified_coeff_mul_linear]
    by (rule laurent_span.zero)
next
  case (add T U)
  show ?case
    unfolding laurent_comp_add_right[OF ramified_coeff_mul_linear]
    by (rule laurent_span.add[OF add.IH])
next
  case (smult T c)
  show ?case
    unfolding laurent_comp_smult_right[OF ramified_coeff_mul_linear]
    by (rule laurent_span.smult[OF smult.IH])
qed

lemma normal_atom_derivative:
  "laurent_comp (ramified_derivative l) (normal_atom l (f,n)) =
    normal_atom l (f,Suc n) + normal_atom l (ramified_derivative l f,n)"
  by (rule ext)
     (simp add: normal_atom_def laurent_comp_def ramified_coeff_mul_def
       ramified_derivative_mul comp_def add.commute)

lemma normal_span_derivative_left:
  assumes "T \<in> normal_span l"
  shows "laurent_comp (ramified_derivative l) T \<in> normal_span l"
  using assms unfolding normal_span_def
proof (induction rule: laurent_span.induct)
  case (generator T)
  then obtain f n where eq: "T = normal_atom l (f,n)" by auto
  show ?case
    unfolding eq normal_atom_derivative
    by (intro laurent_span.add laurent_span.generator rangeI)
next
  case zero
  show ?case
    unfolding laurent_comp_zero_right[OF ramified_derivative_linear]
    by (rule laurent_span.zero)
next
  case (add T U)
  show ?case
    unfolding laurent_comp_add_right[OF ramified_derivative_linear]
    by (rule laurent_span.add[OF add.IH])
next
  case (smult T c)
  show ?case
    unfolding laurent_comp_smult_right[OF ramified_derivative_linear]
    by (rule laurent_span.smult[OF smult.IH])
qed

lemma normal_span_derivative_pow_left:
  assumes "T \<in> normal_span l"
  shows "laurent_comp (ramified_derivative l ^^ n) T \<in> normal_span l"
proof (induction n)
  case 0
  show ?case using assms by (simp only: funpow.simps(1) laurent_comp_id)
next
  case (Suc n)
  have "laurent_comp (ramified_derivative l) (laurent_comp (ramified_derivative l ^^ n) T) \<in> normal_span l"
    by (rule normal_span_derivative_left[OF Suc])
  then show ?case by (simp add: laurent_comp_def comp_def)
qed

lemma normal_span_mul:
  assumes "T \<in> normal_span l" "U \<in> normal_span l"
  shows "laurent_comp T U \<in> normal_span l"
  using assms(1) unfolding normal_span_def
proof (induction rule: laurent_span.induct)
  case (generator T)
  then obtain f n where eq: "T = normal_atom l (f,n)" by auto
  have "laurent_comp T U \<in> normal_span l"
    unfolding eq normal_atom_def
    by (simp add: laurent_comp_assoc normal_span_coeff_left normal_span_derivative_pow_left assms(2))
  then show ?case unfolding normal_span_def .
next
  case zero
  show ?case unfolding laurent_comp_zero_left by (rule laurent_span.zero)
next
  case (add T V)
  show ?case unfolding laurent_comp_add_left by (rule laurent_span.add[OF add.IH])
next
  case (smult T c)
  show ?case unfolding laurent_comp_smult_left by (rule laurent_span.smult[OF smult.IH])
qed

lemma ramified_coeff_mul_one:
  "ramified_coeff_mul 1 = id"
  by (rule ext) (simp add: ramified_coeff_mul_def)

lemma ramified_coeff_mul_C:
  "ramified_coeff_mul (Poly_Mapping.single 0 c) = laurent_scalar c"
  by (rule ext) (simp add: ramified_coeff_mul_def laurent_scalar_def laurent_smult_as_multiplication)

lemma normal_span_scalar:
  "laurent_scalar c \<in> normal_span l"
  using normal_atom_mem[where f="Poly_Mapping.single 0 c" and l=l and n=0]
  by (simp only: funpow.simps(1) laurent_comp_id ramified_coeff_mul_C)

lemma normal_span_add:
  "T \<in> normal_span l \<Longrightarrow> U \<in> normal_span l \<Longrightarrow> T + U \<in> normal_span l"
  unfolding normal_span_def by (rule laurent_span.add)

lemma normal_span_diff:
  "T \<in> normal_span l \<Longrightarrow> U \<in> normal_span l \<Longrightarrow> T - U \<in> normal_span l"
  unfolding normal_span_def by (rule laurent_span_diff)

lemma normal_span_subalgebra:
  "laurent_subalgebra (normal_span l)"
  by (auto simp: laurent_subalgebra_def intro: normal_span_linear normal_span_scalar
      normal_span_mul normal_span_add normal_span_diff)

lemma ramified_operator_algebra_normal:
  "T \<in> ramified_operator_algebra l \<Longrightarrow> T \<in> normal_span l"
proof -
  assume member: "T \<in> ramified_operator_algebra l"
  have coeff: "ramified_coeff_mul f \<in> normal_span l" for f
    using normal_atom_mem[where f=f and l=l and n=0]
    by (simp only: funpow.simps(1) laurent_comp_id)
  have deriv: "ramified_derivative l \<in> normal_span l"
    using normal_atom_mem[where f=1 and l=l and n="Suc 0"]
    by (simp only: funpow.simps comp_id ramified_coeff_mul_one laurent_comp_id)
  have "ramified_operator_algebra l \<subseteq> normal_span l"
    by (rule ramified_operator_algebra_least[OF normal_span_subalgebra coeff deriv])
  then show ?thesis using member by blast
qed

text \<open>Actual finite support on coefficient/order pairs, not an informal
finite-span predicate. The following evaluation is the exact Finsupp sum.\<close>

type_synonym normal_coefficients = "(ramified_laurent \<times> nat, complex) poly_mapping"

definition normal_expansion :: "nat \<Rightarrow> normal_coefficients \<Rightarrow> laurent_operator" where
  "normal_expansion l c = (\<Sum>p\<in>Poly_Mapping.keys c.
     normal_smult (Poly_Mapping.lookup c p) (normal_atom l p))"

lemma normal_expansion_zero [simp]: "normal_expansion l 0 = 0"
  by (simp add: normal_expansion_def)

lemma normal_expansion_single:
  "normal_expansion l (Poly_Mapping.single p a) = normal_smult a (normal_atom l p)"
  by (cases "a = 0") (simp_all add: normal_expansion_def)

lemma normal_expansion_add:
  "normal_expansion l (c + d) = normal_expansion l c + normal_expansion l d"
  unfolding normal_expansion_def
  by (rule Poly_Mapping.setsum_keys_plus_distrib)
     (simp_all only: normal_smult_zero normal_smult_add_scalar)

lemma normal_coefficients_scale_lookup:
  "Poly_Mapping.lookup (Poly_Mapping.map ((*) a) c) p = a * Poly_Mapping.lookup c p"
  for c :: normal_coefficients
  by (simp add: Poly_Mapping.map.rep_eq when_def)

lemma normal_expansion_scale:
  "normal_expansion l (Poly_Mapping.map ((*) a) c) = normal_smult a (normal_expansion l c)"
proof -
  have sum_eq:
    "(\<Sum>p\<in>Poly_Mapping.keys (Poly_Mapping.map ((*) a) c).
        normal_smult (Poly_Mapping.lookup (Poly_Mapping.map ((*) a) c) p) (normal_atom l p)) =
      (\<Sum>p\<in>Poly_Mapping.keys c.
        normal_smult (a * Poly_Mapping.lookup c p) (normal_atom l p))"
    by (rule sum.mono_neutral_cong_left)
       (auto simp: Poly_Mapping.in_keys_iff normal_coefficients_scale_lookup)
  show ?thesis
    unfolding normal_expansion_def
    by (simp only: sum_eq normal_smult_sum normal_smult_assoc)
qed

lemma normal_span_finite_expansion:
  assumes "T \<in> normal_span l"
  shows "\<exists>c :: normal_coefficients. normal_expansion l c = T"
  using assms unfolding normal_span_def
proof (induction rule: laurent_span.induct)
  case (generator T)
  then obtain p where "T = normal_atom l p" by auto
  then show ?case using normal_expansion_single[of l p 1] by auto
next
  case zero
  show ?case using normal_expansion_zero[of l] by blast
next
  case (add T U)
  then obtain c d where "normal_expansion l c = T" "normal_expansion l d = U" by blast
  then show ?case using normal_expansion_add[of l c d] by blast
next
  case (smult T a)
  then obtain c where "normal_expansion l c = T" by blast
  then show ?case using normal_expansion_scale[of l a c] by blast
qed

lemma ramified_operator_algebra_finite_normal:
  assumes "T \<in> ramified_operator_algebra l"
  shows "\<exists>c :: normal_coefficients.
    (\<Sum>p\<in>Poly_Mapping.keys c.
      normal_smult (Poly_Mapping.lookup c p)
        (laurent_comp (ramified_coeff_mul (fst p)) (ramified_derivative l ^^ snd p))) = T"
  using normal_span_finite_expansion[OF ramified_operator_algebra_normal[OF assms]]
  by (simp add: normal_expansion_def normal_atom_def)

lemma laurent_adjoin_iterate:
  "T \<in> laurent_adjoin G \<Longrightarrow> (T ^^ n) \<in> laurent_adjoin G"
proof (induction n)
  case 0
  then show ?case by (simp only: funpow.simps(1) laurent_adjoin_id)
next
  case (Suc n)
  have "laurent_comp T (T ^^ n) \<in> laurent_adjoin G"
    by (intro laurent_adjoin.comp Suc)
  then show ?case by (simp add: laurent_comp_def comp_def)
qed

lemma ramified_operator_algebra_submodule:
  "laurent_submodule (ramified_operator_algebra l)"
  unfolding laurent_submodule_def
  using ramified_operator_algebra_linear
  by (auto simp: ramified_operator_algebra_def normal_smult_def
      intro: laurent_adjoin.add laurent_adjoin_smult)

lemma normal_span_le_operator:
  "normal_span l \<subseteq> ramified_operator_algebra l"
proof (rule normal_span_least[OF _ ramified_operator_algebra_submodule])
  show "range (normal_atom l) \<subseteq> ramified_operator_algebra l"
    unfolding normal_atom_def ramified_operator_algebra_def
    by (auto intro: laurent_adjoin.comp laurent_adjoin_iterate laurent_adjoin.generator)
qed

lemma ramified_operator_algebra_eq_normal_span:
  "ramified_operator_algebra l = normal_span l"
  using ramified_operator_algebra_normal normal_span_le_operator by blast

end
