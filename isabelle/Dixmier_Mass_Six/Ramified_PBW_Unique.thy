theory Ramified_PBW_Unique
  imports Ramified_PBW_Coefficients
begin

text \<open>R1B retains the source proof architecture: the linear evaluation
range contains the normal span; positive-index injectivity then gives uniqueness.
Coefficient sequences have finite natural-order support with arbitrary complex
Laurent coefficients. No truncation or positivity condition on coefficients is used.\<close>

definition ramified_pbw_smult ::
  "complex \<Rightarrow> ramified_pbw_coefficients \<Rightarrow> ramified_pbw_coefficients" where
  "ramified_pbw_smult c a = Poly_Mapping.map (laurent_smult c) a"

lemma ramified_pbw_smult_lookup [simp]:
  "Poly_Mapping.lookup (ramified_pbw_smult c a) j =
    laurent_smult c (Poly_Mapping.lookup a j)"
  by (simp add: ramified_pbw_smult_def Poly_Mapping.map.rep_eq when_def
      laurent_smult_as_multiplication)

lemma ramified_pbw_smult_keys:
  "Poly_Mapping.keys (ramified_pbw_smult c a) \<subseteq> Poly_Mapping.keys a"
  by (auto simp: Poly_Mapping.in_keys_iff laurent_smult_as_multiplication)

lemma ramified_normal_eval_expand:
  assumes "finite S" "Poly_Mapping.keys a \<subseteq> S"
  shows "ramified_normal_eval l a g =
    (\<Sum>j\<in>S. Poly_Mapping.lookup a j * (ramified_derivative l ^^ j) g)"
  unfolding ramified_normal_eval_apply
  by (rule sum.mono_neutral_cong_left)
     (use assms in \<open>auto simp: Poly_Mapping.in_keys_iff\<close>)

lemma ramified_normal_eval_smult:
  "ramified_normal_eval l (ramified_pbw_smult c a) =
    normal_smult c (ramified_normal_eval l a)"
proof (rule ext)
  fix g
  have expanded:
    "ramified_normal_eval l (ramified_pbw_smult c a) g =
      (\<Sum>j\<in>Poly_Mapping.keys a.
        laurent_smult c (Poly_Mapping.lookup a j) * (ramified_derivative l ^^ j) g)"
    using ramified_normal_eval_expand[
        where S="Poly_Mapping.keys a" and a="ramified_pbw_smult c a" and l=l and g=g]
      ramified_pbw_smult_keys[of c a] by simp
  have "ramified_normal_eval l (ramified_pbw_smult c a) g =
      (\<Sum>j\<in>Poly_Mapping.keys a.
        laurent_smult c (Poly_Mapping.lookup a j) * (ramified_derivative l ^^ j) g)"
    by (rule expanded)
  also have "\<dots> = laurent_smult c
      (\<Sum>j\<in>Poly_Mapping.keys a.
        Poly_Mapping.lookup a j * (ramified_derivative l ^^ j) g)"
    by (simp add: laurent_smult_as_multiplication sum_distrib_left mult.assoc)
  also have "\<dots> = normal_smult c (ramified_normal_eval l a) g"
    by (simp only: normal_smult_def ramified_normal_eval_apply)
  finally show "ramified_normal_eval l (ramified_pbw_smult c a) g =
    normal_smult c (ramified_normal_eval l a) g" .
qed

definition ramified_coeff_mul_linear :: "ramified_laurent \<Rightarrow> laurent_operator" where
  "ramified_coeff_mul_linear = ramified_coeff_mul"

lemma ramified_coeff_mul_linear_carrier:
  "laurent_linear (ramified_coeff_mul_linear f)"
  by (simp add: ramified_coeff_mul_linear_def ramified_coeff_mul_linear)

lemma ramified_coeff_mul_linear_add:
  "ramified_coeff_mul_linear (f + g) =
    ramified_coeff_mul_linear f + ramified_coeff_mul_linear g"
  by (rule ext)
     (simp add: ramified_coeff_mul_linear_def ramified_coeff_mul_def algebra_simps)

lemma ramified_coeff_mul_linear_smult:
  "ramified_coeff_mul_linear (laurent_smult c f) =
    normal_smult c (ramified_coeff_mul_linear f)"
  by (rule ext)
     (simp add: ramified_coeff_mul_linear_def ramified_coeff_mul_def normal_smult_def
        laurent_smult_as_multiplication mult.assoc)

definition ramified_normal_eval_linear ::
  "nat \<Rightarrow> ramified_pbw_coefficients \<Rightarrow> laurent_operator" where
  "ramified_normal_eval_linear l = ramified_normal_eval l"

lemma ramified_normal_eval_linear_carrier:
  "laurent_linear (ramified_normal_eval_linear l a)"
  by (simp add: ramified_normal_eval_linear_def ramified_normal_eval_linear)

lemma ramified_normal_eval_linear_add:
  "ramified_normal_eval_linear l (a + b) =
    ramified_normal_eval_linear l a + ramified_normal_eval_linear l b"
  by (simp add: ramified_normal_eval_linear_def ramified_normal_eval_add)

lemma ramified_normal_eval_linear_smult:
  "ramified_normal_eval_linear l (ramified_pbw_smult c a) =
    normal_smult c (ramified_normal_eval_linear l a)"
  by (simp add: ramified_normal_eval_linear_def ramified_normal_eval_smult)

lemma ramified_normal_eval_linear_apply:
  "ramified_normal_eval_linear l a = ramified_normal_eval l a"
  by (simp add: ramified_normal_eval_linear_def)

lemma ramified_normal_eval_linear_single:
  "ramified_normal_eval_linear l (Poly_Mapping.single n f) =
    laurent_comp (ramified_coeff_mul f) (ramified_derivative l ^^ n)"
  by (simp add: ramified_normal_eval_linear_def ramified_normal_eval_single)

lemma ramified_normal_eval_range_submodule:
  "laurent_submodule (range (ramified_normal_eval l))"
proof (unfold laurent_submodule_def, intro conjI)
  show "\<forall>T\<in>range (ramified_normal_eval l). laurent_linear T"
    by (auto intro: ramified_normal_eval_linear)
  show "0 \<in> range (ramified_normal_eval l)"
    by (rule image_eqI[where x=0]) simp_all
  show "\<forall>T\<in>range (ramified_normal_eval l).
    \<forall>U\<in>range (ramified_normal_eval l). T + U \<in> range (ramified_normal_eval l)"
  proof (intro ballI)
    fix T U
    assume T: "T \<in> range (ramified_normal_eval l)"
      and U: "U \<in> range (ramified_normal_eval l)"
    obtain a b where T': "T = ramified_normal_eval l a"
      and U': "U = ramified_normal_eval l b" using T U by blast
    show "T + U \<in> range (ramified_normal_eval l)"
      unfolding T' U'
      by (rule image_eqI[where x="a + b"])
         (simp_all add: ramified_normal_eval_add)
  qed
  show "\<forall>c T. T \<in> range (ramified_normal_eval l) \<longrightarrow>
    normal_smult c T \<in> range (ramified_normal_eval l)"
  proof (intro allI impI)
    fix c T
    assume "T \<in> range (ramified_normal_eval l)"
    then obtain a where T: "T = ramified_normal_eval l a" by blast
    show "normal_smult c T \<in> range (ramified_normal_eval l)"
      unfolding T
      by (rule image_eqI[where x="ramified_pbw_smult c a"])
         (simp_all add: ramified_normal_eval_smult)
  qed
qed

lemma normal_span_in_evaluation_range:
  "normal_span l \<subseteq> range (ramified_normal_eval l)"
proof (rule normal_span_least)
  show "range (normal_atom l) \<subseteq> range (ramified_normal_eval l)"
  proof
    fix T assume "T \<in> range (normal_atom l)"
    then obtain f n where T: "T = normal_atom l (f,n)" by auto
    show "T \<in> range (ramified_normal_eval l)"
      unfolding T normal_atom_def
      by (rule image_eqI[where x="Poly_Mapping.single n f"])
         (simp_all add: ramified_normal_eval_single)
  qed
  show "laurent_submodule (range (ramified_normal_eval l))"
    by (rule ramified_normal_eval_range_submodule)
qed

theorem ramified_operator_algebra_exists_coefficients:
  assumes "T \<in> ramified_operator_algebra l"
  shows "\<exists>a :: ramified_pbw_coefficients. ramified_normal_eval l a = T"
  using normal_span_in_evaluation_range ramified_operator_algebra_normal[OF assms]
  by blast

theorem ramified_operator_algebra_unique_coefficients:
  assumes "0 < l" "T \<in> ramified_operator_algebra l"
  shows "\<exists>!a :: ramified_pbw_coefficients. ramified_normal_eval l a = T"
proof -
  obtain a where a: "ramified_normal_eval l a = T"
    using ramified_operator_algebra_exists_coefficients[OF assms(2)] by blast
  show ?thesis
  proof (rule ex1I[where a=a])
    show "ramified_normal_eval l a = T" by (rule a)
  next
    fix b assume b: "ramified_normal_eval l b = T"
    show "b = a"
    proof (rule injD[OF ramified_normal_eval_injective[OF assms(1)]])
      show "ramified_normal_eval l b = ramified_normal_eval l a" using b a by simp
    qed
  qed
qed

end
