theory Concrete_Field_Base_Change
  imports Embedded_Field_Recovery "Exact_Normal_Order"
begin

definition extend_pbw_coeffs :: "('k \<Rightarrow> 'l) \<Rightarrow> (nat \<times> nat \<Rightarrow> 'k) \<Rightarrow> nat \<times> nat \<Rightarrow> 'l" where
  "extend_pbw_coeffs i c = i \<circ> c"

definition concrete_base_change :: "('k::field \<Rightarrow> 'l::field) \<Rightarrow> 'k poly_operator \<Rightarrow> 'l poly_operator" where
  "concrete_base_change i T = finite_normal_sum
    {u. pbw_coeff T (fst u) (snd u) \<noteq> 0}
    (\<lambda>u. i (pbw_coeff T (fst u) (snd u)))"

lemma bc_weyl_add:
  "T \<in> weyl_algebra \<Longrightarrow> U \<in> weyl_algebra \<Longrightarrow> T+U \<in> weyl_algebra"
  unfolding weyl_algebra_def by (rule op_adjoin.add)
lemma bc_weyl_comp:
  "T \<in> weyl_algebra \<Longrightarrow> U \<in> weyl_algebra \<Longrightarrow> op_comp T U \<in> weyl_algebra"
  unfolding weyl_algebra_def by (rule op_adjoin.comp)
lemma bc_weyl_smult:
  "T \<in> weyl_algebra \<Longrightarrow> (\<lambda>p. smult c (T p)) \<in> weyl_algebra"
  unfolding weyl_algebra_def by (rule op_adjoin_smult)
lemma bc_weyl_sum:
  "(\<And>u. u \<in> S \<Longrightarrow> T u \<in> weyl_algebra) \<Longrightarrow> (\<Sum>u\<in>S. T u) \<in> weyl_algebra"
  unfolding weyl_algebra_def by (rule op_adjoin_sum)
lemma bc_pbw_coeff_sum:
  "pbw_coeff (\<Sum>u\<in>S. T u) a b = (\<Sum>u\<in>S. pbw_coeff (T u) a b)"
proof -
  interpret c: additive "\<lambda>T. pbw_coeff T a b"
    by standard (rule pbw_coeff_add)
  show ?thesis by (rule c.sum)
qed

lemma bc_weyl_diff:
  "T \<in> weyl_algebra \<Longrightarrow> U \<in> weyl_algebra \<Longrightarrow> T-U \<in> weyl_algebra"
  unfolding weyl_algebra_def by (rule op_adjoin.diff)
lemma bc_pbw_coeff_diff:
  "pbw_coeff (T-U) a b = pbw_coeff T a b - pbw_coeff U a b"
proof -
  interpret c: additive "\<lambda>T. pbw_coeff T a b"
    by standard (rule pbw_coeff_add)
  show ?thesis by (rule c.diff)
qed

context dixmier_char_zero_embedding
begin

interpretation coefficient_map: additive i
  by standard (rule map_add)

lemma map_eq_zero_iff [simp]: "i a = 0 \<longleftrightarrow> a = 0"
  using injective map_zero by (metis injD)

lemma embedding_sum:
  "i (\<Sum>u\<in>S. c u) = (\<Sum>u\<in>S. i (c u))"
  by (induction S rule: infinite_finite_induct) (simp_all add: map_add)

lemma extend_pbw_coeffs_support:
  "{u. extend_pbw_coeffs i c u \<noteq> 0} = {u. c u \<noteq> 0}"
  by (simp add: extend_pbw_coeffs_def)

lemma concrete_base_change_in_weyl:
  assumes "T \<in> weyl_algebra"
  shows "concrete_base_change i T \<in> weyl_algebra"
  unfolding concrete_base_change_def
  by (rule finite_normal_sum_in_weyl[OF weyl_pbw_finite_support[OF assms]])

lemma pbw_coeff_concrete_base_change:
  assumes "T \<in> weyl_algebra"
  shows "pbw_coeff (concrete_base_change i T) a b = i (pbw_coeff T a b)"
  unfolding concrete_base_change_def
  by (cases "pbw_coeff T a b = 0")
     (simp_all add: target_pbw_coeff_finite_normal_sum[OF weyl_pbw_finite_support[OF assms]])

lemma concrete_base_change_finite_normal_sum:
  assumes "finite S"
  shows "concrete_base_change i (finite_normal_sum S c) = finite_normal_sum S (i \<circ> c)"
proof (rule target_weyl_pbw_injective)
  show "concrete_base_change i (finite_normal_sum S c) \<in> weyl_algebra"
    by (intro concrete_base_change_in_weyl finite_normal_sum_in_weyl assms)
  show "finite_normal_sum S (i \<circ> c) \<in> weyl_algebra"
    by (rule finite_normal_sum_in_weyl[OF assms])
  fix a b
  show "pbw_coeff (concrete_base_change i (finite_normal_sum S c)) a b =
      pbw_coeff (finite_normal_sum S (i \<circ> c)) a b"
    by (simp add: pbw_coeff_concrete_base_change[OF finite_normal_sum_in_weyl[OF assms]]
        pbw_coeff_finite_normal_sum[OF assms] target_pbw_coeff_finite_normal_sum[OF assms])
qed

lemma concrete_base_change_zero [simp]: "concrete_base_change i 0 = 0"
  using concrete_base_change_finite_normal_sum[OF finite.emptyI, of "\<lambda>_. 0"] by simp

lemma concrete_base_change_normal_monomial:
  "concrete_base_change i (normal_monomial a b) = normal_monomial a b"
  using concrete_base_change_finite_normal_sum[of "{(a,b)}" "\<lambda>_. 1"]
  by (simp add: finite_normal_sum_def map_one)

lemma concrete_base_change_id [simp]: "concrete_base_change i id = id"
  using concrete_base_change_normal_monomial[of 0 0] by simp
lemma concrete_base_change_x [simp]: "concrete_base_change i x_op = x_op"
  using concrete_base_change_normal_monomial[of 1 0] by (simp add: normal_monomial_def)
lemma concrete_base_change_y [simp]: "concrete_base_change i y_op = y_op"
  using concrete_base_change_normal_monomial[of 0 1] by (simp add: normal_monomial_def)

lemma concrete_base_change_add:
  assumes "T \<in> weyl_algebra" "U \<in> weyl_algebra"
  shows "concrete_base_change i (T+U) = concrete_base_change i T + concrete_base_change i U"
proof (rule target_weyl_pbw_injective)
  show "concrete_base_change i (T+U) \<in> weyl_algebra"
    by (intro concrete_base_change_in_weyl bc_weyl_add assms)
  show "concrete_base_change i T + concrete_base_change i U \<in> weyl_algebra"
    by (intro bc_weyl_add concrete_base_change_in_weyl assms)
  fix a b
  show "pbw_coeff (concrete_base_change i (T+U)) a b =
      pbw_coeff (concrete_base_change i T + concrete_base_change i U) a b"
    by (simp add: pbw_coeff_concrete_base_change[OF bc_weyl_add[OF assms]]
        pbw_coeff_add pbw_coeff_concrete_base_change[OF assms(1)]
        pbw_coeff_concrete_base_change[OF assms(2)] map_add)
qed

lemma concrete_base_change_smult:
  assumes "T \<in> weyl_algebra"
  shows "concrete_base_change i (\<lambda>p. smult c (T p)) =
    (\<lambda>p. smult (i c) (concrete_base_change i T p))"
proof (rule target_weyl_pbw_injective)
  show "concrete_base_change i (\<lambda>p. smult c (T p)) \<in> weyl_algebra"
    by (intro concrete_base_change_in_weyl bc_weyl_smult assms)
  show "(\<lambda>p. smult (i c) (concrete_base_change i T p)) \<in> weyl_algebra"
    by (intro bc_weyl_smult concrete_base_change_in_weyl assms)
  fix a b
  show "pbw_coeff (concrete_base_change i (\<lambda>p. smult c (T p))) a b =
      pbw_coeff (\<lambda>p. smult (i c) (concrete_base_change i T p)) a b"
    by (simp add: pbw_coeff_concrete_base_change[OF bc_weyl_smult[OF assms]]
        pbw_coeff_smult pbw_coeff_concrete_base_change[OF assms] map_mult)
qed

lemma concrete_base_change_sum:
  assumes "\<And>u. u \<in> S \<Longrightarrow> T u \<in> weyl_algebra"
  shows "concrete_base_change i (\<Sum>u\<in>S. T u) = (\<Sum>u\<in>S. concrete_base_change i (T u))"
proof (rule target_weyl_pbw_injective)
  show "concrete_base_change i (\<Sum>u\<in>S. T u) \<in> weyl_algebra"
    by (intro concrete_base_change_in_weyl bc_weyl_sum assms)
  show "(\<Sum>u\<in>S. concrete_base_change i (T u)) \<in> weyl_algebra"
    by (intro bc_weyl_sum concrete_base_change_in_weyl assms)
  fix a b
  show "pbw_coeff (concrete_base_change i (\<Sum>u\<in>S. T u)) a b =
      pbw_coeff (\<Sum>u\<in>S. concrete_base_change i (T u)) a b"
    by (simp add: pbw_coeff_concrete_base_change[OF bc_weyl_sum[OF assms]]
        bc_pbw_coeff_sum embedding_sum pbw_coeff_concrete_base_change[OF assms])
qed

lemma concrete_base_change_scalar:
  "concrete_base_change i (op_scalar c) = op_scalar (i c)"
  using concrete_base_change_smult[of id c]
  by (simp add: weyl_algebra_def op_scalar_def)

lemma concrete_base_change_support:
  assumes "T \<in> weyl_algebra"
  shows "{u. pbw_coeff (concrete_base_change i T) (fst u) (snd u) \<noteq> 0} =
    {u. pbw_coeff T (fst u) (snd u) \<noteq> 0}"
  by (simp add: pbw_coeff_concrete_base_change[OF assms])

lemma concrete_base_change_injective:
  assumes "T \<in> weyl_algebra" "U \<in> weyl_algebra"
    "concrete_base_change i T = concrete_base_change i U"
  shows "T = U"
proof (rule weyl_pbw_injective[OF assms(1,2)])
  fix a b
  have "i (pbw_coeff T a b) = i (pbw_coeff U a b)"
    using arg_cong[OF assms(3), of "\<lambda>V. pbw_coeff V a b"]
    by (simp add: pbw_coeff_concrete_base_change[OF assms(1)]
        pbw_coeff_concrete_base_change[OF assms(2)])
  then show "pbw_coeff T a b = pbw_coeff U a b" by (rule injD[OF injective])
qed

lemma concrete_base_change_zero_reflection:
  assumes "T \<in> weyl_algebra" "concrete_base_change i T = 0"
  shows "T = 0"
  by (rule concrete_base_change_injective[OF assms(1)])
     (simp_all add: weyl_algebra_def assms(2))


lemma concrete_base_change_diff:
  assumes "T \<in> weyl_algebra" "U \<in> weyl_algebra"
  shows "concrete_base_change i (T-U) = concrete_base_change i T - concrete_base_change i U"
proof (rule target_weyl_pbw_injective)
  show "concrete_base_change i (T-U) \<in> weyl_algebra"
    by (intro concrete_base_change_in_weyl bc_weyl_diff assms)
  show "concrete_base_change i T - concrete_base_change i U \<in> weyl_algebra"
    by (intro bc_weyl_diff concrete_base_change_in_weyl assms)
  fix a b
  show "pbw_coeff (concrete_base_change i (T-U)) a b =
      pbw_coeff (concrete_base_change i T - concrete_base_change i U) a b"
    by (simp add: pbw_coeff_concrete_base_change[OF bc_weyl_diff[OF assms]]
        bc_pbw_coeff_diff pbw_coeff_concrete_base_change[OF assms(1)]
        pbw_coeff_concrete_base_change[OF assms(2)] coefficient_map.diff)
qed

lemma concrete_base_change_normal_terms:
  "concrete_base_change i (\<Sum>u\<in>S. (\<lambda>p. smult (c u) (normal_monomial (a u) (b u) p))) =
    (\<Sum>u\<in>S. (\<lambda>p. smult (i (c u)) (normal_monomial (a u) (b u) p)))"
proof -
  have mem: "(\<lambda>p. smult (c u) (normal_monomial (a u) (b u) p)) \<in> weyl_algebra" for u
    by (intro bc_weyl_smult normal_monomial_in_weyl)
  show ?thesis
    by (simp only: concrete_base_change_sum[OF mem]
        concrete_base_change_smult[OF normal_monomial_in_weyl] concrete_base_change_normal_monomial)
qed

lemma concrete_base_change_normal_triple_sum:
  "concrete_base_change i
     (\<Sum>u\<in>S. \<Sum>v\<in>T. \<Sum>k\<in>I u v.
       (\<lambda>p. smult (c u v k) (normal_monomial (a u v k) (b u v k) p))) =
     (\<Sum>u\<in>S. \<Sum>v\<in>T. \<Sum>k\<in>I u v.
       (\<lambda>p. smult (i (c u v k)) (normal_monomial (a u v k) (b u v k) p)))"
proof -
  have inner: "(\<Sum>k\<in>I u v. (\<lambda>p. smult (c u v k)
      (normal_monomial (a u v k) (b u v k) p))) \<in> weyl_algebra" for u v
    by (intro bc_weyl_sum bc_weyl_smult normal_monomial_in_weyl)
  have middle: "(\<Sum>v\<in>T. \<Sum>k\<in>I u v. (\<lambda>p. smult (c u v k)
      (normal_monomial (a u v k) (b u v k) p))) \<in> weyl_algebra" for u
    by (intro bc_weyl_sum inner)
  show ?thesis
    by (simp only: concrete_base_change_sum[OF middle] concrete_base_change_sum[OF inner]
        concrete_base_change_normal_terms)
qed

lemma concrete_base_change_finite_product:
  assumes "finite S" "finite T"
  shows "concrete_base_change i (op_comp (finite_normal_sum S c) (finite_normal_sum T d)) =
    op_comp (finite_normal_sum S (i \<circ> c)) (finite_normal_sum T (i \<circ> d))"
  by (simp only: finite_normal_sum_mul[OF assms] concrete_base_change_normal_triple_sum
      map_mult map_of_nat comp_apply)

lemma concrete_base_change_comp:
  assumes "T \<in> weyl_algebra" "U \<in> weyl_algebra"
  shows "concrete_base_change i (op_comp T U) = op_comp (concrete_base_change i T) (concrete_base_change i U)"
proof -
  obtain c where cf: "finite {u. c u \<noteq> 0}" and cT: "finite_normal_sum {u. c u \<noteq> 0} c = T"
    using weyl_exists_finite_coordinates[OF assms(1)] by blast
  obtain d where df: "finite {u. d u \<noteq> 0}" and dU: "finite_normal_sum {u. d u \<noteq> 0} d = U"
    using weyl_exists_finite_coordinates[OF assms(2)] by blast
  have cMap: "concrete_base_change i T = finite_normal_sum {u. c u \<noteq> 0} (i \<circ> c)"
    using concrete_base_change_finite_normal_sum[OF cf, of c] cT by simp
  have dMap: "concrete_base_change i U = finite_normal_sum {u. d u \<noteq> 0} (i \<circ> d)"
    using concrete_base_change_finite_normal_sum[OF df, of d] dU by simp
  show ?thesis
    using concrete_base_change_finite_product[OF cf df, of c d]
    by (simp only: cT dU cMap dMap)
qed

lemma concrete_base_change_commutator_one:
  assumes "P \<in> weyl_algebra" "Q \<in> weyl_algebra"
    "op_comp Q P - op_comp P Q = id"
  shows "op_comp (concrete_base_change i Q) (concrete_base_change i P) -
    op_comp (concrete_base_change i P) (concrete_base_change i Q) = id"
proof -
  have "concrete_base_change i (op_comp Q P - op_comp P Q) = concrete_base_change i id"
    using assms(3) by simp
  then show ?thesis
    by (simp add: concrete_base_change_diff[OF bc_weyl_comp[OF assms(2,1)] bc_weyl_comp[OF assms(1,2)]]
        concrete_base_change_comp[OF assms(1,2)] concrete_base_change_comp[OF assms(2,1)])
qed

end
end
