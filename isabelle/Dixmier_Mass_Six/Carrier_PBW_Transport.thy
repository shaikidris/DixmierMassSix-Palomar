theory Carrier_PBW_Transport
  imports Carrier_PBW_Recovery
begin

definition carrier_weyl :: "'a::field set \<Rightarrow> 'a poly_operator set" where
  "carrier_weyl E = {T. T \<in> weyl_algebra \<and> (\<forall>a b. pbw_coeff T a b \<in> E)}"

lemma carrier_weyl_in_weyl:
  "T \<in> carrier_weyl E \<Longrightarrow> T \<in> weyl_algebra"
  unfolding carrier_weyl_def by simp
lemma carrier_weyl_coeff:
  "T \<in> carrier_weyl E \<Longrightarrow> pbw_coeff T a b \<in> E"
  unfolding carrier_weyl_def by simp

context dixmier_carrier_char_zero_embedding
begin

lemma carrier_weyl_zero: "0 \<in> carrier_weyl E"
  unfolding carrier_weyl_def by (simp add: weyl_algebra_def pbw_coeff_def op_adjoin_zero)
lemma carrier_weyl_add:
  assumes "T \<in> carrier_weyl E" "U \<in> carrier_weyl E"
  shows "T+U \<in> carrier_weyl E"
  using assms unfolding carrier_weyl_def
  by (auto intro: bc_weyl_add E_add simp: pbw_coeff_add)
lemma carrier_weyl_diff:
  assumes "T \<in> carrier_weyl E" "U \<in> carrier_weyl E"
  shows "T-U \<in> carrier_weyl E"
  using assms unfolding carrier_weyl_def
  by (auto intro: bc_weyl_diff E_diff simp: bc_pbw_coeff_diff)
lemma carrier_weyl_smult:
  assumes "T \<in> carrier_weyl E" "c \<in> E"
  shows "(\<lambda>p. smult c (T p)) \<in> carrier_weyl E"
  using assms unfolding carrier_weyl_def
  by (auto intro: bc_weyl_smult E_mult simp: pbw_coeff_smult)
lemma carrier_weyl_sum:
  assumes "finite J" "\<And>j. j \<in> J \<Longrightarrow> T j \<in> carrier_weyl E"
  shows "(\<Sum>j\<in>J. T j) \<in> carrier_weyl E"
  using assms by (induction J rule: finite_induct) (auto intro: carrier_weyl_zero carrier_weyl_add)
lemma carrier_weyl_normal_monomial:
  "normal_monomial a b \<in> carrier_weyl E"
  unfolding carrier_weyl_def
  by (simp add: normal_monomial_in_weyl pbw_coeff_normal_monomial)
lemma carrier_weyl_finite_normal_sum:
  assumes "finite J" "\<And>j. j \<in> J \<Longrightarrow> c j \<in> E"
  shows "finite_normal_sum J c \<in> carrier_weyl E"
  unfolding carrier_weyl_def
  using assms finite_normal_sum_in_weyl[OF assms(1)]
    pbw_coeff_finite_normal_sum[OF assms(1), of c] by auto

text \<open>Coefficient naturality needs no homomorphism laws outside E:
the finite normal form is coefficientwise, and zero is preserved.\<close>
lemma carrier_base_change_in_weyl:
  assumes "T \<in> weyl_algebra"
  shows "concrete_base_change f T \<in> weyl_algebra"
  unfolding concrete_base_change_def
  by (rule finite_normal_sum_in_weyl[OF weyl_pbw_finite_support[OF assms]])
lemma carrier_base_change_coeff:
  assumes "T \<in> weyl_algebra"
  shows "pbw_coeff (concrete_base_change f T) a b = f (pbw_coeff T a b)"
  unfolding concrete_base_change_def
  by (cases "pbw_coeff T a b = 0")
     (simp_all add: target_pbw_coeff_finite_normal_sum[OF weyl_pbw_finite_support[OF assms]])
lemma carrier_base_change_finite_normal_sum:
  assumes "finite S"
  shows "concrete_base_change f (finite_normal_sum S c) = finite_normal_sum S (f \<circ> c)"
proof (rule target_weyl_pbw_injective)
  show "concrete_base_change f (finite_normal_sum S c) \<in> weyl_algebra"
    by (intro carrier_base_change_in_weyl finite_normal_sum_in_weyl assms)
  show "finite_normal_sum S (f \<circ> c) \<in> weyl_algebra"
    by (rule finite_normal_sum_in_weyl[OF assms])
  fix a b
  show "pbw_coeff (concrete_base_change f (finite_normal_sum S c)) a b =
      pbw_coeff (finite_normal_sum S (f \<circ> c)) a b"
    by (simp add: carrier_base_change_coeff[OF finite_normal_sum_in_weyl[OF assms]]
        pbw_coeff_finite_normal_sum[OF assms] target_pbw_coeff_finite_normal_sum[OF assms])
qed
lemma carrier_base_change_support:
  assumes "T \<in> carrier_weyl E"
  shows "{u. pbw_coeff (concrete_base_change f T) (fst u) (snd u) \<noteq> 0} =
    {u. pbw_coeff T (fst u) (snd u) \<noteq> 0}"
  by (simp add: carrier_base_change_coeff[OF carrier_weyl_in_weyl[OF assms]]
      map_eq_zero_on[OF carrier_weyl_coeff[OF assms]])
lemma carrier_base_change_injective:
  assumes "T \<in> carrier_weyl E" "U \<in> carrier_weyl E"
    "concrete_base_change f T = concrete_base_change f U"
  shows "T=U"
proof (rule weyl_pbw_injective[OF carrier_weyl_in_weyl[OF assms(1)] carrier_weyl_in_weyl[OF assms(2)]])
  fix a b
  have "f (pbw_coeff T a b) = f (pbw_coeff U a b)"
    using arg_cong[OF assms(3), of "\<lambda>V. pbw_coeff V a b"]
    by (simp only: carrier_base_change_coeff[OF carrier_weyl_in_weyl[OF assms(1)]]
        carrier_base_change_coeff[OF carrier_weyl_in_weyl[OF assms(2)]])
  then show "pbw_coeff T a b = pbw_coeff U a b"
    by (rule inj_onD[OF injective_on _ carrier_weyl_coeff[OF assms(1)] carrier_weyl_coeff[OF assms(2)]])
qed

lemma carrier_base_change_add:
  assumes T: "T \<in> carrier_weyl E" and U: "U \<in> carrier_weyl E"
  shows "concrete_base_change f (T+U) = concrete_base_change f T + concrete_base_change f U"
proof (rule target_weyl_pbw_injective)
  show "concrete_base_change f (T+U) \<in> weyl_algebra"
    by (intro carrier_base_change_in_weyl bc_weyl_add carrier_weyl_in_weyl[OF T] carrier_weyl_in_weyl[OF U])
  show "concrete_base_change f T + concrete_base_change f U \<in> weyl_algebra"
    by (intro bc_weyl_add carrier_base_change_in_weyl carrier_weyl_in_weyl[OF T] carrier_weyl_in_weyl[OF U])
  fix a b
  show "pbw_coeff (concrete_base_change f (T+U)) a b =
      pbw_coeff (concrete_base_change f T + concrete_base_change f U) a b"
    by (simp only: carrier_base_change_coeff[OF bc_weyl_add[OF carrier_weyl_in_weyl[OF T] carrier_weyl_in_weyl[OF U]]]
        pbw_coeff_add carrier_base_change_coeff[OF carrier_weyl_in_weyl[OF T]]
        carrier_base_change_coeff[OF carrier_weyl_in_weyl[OF U]]
        map_add_on[OF carrier_weyl_coeff[OF T] carrier_weyl_coeff[OF U]])
qed
lemma carrier_base_change_smult:
  assumes T: "T \<in> carrier_weyl E" and c: "c \<in> E"
  shows "concrete_base_change f (\<lambda>p. smult c (T p)) =
    (\<lambda>p. smult (f c) (concrete_base_change f T p))"
proof (rule target_weyl_pbw_injective)
  show "concrete_base_change f (\<lambda>p. smult c (T p)) \<in> weyl_algebra"
    by (intro carrier_base_change_in_weyl bc_weyl_smult carrier_weyl_in_weyl[OF T])
  show "(\<lambda>p. smult (f c) (concrete_base_change f T p)) \<in> weyl_algebra"
    by (intro bc_weyl_smult carrier_base_change_in_weyl carrier_weyl_in_weyl[OF T])
  fix a b
  show "pbw_coeff (concrete_base_change f (\<lambda>p. smult c (T p))) a b =
    pbw_coeff (\<lambda>p. smult (f c) (concrete_base_change f T p)) a b"
    by (simp only: carrier_base_change_coeff[OF bc_weyl_smult[OF carrier_weyl_in_weyl[OF T]]]
        pbw_coeff_smult carrier_base_change_coeff[OF carrier_weyl_in_weyl[OF T]]
        map_mult_on[OF c carrier_weyl_coeff[OF T]])
qed

end
end
