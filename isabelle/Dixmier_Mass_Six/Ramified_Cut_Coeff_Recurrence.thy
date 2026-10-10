theory Ramified_Cut_Coeff_Recurrence
  imports Ramified_Cut_Recurrence
begin
lemma ramified_coeff_left_linear_apply:
  "Poly_Mapping.lookup (ramified_coeff_left_linear h a) j = h * Poly_Mapping.lookup a j"
  unfolding ramified_coeff_left_linear_def
  by (cases "j \<in> Poly_Mapping.keys a")
     (simp_all add: Poly_Mapping.lookup_sum Poly_Mapping.lookup_single when_def Poly_Mapping.in_keys_iff)

lemma ramified_derivative_left_linear_apply:
  "Poly_Mapping.lookup (ramified_derivative_left_linear l a) j =
    (if j = 0 then 0 else Poly_Mapping.lookup a (j-1)) +
      ramified_derivative l (Poly_Mapping.lookup a j)"
proof -
  have index: "\<And>k. Suc k = j \<longleftrightarrow> j \<noteq> 0 \<and> k = j-1" by presburger
  show ?thesis
    unfolding ramified_derivative_left_linear_def
    by (cases "j = 0"; cases "j \<in> Poly_Mapping.keys a"; cases "j-1 \<in> Poly_Mapping.keys a")
       (simp_all add: Poly_Mapping.lookup_sum Poly_Mapping.lookup_add Poly_Mapping.lookup_single
         sum.distrib index when_def Poly_Mapping.in_keys_iff
         laurent_linear_zero_apply[OF ramified_derivative_linear])
qed
lemma ramified_shift_pbw_step_apply:
  "Poly_Mapping.lookup (ramified_shift_pbw_step l h a) j =
    (if j=0 then 0 else Poly_Mapping.lookup a (j-1)) +
      ramified_derivative l (Poly_Mapping.lookup a j) + h * Poly_Mapping.lookup a j"
  by (simp add: ramified_shift_pbw_step_def Poly_Mapping.lookup_add
      ramified_derivative_left_linear_apply ramified_coeff_left_linear_apply)
lemma ramified_shift_pbw_power_zero_above:
  "n < j \<Longrightarrow> Poly_Mapping.lookup (ramified_shift_pbw_power l h n) j = 0"
proof (induction n arbitrary: j)
  case 0
  then have "j \<noteq> 0" by presburger
  then show ?case by (simp only: ramified_shift_pbw_power.simps Poly_Mapping.lookup_single when_def)
      simp
next
  case (Suc n)
  have "j \<noteq> 0" "n < j-1" "n < j" using Suc.prems by presburger+
  then show ?case
    by (simp add: ramified_shift_pbw_step_apply Suc.IH
        laurent_linear_zero_apply[OF ramified_derivative_linear])
qed
lemma ramified_shift_pbw_power_top:
  "Poly_Mapping.lookup (ramified_shift_pbw_power l h n) n = 1"
  by (induction n)
     (simp_all add: ramified_shift_pbw_step_apply ramified_shift_pbw_power_zero_above
       laurent_linear_zero_apply[OF ramified_derivative_linear])
lemma ramified_shifted_Y_gen_order:
  assumes positive: "0 < l"
  shows "ramified_pbw_order l (ramified_shifted_Y_gen l h ^^ n) = n"
proof -
  let ?S = "insert 0 (Poly_Mapping.keys (ramified_shift_pbw_power l h n))"
  have bound: "\<And>j. j \<in> ?S \<Longrightarrow> j \<le> n"
    using ramified_shift_pbw_power_zero_above[of n _ l h]
    by (auto simp: Poly_Mapping.in_keys_iff) (meson not_le)
  have member: "n \<in> ?S"
    by (simp add: Poly_Mapping.in_keys_iff ramified_shift_pbw_power_top)
  have "Max ?S = n"
  proof (rule antisym)
    show "Max ?S \<le> n" by (rule Max.boundedI) (auto intro: bound)
    show "n \<le> Max ?S" by (rule Max.coboundedI) (simp, rule member)
  qed
  then show ?thesis by (simp add: ramified_pbw_order_def ramified_shift_pbw_power_canonical[OF positive])
qed
end
