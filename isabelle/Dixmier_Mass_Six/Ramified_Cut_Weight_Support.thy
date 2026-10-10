theory Ramified_Cut_Weight_Support
  imports "Ramified_Cut_Coeff_Recurrence"
begin

lemmas ramified_derivative_coeff = ramified_derivative_lookup
lemmas ramified_derivative_support_subset = ramified_derivative_support

definition laurent_upper :: "ramified_laurent \<Rightarrow> int \<Rightarrow> bool" where
  "laurent_upper f B \<longleftrightarrow> (\<forall>i\<in>Poly_Mapping.keys f. i \<le> B)"

lemma laurent_upper_derivative:
  "laurent_upper f B \<Longrightarrow> laurent_upper (ramified_derivative l f) (B-int l)"
  using ramified_derivative_support[of l f]
  unfolding laurent_upper_def by force

lemma laurent_upper_add:
  "laurent_upper f B \<Longrightarrow> laurent_upper g B \<Longrightarrow> laurent_upper (f+g) B"
  using Poly_Mapping.keys_add[of f g] unfolding laurent_upper_def by blast

lemma laurent_upper_cut_shift_mul:
  assumes "laurent_upper f B"
  shows "laurent_upper (ramified_cut_shift l rho sigma c * f)
    (B+ramified_cut_exponent l rho sigma)"
proof -
  have shift: "Poly_Mapping.keys (ramified_cut_shift l rho sigma c) \<subseteq>
    {ramified_cut_exponent l rho sigma}"
    by (simp add: ramified_cut_shift_def)
  show ?thesis
    using Poly_Mapping.keys_mult[of "ramified_cut_shift l rho sigma c" f] shift assms
    unfolding laurent_upper_def by force
qed

lemma laurent_upper_zero: "laurent_upper 0 B"
  by (simp add: laurent_upper_def)
lemma laurent_upper_mono:
  "B \<le> C \<Longrightarrow> laurent_upper f B \<Longrightarrow> laurent_upper f C"
  unfolding laurent_upper_def by auto
lemma laurent_upper_one: "laurent_upper 1 0"
  by (simp add: laurent_upper_def)

lemma ramified_cut_exponent_gt_neg_index:
  assumes "0 < l" "0 < rho" "rho dvd int l" "0 < rho+sigma"
  shows "-int l < ramified_cut_exponent l rho sigma"
proof -
  have weight: "rho * ramified_cut_exponent l rho sigma = int l * sigma"
    by (rule ramified_cut_exponent_weight[OF assms(3)])
  have identity: "rho * (ramified_cut_exponent l rho sigma + int l) = int l * (rho+sigma)"
    using weight by (simp add: algebra_simps)
  have product: "0 < rho * (ramified_cut_exponent l rho sigma + int l)"
    by (simp only: identity) (use assms(1,4) in simp)
  have "0 < ramified_cut_exponent l rho sigma + int l"
  proof (rule ccontr)
    assume "\<not> 0 < ramified_cut_exponent l rho sigma + int l"
    then have "rho * (ramified_cut_exponent l rho sigma + int l) \<le> rho*0"
      by (intro mult_left_mono) (use assms(2) in auto)
    then show False using product by simp
  qed
  then show ?thesis by arith
qed

lemma ramified_cut_power_upper:
  assumes positive: "0 < l" and rho: "0 < rho" and divides: "rho dvd int l"
    and sum_positive: "0 < rho+sigma"
  shows "laurent_upper
    (Poly_Mapping.lookup (ramified_shift_pbw_power l (ramified_cut_shift l rho sigma c) n) j)
    ((int n-int j)*ramified_cut_exponent l rho sigma)"
proof -
  let ?k = "ramified_cut_exponent l rho sigma"
  have hk: "-int l < ?k"
    by (rule ramified_cut_exponent_gt_neg_index[OF positive rho divides sum_positive])
  show ?thesis
  proof (induction n arbitrary: j)
    case 0
    show ?case
    proof (cases "j=0")
      case True
      then show ?thesis by (simp only: ramified_shift_pbw_power.simps Poly_Mapping.lookup_single when_def)
        (simp add: laurent_upper_one)
    next
      case False
      then have "0 < j" by simp
      then show ?thesis by (simp add: ramified_shift_pbw_power_zero_above
          Poly_Mapping.lookup_one when_def laurent_upper_zero)
    qed
  next
    case (Suc n)
    let ?a = "ramified_shift_pbw_power l (ramified_cut_shift l rho sigma c) n"
    let ?B = "(int (Suc n)-int j)*?k"
    have prev: "laurent_upper (if j=0 then 0 else Poly_Mapping.lookup ?a (j-1)) ?B"
    proof (cases "j=0")
      case True then show ?thesis by (simp add: laurent_upper_zero)
    next
      case False
      then have cast: "int (j-1)=int j-1" by presburger
      have eq: "(int n-int (j-1))*?k=?B" by (subst cast) (simp add: algebra_simps)
      show ?thesis using Suc.IH[of "j-1"] False by (simp only: if_False eq)
    qed
    have derivative: "laurent_upper (ramified_derivative l (Poly_Mapping.lookup ?a j)) ?B"
    proof (rule laurent_upper_mono[OF _ laurent_upper_derivative[OF Suc.IH[of j]]])
      show "(int n-int j)*?k-int l \<le> ?B"
        using hk by (simp add: algebra_simps)
    qed
    have shift: "laurent_upper (ramified_cut_shift l rho sigma c * Poly_Mapping.lookup ?a j) ?B"
      using laurent_upper_cut_shift_mul[OF Suc.IH[of j], of l rho sigma c]
      by (simp add: algebra_simps)
    show ?case
      by (simp only: ramified_shift_pbw_power.simps ramified_shift_pbw_step_apply)
         (rule laurent_upper_add[OF laurent_upper_add[OF prev derivative] shift])
  qed
qed

lemma ramified_cut_power_weight_upper:
  assumes positive: "0 < l" and rho: "0 < rho" and divides: "rho dvd int l"
    and sum_positive: "0 < rho+sigma"
    and member: "(i,j) \<in> ramified_pbw_support l
      (ramified_shifted_Y_gen l (ramified_cut_shift l rho sigma c) ^^ n)"
  shows "ramified_weight l rho sigma (i,j) \<le> int n * int l * sigma"
proof -
  have carrier: "(ramified_shifted_Y_gen l (ramified_cut_shift l rho sigma c) ^^ n)
      \<in> ramified_operator_algebra l" by (rule ramified_shift_pbw_power_carrier)
  have nonzero: "Poly_Mapping.lookup
    (Poly_Mapping.lookup (ramified_shift_pbw_power l (ramified_cut_shift l rho sigma c) n) j) i \<noteq> 0"
    using ramified_pbw_support_mem_iff[OF positive carrier, of i j] member
    by (simp add: ramified_pbw_coeff_def ramified_shift_pbw_power_canonical[OF positive])
  have upper: "i \<le> (int n-int j)*ramified_cut_exponent l rho sigma"
    using ramified_cut_power_upper[OF positive rho divides sum_positive, of c n j] nonzero
    by (simp add: laurent_upper_def Poly_Mapping.in_keys_iff)
  have scaled: "rho*i \<le> rho*((int n-int j)*ramified_cut_exponent l rho sigma)"
    by (rule mult_left_mono[OF upper]) (use rho in simp)
  have edge: "rho*((int n-int j)*ramified_cut_exponent l rho sigma) =
      (int n-int j)*(int l*sigma)"
  proof -
    have "rho*((int n-int j)*ramified_cut_exponent l rho sigma) =
      (int n-int j)*(rho*ramified_cut_exponent l rho sigma)" by (simp add: algebra_simps)
    then show ?thesis by (simp only: ramified_cut_exponent_weight[OF divides])
  qed
  show ?thesis using scaled
    by (simp only: edge ramified_weight_def fst_conv snd_conv) (simp add: algebra_simps; arith)
qed

lemma ramified_cut_power_top_support:
  "0 < l \<Longrightarrow> (0,n) \<in> ramified_pbw_support l
    (ramified_shifted_Y_gen l (ramified_cut_shift l rho sigma c) ^^ n)"
  by (subst ramified_pbw_support_mem_iff)
     (simp_all add: ramified_shift_pbw_power_carrier ramified_pbw_coeff_def
       ramified_shift_pbw_power_canonical ramified_shift_pbw_power_top)

lemma ramified_cut_power_weight_deg:
  assumes "0 < l" "0 < rho" "rho dvd int l" "0 < rho+sigma"
  shows "ramified_weight_deg l rho sigma
    (ramified_shifted_Y_gen l (ramified_cut_shift l rho sigma c) ^^ n) = int n*int l*sigma"
proof -
  let ?T = "ramified_shifted_Y_gen l (ramified_cut_shift l rho sigma c) ^^ n"
  let ?S = "image (ramified_weight l rho sigma) (ramified_pbw_support l ?T)"
  have finite: "finite ?S" by (simp add: ramified_pbw_support_finite)
  have top: "(0,n) \<in> ramified_pbw_support l ?T" by (rule ramified_cut_power_top_support[OF assms(1)])
  have attained: "int n*int l*sigma \<in> ?S"
    using top by (force simp: ramified_weight_def algebra_simps)
  have nonempty: "?S \<noteq> {}" using attained by blast
  have bound: "\<And>w. w \<in> ?S \<Longrightarrow> w \<le> int n*int l*sigma"
    using ramified_cut_power_weight_upper[OF assms] by auto
  have "Max ?S = int n*int l*sigma"
  proof (rule antisym)
    show "Max ?S \<le> int n*int l*sigma" by (rule Max.boundedI[OF finite nonempty bound])
    show "int n*int l*sigma \<le> Max ?S" by (rule Max.coboundedI[OF finite attained])
  qed
  then show ?thesis using top by (auto simp: ramified_weight_deg_def)
qed
end
