theory Ramified_PBW_Data
  imports "Ramified_PBW_Unique"
begin

text \<open>The source's proof argument and algebra subtype are explicit
premises in HOL. Choice below uses the already proved unique expansion.
No claim is made about canonical data outside that source domain.\<close>

definition ramified_pbw_coeffs ::
  "nat \<Rightarrow> laurent_operator \<Rightarrow> ramified_pbw_coefficients" where
  "ramified_pbw_coeffs l T = (THE a. ramified_normal_eval l a = T)"

lemma ramified_pbw_coeffs_eval:
  assumes "0 < l" "T \<in> ramified_operator_algebra l"
  shows "ramified_normal_eval l (ramified_pbw_coeffs l T) = T"
  unfolding ramified_pbw_coeffs_def
  by (rule theI'[where P="\<lambda>a. ramified_normal_eval l a = T"])
     (rule ramified_operator_algebra_unique_coefficients[OF assms])

lemma ramified_pbw_coeffs_eq_of_eval:
  assumes "0 < l" "T \<in> ramified_operator_algebra l"
    "ramified_normal_eval l a = T"
  shows "ramified_pbw_coeffs l T = a"
proof (rule injD[OF ramified_normal_eval_injective[OF assms(1)]])
  show "ramified_normal_eval l (ramified_pbw_coeffs l T) = ramified_normal_eval l a"
    using ramified_pbw_coeffs_eval[OF assms(1,2)] assms(3) by simp
qed

definition ramified_pbw_order :: "nat \<Rightarrow> laurent_operator \<Rightarrow> nat" where
  "ramified_pbw_order l T = Max (insert 0 (Poly_Mapping.keys (ramified_pbw_coeffs l T)))"

lemma ramified_pbw_coeffs_eq_zero_of_order_lt:
  assumes "0 < l" "T \<in> ramified_operator_algebra l" "ramified_pbw_order l T < j"
  shows "Poly_Mapping.lookup (ramified_pbw_coeffs l T) j = 0"
proof (rule ccontr)
  assume "Poly_Mapping.lookup (ramified_pbw_coeffs l T) j \<noteq> 0"
  then have key: "j \<in> Poly_Mapping.keys (ramified_pbw_coeffs l T)"
    by (simp add: Poly_Mapping.in_keys_iff)
  have "j \<le> ramified_pbw_order l T"
    unfolding ramified_pbw_order_def by (intro Max_ge) (use key in auto)
  then show False using assms(3) by simp
qed

definition ramified_pbw_coeff ::
  "nat \<Rightarrow> laurent_operator \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> complex" where
  "ramified_pbw_coeff l T i j =
    Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l T) j) i"

definition ramified_pbw_support ::
  "nat \<Rightarrow> laurent_operator \<Rightarrow> (int \<times> nat) set" where
  "ramified_pbw_support l T =
    (\<Union>j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
      image (\<lambda>i. (i,j)) (Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l T) j)))"

lemma ramified_pbw_support_finite:
  "finite (ramified_pbw_support l T)"
  by (simp add: ramified_pbw_support_def)

lemma ramified_pbw_support_mem_iff:
  assumes "0 < l" "T \<in> ramified_operator_algebra l"
  shows "(i,j) \<in> ramified_pbw_support l T \<longleftrightarrow> ramified_pbw_coeff l T i j \<noteq> 0"
proof
  assume "(i,j) \<in> ramified_pbw_support l T"
  then show "ramified_pbw_coeff l T i j \<noteq> 0"
    by (auto simp: ramified_pbw_support_def ramified_pbw_coeff_def
        Poly_Mapping.in_keys_iff)
next
  assume nonzero: "ramified_pbw_coeff l T i j \<noteq> 0"
  have outer_nonzero: "Poly_Mapping.lookup (ramified_pbw_coeffs l T) j \<noteq> 0"
  proof
    assume "Poly_Mapping.lookup (ramified_pbw_coeffs l T) j = 0"
    then show False using nonzero by (simp add: ramified_pbw_coeff_def)
  qed
  have outer_key: "j \<in> Poly_Mapping.keys (ramified_pbw_coeffs l T)"
    using outer_nonzero by (simp add: Poly_Mapping.in_keys_iff)
  have inner_key: "i \<in> Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l T) j)"
    using nonzero by (simp add: ramified_pbw_coeff_def Poly_Mapping.in_keys_iff)
  show "(i,j) \<in> ramified_pbw_support l T"
    unfolding ramified_pbw_support_def using outer_key inner_key by blast
qed

lemma ramified_pbw_support_order_bound:
  assumes "0 < l" "T \<in> ramified_operator_algebra l"
    "(i,j) \<in> ramified_pbw_support l T"
  shows "j \<le> ramified_pbw_order l T"
proof (rule ccontr)
  assume "\<not> j \<le> ramified_pbw_order l T"
  then have z: "Poly_Mapping.lookup (ramified_pbw_coeffs l T) j = 0"
    by (intro ramified_pbw_coeffs_eq_zero_of_order_lt[OF assms(1,2)]) simp
  have "ramified_pbw_coeff l T i j \<noteq> 0"
    using ramified_pbw_support_mem_iff[OF assms(1,2)] assms(3) by blast
  then show False by (simp add: ramified_pbw_coeff_def z)
qed

definition ramified_weight :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<times> nat \<Rightarrow> int" where
  "ramified_weight l rho sigma p = rho * fst p + int l * sigma * int (snd p)"

definition ramified_weight_deg ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> laurent_operator \<Rightarrow> int" where
  "ramified_weight_deg l rho sigma T =
    (if ramified_pbw_support l T = {} then 0
     else Max (image (ramified_weight l rho sigma) (ramified_pbw_support l T)))"

definition ramified_leading_support ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> laurent_operator \<Rightarrow> (int \<times> nat) set" where
  "ramified_leading_support l rho sigma T =
    {p \<in> ramified_pbw_support l T.
      ramified_weight l rho sigma p = ramified_weight_deg l rho sigma T}"

lemma ramified_leading_support_finite:
  "finite (ramified_leading_support l rho sigma T)"
  using ramified_pbw_support_finite[of l T]
  by (simp add: ramified_leading_support_def)

text \<open>Carrier and singleton adapters validate the representation choices
against evaluators already checked in the previous slice.\<close>

lemma ramified_pbw_coeffs_zero:
  assumes "0 < l"
  shows "ramified_pbw_coeffs l 0 = 0"
  by (rule ramified_pbw_coeffs_eq_of_eval)
     (simp_all add: assms ramified_operator_algebra_def)

lemma ramified_pbw_zero_data:
  assumes "0 < l"
  shows "ramified_pbw_order l 0 = 0"
    "ramified_pbw_support l 0 = {}"
    "ramified_weight_deg l rho sigma 0 = 0"
    "ramified_leading_support l rho sigma 0 = {}"
  by (simp_all add: ramified_pbw_order_def ramified_pbw_support_def
      ramified_weight_deg_def ramified_leading_support_def ramified_pbw_coeffs_zero[OF assms])

lemma ramified_pbw_coeffs_coeff_mul:
  assumes "0 < l"
  shows "ramified_pbw_coeffs l (ramified_coeff_mul f) = Poly_Mapping.single 0 f"
  by (rule ramified_pbw_coeffs_eq_of_eval)
     (simp_all add: assms coeff_mem_ramified_operator_algebra
       ramified_normal_eval_single laurent_comp_def)

lemma ramified_pbw_coeffs_derivative:
  assumes "0 < l"
  shows "ramified_pbw_coeffs l (ramified_derivative l) = Poly_Mapping.single 1 1"
  by (rule ramified_pbw_coeffs_eq_of_eval)
     (simp_all add: assms derivative_mem_ramified_operator_algebra
       ramified_normal_eval_single ramified_coeff_mul_one)

lemma ramified_pbw_support_coeff_mul:
  assumes "0 < l"
  shows "ramified_pbw_support l (ramified_coeff_mul f) =
    image (\<lambda>i. (i,0)) (Poly_Mapping.keys f)"
  by (cases "f = 0")
     (simp_all add: ramified_pbw_support_def ramified_pbw_coeffs_coeff_mul[OF assms])

end
