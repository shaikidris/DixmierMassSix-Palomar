theory Partial_Derivatives
  imports Weighted_Components
begin

definition biv_dx :: "'a::field bivariate \<Rightarrow> 'a bivariate" where
  "biv_dx p = map_poly pderiv p"
definition biv_dy :: "'a::field bivariate \<Rightarrow> 'a bivariate" where
  "biv_dy p = pderiv p"
definition biv_deriv :: "bool \<Rightarrow> 'a::field bivariate \<Rightarrow> 'a bivariate" where
  "biv_deriv is_y p = (if is_y then biv_dy p else biv_dx p)"
definition biv_poisson :: "'a::field bivariate \<Rightarrow> 'a bivariate \<Rightarrow> 'a bivariate" where
  "biv_poisson p q = biv_dy p * biv_dx q - biv_dx p * biv_dy q"
lemma biv_dx_coeff:
  "biv_coeff (biv_dx p) i j = of_nat (Suc i) * biv_coeff p (Suc i) j"
  by (simp add: biv_coeff_def biv_dx_def coeff_map_poly coeff_pderiv)
lemma biv_dy_coeff:
  "biv_coeff (biv_dy p) i j = of_nat (Suc j) * biv_coeff p i (Suc j)"
  by (simp add: biv_coeff_def biv_dy_def coeff_pderiv of_nat_poly)
lemma biv_dx_zero [simp]: "biv_dx 0 = 0"
  by (simp add: biv_dx_def)
lemma biv_dy_zero [simp]: "biv_dy 0 = 0"
  by (simp add: biv_dy_def)
lemma pair_weight_Suc_x:
  "pair_weight rho sigma (Suc i,j) = pair_weight rho sigma (i,j) + rho"
  by (simp add: pair_weight_def algebra_simps)
lemma pair_weight_Suc_y:
  "pair_weight rho sigma (i,Suc j) = pair_weight rho sigma (i,j) + sigma"
  by (simp add: pair_weight_def algebra_simps)
lemma biv_dx_component:
  "biv_dx (weighted_component rho sigma m p) = weighted_component rho sigma (m-rho) (biv_dx p)"
  by (rule biv_eqI)
     (auto simp: biv_dx_coeff weighted_component_coeff pair_weight_Suc_x)
lemma biv_dy_component:
  "biv_dy (weighted_component rho sigma m p) = weighted_component rho sigma (m-sigma) (biv_dy p)"
  by (rule biv_eqI)
     (auto simp: biv_dy_coeff weighted_component_coeff pair_weight_Suc_y)
lemma biv_deriv_component:
  "biv_deriv is_y (weighted_component rho sigma m p) =
    weighted_component rho sigma (m - (if is_y then sigma else rho)) (biv_deriv is_y p)"
  by (cases is_y) (simp_all add: biv_deriv_def biv_dx_component biv_dy_component)
lemma biv_dx_support_weight:
  assumes "\<And>u. u \<in> biv_support p \<Longrightarrow> pair_weight rho sigma u \<le> m"
    "u \<in> biv_support (biv_dx p)"
  shows "pair_weight rho sigma u \<le> m-rho"
proof -
  have coeff: "biv_coeff p (Suc (fst u)) (snd u) \<noteq> 0"
    using assms(2) by (auto simp: biv_support_def biv_dx_coeff)
  have mem: "(Suc (fst u), snd u) \<in> biv_support p" using coeff by (simp add: biv_support_def)
  have "pair_weight rho sigma u + rho \<le> m"
    using assms(1)[OF mem] by (simp add: pair_weight_Suc_x)
  then show ?thesis by arith
qed
lemma biv_dy_support_weight:
  assumes "\<And>u. u \<in> biv_support p \<Longrightarrow> pair_weight rho sigma u \<le> m"
    "u \<in> biv_support (biv_dy p)"
  shows "pair_weight rho sigma u \<le> m-sigma"
proof -
  have coeff: "biv_coeff p (fst u) (Suc (snd u)) \<noteq> 0"
    using assms(2) by (auto simp: biv_support_def biv_dy_coeff)
  have mem: "(fst u, Suc (snd u)) \<in> biv_support p" using coeff by (simp add: biv_support_def)
  have "pair_weight rho sigma u + sigma \<le> m"
    using assms(1)[OF mem] by (simp add: pair_weight_Suc_y)
  then show ?thesis by arith
qed
lemma biv_deriv_support_weight:
  assumes "\<And>u. u \<in> biv_support p \<Longrightarrow> pair_weight rho sigma u \<le> m"
    "u \<in> biv_support (biv_deriv is_y p)"
  shows "pair_weight rho sigma u \<le> m - (if is_y then sigma else rho)"
proof (cases is_y)
  case True
  have mem: "u \<in> biv_support (biv_dy p)" using assms(2) True by (simp add: biv_deriv_def)
  show ?thesis using biv_dy_support_weight[OF assms(1) mem] True by simp
next
  case False
  have mem: "u \<in> biv_support (biv_dx p)" using assms(2) False by (simp add: biv_deriv_def)
  show ?thesis using biv_dx_support_weight[OF assms(1) mem] False by simp
qed

lemma biv_dx_monom:
  "biv_dx (biv_monom c a b) = biv_monom (of_nat a * c) (a-1) b"
  by (simp add: biv_dx_def biv_monom_def map_poly_monom pderiv_monom)
lemma biv_dy_monom:
  "biv_dy (biv_monom c a b) = biv_monom (of_nat b * c) a (b-1)"
  by (simp add: biv_dy_def biv_monom_def pderiv_monom of_nat_poly smult_monom)

end
