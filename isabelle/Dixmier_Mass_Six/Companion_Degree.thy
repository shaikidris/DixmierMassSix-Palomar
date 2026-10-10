theory Companion_Degree
  imports Semiring_Polynomial_Product "Euler_Coefficients" "HOL.Complex"
begin

definition CompanionEq :: "int \<Rightarrow> int \<Rightarrow> complex poly \<Rightarrow> complex poly \<Rightarrow> bool" where
  "CompanionEq rho s r f \<longleftrightarrow>
    [:of_int rho - of_int s:] * [:0,1:] * f * pderiv r -
      (f + [:of_int rho:] * [:0,1:] * pderiv f + 1) * r = 0"

definition Comp :: "nat \<Rightarrow> nat \<Rightarrow> complex poly \<Rightarrow> complex poly \<Rightarrow> bool" where
  "Comp rho s r f \<longleftrightarrow>
    [:of_nat rho - of_nat s:] * [:0,1:] * f * pderiv r =
      (f + [:of_nat rho:] * [:0,1:] * pderiv f + 1) * r"

lemma companionEq_natCast_iff:
  "CompanionEq (int rho) (int s) r f \<longleftrightarrow> Comp rho s r f"
  by (simp add: CompanionEq_def Comp_def)

lemma natDegree_euler_le:
  fixes p :: "complex poly"
  shows "degree (euler p) \<le> degree p"
  by (rule degree_le) (simp add: coeff_euler coeff_eq_0)

lemma Comp_euler_form:
  assumes h: "Comp rho s r f"
  shows "[:of_nat rho - of_nat s:] * (f * euler r) =
    (f + [:of_nat rho:] * euler f + 1) * r"
  using h by (simp add: Comp_def euler_def monom_altdef mult_ac)

lemma Comp_f_eval_zero:
  assumes h: "Comp rho s r f" and hr0: "poly r 0 = 1"
  shows "poly f 0 = -1"
proof -
  have h0: "poly ([:of_nat rho - of_nat s:] * [:0,1:] * f * pderiv r) 0 =
    poly ((f + [:of_nat rho:] * [:0,1:] * pderiv f + 1) * r) 0"
    using h unfolding Comp_def by simp
  with hr0 show ?thesis by (simp add: eq_neg_iff_add_eq_0)
qed

lemma Comp_natDegree_f_pos:
  assumes h: "Comp rho s r f" and hs: "s < rho"
    and hr0: "poly r 0 = 1" and hr: "0 < degree r"
  shows "0 < degree f"
proof (rule ccontr)
  assume "\<not> 0 < degree f"
  then have hf0: "degree f = 0" by simp
  obtain c where fc: "f = [:c:]" using degree_eq_zeroE[OF hf0] by blast
  have f: "f = [:-1:]" using Comp_f_eval_zero[OF h hr0] fc by simp
  have delta: "(of_nat rho - of_nat s :: complex) \<noteq> 0" using hs by simp
  have "pderiv r = 0" using h delta by (simp add: Comp_def f one_pCons)
  then show False using hr by (simp add: pderiv_eq_0_iff)
qed

lemma Comp_degree_identity:
  assumes h: "Comp rho s r f" and hs: "s < rho"
    and hr: "0 < degree r" and hf: "0 < degree f"
  shows "(rho-s) * degree r = 1 + rho * degree f"
proof -
  let ?L = "degree f"
  let ?e = "degree r"
  have fnz: "f \<noteq> 0" using hf by auto
  have rnz: "r \<noteq> 0" using hr by auto
  have lead: "coeff f ?L * coeff r ?e \<noteq> 0" using fnz rnz by simp
  have bound: "degree (f + [:of_nat rho:] * euler f + 1) \<le> ?L"
    by (intro degree_add_le) (auto intro: order_trans[OF degree_smult_le] natDegree_euler_le)
  have hc: "coeff ([:of_nat rho - of_nat s:] * (f * euler r)) (?L+?e) =
      coeff ((f + [:of_nat rho:] * euler f + 1) * r) (?L+?e)"
    using Comp_euler_form[OF h] by simp
  have rhs: "coeff ((f + [:of_nat rho:] * euler f + 1) * r) (?L+?e) =
      coeff (f + [:of_nat rho:] * euler f + 1) ?L * coeff r ?e"
    by (rule coeff_mult_of_degree_le[OF bound order_refl])
  have equation: "(of_nat rho - of_nat s) * (coeff f ?L * (of_nat ?e * coeff r ?e)) =
    (coeff f ?L + of_nat rho * (of_nat ?L * coeff f ?L)) * coeff r ?e"
    using hc hf unfolding rhs
    by (simp add: coeff_mult_of_degree_le[OF order_refl natDegree_euler_le] coeff_euler)
  have algebra: "(a * (b * (c*d)) - (b + e*(f*b))*d) =
      (a*c-(1+e*f))*(b*d)" for a b c d e f :: complex
    by (simp add: algebra_simps)
  have product_zero: "((of_nat rho - of_nat s) * of_nat ?e -
      (1 + of_nat rho * of_nat ?L)) * (coeff f ?L * coeff r ?e) = 0"
    using equation by (simp only: algebra[symmetric] diff_self)
  have cast_eq: "(of_nat rho - of_nat s :: complex) * of_nat ?e =
      1 + of_nat rho * of_nat ?L"
    using product_zero lead by auto
  have "(of_nat ((rho-s)*?e) :: complex) = of_nat (1+rho*?L)"
    unfolding of_nat_mult of_nat_add of_nat_1 of_nat_diff[OF less_imp_le[OF hs]]
    by (rule cast_eq)
  then show ?thesis by (simp only: of_nat_eq_iff)
qed

lemma Comp_natDegree_f_lt:
  assumes h: "Comp rho s r f" and hs: "s < rho"
    and hr: "0 < degree r" and hf: "0 < degree f"
  shows "degree f < degree r"
proof (rule ccontr)
  assume "\<not> degree f < degree r"
  then have le: "degree r \<le> degree f" by simp
  have a: "(rho-s) * degree r \<le> (rho-s) * degree f"
    by (rule mult_le_mono2[OF le])
  have b: "(rho-s) * degree f \<le> rho * degree f"
    by (rule mult_le_mono1) simp
  have eq: "(rho-s) * degree r = 1+rho*degree f"
    by (rule Comp_degree_identity[OF h hs hr hf])
  from a b eq show False by arith
qed

end
