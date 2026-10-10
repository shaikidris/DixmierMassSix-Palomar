theory Weighted_Components
  imports "PBW_Symbol" "HOL-Library.Lattice_Constructions"
begin

definition coordinate_weight :: "int \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> int" where
  "coordinate_weight rho sigma b = (if b then sigma else rho)"
lemma coordinate_weight_eta:
  "coordinate_weight (w False) (w True) = w"
  by (rule ext) (simp add: coordinate_weight_def split: bool.split)
definition pair_weight :: "int \<Rightarrow> int \<Rightarrow> nat \<times> nat \<Rightarrow> int" where
  "pair_weight rho sigma u = int (fst u) * rho + int (snd u) * sigma"
definition weighted_component :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a::field bivariate \<Rightarrow> 'a bivariate" where
  "weighted_component rho sigma m p = (\<Sum>u\<in>{u\<in>biv_support p. pair_weight rho sigma u = m}.
    biv_monom (biv_coeff p (fst u) (snd u)) (fst u) (snd u))"
definition weighted_degree :: "int \<Rightarrow> int \<Rightarrow> 'a::field bivariate \<Rightarrow> int bot" where
  "weighted_degree rho sigma p = (if biv_support p = {} then bot.Bot
    else bot.Value (Max (pair_weight rho sigma ` biv_support p)))"
definition v_degree :: "int \<Rightarrow> int \<Rightarrow> 'a::field poly_operator \<Rightarrow> int" where
  "v_degree rho sigma T = (case weighted_degree rho sigma (pbw_symbol T) of bot.Bot \<Rightarrow> 0 | bot.Value d \<Rightarrow> d)"
definition leading_form :: "int \<Rightarrow> int \<Rightarrow> 'a::field poly_operator \<Rightarrow> 'a bivariate" where
  "leading_form rho sigma T = weighted_component rho sigma (v_degree rho sigma T) (pbw_symbol T)"

lemma weighted_component_coeff:
  "biv_coeff (weighted_component rho sigma m p) i j =
    (if pair_weight rho sigma (i,j) = m then biv_coeff p i j else 0)"
proof -
  have fin: "finite {u\<in>biv_support p. pair_weight rho sigma u = m}" by simp
  show ?thesis by (simp only: weighted_component_def biv_sum_monom_coeff[OF fin])
    (auto simp: biv_support_def)
qed
lemma weighted_component_zero [simp]: "weighted_component rho sigma m 0 = 0"
  by (rule biv_eqI) (simp add: weighted_component_coeff)
lemma weighted_component_add:
  "weighted_component rho sigma m (p+q) = weighted_component rho sigma m p + weighted_component rho sigma m q"
  by (rule biv_eqI) (simp add: weighted_component_coeff)
lemma weighted_component_smult:
  "weighted_component rho sigma m (smult [:c:] p) = smult [:c:] (weighted_component rho sigma m p)"
  by (rule biv_eqI) (simp add: weighted_component_coeff)
lemma weighted_component_support:
  "biv_support (weighted_component rho sigma m p) = {u\<in>biv_support p. pair_weight rho sigma u = m}"
  by (auto simp: biv_support_def weighted_component_coeff)
lemma biv_support_empty_iff [simp]: "biv_support p = {} \<longleftrightarrow> p = 0"
proof
  assume "biv_support p = {}"
  then have "\<And>i j. biv_coeff p i j = 0" by (auto simp: biv_support_def)
  then show "p=0" by (rule_tac biv_eqI) simp
qed simp
lemma weighted_degree_zero [simp]: "weighted_degree rho sigma 0 = bot.Bot"
  by (simp add: weighted_degree_def)
lemma weighted_degree_bot_iff [simp]: "weighted_degree rho sigma p = bot.Bot \<longleftrightarrow> p = 0"
  by (simp add: weighted_degree_def)
lemma weighted_degree_support_bound:
  assumes "weighted_degree rho sigma p = bot.Value m" "u \<in> biv_support p"
  shows "pair_weight rho sigma u \<le> m"
proof -
  have ne: "biv_support p \<noteq> {}" using assms(2) by blast
  have val: "m = Max (pair_weight rho sigma ` biv_support p)"
    using assms(1) ne by (simp add: weighted_degree_def)
  show ?thesis unfolding val by (rule Max_ge) (use assms(2) in auto)
qed
lemma weighted_degree_attained:
  assumes "weighted_degree rho sigma p = bot.Value m"
  shows "\<exists>u\<in>biv_support p. pair_weight rho sigma u = m"
proof -
  have ne: "biv_support p \<noteq> {}" using assms by (auto simp: weighted_degree_def split: if_splits)
  have val: "m = Max (pair_weight rho sigma ` biv_support p)"
    using assms ne by (simp add: weighted_degree_def)
  have "Max (pair_weight rho sigma ` biv_support p) \<in> pair_weight rho sigma ` biv_support p"
    by (rule Max_in) (use ne in auto)
  then show ?thesis unfolding val by auto
qed
lemma weighted_top_component_nonzero:
  "weighted_degree rho sigma p = bot.Value m \<Longrightarrow> weighted_component rho sigma m p \<noteq> 0"
proof -
  assume deg: "weighted_degree rho sigma p = bot.Value m"
  obtain u where mem: "u \<in> biv_support p" and wt: "pair_weight rho sigma u = m"
    using weighted_degree_attained[OF deg] by blast
  have "biv_coeff (weighted_component rho sigma m p) (fst u) (snd u) \<noteq> 0"
    using mem wt by (simp add: weighted_component_coeff biv_support_def)
  then show ?thesis by auto
qed

lemma expo_weight:
  "(\<Sum>b\<in>UNIV. int (pair_exponent (i,j) b) * coordinate_weight rho sigma b) =
    int i * rho + int j * sigma"
  by (simp add: UNIV_bool pair_exponent_def coordinate_weight_def add.commute)
lemma normal_contraction_weight:
  assumes "k \<le> min c b"
  shows "pair_weight rho sigma (a+c-k,b+d-k) + int k * (rho+sigma) =
    pair_weight rho sigma (a+c,b+d)"
proof -
  have ac: "k \<le> a+c" and bd: "k \<le> b+d" using assms by auto
  show ?thesis by (simp add: pair_weight_def of_nat_diff ac bd algebra_simps)
qed
lemma normal_contraction_weight_lt:
  assumes "0 < rho+sigma" "k \<le> min c b" "0 < k"
  shows "pair_weight rho sigma (a+c-k,b+d-k) < pair_weight rho sigma (a+c,b+d)"
proof -
  have drop: "0 < int k * (rho+sigma)" using assms by (intro mult_pos_pos) auto
  show ?thesis using normal_contraction_weight[OF assms(2), of rho sigma a d] drop by arith
qed

lemma weighted_support_monom:
  "c \<noteq> 0 \<Longrightarrow> biv_support (biv_monom c a b) = {(a,b)}"
  by (auto simp: biv_support_def prod_eq_iff)
lemma weighted_degree_monom:
  "c \<noteq> 0 \<Longrightarrow> weighted_degree rho sigma (biv_monom c a b) =
    bot.Value (pair_weight rho sigma (a,b))"
  by (simp add: weighted_degree_def weighted_support_monom)
lemma weighted_component_monom:
  "weighted_component rho sigma m (biv_monom c a b) =
    (if pair_weight rho sigma (a,b) = m then biv_monom c a b else 0)"
  by (rule biv_eqI) (auto simp: weighted_component_coeff)
lemma v_degree_normal_monomial:
  "v_degree rho sigma (normal_monomial a b :: 'a::field_char_0 poly_operator) =
    pair_weight rho sigma (a,b)"
  by (simp add: v_degree_def pbw_symbol_normal_monomial weighted_degree_monom)
lemma leading_normal_monomial:
  "leading_form rho sigma (normal_monomial a b :: 'a::field_char_0 poly_operator) = biv_monom 1 a b"
  by (simp add: leading_form_def pbw_symbol_normal_monomial v_degree_normal_monomial weighted_component_monom)

end
