theory Weighted_Degree_Bounds
  imports "Weighted_Product_Components"
begin

lemma biv_support_add_subset:
  "biv_support (p+q) \<subseteq> biv_support p \<union> biv_support q"
  by (auto simp: biv_support_def)

lemma biv_support_diff_subset:
  "biv_support (p-q) \<subseteq> biv_support p \<union> biv_support q"
  by (auto simp: biv_support_def)

lemma biv_support_sum_subset:
  assumes "finite S"
  shows "biv_support (\<Sum>i\<in>S. f i) \<subseteq> (\<Union>i\<in>S. biv_support (f i))"
  using assms
proof (induction S rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert i S)
  have sub: "biv_support (f i + (\<Sum>j\<in>S. f j)) \<subseteq>
    biv_support (f i) \<union> biv_support (\<Sum>j\<in>S. f j)"
    by (rule biv_support_add_subset)
  show ?case using sub insert.IH insert.hyps by auto
qed

lemma biv_support_weight_add:
  assumes p: "\<And>u. u \<in> biv_support p \<Longrightarrow> pair_weight rho sigma u \<le> m"
    and q: "\<And>u. u \<in> biv_support q \<Longrightarrow> pair_weight rho sigma u \<le> m"
    and u: "u \<in> biv_support (p+q)"
  shows "pair_weight rho sigma u \<le> m"
  using biv_support_add_subset u p q by blast

lemma biv_support_weight_diff:
  assumes p: "\<And>u. u \<in> biv_support p \<Longrightarrow> pair_weight rho sigma u \<le> m"
    and q: "\<And>u. u \<in> biv_support q \<Longrightarrow> pair_weight rho sigma u \<le> m"
    and u: "u \<in> biv_support (p-q)"
  shows "pair_weight rho sigma u \<le> m"
  using biv_support_diff_subset u p q by blast

lemma biv_support_weight_sum:
  assumes fin: "finite S"
    and bound: "\<And>i u. i \<in> S \<Longrightarrow> u \<in> biv_support (f i) \<Longrightarrow> pair_weight rho sigma u \<le> m"
    and u: "u \<in> biv_support (\<Sum>i\<in>S. f i)"
  shows "pair_weight rho sigma u \<le> m"
  using biv_support_sum_subset[OF fin] u bound by blast

lemma biv_support_weight_product:
  assumes p: "\<And>v. v \<in> biv_support p \<Longrightarrow> pair_weight rho sigma v \<le> m"
    and q: "\<And>v. v \<in> biv_support q \<Longrightarrow> pair_weight rho sigma v \<le> n"
    and u: "u \<in> biv_support (p*q)"
  shows "pair_weight rho sigma u \<le> m+n"
proof -
  have nz: "(\<Sum>b\<le>snd u. \<Sum>a\<le>fst u.
    biv_coeff p a b * biv_coeff q (fst u-a) (snd u-b)) \<noteq> 0"
    using u by (simp add: biv_support_def biv_coeff_product)
  obtain b where b: "b \<in> {..snd u}"
    and bnz: "(\<Sum>a\<le>fst u. biv_coeff p a b * biv_coeff q (fst u-a) (snd u-b)) \<noteq> 0"
    by (rule sum.not_neutral_contains_not_neutral[OF nz])
  obtain a where a: "a \<in> {..fst u}"
    and anz: "biv_coeff p a b * biv_coeff q (fst u-a) (snd u-b) \<noteq> 0"
    by (rule sum.not_neutral_contains_not_neutral[OF bnz])
  have ale: "a \<le> fst u" and ble: "b \<le> snd u" using a b by simp_all
  have pin: "(a,b) \<in> biv_support p"
    and qin: "(fst u-a,snd u-b) \<in> biv_support q"
    using anz by (auto simp: biv_support_def)
  have split: "pair_weight rho sigma (a,b) +
    pair_weight rho sigma (fst u-a,snd u-b) = pair_weight rho sigma u"
    using pair_weight_split[OF ale ble, where rho=rho and sigma=sigma] by simp
  show ?thesis using split p[OF pin] q[OF qin] by arith
qed

lemma weighted_degree_le_of_support_bound:
  assumes bound: "\<And>u. u \<in> biv_support p \<Longrightarrow> pair_weight rho sigma u \<le> m"
  shows "weighted_degree rho sigma p \<le> bot.Value m"
proof (cases "biv_support p = {}")
  case True
  then show ?thesis by (simp add: weighted_degree_def)
next
  case False
  have max_bound: "Max (pair_weight rho sigma ` biv_support p) \<le> m"
    by (rule Max.boundedI) (use False bound in auto)
  show ?thesis using False max_bound by (simp add: weighted_degree_def)
qed

lemma weighted_degree_ge_of_support:
  assumes u: "u \<in> biv_support p"
  shows "bot.Value (pair_weight rho sigma u) \<le> weighted_degree rho sigma p"
proof -
  have ne: "biv_support p \<noteq> {}" using u by blast
  have le: "pair_weight rho sigma u \<le> Max (pair_weight rho sigma ` biv_support p)"
    by (rule Max_ge) (use u in auto)
  show ?thesis using ne le by (simp add: weighted_degree_def)
qed

lemma weighted_degree_support_bound_of_le:
  assumes deg: "weighted_degree rho sigma p \<le> bot.Value m"
    and u: "u \<in> biv_support p"
  shows "pair_weight rho sigma u \<le> m"
proof -
  have "bot.Value (pair_weight rho sigma u) \<le> bot.Value m"
    by (rule order_trans[OF weighted_degree_ge_of_support[OF u] deg])
  then show ?thesis by simp
qed

lemma weighted_degree_le_iff_support_bound:
  "weighted_degree rho sigma p \<le> bot.Value m \<longleftrightarrow>
    (\<forall>u\<in>biv_support p. pair_weight rho sigma u \<le> m)"
  by (auto intro: weighted_degree_le_of_support_bound weighted_degree_support_bound_of_le)

lemma weighted_component_nonzero_degree_lower_bound:
  assumes nz: "weighted_component rho sigma m p \<noteq> 0"
  shows "bot.Value m \<le> weighted_degree rho sigma p"
proof -
  have "biv_support (weighted_component rho sigma m p) \<noteq> {}" using nz by simp
  then obtain u where u: "u \<in> biv_support p" and wt: "pair_weight rho sigma u = m"
    by (auto simp: weighted_component_support)
  show ?thesis
    using weighted_degree_ge_of_support[OF u, where rho=rho and sigma=sigma] wt by simp
qed

lemma weighted_degree_eq_of_bound_component:
  assumes bound: "weighted_degree rho sigma p \<le> bot.Value m"
    and nz: "weighted_component rho sigma m p \<noteq> 0"
  shows "weighted_degree rho sigma p = bot.Value m"
  by (rule antisym[OF bound weighted_component_nonzero_degree_lower_bound[OF nz]])

lemma weighted_degree_eq_of_support_bound_component:
  assumes bound: "\<And>u. u \<in> biv_support p \<Longrightarrow> pair_weight rho sigma u \<le> m"
    and nz: "weighted_component rho sigma m p \<noteq> 0"
  shows "weighted_degree rho sigma p = bot.Value m"
  by (rule weighted_degree_eq_of_bound_component[OF weighted_degree_le_of_support_bound[OF bound] nz])

lemma weighted_degree_sum_le:
  assumes fin: "finite S"
    and bound: "\<And>i u. i \<in> S \<Longrightarrow> u \<in> biv_support (f i) \<Longrightarrow> pair_weight rho sigma u \<le> m"
  shows "weighted_degree rho sigma (\<Sum>i\<in>S. f i) \<le> bot.Value m"
proof (rule weighted_degree_le_of_support_bound)
  fix u assume u: "u \<in> biv_support (\<Sum>i\<in>S. f i)"
  show "pair_weight rho sigma u \<le> m"
    by (rule biv_support_weight_sum[OF fin bound u])
qed

lemma weighted_degree_add_le:
  assumes p: "weighted_degree rho sigma p \<le> bot.Value m"
    and q: "weighted_degree rho sigma q \<le> bot.Value m"
  shows "weighted_degree rho sigma (p+q) \<le> bot.Value m"
proof (rule weighted_degree_le_of_support_bound)
  fix u assume u: "u \<in> biv_support (p+q)"
  show "pair_weight rho sigma u \<le> m"
    by (rule biv_support_weight_add[OF _ _ u])
       (auto intro: weighted_degree_support_bound_of_le[OF p] weighted_degree_support_bound_of_le[OF q])
qed

lemma weighted_degree_diff_le:
  assumes p: "weighted_degree rho sigma p \<le> bot.Value m"
    and q: "weighted_degree rho sigma q \<le> bot.Value m"
  shows "weighted_degree rho sigma (p-q) \<le> bot.Value m"
proof (rule weighted_degree_le_of_support_bound)
  fix u assume u: "u \<in> biv_support (p-q)"
  show "pair_weight rho sigma u \<le> m"
    by (rule biv_support_weight_diff[OF _ _ u])
       (auto intro: weighted_degree_support_bound_of_le[OF p] weighted_degree_support_bound_of_le[OF q])
qed

end
