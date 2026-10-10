theory Weighted_Product_Components
  imports "Partial_Derivatives"
begin

lemma biv_coeff_product:
  "biv_coeff (p*q) i j = (\<Sum>b\<le>j. \<Sum>a\<le>i. biv_coeff p a b * biv_coeff q (i-a) (j-b))"
  by (simp add: biv_coeff_def coeff_mult coeff_sum)
lemma pair_weight_split:
  "a \<le> i \<Longrightarrow> b \<le> j \<Longrightarrow>
    pair_weight rho sigma (a,b) + pair_weight rho sigma (i-a,j-b) = pair_weight rho sigma (i,j)"
  by (simp add: pair_weight_def of_nat_diff algebra_simps)
lemma weighted_product_term:
  fixes x y :: "'a::field" and u v w m n :: int
  assumes sum: "u+v=w" and xb: "x \<noteq> 0 \<Longrightarrow> u \<le> m" and yb: "y \<noteq> 0 \<Longrightarrow> v \<le> n"
  shows "(if w=m+n then x*y else 0) = (if u=m then x else 0) * (if v=n then y else 0)"
proof (cases "x=0 \<or> y=0")
  case True then show ?thesis by auto
next
  case False
  have bounds: "u \<le> m" "v \<le> n" using xb yb False by auto
  have eq: "w=m+n \<longleftrightarrow> u=m \<and> v=n" using sum bounds by linarith
  show ?thesis by (simp only: eq) auto
qed
lemma weighted_component_product_of_bounds:
  assumes p: "\<And>u. u \<in> biv_support p \<Longrightarrow> pair_weight rho sigma u \<le> m"
    and q: "\<And>u. u \<in> biv_support q \<Longrightarrow> pair_weight rho sigma u \<le> n"
  shows "weighted_component rho sigma (m+n) (p*q) =
    weighted_component rho sigma m p * weighted_component rho sigma n q"
proof (rule biv_eqI)
  fix i j
  have point: "(if pair_weight rho sigma (i,j)=m+n then
      biv_coeff p a b * biv_coeff q (i-a) (j-b) else 0) =
    (if pair_weight rho sigma (a,b)=m then biv_coeff p a b else 0) *
    (if pair_weight rho sigma (i-a,j-b)=n then biv_coeff q (i-a) (j-b) else 0)"
    if "a \<le> i" "b \<le> j" for a b
  proof (rule weighted_product_term[OF pair_weight_split[OF that]])
    assume "biv_coeff p a b \<noteq> 0"
    then have "(a,b) \<in> biv_support p" by (simp add: biv_support_def)
    then show "pair_weight rho sigma (a,b) \<le> m" by (rule p)
  next
    assume "biv_coeff q (i-a) (j-b) \<noteq> 0"
    then have "(i-a,j-b) \<in> biv_support q" by (simp add: biv_support_def)
    then show "pair_weight rho sigma (i-a,j-b) \<le> n" by (rule q)
  qed
  have lhs: "biv_coeff (weighted_component rho sigma (m+n) (p*q)) i j =
    (\<Sum>b\<le>j. \<Sum>a\<le>i. if pair_weight rho sigma (i,j)=m+n then
      biv_coeff p a b * biv_coeff q (i-a) (j-b) else 0)"
    by (simp only: weighted_component_coeff biv_coeff_product;
        cases "pair_weight rho sigma (i,j)=m+n"; simp)
  show "biv_coeff (weighted_component rho sigma (m+n) (p*q)) i j =
    biv_coeff (weighted_component rho sigma m p * weighted_component rho sigma n q) i j"
    unfolding lhs biv_coeff_product
  proof (rule sum.cong[OF refl])
    fix b assume b: "b \<in> {..j}"
    show "(\<Sum>a\<le>i. if pair_weight rho sigma (i,j)=m+n then
      biv_coeff p a b * biv_coeff q (i-a) (j-b) else 0) =
      (\<Sum>a\<le>i. biv_coeff (weighted_component rho sigma m p) a b *
        biv_coeff (weighted_component rho sigma n q) (i-a) (j-b))"
    proof (rule sum.cong[OF refl])
      fix a assume a: "a \<in> {..i}"
      show "(if pair_weight rho sigma (i,j)=m+n then
        biv_coeff p a b * biv_coeff q (i-a) (j-b) else 0) =
        biv_coeff (weighted_component rho sigma m p) a b *
        biv_coeff (weighted_component rho sigma n q) (i-a) (j-b)"
        using point[of a b] a b by (simp add: weighted_component_coeff)
    qed
  qed
qed
lemma weighted_component_product_at_top:
  assumes "weighted_degree rho sigma p = bot.Value m" "weighted_degree rho sigma q = bot.Value n"
  shows "weighted_component rho sigma (m+n) (p*q) =
    weighted_component rho sigma m p * weighted_component rho sigma n q"
  by (rule weighted_component_product_of_bounds)
     (auto intro: weighted_degree_support_bound[OF assms(1)] weighted_degree_support_bound[OF assms(2)])
lemma weighted_component_diff:
  "weighted_component rho sigma m (p-q) = weighted_component rho sigma m p - weighted_component rho sigma m q"
  by (rule biv_eqI) (simp add: weighted_component_coeff)
lemma poisson_weighted_component_of_bounds:
  assumes p: "\<And>u. u \<in> biv_support p \<Longrightarrow> pair_weight rho sigma u \<le> m"
    and q: "\<And>u. u \<in> biv_support q \<Longrightarrow> pair_weight rho sigma u \<le> n"
  shows "weighted_component rho sigma (m+n-(rho+sigma)) (biv_poisson p q) =
    biv_poisson (weighted_component rho sigma m p) (weighted_component rho sigma n q)"
proof -
  have py: "\<And>u. u \<in> biv_support (biv_dy p) \<Longrightarrow> pair_weight rho sigma u \<le> m-sigma"
    by (rule biv_dy_support_weight[OF p])
  have px: "\<And>u. u \<in> biv_support (biv_dx p) \<Longrightarrow> pair_weight rho sigma u \<le> m-rho"
    by (rule biv_dx_support_weight[OF p])
  have qy: "\<And>u. u \<in> biv_support (biv_dy q) \<Longrightarrow> pair_weight rho sigma u \<le> n-sigma"
    by (rule biv_dy_support_weight[OF q])
  have qx: "\<And>u. u \<in> biv_support (biv_dx q) \<Longrightarrow> pair_weight rho sigma u \<le> n-rho"
    by (rule biv_dx_support_weight[OF q])
  have w1: "m+n-(rho+sigma) = (m-sigma)+(n-rho)" by arith
  have w2: "m+n-(rho+sigma) = (m-rho)+(n-sigma)" by arith
  have first: "weighted_component rho sigma (m+n-(rho+sigma)) (biv_dy p * biv_dx q) =
    weighted_component rho sigma (m-sigma) (biv_dy p) * weighted_component rho sigma (n-rho) (biv_dx q)"
    unfolding w1 by (rule weighted_component_product_of_bounds[OF py qx])
  have second: "weighted_component rho sigma (m+n-(rho+sigma)) (biv_dx p * biv_dy q) =
    weighted_component rho sigma (m-rho) (biv_dx p) * weighted_component rho sigma (n-sigma) (biv_dy q)"
    unfolding w2 by (rule weighted_component_product_of_bounds[OF px qy])
  show ?thesis by (simp only: biv_poisson_def weighted_component_diff first second biv_dx_component biv_dy_component)
qed

end
