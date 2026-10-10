theory PBW_Contraction_Polynomials
  imports "Weighted_Product_Components"
    "Exact_Normal_Order"
begin

definition coordinate_polynomial :: "(nat \<times> nat) set \<Rightarrow> ((nat \<times> nat) \<Rightarrow> 'a::field) \<Rightarrow> 'a bivariate" where
  "coordinate_polynomial S c = (\<Sum>p\<in>S. biv_monom (c p) (fst p) (snd p))"
definition contraction_term :: "((nat \<times> nat) \<Rightarrow> 'a::field) \<Rightarrow> ((nat \<times> nat) \<Rightarrow> 'a) \<Rightarrow> (nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> nat \<Rightarrow> 'a bivariate" where
  "contraction_term c d p q k = biv_monom
    (c p * d q * of_nat ((snd p choose k) * nat_desc_factorial (fst q) k))
    (fst p + fst q - k) (snd p + snd q - k)"
definition pbw_product_polynomial where
  "pbw_product_polynomial S T c d = (\<Sum>p\<in>S. \<Sum>q\<in>T. \<Sum>k\<le>min (fst q) (snd p). contraction_term c d p q k)"
definition first_contraction_polynomial where
  "first_contraction_polynomial S T c d = (\<Sum>p\<in>S. \<Sum>q\<in>T.
    biv_monom (c p * d q * of_nat (snd p) * of_nat (fst q))
      (fst p + fst q - 1) (snd p + snd q - 1))"
definition higher_contraction_polynomial where
  "higher_contraction_polynomial S T c d = (\<Sum>p\<in>S. \<Sum>q\<in>T.
    \<Sum>k\<in>{k. k\<le>min (fst q) (snd p) \<and> 1<k}. contraction_term c d p q k)"

lemma biv_dx_sum:
  "biv_dx (\<Sum>i\<in>S. f i) = (\<Sum>i\<in>S. biv_dx (f i))"
  by (rule biv_eqI) (simp add: biv_dx_coeff biv_coeff_sum sum_distrib_left)
lemma biv_dy_sum:
  "biv_dy (\<Sum>i\<in>S. f i) = (\<Sum>i\<in>S. biv_dy (f i))"
  by (rule biv_eqI) (simp add: biv_dy_coeff biv_coeff_sum sum_distrib_left)
lemma first_contraction_pair:
  "biv_monom (a*b*of_nat j*of_nat n) (i+n-1) (j+m-1) =
    biv_dy (biv_monom a i j) * biv_dx (biv_monom b n m)"
proof (cases "j=0 \<or> n=0")
  case True
  then show ?thesis by (auto simp: biv_dy_monom biv_dx_monom biv_mult_monom)
next
  case False
  then have x: "i+(n-1)=i+n-1" and y: "j-1+m=j+m-1" by arith+
  show ?thesis by (simp only: biv_dy_monom biv_dx_monom biv_mult_monom x y; simp add: algebra_simps)
qed
lemma first_contraction_derivative_product:
  "first_contraction_polynomial S T c d =
    biv_dy (coordinate_polynomial S c) * biv_dx (coordinate_polynomial T d)"
  by (simp only: first_contraction_polynomial_def coordinate_polynomial_def
      biv_dy_sum biv_dx_sum first_contraction_pair;
      simp only: sum_distrib_right; simp only: sum_distrib_left)
lemma first_contraction_sub_poisson:
  "first_contraction_polynomial S T c d - first_contraction_polynomial T S d c =
    biv_poisson (coordinate_polynomial S c) (coordinate_polynomial T d)"
  by (simp only: first_contraction_derivative_product biv_poisson_def mult.commute)


lemma contraction_term_zero:
  "contraction_term c d p q 0 =
    biv_monom (c p) (fst p) (snd p) * biv_monom (d q) (fst q) (snd q)"
  by (simp add: contraction_term_def biv_mult_monom)
lemma contraction_term_one:
  assumes "0 < min (fst q) (snd p)"
  shows "contraction_term c d p q 1 =
    biv_monom (c p * d q * of_nat (snd p) * of_nat (fst q))
      (fst p+fst q-1) (snd p+snd q-1)"
  by (simp add: contraction_term_def nat_desc_factorial.simps algebra_simps)
lemma contraction_sum_split:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>k\<le>N. f k) = f 0 + (if N=0 then 0 else f 1) +
    (\<Sum>k\<in>{k. k\<le>N \<and> 1<k}. f k)"
proof (cases "N=0")
  case True
  have empty: "{k. k\<le>N \<and> 1<k} = {}" using True by auto
  show ?thesis unfolding empty by (simp add: True)
next
  case False
  let ?H = "{k. k\<le>N \<and> 1<k}"
  have fin: "finite ?H" by (rule finite_subset[of _ "{..N}"]) auto
  have set: "{..N} = {0,1} \<union> ?H" using False by auto
  have dis: "{0,1} \<inter> ?H = {}" by auto
  have f01: "finite {0,1::nat}" by simp
  show ?thesis unfolding set using False
    by (simp only: sum.union_disjoint[OF f01 fin dis]) simp
qed

lemma weighted_component_sum:
  "weighted_component rho sigma m (\<Sum>i\<in>S. f i) =
    (\<Sum>i\<in>S. weighted_component rho sigma m (f i))"
  by (induction S rule: infinite_finite_induct) (simp_all add: weighted_component_add)

lemma contraction_first_conditional:
  "(if min (fst q) (snd p)=0 then 0 else contraction_term c d p q 1) =
    biv_monom (c p*d q*of_nat (snd p)*of_nat (fst q))
      (fst p+fst q-1) (snd p+snd q-1)"
proof (cases "min (fst q) (snd p)=0")
  case True
  then have "fst q=0 \<or> snd p=0" by auto
  then show ?thesis using True by auto
next
  case False
  have pos: "0 < min (fst q) (snd p)" using False by arith
  show ?thesis by (simp only: False if_False contraction_term_one[OF pos])
qed
lemma pbw_product_split:
  "pbw_product_polynomial S T c d =
    coordinate_polynomial S c * coordinate_polynomial T d +
    first_contraction_polynomial S T c d + higher_contraction_polynomial S T c d"
  by (simp only: pbw_product_polynomial_def contraction_sum_split
      contraction_term_zero contraction_first_conditional sum.distrib
      coordinate_polynomial_def first_contraction_polynomial_def
      higher_contraction_polynomial_def;
      simp only: sum_distrib_right; simp only: sum_distrib_left)
lemma pbw_product_commutator:
  "pbw_product_polynomial S T c d - pbw_product_polynomial T S d c =
    biv_poisson (coordinate_polynomial S c) (coordinate_polynomial T d) +
    (higher_contraction_polynomial S T c d - higher_contraction_polynomial T S d c)"
  by (simp only: pbw_product_split first_contraction_derivative_product biv_poisson_def; simp add: algebra_simps)

lemma coordinate_polynomial_support_bound:
  assumes bound: "\<And>p. p\<in>S \<Longrightarrow> pair_weight rho sigma p \<le> m"
    and mem: "u \<in> biv_support (coordinate_polynomial S c)"
  shows "pair_weight rho sigma u \<le> m"
proof -
  have nz: "(\<Sum>p\<in>S. biv_coeff (biv_monom (c p) (fst p) (snd p)) (fst u) (snd u)) \<noteq> 0"
    using mem by (simp add: biv_support_def coordinate_polynomial_def biv_coeff_sum)
  obtain p where p: "p\<in>S" and val: "biv_coeff (biv_monom (c p) (fst p) (snd p)) (fst u) (snd u) \<noteq> 0"
    by (rule sum.not_neutral_contains_not_neutral[OF nz])
  have "u=p" using val by (auto simp: prod_eq_iff split: if_splits)
  then show ?thesis using bound[OF p] by simp
qed
lemma higher_contraction_top_zero:
  assumes pos: "0 < rho+sigma"
    and cb: "\<And>p. p\<in>S \<Longrightarrow> pair_weight rho sigma p \<le> m"
    and db: "\<And>q. q\<in>T \<Longrightarrow> pair_weight rho sigma q \<le> n"
  shows "weighted_component rho sigma (m+n-(rho+sigma))
    (higher_contraction_polynomial S T c d) = 0"
proof -
  have term_zero: "weighted_component rho sigma (m+n-(rho+sigma))
      (contraction_term c d p q k) = 0"
    if p: "p\<in>S" and q: "q\<in>T" and k: "k\<le>min (fst q) (snd p) \<and> 1<k" for p q k
  proof -
    have w: "pair_weight rho sigma (fst p+fst q-k,snd p+snd q-k) + int k*(rho+sigma) =
      pair_weight rho sigma p + pair_weight rho sigma q"
      using normal_contraction_weight[OF k[THEN conjunct1], of rho sigma "fst p" "snd q"]
      by (simp add: pair_weight_def algebra_simps)
    have drop: "rho+sigma < int k*(rho+sigma)"
    proof -
      have "1*(rho+sigma) < int k*(rho+sigma)"
        by (rule mult_strict_right_mono) (use k pos in auto)
      then show ?thesis by simp
    qed
    have neq: "pair_weight rho sigma (fst p+fst q-k,snd p+snd q-k) \<noteq> m+n-(rho+sigma)"
      using w drop cb[OF p] db[OF q] by arith
    show ?thesis by (simp only: contraction_term_def weighted_component_monom neq if_False)
  qed
  show ?thesis unfolding higher_contraction_polynomial_def
    by (simp only: weighted_component_sum; intro sum.neutral; intro ballI; rule sum.neutral;
      intro ballI; rule sum.neutral; intro ballI; rule term_zero; assumption?; simp_all)
qed
lemma pbw_product_commutator_top:
  assumes pos: "0 < rho+sigma"
    and cb: "\<And>p. p\<in>S \<Longrightarrow> pair_weight rho sigma p \<le> m"
    and db: "\<And>q. q\<in>T \<Longrightarrow> pair_weight rho sigma q \<le> n"
  shows "weighted_component rho sigma (m+n-(rho+sigma))
      (pbw_product_polynomial S T c d - pbw_product_polynomial T S d c) =
    biv_poisson (weighted_component rho sigma m (coordinate_polynomial S c))
      (weighted_component rho sigma n (coordinate_polynomial T d))"
proof -
  have h1: "weighted_component rho sigma (m+n-(rho+sigma)) (higher_contraction_polynomial S T c d)=0"
    by (rule higher_contraction_top_zero[OF pos cb db])
  have h2: "weighted_component rho sigma (m+n-(rho+sigma)) (higher_contraction_polynomial T S d c)=0"
    proof -
      have h: "weighted_component rho sigma (n+m-(rho+sigma)) (higher_contraction_polynomial T S d c)=0"
        by (rule higher_contraction_top_zero[OF pos db cb])
      show ?thesis using h by (simp only: add.commute)
    qed
  have cp: "\<And>u. u\<in>biv_support (coordinate_polynomial S c) \<Longrightarrow> pair_weight rho sigma u \<le> m"
    by (rule coordinate_polynomial_support_bound[OF cb])
  have dp: "\<And>u. u\<in>biv_support (coordinate_polynomial T d) \<Longrightarrow> pair_weight rho sigma u \<le> n"
    by (rule coordinate_polynomial_support_bound[OF db])
  have ph: "weighted_component rho sigma (m+n-(rho+sigma))
      (biv_poisson (coordinate_polynomial S c) (coordinate_polynomial T d)) =
      biv_poisson (weighted_component rho sigma m (coordinate_polynomial S c))
        (weighted_component rho sigma n (coordinate_polynomial T d))"
    by (rule poisson_weighted_component_of_bounds[OF cp dp])
  show ?thesis
    by (simp only: pbw_product_commutator weighted_component_add weighted_component_diff h1 h2 diff_self add_0_right ph)
qed

end
