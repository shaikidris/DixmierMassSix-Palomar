theory Derivative_Stable_Kernel
  imports "Partial_Derivatives"
begin

definition bivariate_total_degree :: "complex bivariate \<Rightarrow> nat" where
  "bivariate_total_degree f = Max (insert 0 ((\<lambda>d. fst d+snd d) ` biv_support f))"

lemma bivariate_support_total_degree_bound:
  assumes "d\<in>biv_support f"
  shows "fst d+snd d\<le>bivariate_total_degree f"
  unfolding bivariate_total_degree_def
  by (rule Max_ge) (use assms in auto)

lemma bivariate_pderiv_support_total_degree_bound:
  assumes "d\<in>biv_support (biv_deriv is_y f)"
  shows "fst d+snd d+1\<le>bivariate_total_degree f"
proof -
  obtain i j where d: "d=(i,j)" by (cases d) auto
  show ?thesis
  proof (cases is_y)
    case True
    have source: "(i,Suc j)\<in>biv_support f"
      using assms by (auto simp: d True biv_deriv_def biv_support_def biv_dy_coeff)
    show ?thesis using bivariate_support_total_degree_bound[OF source] by (simp add: d)
  next
    case False
    have source: "(Suc i,j)\<in>biv_support f"
      using assms by (auto simp: d False biv_deriv_def biv_support_def biv_dx_coeff)
    show ?thesis using bivariate_support_total_degree_bound[OF source] by (simp add: d)
  qed
qed

lemma bivariate_pderiv_totalDegree_lt:
  assumes nonzero: "biv_deriv is_y f\<noteq>0"
  shows "bivariate_total_degree (biv_deriv is_y f)<bivariate_total_degree f"
proof -
  have nonempty: "biv_support (biv_deriv is_y f)\<noteq>{}"
  proof
    assume empty: "biv_support (biv_deriv is_y f)={}"
    have "biv_deriv is_y f=0"
      by (rule biv_eqI) (use empty in \<open>auto simp: biv_support_def\<close>)
    then show False using nonzero by blast
  qed
  obtain d where d: "d\<in>biv_support (biv_deriv is_y f)" using nonempty by blast
  have positive: "0<bivariate_total_degree f"
    using bivariate_pderiv_support_total_degree_bound[OF d] by arith
  have bound: "bivariate_total_degree (biv_deriv is_y f)\<le>bivariate_total_degree f-1"
    unfolding bivariate_total_degree_def[of "biv_deriv is_y f"]
  proof (rule Max.boundedI)
    show "finite (insert 0 ((\<lambda>d. fst d+snd d) ` biv_support (biv_deriv is_y f)))" by simp
    show "insert 0 ((\<lambda>d. fst d+snd d) ` biv_support (biv_deriv is_y f))\<noteq>{}" by simp
    fix x assume "x\<in>insert 0 ((\<lambda>d. fst d+snd d) ` biv_support (biv_deriv is_y f))"
    then consider "x=0" | d where "d\<in>biv_support (biv_deriv is_y f)" "x=fst d+snd d" by auto
    then show "x\<le>bivariate_total_degree f-1"
    proof cases
      case 1 then show ?thesis by simp
    next
      case 2
      show ?thesis using bivariate_pderiv_support_total_degree_bound[OF 2(1)] 2(2) by arith
    qed
  qed
  show ?thesis using bound positive by arith
qed

lemma bivariate_zero_partials_constant:
  fixes f :: "complex bivariate"
  assumes dx: "biv_dx f=0" and dy: "biv_dy f=0"
  shows "f=biv_monom (biv_coeff f 0 0) 0 0"
proof (rule biv_eqI)
  fix i j
  have xzero: "biv_coeff f (Suc k) l=0" for k l
    using arg_cong[OF dx, where f="\<lambda>p. biv_coeff p k l"]
    by (simp only: biv_dx_coeff biv_coeff_zero mult_eq_0_iff of_nat_eq_0_iff; simp)
  have yzero: "biv_coeff f k (Suc l)=0" for k l
    using arg_cong[OF dy, where f="\<lambda>p. biv_coeff p k l"]
    by (simp only: biv_dy_coeff biv_coeff_zero mult_eq_0_iff of_nat_eq_0_iff; simp)
  show "biv_coeff f i j=biv_coeff (biv_monom (biv_coeff f 0 0) 0 0) i j"
    by (cases i; cases j) (simp_all add: xzero yzero)
qed

lemma bivariate_linearMap_injective_of_derivative_stable_kernel:
  fixes L :: "complex bivariate \<Rightarrow> 'v::ab_group_add"
  assumes difference: "\<And>f g. L (f-g)=L f-L g"
    and stable: "\<And>f is_y. L f=0 \<Longrightarrow> L (biv_deriv is_y f)=0"
    and constants: "\<And>c. L (biv_monom c 0 0)=0 \<Longrightarrow> c=0"
  shows "inj L"
proof -
  have kernel: "f=0" if "L f=0" for f
  proof -
    have descend: "\<And>f. bivariate_total_degree f=n \<Longrightarrow> L f=0 \<Longrightarrow> f=0" for n
    proof (induction n rule: less_induct)
      case (less n)
      have partials: "biv_deriv is_y f=0" for is_y
      proof (rule ccontr)
        assume nz: "biv_deriv is_y f\<noteq>0"
        have lower: "bivariate_total_degree (biv_deriv is_y f)<n"
          using bivariate_pderiv_totalDegree_lt[OF nz] less.prems(1) by simp
        have zero: "biv_deriv is_y f=0"
          by (rule less.IH[OF lower refl]) (rule stable[OF less.prems(2)])
        show False using nz zero by blast
      qed
      have dx: "biv_dx f=0" and dy: "biv_dy f=0"
        using partials[of False] partials[of True] by (simp_all add: biv_deriv_def)
      have constant_form: "f=biv_monom (biv_coeff f 0 0) 0 0"
        by (rule bivariate_zero_partials_constant[OF dx dy])
      have Lconstant: "L (biv_monom (biv_coeff f 0 0) 0 0)=0"
        using arg_cong[OF constant_form, where f=L] less.prems(2) by simp
      have c0: "biv_coeff f 0 0=0" by (rule constants[OF Lconstant])
      show ?case using constant_form c0 by (metis biv_monom_zero)
    qed
    show ?thesis by (rule descend[OF refl that])
  qed
  show ?thesis
  proof (rule injI)
    fix f g assume "L f=L g"
    then have "L (f-g)=0" by (simp only: difference diff_self)
    then have "f-g=0" by (rule kernel)
    then show "f=g" by simp
  qed
qed

end
