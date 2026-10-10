theory Exponential_Quadratic_Rigidity
  imports "HOL-Computational_Algebra.Polynomial"
begin

lemma finite_derivative_zeros_below_max:
  fixes f f' :: "real \<Rightarrow> real"
  assumes deriv: "\<And>x. (f has_field_derivative f' x) (at x)"
    and fin: "finite s"
    and zeros: "\<And>x. x \<in> s \<Longrightarrow> f x = 0"
  shows "\<exists>t. finite t \<and> (\<forall>y\<in>t. f' y = 0 \<and> y < Max s) \<and> card s \<le> card t + 1"
  using fin zeros
proof (induction s rule: finite_psubset_induct)
  case (psubset s)
  show ?case
  proof (cases "s = {}")
    case True
    then show ?thesis by (intro exI[of _ "{}"]) simp
  next
    case False
    let ?m = "Max s"
    let ?r = "s - {?m}"
    have m: "?m \<in> s" using psubset.hyps False by simp
    have fr: "finite ?r" using psubset.hyps by simp
    have proper: "?r \<subset> s" using m by blast
    have zr: "\<And>x. x \<in> ?r \<Longrightarrow> f x = 0" using psubset.prems by auto
    obtain t where t: "finite t" "\<forall>y\<in>t. f' y = 0 \<and> y < Max ?r"
      "card ?r \<le> card t + 1" using psubset.IH[OF proper zr] by blast
    show ?thesis
    proof (cases "?r = {}")
      case True
      have "s = {?m}" using True m by blast
      then have "card s = card {?m}" by (rule arg_cong)
      then have "card s = 1" by simp
      then show ?thesis by (intro exI[of _ "{}"]) simp
    next
      case False
      have mr: "Max ?r \<in> ?r" by (rule Max_in[OF fr False])
      have lt: "Max ?r < ?m" using Max_ge[OF psubset.hyps] mr by fastforce
      have eq: "f (Max ?r) = f ?m" using psubset.prems m mr by auto
      have cont: "continuous_on {Max ?r..?m} f"
        by (meson deriv DERIV_isCont continuous_at_imp_continuous_on)
      have dif: "\<And>x. f differentiable (at x)"
        using deriv by (auto simp: real_differentiable_def)
      obtain c where c: "Max ?r < c" "c < ?m" "DERIV f c :> 0"
        using Rolle[OF lt eq cont] dif by blast
      have dc: "f' c = 0" using DERIV_unique[OF deriv c(3)] .
      have nt: "c \<notin> t" using c t(2) by auto
      have bound: "\<forall>y\<in>insert c t. f' y = 0 \<and> y < ?m"
        using t(2) c dc lt by (auto intro: less_trans)
      have "s = insert ?m ?r" using m by auto
      then have cs: "card s = card (insert ?m ?r)" by (rule arg_cong)
      have nm: "?m \<notin> ?r" by simp
      have ci: "card (insert ?m ?r) = Suc (card ?r)" by (rule card_insert_disjoint[OF fr nm])
      have cards: "card s = card ?r + 1" using cs ci by arith
      have "card s \<le> card (insert c t) + 1" using cards t nt by simp
      with t(1) bound show ?thesis by blast
    qed
  qed
qed

theorem exists_finset_deriv_eq_zero:
  fixes f f' :: "real \<Rightarrow> real"
  assumes "\<And>x. (f has_field_derivative f' x) (at x)" "finite s"
    "\<And>x. x \<in> s \<Longrightarrow> f x = 0"
  shows "\<exists>t. finite t \<and> (\<forall>y\<in>t. f' y = 0) \<and> card s \<le> card t + 1"
  using finite_derivative_zeros_below_max[OF assms] by blast

theorem hasDerivAt_expQuad:
  fixes tau a0 a1 a2 c0 c1 c2 t :: real
  shows "((\<lambda>t. exp (tau*t) * (a0+a1*t+a2*t^2) - (c0+c1*t+c2*t^2))
    has_field_derivative
    (exp (tau*t) * ((tau*a0+a1)+(tau*a1+2*a2)*t+tau*a2*t^2) - (c1+2*c2*t+0*t^2))) (at t)"
  by (auto intro!: derivative_eq_intros simp: algebra_simps power2_eq_square)

theorem quadratic_eq_zero_of_three_zeros:
  fixes c0 c1 c2 :: real
  assumes fin: "finite s" and card: "3 \<le> card s"
    and zero: "\<And>y. y \<in> s \<Longrightarrow> c0+c1*y+c2*y^2 = 0"
  shows "c0 = 0 \<and> c1 = 0 \<and> c2 = 0"
proof -
  obtain x where x: "x \<in> s" using card card_gt_0_iff[of s] by auto
  have "card (s - {x}) = card s - 1" using fin x by simp
  then have cy: "0 < card (s - {x})" using card by arith
  then obtain y where y: "y \<in> s" "y \<noteq> x" by (auto dest!: card_gt_0_iff[THEN iffD1])
  have "card (s - {x,y}) = card s - 2" using fin x y by (simp add: card_Diff_subset)
  then have cz: "0 < card (s - {x,y})" using card by arith
  then obtain z where z: "z \<in> s" "z \<noteq> x" "z \<noteq> y" by (auto dest!: card_gt_0_iff[THEN iffD1])
  have "(x-y)*(c1+c2*(x+y)) = (c0+c1*x+c2*x^2)-(c0+c1*y+c2*y^2)" by algebra
  then have e1: "(x-y)*(c1+c2*(x+y)) = 0" using zero[OF x] zero[OF y(1)] by simp
  have "(x-z)*(c1+c2*(x+z)) = (c0+c1*x+c2*x^2)-(c0+c1*z+c2*z^2)" by algebra
  then have e2: "(x-z)*(c1+c2*(x+z)) = 0" using zero[OF x] zero[OF z(1)] by simp
  have f1: "c1+c2*(x+y) = 0" using e1 y by auto
  have f2: "c1+c2*(x+z) = 0" using e2 z by auto
  have "(y-z)*c2 = (c1+c2*(x+y))-(c1+c2*(x+z))" by algebra
  then have "(y-z)*c2 = 0" using f1 f2 by simp 
  then have c2: "c2 = 0" using z by auto
  then have c1: "c1 = 0" using f1 by simp
  show ?thesis using zero[OF x] c1 c2 by simp
qed


theorem expQuad_coeffs_eq_zero:
  fixes tau p0 p1 p2 q0 q1 q2 :: real
  assumes tau: "tau \<noteq> 0" and fin: "finite s" and card: "6 \<le> card s"
    and zero: "\<And>t. t \<in> s \<Longrightarrow> exp (tau*t)*(p0+p1*t+p2*t^2) = q0+q1*t+q2*t^2"
  shows "p0 = 0 \<and> p1 = 0 \<and> p2 = 0"
proof -
  let ?b0 = "tau*p0+p1"
  let ?b1 = "tau*p1+2*p2"
  let ?b2 = "tau*p2"
  let ?d0 = "tau*?b0+?b1"
  let ?d1 = "tau*?b1+2*?b2"
  let ?d2 = "tau*?b2"
  obtain s1 where s1: "finite s1"
    "\<forall>t\<in>s1. exp (tau*t)*(?b0+?b1*t+?b2*t^2)-(q1+2*q2*t+0*t^2) = 0"
    "card s \<le> card s1+1"
    using exists_finset_deriv_eq_zero[OF hasDerivAt_expQuad[of tau p0 p1 p2 q0 q1 q2] fin]
      zero by auto
  obtain s2 where s2: "finite s2"
    "\<forall>t\<in>s2. exp (tau*t)*(?d0+?d1*t+?d2*t^2)-(2*q2+2*0*t+0*t^2) = 0"
    "card s1 \<le> card s2+1"
    using exists_finset_deriv_eq_zero[OF hasDerivAt_expQuad[of tau "?b0" "?b1" "?b2" q1 "2*q2" 0] s1(1)]
      s1(2) by auto
  obtain s3 where s3: "finite s3"
    "\<forall>t\<in>s3. exp (tau*t)*((tau*?d0+?d1)+(tau*?d1+2*?d2)*t+(tau*?d2)*t^2)-(2*0+2*0*t+0*t^2) = 0"
    "card s2 \<le> card s3+1"
    using exists_finset_deriv_eq_zero[OF hasDerivAt_expQuad[of tau "?d0" "?d1" "?d2" "2*q2" "2*0" 0] s2(1)]
      s2(2) by auto
  have card3: "3 \<le> card s3" using card s1(3) s2(3) s3(3) by arith
  have quad: "(tau^3*p0+3*tau^2*p1+6*tau*p2)+(tau^3*p1+6*tau^2*p2)*y+(tau^3*p2)*y^2 = 0"
    if "y \<in> s3" for y
  proof -
    have "(tau*?d0+?d1)+(tau*?d1+2*?d2)*y+(tau*?d2)*y^2 = 0"
      using s3(2)[rule_format, OF that] by simp
    moreover have "(tau*?d0+?d1)+(tau*?d1+2*?d2)*y+(tau*?d2)*y^2 =
      (tau^3*p0+3*tau^2*p1+6*tau*p2)+(tau^3*p1+6*tau^2*p2)*y+(tau^3*p2)*y^2"
      by algebra
    ultimately show ?thesis by simp
  qed
  have coeff: "tau^3*p0+3*tau^2*p1+6*tau*p2 = 0 \<and> tau^3*p1+6*tau^2*p2 = 0 \<and> tau^3*p2 = 0"
    using quadratic_eq_zero_of_three_zeros[OF s3(1) card3 quad] .
  have p2: "p2 = 0" using coeff tau by auto
  have p1: "p1 = 0" using coeff tau p2 by auto
  show ?thesis using coeff tau p2 p1 by auto
qed

end
