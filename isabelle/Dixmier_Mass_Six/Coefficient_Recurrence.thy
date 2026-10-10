theory Coefficient_Recurrence
  imports "Classification_Structure"
    "Scalar_Recurrence" Alternating_Square_Support
begin

lemma recurrence_degree_identity:
  fixes rho s e L :: nat
  assumes "s<rho" "e=L+1" "(rho-s)*e=1+rho*L"
  shows "rho=s*e+1"
proof -
  have "rho*e = ((rho-s)+s)*e" using assms by simp
  also have "... = (rho-s)*e+s*e" by (simp add: algebra_simps)
  also have "... = 1+rho*L+s*e" by (simp only: assms(3))
  finally show ?thesis using assms(2) by (simp add: algebra_simps)
qed

lemma recurrence_complex_denominator:
  "(1+of_nat s*(of_nat j+1)::complex)\<noteq>0"
proof -
  have nonneg: "(0::real)\<le>of_nat s*(of_nat j+1)" by (intro mult_nonneg_nonneg) simp_all
  have "(1+of_nat s*(of_nat j+1)::real)>0" using nonneg by arith
  moreover have cast: "(1+of_nat s*(of_nat j+1)::complex) = of_real (1+of_nat s*(of_nat j+1)::real)" by simp
  ultimately show ?thesis by (simp only: cast of_real_eq_0_iff; linarith)
qed

lemma recurrence_identifies_coefficients:
  fixes f :: "complex poly"
  assumes init: "coeff f 0=-1"
    and rec: "\<And>j. (1+of_nat s*(of_nat j+1))*coeff f (j+1) =
      -(of_nat s*(of_nat L-of_nat j))*coeff f j+(if j=0 then 1 else 0)"
  shows "coeff f j = of_real (recSeq s L j)"
proof (induction j)
  case 0
  then show ?case by (simp add: init)
next
  case (Suc j)
  have den: "(1+of_nat s*(of_nat j+1)::complex)\<noteq>0"
    by (rule recurrence_complex_denominator)
  have cast: "(of_real (recSeq s L (Suc j))::complex) =
    (-(of_nat s*(of_nat L-of_nat j))*of_real(recSeq s L j)+(if j=0 then 1 else 0)) /
      (1+of_nat s*(of_nat j+1))"
    by simp
  have eq: "(1+of_nat s*(of_nat j+1))*coeff f (Suc j) =
      -(of_nat s*(of_nat L-of_nat j))*of_real(recSeq s L j)+(if j=0 then 1 else 0)"
    using rec[of j] by (simp only: Suc_eq_plus1 Suc.IH)
  have quotient: "coeff f (Suc j) =
    (-(of_nat s*(of_nat L-of_nat j))*of_real(recSeq s L j)+(if j=0 then 1 else 0)) /
      (1+of_nat s*(of_nat j+1))"
    using eq by (simp only: nonzero_eq_divide_eq[OF den] mult.commute)
  show ?case by (rule trans[OF quotient cast[symmetric]])
qed


lemma recurrence_difference_sign:
  assumes hs: "1\<le>s" and hL: "1\<le>L"
  defines "y \<equiv> \<lambda>k. if k=0 then 1 else recSeq s L (k-1)-recSeq s L k"
  shows "\<forall>k\<le>L+1. 0 < (-1::real)^k*y k"
proof (intro allI impI)
  fix k assume hk: "k\<le>L+1"
  show "0<(-1::real)^k*y k"
  proof (cases k)
    case 0 then show ?thesis by (simp add: y_def)
  next
    case (Suc j)
    have jL: "j\<le>L" using hk Suc by arith
    have first: "0<(-1::real)^(j+1)*recSeq s L j"
      using recSeq_sign[OF hs hL] jL by blast
    have second: "0\<le>(-1::real)^(j+1+1)*recSeq s L (j+1)"
    proof (cases "j+1\<le>L")
      case True
      then show ?thesis using recSeq_sign[OF hs hL] by fastforce
    next
      case False
      then have z: "recSeq s L (j+1)=0" using recSeq_eq_zero[OF hL, where s=s] by (meson not_le)
      show ?thesis by (simp only: z mult_zero_right; rule order_refl)
    qed
    have expand: "(-1::real)^(j+1)*(recSeq s L j-recSeq s L (j+1)) =
      (-1)^(j+1)*recSeq s L j+(-1)^(j+1+1)*recSeq s L (j+1)"
      by (simp only: power_add power_one_right; algebra)
    have "0<(-1::real)^(j+1)*(recSeq s L j-recSeq s L (j+1))"
      using first second by (simp only: expand; linarith)
    then show ?thesis by (simp add: Suc y_def del: recSeq.simps)
  qed
qed


lemma companion_factor_reduction:
  assumes h: "Comp rho s r f" and fact: "r=[:-1,1:]*f" and fnz: "f\<noteq>0"
  shows "[:of_nat rho-of_nat s:] * ([:0,1:]*f + [:0,1:]*euler f-euler f) =
    (f+[:of_nat rho:]*euler f+1)*[:0,1:]-(f+[:of_nat rho:]*euler f+1)"
proof -
  let ?A = "[:of_nat rho-of_nat s:]::complex poly"
  let ?B = "[:of_nat rho:]::complex poly"
  let ?X = "[:0,1:]::complex poly"
  let ?D = "pderiv f"
  let ?U = "?A*(?X*f+?X*euler f-euler f)"
  let ?V = "(f+?B*euler f+1)*?X-(f+?B*euler f+1)"
  have ef: "euler f = ?X*?D" by (simp add: euler_def monom_altdef)
  have lin: "[:-1,1:] = (?X-1)" by (simp add: one_pCons)
  have deriv: "pderiv ([:-1,1:]::complex poly)=1" by (simp add: pderiv_pCons)
  have e: "?A*?X*f*(f+[:-1,1:]*?D) = (f+?B*?X*?D+1)*([:-1,1:]*f)"
    using h unfolding Comp_def by (simp only: fact pderiv_mult deriv mult_1_left mult_1_right add.commute)
  have left: "?A*?X*f*(f+[:-1,1:]*?D) = ?U*f"
    by (simp only: lin ef; algebra)
  have right: "(f+?B*?X*?D+1)*([:-1,1:]*f) = ?V*f"
    by (simp only: lin ef; algebra)
  have "?U*f=?V*f" using e by (simp only: left right)
  then show ?thesis by (simp only: mult_right_cancel[OF fnz])
qed


lemma reduced_equation_coefficients:
  fixes f :: "complex poly"
  assumes red: "[:of_nat rho-of_nat s:] * ([:0,1:]*f + [:0,1:]*euler f-euler f) =
    (f+[:of_nat rho:]*euler f+1)*[:0,1:]-(f+[:of_nat rho:]*euler f+1)"
    and rho: "rho=s*(L+1)+1"
  shows "(1+of_nat s*(of_nat j+1))*coeff f (j+1) =
    -(of_nat s*(of_nat L-of_nat j))*coeff f j+(if j=0 then 1 else 0)"
proof -
  let ?R = "of_nat rho::complex"
  let ?S = "of_nat s::complex"
  let ?J = "of_nat j::complex"
  let ?L = "of_nat L::complex"
  let ?z = "coeff f j"
  let ?w = "coeff f (j+1)"
  let ?d = "if j=0 then 1 else 0::complex"
  have cast: "?R=?S*(?L+1)+1" by (simp add: rho algebra_simps)
  have e: "(?R-?S)*((?J+1)*?z-(?J+1)*?w) =
      (1+?R*?J)*?z+?d-(1+?R*(?J+1))*?w"
    using arg_cong[OF red, of "\<lambda>p. coeff p (j+1)"]
    by (simp add: coeff_euler coeff_pCons' algebra_simps)
  have identity: "(1+?S*(?J+1))*?w - (- (?S*(?L-?J))*?z+?d) =
    (?R-?S)*((?J+1)*?z-(?J+1)*?w) - ((1+?R*?J)*?z+?d-(1+?R*(?J+1))*?w)"
    by (simp only: cast; algebra)
  have "(1+?S*(?J+1))*?w - (- (?S*(?L-?J))*?z+?d)=0"
    by (simp only: identity e diff_self)
  then show ?thesis by simp
qed

end
