theory Crossing_Substitution_Derivatives
  imports Crossing_Base_Shape "Poisson_Power_Cancellation"
begin

lemma biv_univariate_eval_pCons:
  "biv_univariate_eval (pCons c A) W=biv_monom c 0 0+W*biv_univariate_eval A W"
  by (simp add: biv_univariate_eval_def map_poly_pCons poly_pCons biv_monom_def monom_0)
lemma biv_univariate_eval_add:
  "biv_univariate_eval (A+B) W=biv_univariate_eval A W+biv_univariate_eval B W"
  using biv_univariate_eval_hom[of W] by (simp add: coefficient_hom_def)
lemma biv_univariate_eval_zero [simp]: "biv_univariate_eval 0 W=0"
  by (simp add: biv_univariate_eval_def)
lemma crossing_dx_add:
  "biv_dx (p+q)=biv_dx p+biv_dx q"
  by (rule biv_eqI) (simp add: biv_dx_coeff algebra_simps)
lemma crossing_dy_add:
  "biv_dy (p+q)=biv_dy p+biv_dy q"
  by (rule biv_eqI) (simp add: biv_dy_coeff algebra_simps)

lemma pderiv_polynomial_substitution:
  "biv_deriv is_y (biv_univariate_eval A W)=biv_univariate_eval (pderiv A) W*biv_deriv is_y W"
proof (cases is_y)
  case False
  have "biv_dx (biv_univariate_eval A W)=biv_univariate_eval (pderiv A) W*biv_dx W"
    by (induction A) (simp_all add: biv_univariate_eval_pCons pderiv_pCons biv_univariate_eval_add
      crossing_dx_add biv_dx_mult biv_monom_def monom_0 algebra_simps)
  then show ?thesis by (simp add: False biv_deriv_def)
next
  case True
  have "biv_dy (biv_univariate_eval A W)=biv_univariate_eval (pderiv A) W*biv_dy W"
    by (induction A) (simp_all add: biv_univariate_eval_pCons pderiv_pCons biv_univariate_eval_add
      crossing_dy_add biv_dy_mult biv_monom_def monom_0 algebra_simps)
  then show ?thesis by (simp add: True biv_deriv_def)
qed

lemma crossing_euler_x_monomial:
  "biv_monom 1 1 0*biv_dx (biv_monom 1 a b)=biv_monom (of_nat a) 0 0*biv_monom 1 a b"
  by (cases a) (simp_all add: biv_dx_monom biv_mult_monom)
lemma crossing_euler_y_monomial:
  "biv_monom 1 0 1*biv_dy (biv_monom 1 a b)=biv_monom (of_nat b) 0 0*biv_monom 1 a b"
  by (cases b) (simp_all add: biv_dy_monom biv_mult_monom)

lemma euler_crossing_x:
  "biv_monom 1 1 0*biv_dx (biv_monom 1 a b*biv_univariate_eval A (biv_monom 1 s rho))=
    biv_monom 1 a b*(biv_monom (of_nat a) 0 0*biv_univariate_eval A (biv_monom 1 s rho)+
      biv_monom (of_nat s) 0 0*biv_monom 1 s rho*biv_univariate_eval (pderiv A) (biv_monom 1 s rho))"
proof -
  have chain: "biv_dx (biv_univariate_eval A (biv_monom 1 s rho))=
    biv_univariate_eval (pderiv A) (biv_monom 1 s rho)*biv_dx (biv_monom 1 s rho)"
    using pderiv_polynomial_substitution[of False A "biv_monom 1 s rho"] by (simp add: biv_deriv_def)
  have distributed: "biv_monom 1 1 0*biv_dx (biv_monom 1 a b*biv_univariate_eval A (biv_monom 1 s rho))=
    (biv_monom 1 1 0*biv_dx (biv_monom 1 a b))*biv_univariate_eval A (biv_monom 1 s rho)+
    biv_monom 1 a b*((biv_monom 1 1 0*biv_dx (biv_monom 1 s rho))*biv_univariate_eval (pderiv A) (biv_monom 1 s rho))"
    by (simp only: biv_dx_mult chain; simp only: algebra_simps)
  show ?thesis by (simp only: distributed crossing_euler_x_monomial; simp only: algebra_simps)
qed

lemma euler_crossing_y:
  "biv_monom 1 0 1*biv_dy (biv_monom 1 a b*biv_univariate_eval A (biv_monom 1 s rho))=
    biv_monom 1 a b*(biv_monom (of_nat b) 0 0*biv_univariate_eval A (biv_monom 1 s rho)+
      biv_monom (of_nat rho) 0 0*biv_monom 1 s rho*biv_univariate_eval (pderiv A) (biv_monom 1 s rho))"
proof -
  have chain: "biv_dy (biv_univariate_eval A (biv_monom 1 s rho))=
    biv_univariate_eval (pderiv A) (biv_monom 1 s rho)*biv_dy (biv_monom 1 s rho)"
    using pderiv_polynomial_substitution[of True A "biv_monom 1 s rho"] by (simp add: biv_deriv_def)
  have distributed: "biv_monom 1 0 1*biv_dy (biv_monom 1 a b*biv_univariate_eval A (biv_monom 1 s rho))=
    (biv_monom 1 0 1*biv_dy (biv_monom 1 a b))*biv_univariate_eval A (biv_monom 1 s rho)+
    biv_monom 1 a b*((biv_monom 1 0 1*biv_dy (biv_monom 1 s rho))*biv_univariate_eval (pderiv A) (biv_monom 1 s rho))"
    by (simp only: biv_dy_mult chain; simp only: algebra_simps)
  show ?thesis by (simp only: distributed crossing_euler_y_monomial; simp only: algebra_simps)
qed

lemma crossing_substitution_coefficient:
  assumes ell: "0<ell"
  shows "biv_coeff (biv_univariate_eval A (biv_monom 1 d ell)) (d*t) (ell*t)=coeff A t"
proof -
  have reconstruction: "A=(\<Sum>n\<le>degree A. monom (coeff A n) n)"
    using poly_as_sum_of_monoms[of A] by simp
  have evaluated: "biv_univariate_eval A (biv_monom 1 d ell)=
    (\<Sum>n\<le>degree A. biv_monom (coeff A n) (d*n) (ell*n))"
  proof -
    have "biv_univariate_eval A (biv_monom 1 d ell)=
      biv_univariate_eval (\<Sum>n\<le>degree A. monom (coeff A n) n) (biv_monom 1 d ell)"
      by (simp only: poly_as_sum_of_monoms)
    also have "\<dots>=(\<Sum>n\<le>degree A. biv_monom (coeff A n) (d*n) (ell*n))"
      by (simp add: biv_univariate_eval_sum biv_univariate_eval_monom biv_monom_def monom_power mult_monom)
    finally show ?thesis .
  qed
  have indices: "\<And>n. (d*t=d*n \<and> ell*t=ell*n) \<longleftrightarrow> t=n" using ell by auto
  have coefficient_sum: "biv_coeff (biv_univariate_eval A (biv_monom 1 d ell)) (d*t) (ell*t)=
    (\<Sum>n\<le>degree A. if t=n then coeff A n else 0)"
    by (simp only: evaluated biv_coeff_sum biv_coeff_monom indices)
  have delta: "(\<Sum>n\<le>degree A. if t=n then coeff A n else 0)=
    (if t\<le>degree A then coeff A t else 0)"
    by (simp only: sum.delta'[OF finite_atMost] atMost_iff)
  show ?thesis
  proof (cases "t\<le>degree A")
    case True
    show ?thesis by (simp only: coefficient_sum delta True if_True)
  next
    case False
    have zero: "coeff A t=0" by (rule coeff_eq_0) (use False in arith)
    show ?thesis by (simp only: coefficient_sum delta False if_False zero)
  qed
qed

lemma crossing_substitution_injective:
  assumes ell: "0<ell" and equal: "biv_univariate_eval A (biv_monom 1 d ell)=biv_univariate_eval B (biv_monom 1 d ell)"
  shows "A=B"
proof (rule poly_eqI)
  fix t
  have "biv_coeff (biv_univariate_eval A (biv_monom 1 d ell)) (d*t) (ell*t)=
    biv_coeff (biv_univariate_eval B (biv_monom 1 d ell)) (d*t) (ell*t)"
    by (simp only: equal)
  then show "coeff A t=coeff B t" by (simp add: crossing_substitution_coefficient[OF ell])
qed

end
