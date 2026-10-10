theory Poisson_Power_Cancellation
 imports "Partial_Derivatives"
begin
lemma derivative_finite_sum:
 "pderiv(sum f S)=sum (\<lambda>x. pderiv(f x)) S"
 using higher_pderiv_sum[where n=1 and f=f and A=S] by simp
lemma biv_dx_mult:
 "biv_dx(p*q)=biv_dx p*q+p*biv_dx q"
 by (rule poly_eqI; simp only: biv_dx_def coeff_map_poly pderiv_0 coeff_add coeff_mult derivative_finite_sum pderiv_mult sum.distrib) (simp add: algebra_simps)
lemma biv_dy_mult:
 "biv_dy(p*q)=biv_dy p*q+p*biv_dy q"
 by (simp add: biv_dy_def pderiv_mult algebra_simps)
lemma biv_dx_one [simp]: "biv_dx 1=0"
 by (simp add: biv_dx_def one_pCons map_poly_pCons)
lemma biv_dy_one [simp]: "biv_dy 1=0"
 by (simp add: biv_dy_def)
lemma biv_dx_power_Suc:
 "biv_dx(p^Suc n)=of_nat(Suc n)*p^n*biv_dx p"
 by (induction n) (simp_all add: biv_dx_mult algebra_simps)
lemma biv_dy_power_Suc:
 "biv_dy(p^Suc n)=of_nat(Suc n)*p^n*biv_dy p"
 by (induction n) (simp_all add: biv_dy_mult algebra_simps)
lemma biv_dx_power:
 "biv_dx(p^n)=of_nat n*p^(n-1)*biv_dx p"
 by (cases n) (simp_all add: biv_dx_power_Suc del: power_Suc)
lemma biv_dy_power:
 "biv_dy(p^n)=of_nat n*p^(n-1)*biv_dy p"
 by (cases n) (simp_all add: biv_dy_power_Suc del: power_Suc)
lemma biv_dx_const [simp]: "biv_dx [:[:c:]:]=0"
 by (simp add: biv_dx_def map_poly_pCons)
lemma biv_dy_const [simp]: "biv_dy [:[:c:]:]=0"
 by (simp add: biv_dy_def)
lemma biv_poisson_const_left:
 "biv_poisson ([:[:c:]:]*R) F=[:[:c:]:]*biv_poisson R F"
 by (simp only: biv_poisson_def biv_dx_mult biv_dy_mult biv_dx_const biv_dy_const) (simp add: algebra_simps)
lemma biv_poisson_const_right:
 "biv_poisson R ([:[:c:]:]*F)=[:[:c:]:]*biv_poisson R F"
 by (simp only: biv_poisson_def biv_dx_mult biv_dy_mult biv_dx_const biv_dy_const) (simp add: algebra_simps)
lemma poisson_power_left:
 fixes R F :: "complex bivariate"
 shows "biv_poisson(R^k)F=of_nat k*R^(k-1)*biv_poisson R F"
 by (simp only: biv_poisson_def biv_dx_power biv_dy_power) (simp add: algebra_simps)
lemma poisson_power_companion_cancel:
 fixes R F :: "complex bivariate" and mu :: complex
 assumes mu: "mu\<noteq>0" and k: "0<k" and R: "R\<noteq>0"
 and h: "biv_poisson ([:[:mu:]:]*R^k) F=[:[:mu:]:]*R^k"
 shows "biv_poisson R ([:[:of_nat k:]:]*F)=R"
proof -
 have power: "R^k=R^(k-1)*R"
 proof -
  have eq: "Suc(k-1)=k" using k by arith
  show ?thesis using power_Suc2[of R "k-1"] by (simp only: eq)
 qed
 have expanded: "[:[:mu:]:]*(of_nat k*R^(k-1)*biv_poisson R F)=[:[:mu:]:]*R^k"
  using h by (simp only: biv_poisson_const_left poisson_power_left)
 have factor: "([:[:mu:]:]*R^(k-1))*(of_nat k*biv_poisson R F)=([:[:mu:]:]*R^(k-1))*R"
  using expanded by (simp only: power) (simp add: algebra_simps)
 have nz: "[:[:mu:]:]*R^(k-1)\<noteq>0" using mu R by simp
 have cancel: "of_nat k*biv_poisson R F=R" using factor by (simp only: mult_left_cancel[OF nz])
 show ?thesis unfolding biv_poisson_const_right using cancel by (simp only: of_nat_poly)
qed

lemma zeroth_power_bracket_control:
 "biv_poisson ((R::complex bivariate)^0) F=0"
 by (simp add: biv_poisson_def)
lemma first_power_bracket_control:
 "biv_poisson ((R::complex bivariate)^1) F=biv_poisson R F"
 by simp
lemma poisson_sign_control:
 "biv_poisson (biv_monom (1::complex) 0 1) (biv_monom 1 1 0)=biv_monom 1 0 0"
 by (simp add: biv_poisson_def biv_dx_monom biv_dy_monom biv_mult_monom numeral_eq_Suc)
end
