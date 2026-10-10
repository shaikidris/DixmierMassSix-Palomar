theory Crossing_Poisson_Scalar
 imports "Opposite_Crossing_Bases"
   "General_Companion"
begin

lemma biv_univariate_eval_diff:
 "biv_univariate_eval(A-B) W=biv_univariate_eval A W-biv_univariate_eval B W"
proof -
 have addition: "biv_univariate_eval (A-B) W+biv_univariate_eval B W=biv_univariate_eval A W"
  using biv_univariate_eval_add[where A="A-B" and B=B and W=W]
  by (simp only: diff_add_cancel)
 show ?thesis by (simp only: eq_diff_eq) (rule addition)
qed

lemma crossing_poisson_formula:
 fixes p f::"complex poly" and a b s rho::nat
 defines "W\<equiv>biv_monom 1 s rho"
 shows "biv_monom 1 1 1*biv_poisson
 (biv_monom 1 a b*biv_univariate_eval p W)
 (biv_monom 1 1 1*biv_univariate_eval f W)=
 biv_monom 1 a b*biv_monom 1 1 1*
 ((biv_monom (of_nat rho- of_nat s) 0 0)*W*biv_univariate_eval f W*biv_univariate_eval(pderiv p) W-
 ((biv_monom (of_nat a- of_nat b) 0 0)*biv_univariate_eval f W+
 biv_monom (of_nat rho* of_nat a- of_nat s* of_nat b) 0 0*W*biv_univariate_eval(pderiv f) W)*biv_univariate_eval p W)"
proof -
 let ?X = "biv_monom 1 1 0::complex bivariate"
 let ?Y = "biv_monom 1 0 1::complex bivariate"
 let ?A = "biv_monom 1 a b::complex bivariate"
 let ?B = "biv_monom 1 1 1::complex bivariate"
 let ?U = "biv_univariate_eval p W" let ?V = "biv_univariate_eval f W"
 let ?U' = "biv_univariate_eval(pderiv p) W" let ?V' = "biv_univariate_eval(pderiv f) W"
 have xy: "?X*?Y=?B" by (simp add: biv_mult_monom)
 have rx: "?X*biv_dx(?A*?U)=?A*(biv_monom(of_nat a) 0 0*?U+biv_monom(of_nat s) 0 0*W*?U')"
  using euler_crossing_x[of a b p s rho] by (simp only: W_def)
 have ry: "?Y*biv_dy(?A*?U)=?A*(biv_monom(of_nat b) 0 0*?U+biv_monom(of_nat rho) 0 0*W*?U')"
  using euler_crossing_y[of a b p s rho] by (simp only: W_def)
 have fx: "?X*biv_dx(?B*?V)=?B*(?V+biv_monom(of_nat s) 0 0*W*?V')"
  using euler_crossing_x[of 1 1 f s rho]
  by (simp add: W_def biv_monom_def monom_0 one_pCons smult_1_left; simp only: crossing_inner_unit smult_1_left)
 have fy: "?Y*biv_dy(?B*?V)=?B*(?V+biv_monom(of_nat rho) 0 0*W*?V')"
  using euler_crossing_y[of 1 1 f s rho]
  by (simp add: W_def biv_monom_def monom_0 one_pCons smult_1_left; simp only: crossing_inner_unit smult_1_left)
 have scaled: "?B*biv_poisson(?A*?U)(?B*?V)=
 (?A*(biv_monom(of_nat b) 0 0*?U+biv_monom(of_nat rho) 0 0*W*?U'))*
 (?B*(?V+biv_monom(of_nat s) 0 0*W*?V'))-
 (?A*(biv_monom(of_nat a) 0 0*?U+biv_monom(of_nat s) 0 0*W*?U'))*
 (?B*(?V+biv_monom(of_nat rho) 0 0*W*?V'))"
  using xy_mul_poisson[where X="?X" and Y="?Y" and R="?A*?U" and F="?B*?V"]
  by (simp only: xy rx ry fx fy)
 have constant_diff: "biv_monom (x-y) 0 0=biv_monom x 0 0-biv_monom y 0 0"
   for x y::complex by (simp add: biv_monom_def monom_0)
 have constant_mult: "biv_monom (x*y) 0 0=biv_monom x 0 0*biv_monom y 0 0"
   for x y::complex by (simp add: biv_mult_monom)
 show ?thesis by (simp only: scaled constant_diff constant_mult; algebra)
qed

lemma crossing_poisson_implies_scalar:
 fixes p f::"complex poly" and a b s rho::nat
 assumes rho: "0<rho" and bracket: "biv_poisson
 (biv_monom 1 a b*biv_univariate_eval p (biv_monom 1 s rho))
 (biv_monom 1 1 1*biv_univariate_eval f (biv_monom 1 s rho))=
 biv_monom 1 a b*biv_univariate_eval p (biv_monom 1 s rho)"
 shows "[:of_nat rho- of_nat s:]*[:0,1:]*f*pderiv p-
 (([:of_nat a- of_nat b:]*f+[:of_nat rho* of_nat a- of_nat s* of_nat b:]*[:0,1:]*pderiv f+1)*p)=0"
proof -
 let ?W = "biv_monom 1 s rho::complex bivariate"
 let ?A = "biv_monom 1 a b::complex bivariate"
 let ?B = "biv_monom 1 1 1::complex bivariate"
 let ?C = "[:of_nat rho- of_nat s:]*[:0,1:]*f*pderiv p-
 (([:of_nat a- of_nat b:]*f+[:of_nat rho* of_nat a- of_nat s* of_nat b:]*[:0,1:]*pderiv f)*p)"
 have eval_variable: "biv_univariate_eval [:0,1:] ?W=?W"
  by (simp add: biv_univariate_eval_pCons biv_monom_def monom_0 one_pCons; simp only: crossing_inner_unit smult_1_left)
 have evaluated: "biv_univariate_eval ?C ?W=
 (biv_monom (of_nat rho- of_nat s) 0 0)*?W*biv_univariate_eval f ?W*biv_univariate_eval(pderiv p) ?W-
 ((biv_monom (of_nat a- of_nat b) 0 0)*biv_univariate_eval f ?W+
 biv_monom (of_nat rho* of_nat a- of_nat s* of_nat b) 0 0*?W*biv_univariate_eval(pderiv f) ?W)*biv_univariate_eval p ?W"
  by (simp only: biv_univariate_eval_diff biv_univariate_eval_add biv_univariate_eval_mult
   biv_univariate_eval_const eval_variable)
 have scaled: "?A*?B*biv_univariate_eval ?C ?W=?A*?B*biv_univariate_eval p ?W"
  using crossing_poisson_formula[where s=s and rho=rho and p=p and f=f and a=a and b=b] bracket
  by (simp only: evaluated[symmetric] bracket; simp only: mult_ac)
 have equal: "biv_univariate_eval ?C ?W=biv_univariate_eval p ?W"
  using scaled by simp
 have scalar: "?C=p" by (rule crossing_substitution_injective[OF rho equal])
 show ?thesis using scalar by (simp add: algebra_simps)
qed

lemma crossing_scalar_to_GenComp:
 fixes rho s a b::nat and p f::"complex poly"
 assumes direction: "s<rho" and base: "b<a"
   and scalar: "[:of_nat rho- of_nat s:]*[:0,1:]*f*pderiv p-
 (([:of_nat a- of_nat b:]*f+[:of_nat rho* of_nat a- of_nat s* of_nat b:]*[:0,1:]*pderiv f+1)*p)=0"
 shows "GenComp(rho-s)(a-b)(rho*a-s*b) p f"
proof -
 have first: "s*b\<le>rho*b" by (rule mult_le_mono1) (use direction in arith)
 have second: "rho*b\<le>rho*a" by (rule mult_le_mono2) (use base in arith)
 have product: "s*b\<le>rho*a" using first second by arith
 show ?thesis using scalar direction base product
  by (simp add: GenComp_def of_nat_diff)
qed

end
