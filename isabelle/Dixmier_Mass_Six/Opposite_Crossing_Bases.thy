theory Opposite_Crossing_Bases
  imports Crossing_Substitution_Derivatives Weighted_Face_Rigidity
begin

lemma crossing_inner_unit:
  "[:1:] = (1::complex poly)"
  by (simp add: one_pCons)

lemma biv_univariate_eval_euler:
  "biv_univariate_eval (euler A) W=W*biv_univariate_eval (pderiv A) W"
  by (simp add: euler_def biv_univariate_eval_mult biv_univariate_eval_monom biv_monom_def monom_0 one_pCons smult_1_left; simp only: crossing_inner_unit smult_1_left)

lemma xy_mul_poisson:
  "(X*Y)*biv_poisson R F=(Y*biv_dy R)*(X*biv_dx F)-(X*biv_dx R)*(Y*biv_dy F)"
  by (simp add: biv_poisson_def algebra_simps)

lemma poisson_opposite_crossing_bases_formula:
  fixes A B::"complex poly" and d ell::nat
  defines "W\<equiv>biv_monom 1 d ell"
  shows "biv_poisson (biv_monom 1 0 1*biv_univariate_eval A W)
    (biv_monom 1 1 0*biv_univariate_eval B W)=
    biv_univariate_eval (A*B+[:of_nat d:]*A*euler B+[:of_nat ell:]*euler A*B) W"
proof -
  let ?X = "biv_monom 1 1 0::complex bivariate"
  let ?Y = "biv_monom 1 0 1::complex bivariate"
  let ?U = "biv_univariate_eval A W" let ?V = "biv_univariate_eval B W"
  let ?U' = "biv_univariate_eval (pderiv A) W" let ?V' = "biv_univariate_eval (pderiv B) W"
  let ?D = "biv_monom (of_nat d) 0 0::complex bivariate"
  let ?E = "biv_monom (of_nat ell) 0 0::complex bivariate"
  have rx: "?X*biv_dx (?Y*?U)=?Y*(?D*W*?U')"
    using euler_crossing_x[of 0 1 A d ell] by (simp add: W_def)
  have ry: "?Y*biv_dy (?Y*?U)=?Y*(?U+?E*W*?U')"
    using euler_crossing_y[of 0 1 A d ell] by (simp add: W_def biv_monom_def monom_0 one_pCons smult_1_left; simp only: crossing_inner_unit smult_1_left)
  have fx: "?X*biv_dx (?X*?V)=?X*(?V+?D*W*?V')"
    using euler_crossing_x[of 1 0 B d ell] by (simp add: W_def biv_monom_def monom_0 one_pCons smult_1_left; simp only: crossing_inner_unit smult_1_left)
  have fy: "?Y*biv_dy (?X*?V)=?X*(?E*W*?V')"
    using euler_crossing_y[of 1 0 B d ell] by (simp add: W_def)
  have scaled: "(?X*?Y)*biv_poisson (?Y*?U) (?X*?V)=
    (?X*?Y)*(?U*?V+?D*W*?U*?V'+?E*W*?U'*?V)"
    by (simp only: xy_mul_poisson ry fx rx fy) (simp add: algebra_simps)
  have evaluated: "biv_univariate_eval (A*B+[:of_nat d:]*A*euler B+[:of_nat ell:]*euler A*B) W=
    ?U*?V+?D*W*?U*?V'+?E*W*?U'*?V"
    by (simp add: biv_univariate_eval_add biv_univariate_eval_mult biv_univariate_eval_smult biv_univariate_eval_euler algebra_simps)
  have nonzero: "?X*?Y\<noteq>0" by simp
  have "(?X*?Y)*biv_poisson (?Y*?U) (?X*?V)=
    (?X*?Y)*biv_univariate_eval (A*B+[:of_nat d:]*A*euler B+[:of_nat ell:]*euler A*B) W"
    using scaled evaluated by simp
  then show ?thesis using nonzero by simp
qed

lemma poisson_opposite_crossing_bases_eq_one_forces_degree_zero:
  fixes A B::"complex poly" and d ell::nat
  assumes ell: "0<ell" and A: "A\<noteq>0" and B: "B\<noteq>0"
    and bracket: "biv_poisson (biv_monom 1 0 1*biv_univariate_eval A (biv_monom 1 d ell))
      (biv_monom 1 1 0*biv_univariate_eval B (biv_monom 1 d ell))=1"
  shows "degree A=0 \<and> degree B=0"
proof -
  let ?H = "A*B+[:of_nat d:]*A*euler B+[:of_nat ell:]*euler A*B"
  have evaluated: "biv_univariate_eval ?H (biv_monom 1 d ell)=biv_univariate_eval [:1:] (biv_monom 1 d ell)"
    using poisson_opposite_crossing_bases_formula[where A=A and B=B and d=d and ell=ell] bracket
    by (simp add: biv_monom_def monom_0 one_pCons smult_1_left; simp only: crossing_inner_unit smult_1_left)
  have equation: "?H=[:1:]" by (rule crossing_substitution_injective[OF ell evaluated])
  show ?thesis by (rule weightedFaceEuler_eq_constant_forces_degree_zero[where A=A and B=B and d=d and ell=ell and c=1, OF A B]) (use equation in simp)
qed

end
