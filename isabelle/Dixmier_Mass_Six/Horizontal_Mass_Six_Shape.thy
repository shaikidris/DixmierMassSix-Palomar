theory Horizontal_Mass_Six_Shape
 imports "Horizontal_Crossing_Support"
   "Horizontal_Square"
begin

lemma horizontal_counterexample_mass_six_scalar_shape:
 fixes P Q::"complex poly_operator"
 assumes inputs: GGVInputs and pair: "is_counterexample_pair P Q"
 and crossing: "strict_crossing 1 0 P" and mass: "weyl_mass P\<le>6"
 shows "\<exists>mu c beta::complex. mu\<noteq>0 \<and> c\<noteq>0 \<and> beta\<noteq>0 \<and>
 leading_form 1 0 P = [:[:mu:]:] * (biv_monom 1 1 0 * biv_univariate_eval ([:c:] * [: - beta,1:] ^ 2)(biv_monom 1 0 1)) ^ 2"
proof -
 obtain mu k a g f where mu: "mu\<noteq>0" and k: "2\<le>k" and g: "g\<noteq>0"
 and face: "leading_form 1 0 P = [:[:mu:]:] * (biv_monom 1 a 0 * biv_univariate_eval g(biv_monom 1 0 1)) ^ k"
 and scalar: "f * pderiv g - [:of_nat a:] * pderiv f * g = g"
 using horizontal_counterexample_scalar_of_GGV[OF inputs pair] by blast
 have comp: "HorizComp a g f" using scalar unfolding HorizComp_def by blast
 have bounds: "rootMultiplicity 0 g < a \<and> a < degree g" by (rule horizontal_crossing_order_bounds[OF mu face crossing])
 have P: "P\<in>weyl_algebra" using pair unfolding is_counterexample_pair_def by blast
 have terms: "termCount(g ^ k)\<le>6"
  using horizontal_face_termCount_le_mass[OF P mu face] mass by arith
 have positive: "0 < degree g" using bounds by arith
 have parameters: "k = 2 \<and> a = 1" using HorizComp_mass_six_parameters[OF comp positive _ _ k terms] bounds by blast
 have special: "HorizComp 1 g f" using comp parameters by simp
 have zero: "rootMultiplicity 0 g < 1" using bounds parameters by simp
 have square_terms: "termCount(g ^ 2)\<le>6" using terms parameters by simp
 obtain c beta where c: "c\<noteq>0" and beta: "beta\<noteq>0" and shape: "g = [:c:] * [: - beta,1:] ^ 2"
  using HorizComp_mass_six_quadratic[OF special positive zero square_terms] by blast
 show ?thesis using mu c beta face parameters shape by blast
qed

lemma horizontal_quadratic_normalize:
 fixes c beta::complex
 assumes beta: "beta\<noteq>0"
 shows "[:c:] * [: - beta,1:] ^ 2 = [:c * beta ^ 2:] * (1 + [: - inverse beta:] * [:0,1:]) ^ 2"
proof -
 have linear: "[: - beta,1:] = [: - beta:] * (1 + [: - inverse beta:] * [:0,1:])"
 proof (rule poly_eqI)
  fix n
  show "coeff [: - beta,1:] n = coeff ([: - beta:] * (1 + [: - inverse beta:] * [:0,1:])) n"
   using beta by (cases n; simp add: coeff_pCons' coeff_mult split: if_splits)
 qed
 have scalar_power: "([:z:]::complex poly) ^ m = [:z ^ m:]" for z::complex and m::nat
   by (induction m) (simp_all add: one_pCons)
 show ?thesis by (simp only: linear power_mult_distrib scalar_power; simp add: mult_ac)
qed

lemma horizontal_face_normalize:
 fixes mu c beta::complex
 assumes beta: "beta\<noteq>0"
 shows "[:[:mu:]:] * (biv_monom 1 1 0 * biv_univariate_eval ([:c:] * [: - beta,1:] ^ 2)(biv_monom 1 0 1)) ^ 2 = 
 [:[:mu * (c * beta ^ 2) ^ 2:]:] * (biv_monom 1 1 0) ^ 2 * 
 (1 + [:[: - inverse beta:]:] * biv_monom 1 0 1) ^ 4"
proof -
 have power: "biv_univariate_eval(g ^ k)W = (biv_univariate_eval g W) ^ k" for g::"complex poly" and W and k
  by (rule coefficient_hom_power[OF biv_univariate_eval_hom])
 have scalar_monom: "(biv_monom z 0 0::complex bivariate) = [:[:z:]:]" for z
   by (simp only: biv_monom_def monom_0)
 have eval_one: "biv_univariate_eval (1::complex poly) W = 1" for W::"complex bivariate"
   using biv_univariate_eval_hom[of W] by (simp add: coefficient_hom_def)
 have eval_X: "biv_univariate_eval ([:0,1:]::complex poly) W = W" for W::"complex bivariate"
   by (simp add: biv_univariate_eval_pCons scalar_monom pCons_one eval_one)
 let ?Y = "biv_monom 1 0 1::complex bivariate"
 let ?B = "1 + [:[: - inverse beta:]:] * ?Y"
 have eval_base: "biv_univariate_eval (1 + [: - inverse beta:] * [:0,1:]) ?Y = ?B"
   by (simp only: biv_univariate_eval_add biv_univariate_eval_mult biv_univariate_eval_const
     scalar_monom eval_one eval_X)
 have eval_quad: "biv_univariate_eval ([:c:] * [: - beta,1:] ^ 2) ?Y = [:[:c * beta ^ 2:]:] * ?B ^ 2"
   by (simp only: horizontal_quadratic_normalize[OF beta] biv_univariate_eval_mult
     biv_univariate_eval_const scalar_monom power eval_base)
 have constant_power: "([:[:z:]:]::complex bivariate) ^ k = [:[:z ^ k:]:]" for z::complex and k::nat
   by (induction k) (simp_all add: one_pCons)
 show ?thesis
   by (simp only: eval_quad power_mult_distrib constant_power power_mult[symmetric]; simp add: mult_ac)
qed

end
