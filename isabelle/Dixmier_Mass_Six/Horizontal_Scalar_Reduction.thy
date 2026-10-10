theory Horizontal_Scalar_Reduction
 imports "GGV_Inputs"
   "Crossing_Poisson_Scalar"
begin

lemma horizontal_Y_substitution:
 "biv_univariate_eval(g::complex poly)(biv_monom 1 0 1) = map_poly (\<lambda>c. [:c:])g"
proof -
 have Y: "(biv_monom 1 0 1::complex bivariate) = [:0,1:]"
   by (simp add: biv_monom_def monom_altdef one_pCons)
 have constant_monom: "(biv_monom c 0 0::complex bivariate) = [:[:c:]:]" for c
   by (simp only: biv_monom_def monom_0)
 show ?thesis
 proof (induction g)
   case 0 show ?case by simp
 next
   case (pCons a g)
   have mapped: "map_poly (\<lambda>c::complex. [:c:]) (pCons a g) = 
     pCons [:a:] (map_poly (\<lambda>c. [:c:]) g)"
     by (simp add: map_poly_pCons)
   have induction_Y: "biv_univariate_eval g [:0,1:] = map_poly (\<lambda>c. [:c:]) g"
     using pCons.IH by (simp only: Y)
   have evaluated: "biv_univariate_eval (pCons a g) (biv_monom 1 0 1) = 
     [:[:a:]:] + [:0,1:] * map_poly (\<lambda>c. [:c:]) g"
     by (simp only: biv_univariate_eval_pCons constant_monom Y induction_Y)
   show ?case
     by (simp only: evaluated mapped;
       simp add: mult_pCons_left crossing_inner_unit smult_1_left add_pCons)
 qed
qed

lemma horizontal_base_coeff_general:
 "biv_coeff(biv_monom 1 a 0 * biv_univariate_eval(g::complex poly)(biv_monom 1 0 1)) i j = 
 (if i = a then coeff g j else 0)"
 by (simp only: horizontal_Y_substitution; simp add: biv_monom_def coeff_monom_mult coeff_map_poly biv_coeff_def coeff_pCons split: if_splits)

lemma horizontal_homogeneous_shape:
 fixes F::"complex bivariate" and a::nat
 assumes homogeneous: "weighted_homogeneous 1 0 (int a) F"
 shows "\<exists>g::complex poly. F = biv_monom 1 a 0 * biv_univariate_eval g(biv_monom 1 0 1)"
proof -
 let ?g="map_poly (\<lambda>q. coeff q a) F"
 have shape: "F = biv_monom 1 a 0 * biv_univariate_eval ?g(biv_monom 1 0 1)"
 proof (rule biv_eqI)
  fix i j
  have zero: "i\<noteq>a \<Longrightarrow> biv_coeff F i j = 0"
  proof -
   assume other: "i\<noteq>a"
   have "(i,j)\<notin>biv_support F"
    using homogeneous other by (auto simp: weighted_homogeneous_def pair_weight_def)
   then show "biv_coeff F i j = 0" by (simp add: biv_support_def)
  qed
  show "biv_coeff F i j = biv_coeff(biv_monom 1 a 0 * biv_univariate_eval ?g(biv_monom 1 0 1)) i j"
   using zero by (simp only: horizontal_base_coeff_general; cases "i = a"; simp add: coeff_map_poly biv_coeff_def)
 qed
 show ?thesis using shape by blast
qed

lemma horizontal_nonzero_homogeneous_shape:
 fixes R::"complex bivariate" and m::int
 assumes nonzero: "R\<noteq>0" and homogeneous: "weighted_homogeneous 1 0 m R"
 shows "\<exists>a::nat. \<exists>g::complex poly. m = int a \<and> g\<noteq>0 \<and>
 R = biv_monom 1 a 0 * biv_univariate_eval g(biv_monom 1 0 1)"
proof -
 have nonempty: "biv_support R\<noteq>{}" using nonzero by (simp only: biv_support_empty_iff not_False_eq_True)
 obtain e where e: "e\<in>biv_support R" using nonempty by blast
 have m: "m = int(fst e)" using homogeneous e by (simp add: weighted_homogeneous_def pair_weight_def)
 have hom: "weighted_homogeneous 1 0 (int(fst e))R" by (simp only: m[symmetric]; rule homogeneous)
 obtain g where shape: "R = biv_monom 1 (fst e)0 * biv_univariate_eval g(biv_monom 1 0 1)"
  using horizontal_homogeneous_shape[OF hom] by blast
 have g: "g\<noteq>0" using nonzero shape by auto
 show ?thesis using m shape g by blast
qed

lemma horizontal_poisson_formula:
 fixes g f::"complex poly" and a::nat
 shows "biv_poisson(biv_monom 1 a 0 * biv_univariate_eval g(biv_monom 1 0 1))
 (biv_monom 1 1 0 * biv_univariate_eval f(biv_monom 1 0 1)) = 
 biv_monom 1 a 0 * biv_univariate_eval(f * pderiv g - [:of_nat a:] * g * pderiv f)(biv_monom 1 0 1)"
proof -
 let ?X="biv_monom 1 1 0::complex bivariate" let ?Y="biv_monom 1 0 1::complex bivariate"
 let ?A="biv_monom 1 a 0::complex bivariate"
 let ?U="biv_univariate_eval g ?Y" let ?V="biv_univariate_eval f ?Y"
 let ?U'="biv_univariate_eval(pderiv g)?Y" let ?V'="biv_univariate_eval(pderiv f)?Y"
 have rx: "?X * biv_dx(?A * ?U) = ?A * (biv_monom(of_nat a)0 0 * ?U)"
  using euler_crossing_x[of a 0 g 0 1] by simp
 have ry: "?Y * biv_dy(?A * ?U) = ?A * (?Y * ?U')"
  using euler_crossing_y[of a 0 g 0 1]
  by (simp add: biv_monom_def monom_0 one_pCons smult_1_left; simp only: crossing_inner_unit smult_1_left)
 have fx: "?X * biv_dx(?X * ?V) = ?X * ?V"
  using euler_crossing_x[of 1 0 f 0 1]
  by (simp add: biv_monom_def monom_0 one_pCons smult_1_left; simp only: crossing_inner_unit smult_1_left)
 have fy: "?Y * biv_dy(?X * ?V) = ?X * (?Y * ?V')"
  using euler_crossing_y[of 1 0 f 0 1]
  by (simp add: biv_monom_def monom_0 one_pCons smult_1_left; simp only: crossing_inner_unit smult_1_left)
 have evaluated: "biv_univariate_eval(f * pderiv g - [:of_nat a:] * g * pderiv f)?Y = 
 ?V * ?U' - biv_monom(of_nat a)0 0 * ?U * ?V'"
  by (simp add: biv_univariate_eval_diff biv_univariate_eval_mult biv_univariate_eval_smult mult.assoc)
 have scaled: "(?X * ?Y) * biv_poisson(?A * ?U)(?X * ?V) = 
 (?X * ?Y) * (?A * biv_univariate_eval(f * pderiv g - [:of_nat a:] * g * pderiv f)?Y)"
  by (simp only: xy_mul_poisson rx ry fx fy evaluated) (simp add: algebra_simps)
 show ?thesis using scaled by simp
qed

lemma horizontal_poisson_implies_scalar:
 fixes g f::"complex poly" and a::nat
 assumes bracket: "biv_poisson(biv_monom 1 a 0 * biv_univariate_eval g(biv_monom 1 0 1))
 (biv_monom 1 1 0 * biv_univariate_eval f(biv_monom 1 0 1)) = biv_monom 1 a 0 * biv_univariate_eval g(biv_monom 1 0 1)"
 shows "f * pderiv g - [:of_nat a:] * pderiv f * g = g"
proof -
 have equal: "biv_univariate_eval(f * pderiv g - [:of_nat a:] * g * pderiv f)(biv_monom 1 0 1) = biv_univariate_eval g(biv_monom 1 0 1)"
 proof -
   have expanded: "biv_monom 1 a 0 * biv_univariate_eval(f * pderiv g - [:of_nat a:] * g * pderiv f)(biv_monom 1 0 1) = 
     biv_monom 1 a 0 * biv_univariate_eval g(biv_monom 1 0 1)"
     using bracket by (simp only: horizontal_poisson_formula)
   have nonzero_monom: "(biv_monom 1 a 0::complex bivariate)\<noteq>0" by simp
   show ?thesis using expanded by (simp only: mult_left_cancel[OF nonzero_monom])
 qed
 have "f * pderiv g - [:of_nat a:] * g * pderiv f = g"
  by (rule crossing_substitution_injective[OF zero_less_one equal])
 then show ?thesis by (simp add: mult_ac)
qed

lemma horizontal_counterexample_scalar_of_GGV:
 fixes P Q::"complex poly_operator"
 assumes inputs: GGVInputs and pair: "is_counterexample_pair P Q"
 shows "\<exists>mu::complex. \<exists>k a::nat. \<exists>g f::complex poly.
 mu\<noteq>0 \<and> 2\<le>k \<and> g\<noteq>0 \<and>
 leading_form 1 0 P = [:[:mu:]:] * (biv_monom 1 a 0 * biv_univariate_eval g(biv_monom 1 0 1)) ^ k \<and>
 f * pderiv g - [:of_nat a:] * pderiv f * g = g"
proof -
 have companion: GGVCompanionInput using inputs unfolding GGVInputs_def by blast
 have dir: "is_direction 1 0" by (simp add: is_direction_def)
 note input_all = companion[unfolded GGVCompanionInput_def]
 note input_pair = mp[OF spec[OF spec[OF input_all, of P], of Q] pair]
 note input_direction = mp[OF spec[OF spec[OF input_pair, of "1::int"], of "0::int"] dir]
 obtain mu k R F m where mu: "mu\<noteq>0" and k: "2\<le>k" and R: "R\<noteq>0"
 and Rhom: "weighted_homogeneous 1 0 m R" and Fhom: "weighted_homogeneous 1 0 1 F"
 and face: "leading_form 1 0 P = [:[:mu:]:] * R ^ k" and bracket: "biv_poisson R F = R"
 using input_direction by (simp only: add_0_right; blast)
 obtain a g where g: "g\<noteq>0" and Rshape: "R = biv_monom 1 a 0 * biv_univariate_eval g(biv_monom 1 0 1)"
  using horizontal_nonzero_homogeneous_shape[OF R Rhom] by blast
 have Fhom_cast: "weighted_homogeneous 1 0 (int 1) F" using Fhom by simp
 obtain f where Fshape: "F = biv_monom 1 1 0 * biv_univariate_eval f(biv_monom 1 0 1)"
   using horizontal_homogeneous_shape[where a=1, OF Fhom_cast] by blast
 have scalar: "f * pderiv g - [:of_nat a:] * pderiv f * g = g"
  by (rule horizontal_poisson_implies_scalar) (use bracket in \<open>simp only: Rshape Fshape\<close>)
 show ?thesis using mu k g face Rshape scalar by blast
qed

end
