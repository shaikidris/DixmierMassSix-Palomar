theory Negative_Crossing
 imports "Crossing_Scalar_Reduction"
   "Crossing_Mass_Six"
   "Crossing_Term_Count"
   "Scalar_Classification"
   "Pure_Power_Face_Exclusion"
begin

lemma negativeCrossingExclusion_of_GGV:
 fixes P Q::"complex poly_operator" and rho s::nat
 assumes inputs: GGVInputs and pair: "is_counterexample_pair P Q"
 and mass: "weyl_mass P\<le>6" and s: "1\<le>s" and direction: "s<rho" and primitive: "coprime rho s"
 shows "\<not>strict_crossing(int rho)(-int s)P"
proof
 assume crossing: "strict_crossing(int rho)(-int s)P"
 have spos: "0<s" using s by arith
 have dir: "is_direction(int rho)(-int s)"
  using primitive direction unfolding is_direction_def coprime_iff_gcd_eq_1 by simp
 obtain mu k a b r f where mu: "mu\<noteq>0" and k: "2\<le>k" and base: "b<a" and r0: "coeff r 0=1" and r: "0<degree r"
 and face: "leading_form(int rho)(-int s)P=[:[:mu:]:]*(biv_monom 1 a b*biv_univariate_eval r(biv_monom 1 s rho))^k"
 and scalar: "[:of_nat rho- of_nat s:]*[:0,1:]*f*pderiv r-
 (([:of_nat a- of_nat b:]*f+[:of_nat rho* of_nat a- of_nat s* of_nat b:]*[:0,1:]*pderiv f+1)*r)=0"
  using strictCounterexample_crossing_scalar_of_GGV[OF inputs pair spos direction primitive dir crossing] by blast
 have P: "P\<in>weyl_algebra" using pair unfolding is_counterexample_pair_def by blast
 have terms: "termCount(r^k)\<le>6"
  using crossingFace_general_termCount_le_mass[OF P mu direction face] mass by arith
 have parameters: "k=2 \<and> a=1 \<and> b=0"
  using crossing_mass_six_parameters_of_scalar[OF spos direction base k r0 r scalar terms] by blast
 have comp: "Comp rho s r f" using scalar parameters unfolding Comp_def by simp
 have zero: "poly r 0=1" using r0 by (simp only: poly_0_coeff_0)
 have square_terms: "termCount(r^2)\<le>6" using terms parameters by simp
 obtain lam where lam: "lam\<noteq>0" and rform: "r=(1-[:lam:]*[:0,1:])^2" and rho: "rho=2*s+1"
  using Comp_classification[OF comp s direction r zero square_terms] by blast
 have parameter: "(2-1)*rho=2*s+1" using rho by simp
 have face': "leading_form(int rho)(-int s)P=[:[:mu:]:]*(biv_monom 1 1 0)^2*
 (1+[:[:-lam:]:]*(biv_monom 1 1 0)^s*(biv_monom 1 0 1)^rho)^(2*2)"
 proof -
  let ?W="biv_monom (1::complex) s rho"
  have input: "1-[:lam:]*[:0,1:]=[:1,-lam:]"
   by (simp add: one_pCons diff_pCons)
  have scalar_constant: "biv_monom c 0 0=[:[:c:]:]" for c::complex
   by (simp add: biv_monom_def monom_0)
  have linear: "biv_univariate_eval (1-[:lam:]*[:0,1:]) ?W=1+[:[:-lam:]:]*?W"
  proof -
   have evaluated: "biv_univariate_eval [:1,-lam:] ?W=1+?W*[:[:-lam:]:]"
    by (simp only: biv_univariate_eval_pCons biv_univariate_eval_zero scalar_constant
      mult_zero_right add_0_right one_pCons[symmetric])
   have transported: "biv_univariate_eval (1-[:lam:]*[:0,1:]) ?W=1+?W*[:[:-lam:]:]"
    by (subst input) (rule evaluated)
   show ?thesis by (rule trans[OF transported]) (simp only: mult.commute)
  qed
  have evaluation: "biv_univariate_eval r ?W=(1+[:[:-lam:]:]*?W)^2"
   by (simp only: rform coefficient_hom_power[OF biv_univariate_eval_hom] linear)
  have Wfactor: "?W=(biv_monom 1 1 0)^s*(biv_monom 1 0 1)^rho"
   by (subst biv_monom_factor) (simp add: biv_monom_def monom_0 pCons_one smult_1_left)
  have k2: "k=2" and a1: "a=1" and b0: "b=0" using parameters by blast+
  have normalized: "leading_form(int rho)(-int s)P=[:[:mu:]:]*(biv_monom 1 1 0*((1+[:[:-lam:]:]*?W)^2))^2"
   using face by (simp only: k2 a1 b0 evaluation)
  show ?thesis
   by (rule trans[OF normalized]; simp only: Wfactor power_mult_distrib power_mult[symmetric];
     simp add: mult.assoc)
 qed
 have forbidden: "leading_form(int rho)(-int s)P\<noteq>[:[:mu:]:]*(biv_monom 1 1 0)^2*
 (1+[:[:-lam:]:]*(biv_monom 1 1 0)^s*(biv_monom 1 0 1)^rho)^(2*2)"
 proof -
  have X: "(biv_monom 1 1 0::complex bivariate)=[:[:0,1:]:]"
   by (simp add: biv_monom_def monom_altdef)
  have Y: "(biv_monom 1 0 1::complex bivariate)=[:0,1:]"
   by (simp add: biv_monom_def monom_altdef pCons_one)
  have two: "2\<le>(2::nat)" and prime: "prime(2::nat)" by simp_all
  have alpha: "-lam\<noteq>0" using lam by simp
  show ?thesis using purePowerFaceExclusion_of_GGV[OF inputs two parameter prime alpha mu pair]
   by (simp only: X Y not_False_eq_True)
 qed
 show False using forbidden face' by blast
qed

end
