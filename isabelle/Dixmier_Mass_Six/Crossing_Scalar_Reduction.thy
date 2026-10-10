theory Crossing_Scalar_Reduction
 imports "GGV_Inputs"
   "Small_Companion_Support"
   "Crossing_Poisson_Scalar"
   "Homogeneous_Power_Endpoints"
begin

lemma crossing_homogeneous_companion_scalar:
 fixes R F::"complex bivariate" and rho s::nat and m::int
 assumes s: "0 < s" and direction: "s < rho" and primitive: "coprime rho s" and R: "R\<noteq>0"
 and Rhom: "weighted_homogeneous(int rho)( - int s)m R"
 and Fhom: "weighted_homogeneous(int rho)( - int s)(int rho - int s) F"
 and bracket: "biv_poisson R F = R"
 shows "\<exists>a b::nat. \<exists>c::complex. \<exists>p f::complex poly.
 c\<noteq>0 \<and> coeff p 0 = 1 \<and>
 (\<forall>e\<in>biv_support R. \<exists>k::nat. e = (a + s * k,b + rho * k)) \<and>
 R = biv_monom c 0 0 * (biv_monom 1 a b * biv_univariate_eval p(biv_monom 1 s rho)) \<and>
 F = biv_monom 1 1 1 * biv_univariate_eval f(biv_monom 1 s rho) \<and>
 [:of_nat rho - of_nat s:] * [:0,1:] * f * pderiv p - 
 (([:of_nat a - of_nat b:] * f + [:of_nat rho * of_nat a - of_nat s * of_nat b:] * [:0,1:] * pderiv f + 1) * p) = 0"
proof -
 have homogeneous: "\<And>e. e\<in>biv_support R \<Longrightarrow> pair_weight(int rho)( - int s)e = m"
  using Rhom unfolding weighted_homogeneous_def by blast
 obtain a b c p where c: "c\<noteq>0" and p0: "coeff p 0 = 1"
 and ray: "\<forall>e\<in>biv_support R. \<exists>k::nat. e = (a + s * k,b + rho * k)"
 and Rshape: "R = biv_monom c 0 0 * (biv_monom 1 a b * biv_univariate_eval p(biv_monom 1 s rho))"
 using crossing_base_normalized_shape[OF s direction primitive R homogeneous] by blast
 obtain f where Fshape: "F = biv_monom 1 1 1 * biv_univariate_eval f(biv_monom 1 s rho)"
  using companion_homogeneous_shape[OF s direction primitive Fhom] by blast
 have Rconst: "R = [:[:c:]:] * (biv_monom 1 a b * biv_univariate_eval p(biv_monom 1 s rho))"
  using Rshape by (simp only: biv_monom_def monom_0)
 have scaled: "[:[:c:]:] * biv_poisson(biv_monom 1 a b * biv_univariate_eval p(biv_monom 1 s rho)) F = 
 [:[:c:]:] * (biv_monom 1 a b * biv_univariate_eval p(biv_monom 1 s rho))"
  using bracket by (simp only: Rconst biv_poisson_const_left)
 have constant_nz: "([:[:c:]:]::complex bivariate)\<noteq>0" using c by simp
 have unscaled: "biv_poisson(biv_monom 1 a b * biv_univariate_eval p(biv_monom 1 s rho)) F = 
   biv_monom 1 a b * biv_univariate_eval p(biv_monom 1 s rho)"
   using scaled by (simp only: mult_left_cancel[OF constant_nz])
 have normalized: "biv_poisson(biv_monom 1 a b * biv_univariate_eval p(biv_monom 1 s rho))
 (biv_monom 1 1 1 * biv_univariate_eval f(biv_monom 1 s rho)) = biv_monom 1 a b * biv_univariate_eval p(biv_monom 1 s rho)"
  using unscaled by (simp only: Fshape)
 have rho: "0 < rho" using s direction by arith
 have scalar: "[:of_nat rho - of_nat s:] * [:0,1:] * f * pderiv p - 
 (([:of_nat a - of_nat b:] * f + [:of_nat rho * of_nat a - of_nat s * of_nat b:] * [:0,1:] * pderiv f + 1) * p) = 0"
  by (rule crossing_poisson_implies_scalar[OF rho normalized])
 show ?thesis using c p0 ray Rshape Fshape scalar by blast
qed

lemma crossing_ray_nonpos_of_base_le:
 assumes direction: "s < rho" and base: "a\<le>b"
 and ray: "\<forall>e\<in>biv_support(R::complex bivariate). \<exists>k::nat. e = (a + s * k,b + rho * k)"
 shows "\<forall>e\<in>biv_support R. pair_grade e\<le>0"
proof (intro ballI)
 fix e assume "e\<in>biv_support R"
 then obtain k where shape: "e = (a + s * k,b + rho * k)" using ray by blast
 have product: "s * k\<le>rho * k" by (rule mult_le_mono1) (use direction in arith)
 have natural_bound: "a + s * k\<le>b + rho * k" using product base by arith
 have integer_bound: "int(a + s * k)\<le>int(b + rho * k)"
   using natural_bound by (simp only: of_nat_le_iff)
 show "pair_grade e\<le>0"
   using integer_bound by (simp only: shape pair_grade_def fst_conv snd_conv; arith)
qed

lemma support_grade_nonpos_pow:
 fixes R::"complex bivariate"
 assumes nonpositive: "\<forall>e\<in>biv_support R. pair_grade e\<le>0"
 shows "\<forall>e\<in>biv_support(R ^ k). pair_grade e\<le>0"
proof -
 have bound: "\<And>e. e\<in>biv_support R \<Longrightarrow> pair_weight 1 ( - 1)e\<le>0"
  using nonpositive by (simp add: pair_weight_def pair_grade_def)
 have power: "\<And>e. e\<in>biv_support(R ^ k) \<Longrightarrow> pair_weight 1 ( - 1)e\<le>int k * 0"
  by (rule corner_support_weight_power[OF bound])
 show ?thesis using power by (simp add: pair_weight_def pair_grade_def)
qed

lemma crossing_base_a_gt_b_of_strict_face:
 fixes P::"complex poly_operator" and R::"complex bivariate" and mu::complex
 assumes mu: "mu\<noteq>0" and direction: "s < rho"
 and ray: "\<forall>e\<in>biv_support R. \<exists>k::nat. e = (a + s * k,b + rho * k)"
 and face: "leading_form(int rho)( - int s) P = [:[:mu:]:] * R ^ k"
 and crossing: "strict_crossing(int rho)( - int s) P"
 shows "b < a"
proof (rule ccontr)
 assume "\<not>b < a"
 then have base: "a\<le>b" by arith
 have nonpositive: "\<forall>e\<in>biv_support R. pair_grade e\<le>0" by (rule crossing_ray_nonpos_of_base_le[OF direction base ray])
 have powers: "\<forall>e\<in>biv_support(R ^ k). pair_grade e\<le>0" by (rule support_grade_nonpos_pow[OF nonpositive])
 obtain e where occupied: "e\<in>biv_support(leading_form(int rho)( - int s) P)" and positive: "0 < pair_grade e"
  using crossing unfolding strict_crossing_def by blast
 have member: "e\<in>biv_support(R ^ k)" using occupied mu by (auto simp: face biv_support_def biv_coeff_def)
 have bound: "pair_grade e\<le>0" by (rule bspec[OF powers member])
 show False using bound positive by arith
qed

lemma monomial_power_face_support_one:
 fixes mu::complex
 assumes mu: "mu\<noteq>0"
 shows "card(biv_support([:[:mu:]:] * (biv_monom 1 a b) ^ k)) = 1"
proof -
 have shape: "[:[:mu:]:] * (biv_monom 1 a b) ^ k = biv_monom mu (k * a)(k * b)"
  by (simp only: corner_biv_monom_power power_one)
    (simp add: biv_monom_def monom_0 mult_monom smult_monom)
 have support: "biv_support([:[:mu:]:] * (biv_monom 1 a b) ^ k) = {(k * a,k * b)}"
   by (simp only: shape weighted_support_monom[OF mu])
 show ?thesis by (simp only: support; simp)
qed

lemma strictCounterexample_crossing_scalar_of_GGV:
 fixes P Q::"complex poly_operator" and rho s::nat
 assumes inputs: GGVInputs and pair: "is_counterexample_pair P Q"
 and s: "0 < s" and direction: "s < rho" and primitive: "coprime rho s"
 and dir: "is_direction(int rho)( - int s)" and crossing: "strict_crossing(int rho)( - int s) P"
 shows "\<exists>mu::complex. \<exists>k a b::nat. \<exists>p f::complex poly.
 mu\<noteq>0 \<and> 2\<le>k \<and> b < a \<and> coeff p 0 = 1 \<and> 0 < degree p \<and>
 leading_form(int rho)( - int s) P = [:[:mu:]:] * (biv_monom 1 a b * biv_univariate_eval p(biv_monom 1 s rho)) ^ k \<and>
 [:of_nat rho - of_nat s:] * [:0,1:] * f * pderiv p - 
 (([:of_nat a - of_nat b:] * f + [:of_nat rho * of_nat a - of_nat s * of_nat b:] * [:0,1:] * pderiv f + 1) * p) = 0"
proof -
 have companion: GGVCompanionInput using inputs unfolding GGVInputs_def by blast
 note input_all = companion[unfolded GGVCompanionInput_def]
 note input_pair = mp[OF spec[OF spec[OF input_all, of P], of Q] pair]
 note input_direction = mp[OF spec[OF spec[OF input_pair, of "int rho"], of " - int s"] dir]
 obtain mu0 k R F m where mu0: "mu0\<noteq>0" and k: "2\<le>k" and R: "R\<noteq>0"
 and Rhom: "weighted_homogeneous(int rho)( - int s)m R"
 and Fhom: "weighted_homogeneous(int rho)( - int s)(int rho - int s)F"
 and face: "leading_form(int rho)( - int s)P = [:[:mu0:]:] * R ^ k" and bracket: "biv_poisson R F = R"
 using input_direction by (simp only: add_uminus_conv_diff; blast)
 obtain a b c p f where c: "c\<noteq>0" and p0: "coeff p 0 = 1"
 and ray: "\<forall>e\<in>biv_support R. \<exists>k::nat. e = (a + s * k,b + rho * k)"
 and shape: "R = biv_monom c 0 0 * (biv_monom 1 a b * biv_univariate_eval p(biv_monom 1 s rho))"
 and scalar: "[:of_nat rho - of_nat s:] * [:0,1:] * f * pderiv p - 
 (([:of_nat a - of_nat b:] * f + [:of_nat rho * of_nat a - of_nat s * of_nat b:] * [:0,1:] * pderiv f + 1) * p) = 0"
 using crossing_homogeneous_companion_scalar[OF s direction primitive R Rhom Fhom bracket] by blast
 have base: "b < a" by (rule crossing_base_a_gt_b_of_strict_face[OF mu0 direction ray face crossing])
 have mu: "mu0 * c ^ k\<noteq>0" using mu0 c by simp
 have newface: "leading_form(int rho)( - int s)P = [:[:mu0 * c ^ k:]:] * (biv_monom 1 a b * biv_univariate_eval p(biv_monom 1 s rho)) ^ k"
 proof -
   let ?A="biv_monom 1 a b * biv_univariate_eval p(biv_monom 1 s rho)"
   have cpower: "(biv_monom c 0 0::complex bivariate) ^ k = biv_monom(c ^ k)0 0"
     by (simp only: corner_biv_monom_power mult_0_right)
   have combine: "[:[:mu0:]:] * (biv_monom(c ^ k)0 0::complex bivariate) = [:[:mu0 * c ^ k:]:]"
     by (simp add: biv_monom_def monom_0 mult_monom smult_monom)
   have "leading_form(int rho)( - int s)P = [:[:mu0:]:] * (biv_monom c 0 0 * ?A) ^ k"
     by (simp only: face shape)
   also have "... = ([:[:mu0:]:] * biv_monom(c ^ k)0 0) * ?A ^ k"
     by (simp only: power_mult_distrib cpower mult.assoc)
   also have "... = [:[:mu0 * c ^ k:]:] * ?A ^ k" by (simp only: combine)
   finally show ?thesis .
 qed
 have positive: "0 < degree p"
 proof (rule ccontr)
  assume "\<not>0 < degree p"
  then have degree: "degree p = 0" by arith
  obtain z where constant_poly: "p = [:z:]" using degree by (elim degree_eq_zeroE)
  have p: "p = 1" using p0 constant_poly by (simp add: one_pCons)
  have eval_one: "biv_univariate_eval (1::complex poly) (biv_monom 1 s rho) = 1"
    by (simp add: biv_univariate_eval_def one_pCons map_poly_pCons map_poly_0 poly_pCons)
  have monomial: "leading_form(int rho)( - int s)P = [:[:mu0 * c ^ k:]:] * (biv_monom 1 a b) ^ k"
    using newface by (simp only: p eval_one mult_1_right)
  have cardinality: "card(biv_support(leading_form(int rho)( - int s)P)) = 1"
   by (simp only: monomial; rule monomial_power_face_support_one[OF mu])
  have "1 < card(biv_support(leading_form(int rho)( - int s)P))"
   using crossing unfolding strict_crossing_def in_direction_def by blast
  then show False using cardinality by arith
 qed
 show ?thesis by (intro exI[of _ "mu0 * c ^ k"] exI[of _ k] exI[of _ a] exI[of _ b] exI[of _ p] exI[of _ f])
  (use mu k base p0 positive newface scalar in blast)
qed

end
