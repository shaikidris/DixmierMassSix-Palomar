theory Diagonal_Factor_Dispatch
 imports "Diagonal_Binomial_Face"
   "Positive_Singleton_Case_Dispatch"
   "Horizontal_Last_Zero_Exclusion"
begin

lemma preliminary_diagonal_first_point_horizontal_endpoint:
 fixes P Q::"complex poly_operator" and a b::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and a: "0<a" and member: "(a,b)\<in>biv_support(leading_form 1 1 P)"
   and first: "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> fst e\<le>a"
 shows "(a,b)\<in>biv_support(leading_form 1 0 P) \<and>
   (\<forall>e\<in>biv_support(leading_form 1 0 P). snd e\<le>b)"
proof -
 have bound: "\<forall>e\<in>biv_support(pbw_symbol P). fst e\<le>a"
   by (rule preliminary_diagonal_first_point_x_bound[OF source pair a member first])
 have raw: "(a,b)\<in>biv_support(pbw_symbol P)"
   using member by (simp add: leading_form_def weighted_component_support)
 have maximal: "\<forall>e\<in>biv_support(pbw_symbol P). rationalNewtonWeight 0 e\<le>rationalNewtonWeight 0 (a,b)"
   using bound by (simp add: rationalNewtonWeight_def)
 have horizontal: "(a,b)\<in>biv_support(leading_form 1 0 P)"
   by (simp only: leadingForm_mem_iff_rational_slope[where P=P and rho=1 and sigma=0, OF zero_less_one];
     simp only: of_int_0 of_int_1 div_0; rule conjI[OF raw maximal])
 have total: "a+b=total_degree P" using diagonal_face_point_total_degree[OF member] by simp
 have last: "snd e\<le>b" if e: "e\<in>biv_support(leading_form 1 0 P)" for e
 proof -
   have face_data: "e\<in>biv_support(pbw_symbol P) \<and>
     (\<forall>d\<in>biv_support(pbw_symbol P). rationalNewtonWeight 0 d\<le>rationalNewtonWeight 0 e)"
     using iffD1[OF leadingForm_mem_iff_rational_slope[where P=P and rho=1 and sigma=0 and a=e, OF zero_less_one] e]
     by (simp only: of_int_0 of_int_1 div_0; blast)
   have eraw: "e\<in>biv_support(pbw_symbol P)" by (rule conjunct1[OF face_data])
   have emax: "\<forall>d\<in>biv_support(pbw_symbol P). rationalNewtonWeight 0 d\<le>rationalNewtonWeight 0 e"
     by (rule conjunct2[OF face_data])
   have at_corner: "rationalNewtonWeight 0 (a,b)\<le>rationalNewtonWeight 0 e"
     by (rule bspec[OF emax raw])
   have lower: "a\<le>fst e" using at_corner by (simp add: rationalNewtonWeight_def)
   have upper: "fst e\<le>a" using bound eraw by blast
   have equal: "fst e=a" using lower upper by arith
   have degree: "fst e+snd e\<le>a+b" using support_total_degree_bound[OF eraw] total by simp
   show ?thesis using degree equal by arith
 qed
 show ?thesis using horizontal last by blast
qed

lemma preliminary_diagonal_first_point_grade_ne_zero:
 fixes P Q::"complex poly_operator" and a b::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and a: "0<a" and member: "(a,b)\<in>biv_support(leading_form 1 1 P)"
   and first: "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> fst e\<le>a"
 shows "pair_grade(a,b)\<noteq>0"
proof -
 have h: "(a,b)\<in>biv_support(leading_form 1 0 P)" and last:
   "\<And>e. e\<in>biv_support(leading_form 1 0 P) \<Longrightarrow> snd e\<le>snd(a,b)"
   using preliminary_diagonal_first_point_horizontal_endpoint[OF source pair a member first] by auto
 show ?thesis by (rule preliminary_horizontal_max_y_grade_ne_zero[OF source pair h last])
qed

lemma preliminary_diagonal_negative_first_point_caseAlternative:
 fixes P Q::"complex poly_operator" and a b::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and a: "0<a" and negative: "a<b" and member: "(a,b)\<in>biv_support(leading_form 1 1 P)"
   and first: "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> fst e\<le>a"
 shows "case_alternative P"
proof -
 have horizontal: "(a,b)\<in>biv_support(leading_form 1 0 P)"
   using preliminary_diagonal_first_point_horizontal_endpoint[OF source pair a member first] by blast
 have grade: "pair_grade(a,b)<0" using negative by (simp add: pair_grade_def)
 show ?thesis by (rule preliminary_horizontal_negative_point_caseAlternative[OF source pair]) (use horizontal grade in blast)
qed

lemma diagonal_y_factor_caseAlternative:
 fixes P Q::"complex poly_operator" and b k::nat and lam alpha::complex
 assumes bound: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 16\<le>total_degree R"
   and pair: "is_counterexample_pair P Q" and less: "b<k" and lam: "lam\<noteq>0" and alpha: "alpha\<noteq>0"
   and shape: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 0 1)^b*
     (biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^k"
 shows "case_alternative P"
proof -
 have mass: "10\<le>weyl_mass P" by (rule diagonal_y_factor_mass_ge_ten[OF bound pair less lam alpha shape])
 have carrier: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have linear: "poly_linear P" by (rule weyl_linear[OF carrier])
 show ?thesis using mass linear by (simp add: case_alternative_def)
qed

lemma preliminary_diagonal_y_factor_complete_caseAlternative:
 fixes P Q::"complex poly_operator" and b k::nat and lam alpha::complex
 assumes source: "GGVPreliminaryCompanionInput"
   and bound: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 16\<le>total_degree R"
   and pair: "is_counterexample_pair P Q" and k: "1\<le>k" and lam: "lam\<noteq>0" and alpha: "alpha\<noteq>0"
   and shape: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 0 1)^b*
     (biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^k"
 shows "case_alternative P"
proof (cases "b<k")
 case True show ?thesis by (rule diagonal_y_factor_caseAlternative[OF bound pair True lam alpha shape])
next
 case False
 have member: "(k,b)\<in>biv_support(leading_form 1 1 P)" and first:
   "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> fst e\<le>k"
   using diagonal_y_factor_first_face_point[OF lam alpha shape] by blast+
 have kp: "0<k" using k by arith
 have nonzero: "pair_grade(k,b)\<noteq>0"
   by (rule preliminary_diagonal_first_point_grade_ne_zero[OF source pair kp member first])
 have negative: "k<b" using False nonzero by (simp add: pair_grade_def; arith)
 show ?thesis by (rule preliminary_diagonal_negative_first_point_caseAlternative[OF source pair kp negative member first])
qed

lemma preliminary_diagonal_x_factor_complete_caseSplit:
 fixes P Q::"complex poly_operator" and a k::nat and lam alpha::complex
 assumes source: "GGVPreliminaryCompanionInput"
   and bound: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 16\<le>total_degree R"
   and pair: "is_counterexample_pair P Q" and k: "1\<le>k" and lam: "lam\<noteq>0" and alpha: "alpha\<noteq>0"
   and shape: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
     (biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^k"
 shows "case_alternative P \<or> case_alternative (fourier_alg_hom P)"
proof (cases "a<k")
 case True
 have mass: "10\<le>weyl_mass P" by (rule diagonal_x_factor_mass_ge_ten[OF bound pair True lam alpha shape])
 have carrier: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have linear: "poly_linear P" by (rule weyl_linear[OF carrier])
 show ?thesis using mass linear by (simp add: case_alternative_def)
next
 case False
 have carrier: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have weight: "v_degree 1 1 P=int(a+k)" by (rule diagonal_x_factor_vDeg[OF lam shape])
 have member: "(a,k)\<in>biv_support(leading_form 1 1 P)" and last:
   "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> snd e\<le>k"
   using positive_binomial_top_face_point[where P=P and sigma=1 and a=a and k=k and lam=lam and alpha=alpha]
     lam weight shape by simp_all
 have fm: "(k,a)\<in>biv_support(leading_form 1 1 (fourier_alg_hom P))"
   using fourier_diagonal_point_mem[OF carrier member] by simp
 have first: "fst e\<le>k" if "e\<in>biv_support(leading_form 1 1 (fourier_alg_hom P))" for e
   using last[OF fourier_diagonal_point_preimage[OF carrier that]] by simp
 have fp: "is_counterexample_pair (fourier_alg_hom P) (fourier_alg_hom Q)"
   by (rule isCounterexamplePair_fourier[OF pair])
 have kp: "0<k" using k by arith
 have nonzero: "pair_grade(k,a)\<noteq>0"
   by (rule preliminary_diagonal_first_point_grade_ne_zero[OF source fp kp fm first])
 have negative: "k<a" using nonzero False by (simp add: pair_grade_def; arith)
 have alternative: "case_alternative (fourier_alg_hom P)"
   by (rule preliminary_diagonal_negative_first_point_caseAlternative[OF source fp kp negative fm first])
 show ?thesis using alternative by blast
qed
end
