theory Universal_Diagonal_Case_Map
 imports "Diagonal_Factor_Dispatch"
   "GGV_Diagonal_Root_Budget"
   "Y_Axis_Positive_Horizontal_Mass"
begin

text \<open>Source composition using the imported positive-axis producer. This
file introduces no replacement premise for that producer.\<close>

lemma preliminary_y_axis_diagonal_caseAlternative:
 fixes P Q::"complex poly_operator" and n::nat
 assumes source: "GGVPreliminaryCompanionInput"
   and bound: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 16\<le>total_degree R"
   and pair: "is_counterexample_pair P Q" and degree: "total_degree P=n"
   and unique: "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> e=(0,n)"
   and nozero: "\<And>e. e\<in>biv_support(leading_form 1 0 P) \<Longrightarrow>
     (\<And>d. d\<in>biv_support(leading_form 1 0 P) \<Longrightarrow> snd d\<le>snd e) \<Longrightarrow> pair_grade e\<noteq>0"
 shows "case_alternative P"
proof -
 have direction: "is_direction 1 0" by (simp add: is_direction_def)
 have positive: "0<v_degree 1 0 P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have nonempty: "biv_support(leading_form 1 0 P)\<noteq>{}"
   using global_leading_form_nonzero_of_positive_degree[OF positive] by simp
 have maximum_member: "Max(snd ` biv_support(leading_form 1 0 P))\<in>snd ` biv_support(leading_form 1 0 P)"
   by (rule Max_in) (use nonempty in auto)
 obtain e where e: "e\<in>biv_support(leading_form 1 0 P)" and maximum:
   "snd e=Max(snd ` biv_support(leading_form 1 0 P))"
 proof (rule imageE[OF maximum_member])
  fix e assume e: "e\<in>biv_support(leading_form 1 0 P)" and eq: "Max(snd ` biv_support(leading_form 1 0 P))=snd e"
  show thesis by (rule that[OF e eq[symmetric]])
 qed
 have last: "snd d\<le>snd e" if "d\<in>biv_support(leading_form 1 0 P)" for d
   by (simp only: maximum; rule Max_ge) (simp, rule imageI[OF that])
 have face_data: "e\<in>biv_support(pbw_symbol P) \<and>
   (\<forall>d\<in>biv_support(pbw_symbol P). rationalNewtonWeight 0 d\<le>rationalNewtonWeight 0 e)"
   using iffD1[OF leadingForm_mem_iff_rational_slope[where P=P and rho=1 and sigma=0 and a=e, OF zero_less_one] e]
   by (simp only: of_int_0 of_int_1 div_0; blast)
 have raw: "e\<in>biv_support(pbw_symbol P)" by (rule conjunct1[OF face_data])
 have maximal: "\<forall>d\<in>biv_support(pbw_symbol P). rationalNewtonWeight 0 d\<le>rationalNewtonWeight 0 e"
   by (rule conjunct2[OF face_data])
 have xbound: "fst d\<le>fst e" if "d\<in>biv_support(pbw_symbol P)" for d
   using maximal that by (simp add: rationalNewtonWeight_def)
 have ybound: "snd d\<le>snd e" if d: "d\<in>biv_support(pbw_symbol P)" and x: "fst d=fst e" for d
 proof -
   have maximald: "\<forall>c\<in>biv_support(pbw_symbol P). rationalNewtonWeight 0 c\<le>rationalNewtonWeight 0 d"
     using maximal x by (simp add: rationalNewtonWeight_def)
   have horizontal: "d\<in>biv_support(leading_form 1 0 P)"
     by (simp only: leadingForm_mem_iff_rational_slope[where P=P and rho=1 and sigma=0, OF zero_less_one];
       simp only: of_int_0 of_int_1 div_0; rule conjI[OF d maximald])
   show ?thesis by (rule last[OF horizontal])
 qed
 show ?thesis
 proof (cases "pair_grade e<0")
   case True
   show ?thesis by (rule preliminary_horizontal_negative_point_caseAlternative[OF source pair]) (use e True in blast)
 next
   case False
   have positive: "0<pair_grade e" using nozero[OF e last] False by arith
   have order: "snd e<fst e" using positive by (simp add: pair_grade_def)
   have rawpair: "(fst e,snd e)\<in>biv_support(pbw_symbol P)" using raw by simp
   show ?thesis by (rule preliminary_y_axis_positive_horizontal_caseAlternative[OF source bound pair degree unique rawpair xbound ybound order])
 qed
qed

lemma preliminary_y_axis_diagonal_caseAlternative_of_companion:
 fixes P Q::"complex poly_operator" and n::nat
 assumes source: "GGVPreliminaryCompanionInput"
   and bound: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 16\<le>total_degree R"
   and pair: "is_counterexample_pair P Q" and degree: "total_degree P=n"
   and unique: "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> e=(0,n)"
 shows "case_alternative P"
proof -
 have nozero: "pair_grade e\<noteq>0"
   if e: "e\<in>biv_support(leading_form 1 0 P)"
   and maximal: "\<And>d. d\<in>biv_support(leading_form 1 0 P) \<Longrightarrow> snd d\<le>snd e" for e
   by (rule preliminary_horizontal_max_y_grade_ne_zero[where P=P and Q=Q and e=e, OF source pair e maximal])
 show ?thesis
   by (rule preliminary_y_axis_diagonal_caseAlternative[where P=P and Q=Q and n=n, OF source bound pair degree unique nozero])
qed

lemma preliminary_singleton_diagonal_complete_caseSplit:
 fixes P Q::"complex poly_operator" and a b::nat
 assumes source: "GGVPreliminaryCompanionInput"
   and bound: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 16\<le>total_degree R"
   and pair: "is_counterexample_pair P Q" and degree: "total_degree P=a+b"
   and member: "(a,b)\<in>biv_support(leading_form 1 1 P)"
   and unique: "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> e=(a,b)"
 shows "case_alternative P \<or> case_alternative (fourier_alg_hom P)"
proof (cases "a=0")
 case True
 have d: "total_degree P=b" using degree True by simp
 have u: "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> e=(0,b)" using unique True by simp
 have alternative: "case_alternative P"
   by (rule preliminary_y_axis_diagonal_caseAlternative_of_companion[where P=P and Q=Q and n=b, OF source bound pair d u])
 show ?thesis by (rule disjI1[OF alternative])
next
 case False
 note a_nonzero = False
 show ?thesis
 proof (cases "b=0")
   case True
   have carrier: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
   have positive: "0<a+b" using a_nonzero by arith
   have fu: "\<And>e. e\<in>biv_support(leading_form 1 1 (fourier_alg_hom P)) \<Longrightarrow> e=(0,a)"
     using fourier_diagonal_face_unique[OF carrier degree positive unique] True by auto
   have fd: "total_degree (fourier_alg_hom P)=a" using totalDeg_fourier_eq[OF carrier] degree True by simp
   have fp: "is_counterexample_pair (fourier_alg_hom P) (fourier_alg_hom Q)" by (rule isCounterexamplePair_fourier[OF pair])
   have alternative: "case_alternative(fourier_alg_hom P)"
     by (rule preliminary_y_axis_diagonal_caseAlternative_of_companion[
       where P="fourier_alg_hom P" and Q="fourier_alg_hom Q" and n=a, OF source bound fp fd fu])
   show ?thesis by (rule disjI2[OF alternative])
 next
   case False
   have ap: "0<a" using a_nonzero by arith
   have bp: "0<b" using False by arith
   show ?thesis by (rule preliminary_positive_singleton_diagonal_caseSplit[OF source pair degree member unique ap bp])
 qed
qed

lemma preliminary_diagonal_monomial_complete_caseSplit:
 fixes P Q::"complex poly_operator" and a b::nat and lam::complex
 assumes source: "GGVPreliminaryCompanionInput"
   and bound: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 16\<le>total_degree R"
   and pair: "is_counterexample_pair P Q" and lam: "lam\<noteq>0"
   and shape: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 1 0)^a*(biv_monom 1 0 1)^b"
 shows "case_alternative P \<or> case_alternative (fourier_alg_hom P)"
proof -
 have scalar: "biv_monom lam 0 0=[:[:lam:]:]" by (simp only: biv_monom_def monom_0)
 have expansion: "biv_monom lam a b=[:[:lam:]:]*(biv_monom 1 1 0)^a*(biv_monom 1 0 1)^b"
   using biv_monom_factor[where c=lam and i=a and j=b] by (simp only: scalar)
 have factor: "leading_form 1 1 P=biv_monom lam a b"
   by (rule trans[OF shape expansion[symmetric]])
 have support: "biv_support(leading_form 1 1 P)={(a,b)}"
   by (simp only: factor; simp add: weighted_support_monom lam)
 have member: "(a,b)\<in>biv_support(leading_form 1 1 P)" by (simp only: support; simp)
 have unique: "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> e=(a,b)" by (simp only: support; simp)
 have degree: "total_degree P=a+b" using diagonal_face_point_total_degree[OF member] by simp
 show ?thesis by (rule preliminary_singleton_diagonal_complete_caseSplit[OF source bound pair degree member unique])
qed

lemma preliminary_diagonal_single_factor_complete_caseSplit:
 fixes P Q::"complex poly_operator" and a k::nat and lam alpha::complex
 assumes source: "GGVPreliminaryCompanionInput"
   and bound: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 16\<le>total_degree R"
   and pair: "is_counterexample_pair P Q" and k: "1\<le>k" and lam: "lam\<noteq>0"
   and shape: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
     (biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^k"
 shows "case_alternative P \<or> case_alternative (fourier_alg_hom P)"
proof (cases "alpha=0")
 case True
 have monomial: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 1 0)^a*(biv_monom 1 0 1)^k"
   using shape True by simp
 show ?thesis by (rule preliminary_diagonal_monomial_complete_caseSplit[OF source bound pair lam monomial])
next
 case False show ?thesis by (rule preliminary_diagonal_x_factor_complete_caseSplit[OF source bound pair k lam False shape])
qed

lemma preliminary_universal_caseSplit:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput"
   and bound: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 16\<le>total_degree R"
   and pair: "is_counterexample_pair P Q"
 shows "case_alternative P \<or> case_alternative (fourier_alg_hom P)"
proof -
 have direction: "is_direction 1 1" by (simp add: is_direction_def)
 have positive: "0<v_degree 1 1 P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 let ?n="nat(v_degree 1 1 P)"
 have weight: "v_degree 1 1 P=int ?n" using positive by simp
 consider (constantcut) lam where "lam\<noteq>0" "cut_poly 1 1 P=[:lam:]"
   | (one) lam alpha k where "lam\<noteq>0" "1\<le>k" "cut_poly 1 1 P=[:lam:]*[:-alpha,1:]^k"
   | (two) lam alpha beta u v where "lam\<noteq>0" "alpha\<noteq>beta" "1\<le>u" "1\<le>v"
      "cut_poly 1 1 P=[:lam:]*[:-alpha,1:]^u*[:-beta,1:]^v"
   using preliminary_diagonal_cut_factorization[OF source pair] by blast
 then show ?thesis
 proof cases
   case constantcut
   have face: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 1 0)^?n*(biv_monom 1 0 1)^0"
     using diagonal_face_eq_of_constant_cut[OF weight constantcut(2)] by simp
   show ?thesis by (rule preliminary_diagonal_monomial_complete_caseSplit[OF source bound pair constantcut(1) face])
 next
   case one
   have cut_bound: "degree(cut_poly 1 1 P)\<le>?n" by (rule diagonal_cut_natDegree_le[OF weight])
   have degree: "degree(cut_poly 1 1 P)=k" by (simp add: one(3) degree_mult_eq degree_power_eq one(1))
   have kbound: "k\<le>?n" using cut_bound degree by simp
   have combined: "v_degree 1 1 P=int(?n-k+k+0)" using weight kbound by simp
   have cut: "cut_poly 1 1 P=[:lam:]*[:-alpha,1:]^k*[:-0,1:]^0" using one(3) by simp
   have face: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 1 0)^(?n-k)*
     (biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^k"
     using diagonal_face_eq_of_factored_cut[OF combined cut] by simp
   show ?thesis by (rule preliminary_diagonal_single_factor_complete_caseSplit[OF source bound pair one(2) one(1) face])
 next
   case two
   have face: "leading_form 1 1 P=[:[:lam:]:]*
     (biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^u*
     (biv_monom 1 0 1-[:[:beta:]:]*biv_monom 1 1 0)^v"
     by (rule preliminary_two_root_cut_face[OF source pair two])
   show ?thesis
   proof (cases "alpha=0")
     case True
     have beta: "beta\<noteq>0" using two(2) True by auto
     have yshape: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 0 1)^u*
       (biv_monom 1 0 1-[:[:beta:]:]*biv_monom 1 1 0)^v" using face True by simp
     have alternative: "case_alternative P"
       by (rule preliminary_diagonal_y_factor_complete_caseAlternative[
         where P=P and Q=Q and b=u and k=v and lam=lam and alpha=beta,
         OF source bound pair two(4) two(1) beta yshape])
     show ?thesis by (rule disjI1[OF alternative])
   next
     case False
     note alpha_nonzero = False
     show ?thesis
     proof (cases "beta=0")
       case True
       have yshape: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 0 1)^v*
         (biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^u"
         using face True by (simp add: mult.assoc mult.commute mult.left_commute)
       have alternative: "case_alternative P"
         by (rule preliminary_diagonal_y_factor_complete_caseAlternative[
           where P=P and Q=Q and b=v and k=u and lam=lam and alpha=alpha,
           OF source bound pair two(3) two(1) alpha_nonzero yshape])
       show ?thesis by (rule disjI1[OF alternative])
     next
       case False
       have carrier: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
       have linear: "poly_linear P" by (rule weyl_linear[OF carrier])
       have scalar_shape: "biv_monom c 0 0=[:[:c:]:]" for c::complex
         by (simp only: biv_monom_def monom_0)
       have linear_monom: "[:[:c:]:]*biv_monom 1 1 0=biv_monom c 1 0" for c::complex
         using biv_mult_monom[where c=c and a=0 and b=0 and d=1 and e=1 and f=0]
         by (simp only: scalar_shape mult_1_right add_0_left)
       have face_linear: "leading_form 1 1 P=[:[:lam:]:]*
         (biv_monom 1 0 1-biv_monom alpha 1 0)^u*
         (biv_monom 1 0 1-biv_monom beta 1 0)^v"
         using face by (simp only: linear_monom)
       have face_exact: "leading_form 1 1 P=biv_monom lam 0 0*
         (biv_monom 1 0 1-biv_monom alpha 1 0)^u*
         (biv_monom 1 0 1-biv_monom beta 1 0)^v"
         using face_linear by (simp only: scalar_shape[symmetric])
       have alternative: "two_root_total_symbol P"
       proof (unfold two_root_total_symbol_def, rule conjI[OF linear])
         show "\<exists>lam alpha beta u v. lam\<noteq>0 \<and> alpha\<noteq>0 \<and> beta\<noteq>0 \<and> alpha\<noteq>beta \<and> 1\<le>u \<and> 1\<le>v \<and>
           leading_form 1 1 P=biv_monom lam 0 0*(biv_monom 1 0 1-biv_monom alpha 1 0)^u*(biv_monom 1 0 1-biv_monom beta 1 0)^v"
           by (rule exI[where x=lam], rule exI[where x=alpha], rule exI[where x=beta], rule exI[where x=u], rule exI[where x=v])
              (intro conjI two(1) alpha_nonzero False two(2) two(3) two(4) face_exact)
       qed
       show ?thesis using linear alternative by (auto simp: case_alternative_def)
     qed
   qed
 qed
qed

lemma ggv_caseSplit_of_companion_degree_fields:
 assumes companion: "\<forall>P Q::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
 (\<forall>rho sigma::int. is_direction rho sigma \<longrightarrow>
 (\<exists>mu::complex. \<exists>k::nat. \<exists>R F::complex bivariate. \<exists>m::int.
 mu\<noteq>0 \<and> 2\<le>k \<and> R\<noteq>0 \<and> weighted_homogeneous rho sigma m R \<and>
 weighted_homogeneous rho sigma (rho+sigma) F \<and>
 leading_form rho sigma P=[:[:mu:]:]*R^k \<and> biv_poisson R F=R))"
   and degree: "\<And>P Q::complex poly_operator. is_counterexample_pair P Q \<Longrightarrow>
     15<gcd(total_degree P)(total_degree Q)"
 shows "\<forall>P Q::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
   case_alternative P \<or> case_alternative(fourier_alg_hom P)"
proof (intro allI impI)
 fix P Q::"complex poly_operator" assume pair: "is_counterexample_pair P Q"
 have source: "GGVPreliminaryCompanionInput" by (rule preliminary_companion_of_power_companion_field[OF companion])
 have bound: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 16\<le>total_degree R"
   by (rule uniform_degree_bound_of_degree_gcd[OF degree])
 show "case_alternative P \<or> case_alternative(fourier_alg_hom P)"
   by (rule preliminary_universal_caseSplit[OF source bound pair])
qed

end
