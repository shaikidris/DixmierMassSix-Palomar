theory GGV_Positive_Face_Minimal_Exclusion
 imports "GGV_Proportional_Descent_Exclusion"
begin

lemma positive_cut_constant_totalDeg:
 fixes P::"complex poly_operator" and sigma N::nat
 assumes sigma: "1\<le>sigma" and degree: "v_degree 1 (int sigma) P=int N"
   and constant_coefficient: "coeff(cut_poly 1 (int sigma) P) 0\<noteq>0"
 shows "total_degree P=N"
proof -
 have weight: "pair_weight 1 (int sigma) (N,0)=v_degree 1 (int sigma) P"
   by (simp add: pair_weight_def degree)
 have coefficient: "biv_coeff (leading_form 1 (int sigma) P) N 0\<noteq>0"
   using constant_coefficient by (simp only: cutPoly_coeff_at_face_point[OF zero_less_one weight]; simp)
 have face: "(N,0)\<in>biv_support(leading_form 1 (int sigma) P)"
   using coefficient by (simp add: biv_support_def)
 have face_data: "(N,0)\<in>biv_support(pbw_symbol P) \<and>
   (\<forall>e\<in>biv_support(pbw_symbol P).
     rationalNewtonWeight (of_int(int sigma)/ of_int(1::int)) e\<le>
     rationalNewtonWeight (of_int(int sigma)/ of_int(1::int)) (N,0))"
   by (rule iffD1[OF leadingForm_mem_iff_rational_slope[where P=P and rho=1 and sigma="int sigma" and a="(N,0)", OF zero_less_one] face])
 have raw: "(N,0)\<in>biv_support(pbw_symbol P)" by (rule conjunct1[OF face_data])
 have bound: "\<forall>e\<in>biv_support(pbw_symbol P). rationalNewtonWeight (of_nat sigma) e\<le> of_nat N"
   using conjunct2[OF face_data] by (simp add: rationalNewtonWeight_def)
 have upper: "fst e+snd e\<le>N" if e: "e\<in>biv_support(pbw_symbol P)" for e
 proof -
   have slope: "(1::rat)\<le> of_nat sigma" using sigma by simp
   have nonnegative: "(0::rat)\<le> of_nat(snd e)" by simp
   have monotone: "(of_nat(snd e)::rat)\<le> of_nat sigma* of_nat(snd e)"
     using mult_right_mono[OF slope nonnegative] by simp
   have weighted: "(of_nat(fst e)+ of_nat sigma* of_nat(snd e)::rat)\<le> of_nat N"
     using bound e by (simp add: rationalNewtonWeight_def)
   have "(of_nat(fst e+snd e)::rat)\<le> of_nat N" using weighted monotone by (simp only: of_nat_add; arith)
   then show ?thesis by (simp only: of_nat_le_iff)
 qed
 have upper_native: "fst e+snd e\<le>N+0" if member: "e\<in>biv_support(pbw_symbol P)" for e
   using upper[OF member] by simp
 show ?thesis using totalDeg_eq_of_support_sum_bound[where P=P and a=N and b=0, OF raw upper_native] by simp
qed

lemma polynomial_cut_inverse_translation:
 fixes p q::"complex poly" and alpha::complex
 assumes translate: "q=pcompose p [:alpha,1:]"
 shows "p=pcompose q [:-alpha,1:]"
 by (simp add: translate pcompose_assoc[symmetric] pcompose_pCons)

lemma bivariate_singleton_support_eq_monomial:
 fixes p::"complex bivariate"
 assumes support: "biv_support p={(a,b)}"
 shows "p=biv_monom (biv_coeff p a b) a b"
proof (rule poly_eqI)
 fix j show "coeff p j=coeff (biv_monom (biv_coeff p a b) a b) j"
 proof (rule poly_eqI)
   fix i
   have zero: "(i,j)\<noteq>(a,b) \<Longrightarrow> biv_coeff p i j=0"
   proof -
     assume different: "(i,j)\<noteq>(a,b)"
     have nonmember: "(i,j)\<notin>biv_support p" using different by (simp only: support; blast)
     show "biv_coeff p i j=0"
       using nonmember by (simp only: biv_support_def mem_Collect_eq fst_conv snd_conv not_not)
   qed
   show "coeff (coeff p j) i=coeff (coeff (biv_monom (biv_coeff p a b) a b) j) i"
     using zero by (auto simp: biv_coeff_def biv_monom_def coeff_monom prod_eq_iff)
 qed
qed

lemma degreeMinimal_positive_face_impossible:
 fixes P Q::"complex poly_operator" and sigma::nat
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
   and sigma: "1<sigma" and face: "in_direction 1 (int sigma) P"
 shows False
proof -
 have pair: "is_counterexample_pair P Q" using minimal by (simp add: is_degree_minimal_counterexample_pair_def)
 have slope: "1\<le>sigma" using sigma by arith
 obtain lam alpha a b where lam: "lam\<noteq>0" and alpha: "alpha\<noteq>0" and b: "1\<le>b"
   and Pweight: "v_degree 1 (int sigma) P=int(a+sigma*b)"
   and Pshape: "leading_form 1 (int sigma) P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
     (biv_monom 1 0 1-[:[:alpha:]:]*(biv_monom 1 1 0)^sigma)^b"
   using preliminary_positive_face_binomial[OF preliminary_companion_from_actual_GGV_companion pair sigma face] by blast
 have bp: "0<b" using b by arith
 have Pcut: "cut_poly 1 (int sigma) P=[:lam:]*[:-alpha,1:]^b" by (rule positive_binomial_face_cut[OF Pshape])
 have Pconstant: "coeff(cut_poly 1 (int sigma) P) 0\<noteq>0" by (simp only: poly_0_coeff_0[symmetric]) (simp add: Pcut lam alpha)
 have Pdegree: "total_degree P=a+sigma*b" by (rule positive_cut_constant_totalDeg[OF slope Pweight Pconstant])
 obtain R S where RS: "is_counterexample_pair R S"
   and recoverR: "polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 (int sigma) alpha (polynomial_ramified_lift 1 P)"
   and recoverS: "polynomial_ramified_lift 1 S=ramified_cut_aut 1 1 (int sigma) alpha (polynomial_ramified_lift 1 Q)"
   using polynomial_monomial_cut_recovers_polynomial_counterexample[OF pair, where sigma=sigma and c=alpha] by blast
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra" and R: "R\<in>weyl_algebra" and S: "S\<in>weyl_algebra"
   using pair RS by (simp_all add: is_counterexample_pair_def)
 have direction: "is_direction 1 (int sigma)" by (simp add: is_direction_def)
 have Ppos: "0<v_degree 1 (int sigma) P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have Rpos: "0<v_degree 1 (int sigma) R" by (rule counterexample_vDeg_pos_all_directions[OF RS direction])
 have Qpos: "0<v_degree 1 (int sigma) Q" by (rule counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF pair] direction])
 have Spos: "0<v_degree 1 (int sigma) S" by (rule counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF RS] direction])
 have Pnz: "P\<noteq>0" using Ppos by auto
 have Qnz: "Q\<noteq>0" using Qpos by auto
 have Rt: "v_degree 1 (int sigma) R=v_degree 1 (int sigma) P \<and>
   cut_poly 1 (int sigma) R=pcompose (cut_poly 1 (int sigma) P) [:alpha,1:]"
   by (rule polynomial_monomial_cut_weight_and_translate[OF P R Pnz Ppos Rpos recoverR])
 have affine: "pcompose ([:-alpha,1:]::complex poly) [:alpha,1:]=[:0,1:]"
   by (simp add: pcompose_pCons pcompose_1)
 have Rcut: "cut_poly 1 (int sigma) R=[:lam:]*[:0,1:]^b"
   using conjunct2[OF Rt] by (simp add: Pcut pcompose_smult native_pcompose_power affine)
 have Rweight: "v_degree 1 (int sigma) R=int(a+sigma*b)" using Rt Pweight by simp
 have Rshape: "leading_form 1 (int sigma) R=[:[:lam:]:]*(biv_monom 1 1 0)^a*(biv_monom 1 0 1)^b"
   using positive_face_eq_of_linear_power_cut[OF Rweight, where lam=lam and alpha=0] Rcut by simp
 have Rsupport: "biv_support(leading_form 1 (int sigma) R)={(a,b)}" by (simp only: Rshape weighted_monomial_support[OF lam])
 have Rpoint: "(a,b)\<in>biv_support(leading_form 1 (int sigma) R)" by (simp add: Rsupport)
 have Runique: "e=(a,b)" if "e\<in>biv_support(leading_form 1 (int sigma) R)" for e using that by (simp add: Rsupport)
 obtain c d where d: "0<d" and Ssupport: "biv_support(leading_form 1 (int sigma) S)={(c,d)}"
   and Sweight: "v_degree 1 (int sigma) S=int(c+sigma*d)"
   using counterexample_positive_singleton_proportional_mate[OF RS Runique slope bp] by blast
 let ?mu="biv_coeff (leading_form 1 (int sigma) S) c d"
 have Smember: "(c,d)\<in>biv_support(leading_form 1 (int sigma) S)" by (simp add: Ssupport)
 have mu: "?mu\<noteq>0" using Smember by (simp add: biv_support_def)
 have Smono: "leading_form 1 (int sigma) S=biv_monom ?mu c d"
   by (rule bivariate_singleton_support_eq_monomial[OF Ssupport])
 have Sshape: "leading_form 1 (int sigma) S=[:[:?mu:]:]*(biv_monom 1 1 0)^c*(biv_monom 1 0 1)^d"
   by (rule trans[OF Smono native_weighted_monomial_eq[symmetric]])
 have Sbinomial: "leading_form 1 (int sigma) S=[:[:?mu:]:]*(biv_monom 1 1 0)^c*
   (biv_monom 1 0 1-[:[:(0::complex):]:]*(biv_monom 1 1 0)^sigma)^d"
   by (simp only: pCons_0_0 mult_zero_left diff_zero; rule Sshape)
 have Scut: "cut_poly 1 (int sigma) S=[:?mu:]*[:0,1:]^d"
   using positive_binomial_face_cut[where P=S and sigma=sigma and a=c and k=d and lam="?mu" and alpha=0,
     OF Sbinomial] by (simp only: minus_zero)
 have St: "v_degree 1 (int sigma) S=v_degree 1 (int sigma) Q \<and>
   cut_poly 1 (int sigma) S=pcompose (cut_poly 1 (int sigma) Q) [:alpha,1:]"
   by (rule polynomial_monomial_cut_weight_and_translate[OF Q S Qnz Qpos Spos recoverS])
 have inverse_cut: "cut_poly 1 (int sigma) Q=pcompose (cut_poly 1 (int sigma) S) [:-alpha,1:]"
   by (rule polynomial_cut_inverse_translation[where p="cut_poly 1 (int sigma) Q" and
     q="cut_poly 1 (int sigma) S" and alpha=alpha, OF conjunct2[OF St]])
 have X_inverse: "pcompose ([:0,1:]::complex poly) [:-alpha,1:]=[:-alpha,1:]"
   by (simp add: pcompose_pCons pcompose_1)
 have inverse_monomial: "pcompose ([:z:]*[:0,1:]^d) [:-alpha,1:]=[:z:]*[:-alpha,1:]^d" for z::complex
   by (simp add: pcompose_smult native_pcompose_power X_inverse)
 have translated_back: "pcompose (cut_poly 1 (int sigma) S) [:-alpha,1:]=[:?mu:]*[:-alpha,1:]^d"
   by (simp only: Scut inverse_monomial)
 have Qcut: "cut_poly 1 (int sigma) Q=[:?mu:]*[:-alpha,1:]^d"
   by (rule trans[OF inverse_cut translated_back])
 have Qconstant: "coeff(cut_poly 1 (int sigma) Q) 0\<noteq>0" by (simp only: poly_0_coeff_0[symmetric]) (simp add: Qcut mu alpha)
 have Qweight: "v_degree 1 (int sigma) Q=int(c+sigma*d)" using St Sweight by simp
 have Qdegree_nat: "total_degree Q=c+sigma*d"
   by (rule positive_cut_constant_totalDeg[OF slope Qweight Qconstant])
 have mate_weight_nat: "nat(v_degree 1 (int sigma) S)=c+sigma*d"
   by (simp only: Sweight nat_int)
 have Qdegree: "total_degree Q=nat(v_degree 1 (int sigma) S)"
   by (rule trans[OF Qdegree_nat mate_weight_nat[symmetric]])
 show False by (rule degreeMinimal_proportional_positive_descent_impossible[OF minimal RS sigma bp Pdegree Qdegree Rpoint Runique])
qed

lemma degreeMinimal_diagonal_axis_singleton_impossible:
 fixes P Q::"complex poly_operator" and n::nat
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
   and member: "(n,0)\<in>biv_support(leading_form 1 1 P)"
   and unique: "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> e=(n,0)"
 shows False
proof -
 have pair: "is_counterexample_pair P Q" using minimal by (simp add: is_degree_minimal_counterexample_pair_def)
 obtain sigma where sigma: "1<sigma" and face: "in_direction 1 (int sigma) P"
   using preliminary_axis_diagonal_positive_face[OF preliminary_companion_from_actual_GGV_companion pair member unique] by blast
 show False by (rule degreeMinimal_positive_face_impossible[OF minimal sigma face])
qed

end
