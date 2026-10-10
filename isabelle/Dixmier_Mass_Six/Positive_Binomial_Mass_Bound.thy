theory Positive_Binomial_Mass_Bound
 imports "Positive_Shear_Finite_Descent"
   "Positive_Binomial_Top_Boundary"
begin

lemma preliminary_positive_binomial_mass_ge_ten:
 fixes P Q::"complex poly_operator" and sigma a b::nat and lam alpha::complex
 assumes source: "GGVPreliminaryCompanionInput"
 and bound: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 16\<le>total_degree R"
 and pair: "is_counterexample_pair P Q" and sigma: "1<sigma" and less: "a<b"
 and lam: "lam\<noteq>0" and alpha: "alpha\<noteq>0"
 and degree: "v_degree 1 (int sigma) P=int(a+sigma*b)"
 and shape: "leading_form 1 (int sigma) P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
   (biv_monom 1 0 1-[:[:alpha:]:]*(biv_monom 1 1 0)^sigma)^b"
 shows "10\<le>weyl_mass P"
proof -
 have cut: "cut_poly 1 (int sigma) P=[:lam:]*[:-alpha,1:]^b"
   by (rule positive_binomial_face_cut[OF shape])
 obtain R S where RS: "is_counterexample_pair R S"
 and mono: "leading_form 1 (int sigma) R=[:[:lam:]:]*(biv_monom 1 1 0)^a*(biv_monom 1 0 1)^b"
   using polynomial_root_shear_monomial_face[OF pair degree cut] by blast
 have support: "biv_support(leading_form 1 (int sigma) R)={(a,b)}"
   by (simp only: mono weighted_monomial_support[OF lam])
 have point: "(a,b)\<in>biv_support(leading_form 1 (int sigma) R)" by (simp add: support)
 have unique: "d=(a,b)" if "d\<in>biv_support(leading_form 1 (int sigma) R)" for d using that by (simp add: support)
 have sigmale: "1\<le>sigma" using sigma by arith
 have bp: "0<b" using less by arith
 obtain T U where TU: "is_counterexample_pair T U" and total: "total_degree T=a+b"
   using preliminary_positive_singleton_finite_descent[OF source RS sigmale bp point unique] by blast
 have large: "16\<le>a+b" using bound[OF TU] total by simp
 have nz: "cut_poly 1 (int sigma) P\<noteq>0" using lam by (simp add: cut)
 have divides: "([:0,1:]-[:alpha:])^b dvd cut_poly 1 (int sigma) P"
   by (rule dvdI[where k="[:lam:]"]) (simp add: cut mult.commute)
 have terms: "b<termCount(cut_poly 1 (int sigma) P)" by (rule pow_dvd_imp_lt_termCount[OF nz alpha divides])
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have mass: "termCount(cut_poly 1 (int sigma) P)\<le>weyl_mass P"
   by (rule cutPoly_termCount_le_mass[OF P]) simp
 show ?thesis using less large terms mass by arith
qed

lemma preliminary_positive_binomial_mass_of_negative_top_boundary:
 fixes P Q::"complex poly_operator" and sigma a b::nat and lam alpha::complex and e::"nat\<times>nat"
 assumes source: "GGVPreliminaryCompanionInput"
 and bound: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 16\<le>total_degree R"
 and pair: "is_counterexample_pair P Q" and sigma: "1<sigma" and bp: "0<b"
 and lam: "lam\<noteq>0" and alpha: "alpha\<noteq>0"
 and degree: "v_degree 1 (int sigma) P=int(a+sigma*b)"
 and shape: "leading_form 1 (int sigma) P=[:[:lam:]:]*(biv_monom 1 1 0)^a*
   (biv_monom 1 0 1-[:[:alpha:]:]*(biv_monom 1 1 0)^sigma)^b"
 and e: "e\<in>biv_support(pbw_symbol P)"
 and ey: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> snd d\<le>snd e"
 and ex: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> snd d=snd e \<Longrightarrow> fst d\<le>fst e"
 and negative: "pair_grade e<0"
 shows "10\<le>weyl_mass P"
proof -
 have sigmale: "1\<le>sigma" using sigma by arith
 have boundary: "(a,b)\<in>biv_support(pbw_symbol P) \<and>
   (\<forall>d\<in>biv_support(pbw_symbol P). snd d\<le>b) \<and>
   (\<forall>d\<in>biv_support(pbw_symbol P). snd d=b \<longrightarrow> fst d\<le>a)"
   by (rule preliminary_positive_binomial_top_boundary[OF source pair sigmale bp lam degree shape])
 have point: "(a,b)\<in>biv_support(pbw_symbol P)" using boundary by blast
 have eqy: "snd e=b" using boundary e ey[OF point] by auto
 have eqx: "fst e=a" using boundary e eqy ex[OF point] by auto
 have less: "a<b" using negative by (simp add: pair_grade_def eqx eqy)
 show ?thesis by (rule preliminary_positive_binomial_mass_ge_ten[OF source bound pair sigma less lam alpha degree shape])
qed

end
