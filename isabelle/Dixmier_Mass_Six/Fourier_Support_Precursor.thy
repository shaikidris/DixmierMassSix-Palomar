theory Fourier_Support_Precursor
 imports "Fourier_Grade_Mass"
   "Weighted_Newton_Definitions"
begin

lemma fourier_support_precursor:
 fixes P::"'k::field_char_0 poly_operator"
 assumes P: "P\<in>weyl_algebra" and e: "e\<in>biv_support(pbw_symbol(fourier_alg_hom P))"
 shows "\<exists>i j k::nat. (i,j)\<in>biv_support(pbw_symbol P) \<and>
   k\<le>i \<and> k\<le>j \<and> e=(j-k,i-k)"
proof -
 obtain c::"(nat\<times>nat,'k) poly_mapping" where expansion:
   "finite_normal_sum (Poly_Mapping.keys c)(Poly_Mapping.lookup c)=P"
   using fourier_exists_poly_mapping[OF P] by blast
 have coefficients: "pbw_coeff P (fst u)(snd u)=Poly_Mapping.lookup c u" for u
   by (simp add: expansion[symmetric] pbw_coeff_finite_normal_sum Poly_Mapping.in_keys_iff)
 have support: "biv_support(pbw_symbol P)=Poly_Mapping.keys c"
   by (auto simp: biv_support_def weyl_symbol_coeff[OF P] coefficients Poly_Mapping.in_keys_iff)
 have nonzero_sum: "(\<Sum>u\<in>Poly_Mapping.keys c. biv_coeff
   (smult [:Poly_Mapping.lookup c u:] (smult [:(-1)^snd u:]
   (pbw_symbol (op_comp (y_op ^^ fst u)(x_op ^^ snd u))))) (fst e)(snd e))\<noteq>0"
   using e by (simp add: biv_support_def symbol_fourierAlgHom_eq_sum[OF P expansion] biv_coeff_sum)
 obtain u where u: "u\<in>Poly_Mapping.keys c" and summand:
   "biv_coeff (smult [:Poly_Mapping.lookup c u:] (smult [:(-1)^snd u:]
   (pbw_symbol (op_comp (y_op ^^ fst u)(x_op ^^ snd u))))) (fst e)(snd e)\<noteq>0"
   using sum.not_neutral_contains_not_neutral[OF nonzero_sum] by blast
 have anti: "e\<in>biv_support(pbw_symbol(op_comp (y_op ^^ fst u)(x_op ^^ snd u)::'k poly_operator))"
   using summand by (auto simp: biv_support_def)
 have anti_sum: "(\<Sum>k\<le>min(snd u)(fst u). biv_coeff
   (biv_monom (of_nat ((fst u choose k)*nat_desc_factorial (snd u) k)::'k)
   (snd u-k)(fst u-k)) (fst e)(snd e))\<noteq>0"
   using anti by (simp add: biv_support_def symbol_concreteAntiNormalMonomial biv_coeff_sum)
 obtain k where k: "k\<le>min(snd u)(fst u)" and monomial:
   "biv_coeff (biv_monom (of_nat ((fst u choose k)*nat_desc_factorial (snd u) k)::'k)
   (snd u-k)(fst u-k)) (fst e)(snd e)\<noteq>0"
   using sum.not_neutral_contains_not_neutral[OF anti_sum] by auto
 have coordinates: "fst e=snd u-k" "snd e=fst u-k" using monomial by (auto split: if_splits)
 have original: "(fst u,snd u)\<in>biv_support(pbw_symbol P)" using u by (simp add: support)
 show ?thesis by (intro exI[of _ "fst u"] exI[of _ "snd u"] exI[of _ k])
   (use original k coordinates in \<open>auto simp: prod_eq_iff\<close>)
qed

lemma totalDeg_fourier_le:
 fixes P::"'k::field_char_0 poly_operator"
 assumes P: "P\<in>weyl_algebra"
 shows "total_degree(fourier_alg_hom P)\<le>total_degree P"
 unfolding total_degree_def[of "fourier_alg_hom P"]
proof (rule Max.boundedI)
 show "finite(insert 0 ((\<lambda>u. fst u+snd u) ` biv_support(pbw_symbol(fourier_alg_hom P))))" by simp
 show "insert 0 ((\<lambda>u. fst u+snd u) ` biv_support(pbw_symbol(fourier_alg_hom P)))\<noteq>{}" by simp
 show "\<And>x. x\<in>insert 0 ((\<lambda>u. fst u+snd u) ` biv_support(pbw_symbol(fourier_alg_hom P))) \<Longrightarrow>
   x\<le>total_degree P"
 proof -
   fix x assume member: "x\<in>insert 0 ((\<lambda>u. fst u+snd u) ` biv_support(pbw_symbol(fourier_alg_hom P)))"
   show "x\<le>total_degree P"
   proof (cases "x=0")
     case True then show ?thesis by simp
   next
     case False
     obtain e where e: "e\<in>biv_support(pbw_symbol(fourier_alg_hom P))" and x: "x=fst e+snd e"
       using member False by blast
     obtain i j k where original: "(i,j)\<in>biv_support(pbw_symbol P)"
       and ki: "k\<le>i" and kj: "k\<le>j" and coordinate: "e=(j-k,i-k)"
       using fourier_support_precursor[OF P e] by blast
     have image_member: "(\<lambda>u. fst u+snd u)(i,j)\<in>(\<lambda>u. fst u+snd u) ` biv_support(pbw_symbol P)"
       by (rule imageI[OF original])
     have bound: "i+j\<le>total_degree P"
       unfolding total_degree_def by (rule Max_ge) (use image_member in simp_all)
     show ?thesis using bound ki kj by (simp add: x coordinate; arith)
   qed
 qed
qed

lemma totalDeg_fourier_eq:
 fixes P::"'k::field_char_0 poly_operator"
 assumes P: "P\<in>weyl_algebra"
 shows "total_degree(fourier_alg_hom P)=total_degree P"
proof -
 have P1: "fourier_alg_hom P\<in>weyl_algebra" by (rule fourier_alg_hom_closed[OF P])
 have P2: "fourier_alg_hom(fourier_alg_hom P)\<in>weyl_algebra" by (rule fourier_alg_hom_closed[OF P1])
 have P3: "fourier_alg_hom(fourier_alg_hom(fourier_alg_hom P))\<in>weyl_algebra"
   by (rule fourier_alg_hom_closed[OF P2])
 have a: "total_degree(fourier_alg_hom P)\<le>total_degree P" by (rule totalDeg_fourier_le[OF P])
 have b: "total_degree(fourier_alg_hom(fourier_alg_hom P))\<le>total_degree(fourier_alg_hom P)"
   by (rule totalDeg_fourier_le[OF P1])
 have c: "total_degree(fourier_alg_hom(fourier_alg_hom(fourier_alg_hom P)))\<le>
   total_degree(fourier_alg_hom(fourier_alg_hom P))" by (rule totalDeg_fourier_le[OF P2])
 have d: "total_degree P\<le>total_degree(fourier_alg_hom(fourier_alg_hom(fourier_alg_hom P)))"
   using totalDeg_fourier_le[OF P3] by (simp only: fourierAlgHom_fourth[OF P])
 show ?thesis using a b c d by arith
qed

end
