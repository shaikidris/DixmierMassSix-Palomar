theory Fourier_Rectangle
 imports "Fourier_Support_Precursor"
   "Positive_Companion_Coordinates"
   "Subrectangular_Case_Support"
   "Fourier_Generation"
begin

lemma support_total_degree_bound:
 assumes e: "e\<in>biv_support(pbw_symbol P)"
 shows "fst e+snd e\<le>total_degree P"
 unfolding total_degree_def
 by (rule Max_ge) (simp, rule insertI2, rule imageI[OF e])

lemma support_totalDeg_mem_diagonal_leadingForm:
 fixes P::"complex poly_operator"
 assumes e: "e\<in>biv_support(pbw_symbol P)" and top: "fst e+snd e=total_degree P"
 shows "e\<in>biv_support(leading_form 1 1 P)"
proof -
 have bound: "rationalNewtonWeight 1 z\<le>rationalNewtonWeight 1 e"
   if z: "z\<in>biv_support(pbw_symbol P)" for z
 proof -
   have "fst z+snd z\<le>fst e+snd e" using support_total_degree_bound[OF z] top by simp
   then have "(of_nat(fst z+snd z)::rat)\<le>of_nat(fst e+snd e)" by simp
   then show ?thesis by (simp add: rationalNewtonWeight_def)
 qed
 show ?thesis by (simp only: leadingForm_mem_iff_rational_slope[where P=P and rho=1 and sigma=1, OF zero_less_one]; simp only: of_int_1 divide_self[OF one_neq_zero]; rule conjI[OF e]; use bound in blast)
qed

lemma fourier_diagonal_face_unique:
 fixes P::"complex poly_operator" and a b::nat
 assumes P: "P\<in>weyl_algebra" and diagonal: "total_degree P=a+b" and positive: "0<a+b"
   and unique: "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> e=(a,b)"
 shows "(b,a)\<in>biv_support(leading_form 1 1 (fourier_alg_hom P)) \<and>
   (\<forall>e\<in>biv_support(leading_form 1 1 (fourier_alg_hom P)). e=(b,a))"
proof -
 let ?T="fourier_alg_hom P"
 let ?S="biv_support(pbw_symbol ?T)"
 have degree: "total_degree ?T=a+b" using totalDeg_fourier_eq[OF P] diagonal by simp
 have top_unique: "e=(b,a)" if e: "e\<in>?S" and top: "fst e+snd e=a+b" for e
 proof -
   obtain i j k::nat where original: "(i,j)\<in>biv_support(pbw_symbol P)"
     and ki: "k\<le>i" and kj: "k\<le>j" and eq: "e=(j-k,i-k)"
     using fourier_support_precursor[OF P e] by blast
   have contract: "j-k+(i-k)=a+b" using top eq by simp
   have bounded: "i+j\<le>a+b" using support_total_degree_bound[OF original] diagonal by simp
   have zero: "k=0" using ki kj bounded contract by arith
   have original_top: "i+j=total_degree P" using diagonal contract zero by simp
   have original_face: "(i,j)\<in>biv_support(leading_form 1 1 P)"
     by (rule support_totalDeg_mem_diagonal_leadingForm[OF original]) (simp only: fst_conv snd_conv; rule original_top)
   have pair: "(i,j)=(a,b)" by (rule unique[OF original_face])
   show ?thesis using eq zero pair by auto
 qed
 have finite: "finite(insert 0 ((\<lambda>e. fst e+snd e) ` ?S))" by simp
 have maximum_member: "total_degree ?T\<in>insert 0 ((\<lambda>e. fst e+snd e) ` ?S)"
   unfolding total_degree_def by (rule Max_in) simp_all
 obtain e where e: "e\<in>?S" and top: "fst e+snd e=a+b"
   using maximum_member degree positive by auto
 have corner: "(b,a)\<in>?S" using top_unique[OF e top] e by simp
 have corner_face: "(b,a)\<in>biv_support(leading_form 1 1 ?T)"
   by (rule support_totalDeg_mem_diagonal_leadingForm[OF corner]) (simp add: degree add.commute)
 have each: "e=(b,a)" if face: "e\<in>biv_support(leading_form 1 1 ?T)" for e
 proof -
   have e: "e\<in>?S" and emax: "\<forall>z\<in>?S. rationalNewtonWeight 1 z\<le>rationalNewtonWeight 1 e"
     using iffD1[OF leadingForm_mem_iff_rational_slope[where P="?T" and rho=1 and sigma=1, OF zero_less_one] face]
     by (auto simp only: of_int_1 divide_self[OF one_neq_zero])
   have lower: "a+b\<le>fst e+snd e"
   proof -
     have rational: "rationalNewtonWeight 1 (b,a)\<le>rationalNewtonWeight 1 e"
       by (rule bspec[OF emax corner])
     have "(of_nat(b+a)::rat)\<le>of_nat(fst e+snd e)"
       using rational by (simp only: rationalNewtonWeight_def fst_conv snd_conv mult_1_left of_nat_add)
     then show ?thesis by (simp only: of_nat_le_iff add.commute)
   qed
   have upper: "fst e+snd e\<le>a+b" using support_total_degree_bound[OF e] degree by simp
   show ?thesis by (rule top_unique[OF e]) (use lower upper in arith)
 qed
 show ?thesis using corner_face each by blast
qed

lemma fourier_support_second_coord_le_of_first:
 fixes P::"'k::field_char_0 poly_operator"
 assumes P: "P\<in>weyl_algebra" and bound: "\<And>e. e\<in>biv_support(pbw_symbol P) \<Longrightarrow> fst e\<le>a"
 shows "\<forall>e\<in>biv_support(pbw_symbol(fourier_alg_hom P)). snd e\<le>a"
proof (rule ballI)
 fix e assume e: "e\<in>biv_support(pbw_symbol(fourier_alg_hom P))"
 obtain i j k where original: "(i,j)\<in>biv_support(pbw_symbol P)" and shape: "e=(j-k,i-k)"
   using fourier_support_precursor[OF P e] by blast
 show "snd e\<le>a" using bound[OF original] by (simp only: shape fst_conv snd_conv; arith)
qed

lemma fourier_support_first_coord_le_of_second:
 fixes P::"'k::field_char_0 poly_operator"
 assumes P: "P\<in>weyl_algebra" and bound: "\<And>e. e\<in>biv_support(pbw_symbol P) \<Longrightarrow> snd e\<le>b"
 shows "\<forall>e\<in>biv_support(pbw_symbol(fourier_alg_hom P)). fst e\<le>b"
proof (rule ballI)
 fix e assume e: "e\<in>biv_support(pbw_symbol(fourier_alg_hom P))"
 obtain i j k where original: "(i,j)\<in>biv_support(pbw_symbol P)" and shape: "e=(j-k,i-k)"
   using fourier_support_precursor[OF P e] by blast
 show "fst e\<le>b" using bound[OF original] by (simp only: shape fst_conv snd_conv; arith)
qed

lemma support_first_coord_le_of_fourier_second:
 fixes P::"'k::field_char_0 poly_operator"
 assumes P: "P\<in>weyl_algebra"
   and bound: "\<And>e. e\<in>biv_support(pbw_symbol(fourier_alg_hom P)) \<Longrightarrow> snd e\<le>a"
 shows "\<forall>e\<in>biv_support(pbw_symbol P). fst e\<le>a"
proof -
 have P1: "fourier_alg_hom P\<in>weyl_algebra" by (rule fourier_alg_hom_closed[OF P])
 have P2: "fourier_alg_hom(fourier_alg_hom P)\<in>weyl_algebra" by (rule fourier_alg_hom_closed[OF P1])
 have P3: "fourier_alg_hom(fourier_alg_hom(fourier_alg_hom P))\<in>weyl_algebra" by (rule fourier_alg_hom_closed[OF P2])
 have b2: "\<forall>e\<in>biv_support(pbw_symbol(fourier_alg_hom(fourier_alg_hom P))). fst e\<le>a"
   by (rule fourier_support_first_coord_le_of_second[OF P1 bound])
 have b3: "\<forall>e\<in>biv_support(pbw_symbol(fourier_alg_hom(fourier_alg_hom(fourier_alg_hom P)))). snd e\<le>a"
   by (rule fourier_support_second_coord_le_of_first[OF P2]) (use b2 in blast)
 have b4: "\<forall>e\<in>biv_support(pbw_symbol(fourier_alg_hom(fourier_alg_hom(fourier_alg_hom(fourier_alg_hom P))))). fst e\<le>a"
   by (rule fourier_support_first_coord_le_of_second[OF P3]) (use b3 in blast)
 show ?thesis using b4 by (simp only: fourierAlgHom_fourth[OF P])
qed

lemma preliminary_companion_singleton_diagonal_subrectangular:
 fixes P Q::"complex poly_operator" and a b::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and diagonal: "total_degree P=a+b" and occupied: "(a,b)\<in>biv_support(leading_form 1 1 P)"
   and unique: "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> e=(a,b)"
   and a: "0<a" and b: "0<b"
 shows "is_subrectangular_at P a b"
proof -
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have y: "\<forall>e\<in>biv_support(pbw_symbol P). snd e\<le>b"
   by (rule preliminary_companion_support_second_coord_le[OF source pair diagonal occupied unique b])
 have positive: "0<a+b" using a by simp
 have Fface: "(b,a)\<in>biv_support(leading_form 1 1 (fourier_alg_hom P))"
   and Funique: "\<And>e. e\<in>biv_support(leading_form 1 1 (fourier_alg_hom P)) \<Longrightarrow> e=(b,a)"
   using fourier_diagonal_face_unique[OF P diagonal positive unique] by blast+
 have Fdegree: "total_degree(fourier_alg_hom P)=b+a" using totalDeg_fourier_eq[OF P] diagonal by (simp add: add.commute)
 have Fpair: "is_counterexample_pair (fourier_alg_hom P) (fourier_alg_hom Q)" by (rule isCounterexamplePair_fourier[OF pair])
 have Fy: "\<forall>e\<in>biv_support(pbw_symbol(fourier_alg_hom P)). snd e\<le>a"
   by (rule preliminary_companion_support_second_coord_le[OF source Fpair Fdegree Fface Funique a])
 have x: "\<forall>e\<in>biv_support(pbw_symbol P). fst e\<le>a"
   by (rule support_first_coord_le_of_fourier_second[OF P]) (use Fy in blast)
 have raw: "(a,b)\<in>biv_support(pbw_symbol P)" using occupied by (simp add: leading_form_def weighted_component_support)
 show ?thesis using raw x y by (simp add: is_subrectangular_at_def)
qed
end
