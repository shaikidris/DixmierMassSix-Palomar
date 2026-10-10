theory Fourier_Diagonal_Endpoints
 imports Fourier_Rectangle
begin

lemma diagonal_face_point_total_degree:
 fixes P::"complex poly_operator"
 assumes e: "e\<in>biv_support(leading_form 1 1 P)"
 shows "fst e+snd e=total_degree P"
proof -
 have raw: "e\<in>biv_support(pbw_symbol P)" and maximal:
   "\<forall>d\<in>biv_support(pbw_symbol P). rationalNewtonWeight 1 d\<le>rationalNewtonWeight 1 e"
   using iffD1[OF leadingForm_mem_iff_rational_slope[where P=P and rho=1 and sigma=1, OF zero_less_one] e]
   by (auto simp only: of_int_1 divide_self[OF one_neq_zero])
 have bounded: "fst d+snd d\<le>fst e+snd e" if "d\<in>biv_support(pbw_symbol P)" for d
   proof -
   have rational: "rationalNewtonWeight 1 d\<le>rationalNewtonWeight 1 e"
     by (rule bspec[OF maximal that])
   have "(of_nat(fst d+snd d)::rat)\<le>of_nat(fst e+snd e)"
     using rational by (simp only: rationalNewtonWeight_def mult_1_left of_nat_add)
   then show ?thesis by (simp only: of_nat_le_iff)
 qed
 have upper: "total_degree P\<le>fst e+snd e"
   unfolding total_degree_def by (rule Max.boundedI) (use bounded in auto)
 have lower: "fst e+snd e\<le>total_degree P" by (rule support_total_degree_bound[OF raw])
 show ?thesis using upper lower by arith
qed

lemma fourier_diagonal_point_preimage:
 fixes P::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and e: "e\<in>biv_support(leading_form 1 1 (fourier_alg_hom P))"
 shows "(snd e,fst e)\<in>biv_support(leading_form 1 1 P)"
proof -
 have raw: "e\<in>biv_support(pbw_symbol(fourier_alg_hom P))"
   using e by (simp add: leading_form_def weighted_component_support)
 obtain i j k where original: "(i,j)\<in>biv_support(pbw_symbol P)" and ki: "k\<le>i" and kj: "k\<le>j"
   and eq: "e=(j-k,i-k)" using fourier_support_precursor[OF P raw] by blast
 have top: "fst e+snd e=total_degree P"
   using diagonal_face_point_total_degree[OF e] totalDeg_fourier_eq[OF P] by simp
 have upper: "i+j\<le>total_degree P" using support_total_degree_bound[OF original] by simp
 have zero: "k=0" using top upper ki kj by (simp only: eq fst_conv snd_conv; arith)
 have original_top: "fst(i,j)+snd(i,j)=total_degree P" using top by (simp add: eq zero add.commute)
 have face: "(i,j)\<in>biv_support(leading_form 1 1 P)"
   by (rule support_totalDeg_mem_diagonal_leadingForm[OF original original_top])
 show ?thesis using face by (simp add: eq zero)
qed

lemma fourier_diagonal_point_mem:
 fixes P::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and e: "e\<in>biv_support(leading_form 1 1 P)"
 shows "(snd e,fst e)\<in>biv_support(leading_form 1 1 (fourier_alg_hom P))"
proof -
 let ?F="fourier_alg_hom"
 have P1: "?F P\<in>weyl_algebra" by (rule fourier_alg_hom_closed[OF P])
 have P2: "?F(?F P)\<in>weyl_algebra" by (rule fourier_alg_hom_closed[OF P1])
 have P3: "?F(?F(?F P))\<in>weyl_algebra" by (rule fourier_alg_hom_closed[OF P2])
 have fourth: "e\<in>biv_support(leading_form 1 1 (?F(?F(?F(?F P)))))"
   by (simp only: fourierAlgHom_fourth[OF P]; rule e)
 have h3: "(snd e,fst e)\<in>biv_support(leading_form 1 1 (?F(?F(?F P))))"
   by (rule fourier_diagonal_point_preimage[OF P3 fourth])
 have h2: "(fst e,snd e)\<in>biv_support(leading_form 1 1 (?F(?F P)))"
   using fourier_diagonal_point_preimage[OF P2 h3] by simp
 show ?thesis by (rule fourier_diagonal_point_preimage[OF P1 h2, simplified])
qed

lemma preliminary_diagonal_first_point_x_bound:
 fixes P Q::"complex poly_operator" and a b::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and a: "0<a" and member: "(a,b)\<in>biv_support(leading_form 1 1 P)"
   and first: "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> fst e\<le>a"
 shows "\<forall>e\<in>biv_support(pbw_symbol P). fst e\<le>a"
proof -
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have Fpair: "is_counterexample_pair (fourier_alg_hom P) (fourier_alg_hom Q)"
   by (rule isCounterexamplePair_fourier[OF pair])
 have fm: "(b,a)\<in>biv_support(leading_form 1 1 (fourier_alg_hom P))"
   using fourier_diagonal_point_mem[OF P member] by simp
 have last: "snd e\<le>a" if "e\<in>biv_support(leading_form 1 1 (fourier_alg_hom P))" for e
   using first[OF fourier_diagonal_point_preimage[OF P that]] by simp
 have unit_bound: "(1::nat)\<le>1" by simp
 have fm_int: "(b,a)\<in>biv_support(leading_form 1 (int 1) (fourier_alg_hom P))"
   using fm by (simp only: of_nat_1)
 have last_int: "snd e\<le>a" if "e\<in>biv_support(leading_form 1 (int 1) (fourier_alg_hom P))" for e
   by (rule last) (use that in \<open>simp only: of_nat_1\<close>)
 have bound: "\<forall>e\<in>biv_support(pbw_symbol(fourier_alg_hom P)). snd e\<le>a"
   by (rule preliminary_positive_last_point_y_bound[where sigma=1 and a=b and b=a,
     OF source Fpair unit_bound fm_int last_int a])
 show ?thesis by (rule support_first_coord_le_of_fourier_second[OF P]) (use bound in blast)
qed
end
