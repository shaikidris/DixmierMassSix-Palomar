theory Y_Axis_Positive_Horizontal_Mass
 imports "Axis_Negative_Top_Mass"
   "Fourier_Boundary_Occupancy"
begin

lemma preliminary_y_axis_positive_horizontal_mass_ge_ten:
 fixes P Q::"complex poly_operator" and n a b::nat
 assumes source: "GGVPreliminaryCompanionInput"
 and bound: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 16\<le>total_degree R"
 and pair: "is_counterexample_pair P Q" and degree: "total_degree P=n"
 and unique: "\<And>d. d\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> d=(0,n)"
 and point: "(a,b)\<in>biv_support(pbw_symbol P)"
 and hx: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> fst d\<le>a"
 and hy: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> fst d=a \<Longrightarrow> snd d\<le>b"
 and positive: "b<a"
 shows "10\<le>weyl_mass P"
proof -
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have n: "0<n" using bound[OF pair] degree by arith
 have d: "total_degree P=0+n" using degree by simp
 have np: "0<0+n" using n by simp
 have diagonal: "(n,0)\<in>biv_support(leading_form 1 1 (fourier_alg_hom P)) \<and>
   (\<forall>d\<in>biv_support(leading_form 1 1 (fourier_alg_hom P)). d=(n,0))"
   by (rule fourier_diagonal_face_unique[OF P d np unique])
 have ap: "0<a" using positive by arith
 have fpoint: "(b,a)\<in>biv_support(pbw_symbol(fourier_alg_hom P))"
   by (rule fourier_rightmost_column_endpoint_mem[OF P ap point hx hy])
 have fbounds: "(\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom P)). snd d\<le>a) \<and>
   (\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom P)). snd d=a \<longrightarrow> fst d\<le>b)"
   by (rule fourier_rightmost_column_boundary_bounds[OF P hx hy])
 have fpair: "is_counterexample_pair (fourier_alg_hom P)(fourier_alg_hom Q)"
   by (rule isCounterexamplePair_fourier[OF pair])
 have negative: "pair_grade (b,a)<0" using positive by (simp add: pair_grade_def)
 have fmem: "(n,0)\<in>biv_support(leading_form 1 1 (fourier_alg_hom P))" using diagonal by blast
 have funique: "d=(n,0)" if "d\<in>biv_support(leading_form 1 1 (fourier_alg_hom P))" for d
   using diagonal that by blast
 have fy: "snd d\<le>snd(b,a)" if "d\<in>biv_support(pbw_symbol(fourier_alg_hom P))" for d
   using fbounds that by auto
 have fx: "fst d\<le>fst(b,a)" if "d\<in>biv_support(pbw_symbol(fourier_alg_hom P))" and "snd d=snd(b,a)" for d
   using fbounds that by auto
 have mass: "10\<le>weyl_mass(fourier_alg_hom P)"
   by (rule preliminary_axis_diagonal_negative_top_mass_ge_ten[OF source bound fpair fmem funique fpoint fy fx negative])
 show ?thesis using mass by (simp only: mass_fourierAlgHom[OF P])
qed

lemma preliminary_y_axis_positive_horizontal_caseAlternative:
 fixes P Q::"complex poly_operator" and n a b::nat
 assumes source: "GGVPreliminaryCompanionInput"
 and bound: "\<And>R S::complex poly_operator. is_counterexample_pair R S \<Longrightarrow> 16\<le>total_degree R"
 and pair: "is_counterexample_pair P Q" and degree: "total_degree P=n"
 and unique: "\<And>d. d\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> d=(0,n)"
 and point: "(a,b)\<in>biv_support(pbw_symbol P)"
 and hx: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> fst d\<le>a"
 and hy: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> fst d=a \<Longrightarrow> snd d\<le>b"
 and positive: "b<a"
 shows "case_alternative P"
proof -
 have mass: "10\<le>weyl_mass P"
   by (rule preliminary_y_axis_positive_horizontal_mass_ge_ten[OF source bound pair degree unique point hx hy positive])
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have linearP: "poly_linear P" by (rule weyl_linear[OF P])
 show ?thesis using mass linearP by (simp add: case_alternative_def)
qed

end
