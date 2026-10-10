theory One_Sided_Diagonal_Exclusion
 imports "One_Sided_Diagonal_Vertex"
   "One_Sided_Roof_Zero"
   "One_Sided_Generator_Extraction"
begin

lemma oneSidedSymbol_maximal_diagonal_singleton_face_of_bound:
 fixes T::"complex poly_operator" and N::nat
 assumes side: "\<forall>e\<in>biv_support(pbw_symbol T). pair_grade e\<le>0"
 and d: "d\<in>biv_support(pbw_symbol T)" and diagonal: "fst d=snd d"
 and maximal: "\<forall>e\<in>biv_support(pbw_symbol T). fst e=snd e \<longrightarrow> snd e\<le>snd d"
 and bound: "\<forall>e\<in>biv_support(pbw_symbol T). snd e<N"
 shows "biv_support(leading_form (int N) (1-int N) T)={d}"
proof -
 have coords: "\<forall>e\<in>biv_support(pbw_symbol T). fst e\<le>snd e"
   using side by (auto simp: pair_grade_def)
 have exposed: "\<forall>e\<in>biv_support(pbw_symbol T). e\<noteq>d \<longrightarrow>
   pair_weight (int N) (1-int N) e<pair_weight (int N) (1-int N) d"
   using one_sided_maximal_diagonal_exposed_of_bound[OF coords d diagonal maximal bound]
   by (simp only: diagonal_vertex_weight_pair_weight)
 have top: "pair_weight (int N) (1-int N) e\<le>pair_weight (int N) (1-int N) d"
   if "e\<in>biv_support(pbw_symbol T)" for e
   using exposed that by (cases "e=d") auto
 have member: "d\<in>biv_support(leading_form (int N) (1-int N) T)"
   by (rule symbol_maximizer_mem_leading_form[OF d top])
 have degree: "v_degree (int N) (1-int N) T=pair_weight (int N) (1-int N) d"
   using member by (simp add: leading_form_def weighted_component_support)
 have unique: "e=d" if e: "e\<in>biv_support(leading_form (int N) (1-int N) T)" for e
 proof -
   have full: "e\<in>biv_support(pbw_symbol T)"
     and weight: "pair_weight (int N) (1-int N) e=pair_weight (int N) (1-int N) d"
     using e by (simp_all add: leading_form_def weighted_component_support degree)
   show ?thesis using exposed full weight by (cases "e=d") auto
 qed
 show ?thesis using member unique by blast
qed

lemma oneSidedSymbol_maximal_diagonal_singleton_face:
 fixes T::"complex poly_operator"
 assumes side: "\<forall>e\<in>biv_support(pbw_symbol T). pair_grade e\<le>0"
 and d: "d\<in>biv_support(pbw_symbol T)" and diagonal: "fst d=snd d"
 and maximal: "\<forall>e\<in>biv_support(pbw_symbol T). fst e=snd e \<longrightarrow> snd e\<le>snd d"
 shows "\<exists>N::nat. 0<N \<and> biv_support(leading_form (int N) (1-int N) T)={d}"
proof -
 let ?N="Suc(Max(snd ` biv_support(pbw_symbol T)))"
 have bound: "\<forall>e\<in>biv_support(pbw_symbol T). snd e<?N"
 proof (intro ballI)
   fix e
   assume member: "e\<in>biv_support(pbw_symbol T)"
   have finite: "finite(snd ` biv_support(pbw_symbol T))" by simp
   have image: "snd e\<in>snd ` biv_support(pbw_symbol T)" using member by (rule imageI)
   have "snd e\<le>Max(snd ` biv_support(pbw_symbol T))" by (rule Max_ge[OF finite image])
   then show "snd e<?N" by simp
 qed
 have face: "biv_support(leading_form (int ?N) (1-int ?N) T)={d}"
   by (rule oneSidedSymbol_maximal_diagonal_singleton_face_of_bound[OF side d diagonal maximal bound])
 show ?thesis using face by blast
qed

lemma positive_grade_in_diagonal_leading_face:
 fixes T::"complex poly_operator" and N::nat
 assumes bound: "\<forall>e\<in>biv_support(pbw_symbol T). snd e<N"
 and positive: "\<exists>e\<in>biv_support(pbw_symbol T). 0<pair_grade e"
 shows "\<exists>d\<in>biv_support(leading_form (int N) (1-int N) T). 0<pair_grade d"
proof -
 have coords: "\<exists>e\<in>biv_support(pbw_symbol T). snd e<fst e"
   using positive by (auto simp: pair_grade_def)
 obtain d where d: "d\<in>biv_support(pbw_symbol T)" and grade: "snd d<fst d"
   and top: "\<forall>e\<in>biv_support(pbw_symbol T). diagonal_vertex_weight N e\<le>diagonal_vertex_weight N d"
   using positive_grade_at_diagonal_normal_max[OF finite_biv_support bound coords] by blast
 have weight: "pair_weight (int N) (1-int N) e\<le>pair_weight (int N) (1-int N) d"
   if "e\<in>biv_support(pbw_symbol T)" for e
   using top that by (simp only: diagonal_vertex_weight_pair_weight; blast)
 have face: "d\<in>biv_support(leading_form (int N) (1-int N) T)"
   by (rule symbol_maximizer_mem_leading_form[OF d weight])
 show ?thesis using face grade by (auto simp: pair_grade_def)
qed

lemma diagonal_singleton_face_poisson_ne_one:
 fixes R F::"complex bivariate"
 assumes diagonal: "fst d=snd d" and support: "biv_support R={d}"
 shows "biv_poisson R F\<noteq>1 \<and> biv_poisson F R\<noteq>1"
proof -
 have avoid_y: "(0,1)\<notin>biv_support R" and avoid_x: "(1,0)\<notin>biv_support R"
   using diagonal by (auto simp: support)
 have y: "biv_coeff R 0 1=0" and x: "biv_coeff R 1 0=0"
   using avoid_y avoid_x by (simp_all add: biv_support_def)
 have first: "biv_coeff (biv_poisson R F) 0 0=0"
   by (simp only: poisson_coeff_zero y x mult_zero_left diff_self)
 have second: "biv_coeff (biv_poisson F R) 0 0=0"
   by (simp only: poisson_coeff_zero y x mult_zero_right diff_self)
 show ?thesis using first second by (auto simp: biv_coeff_def)
qed

lemma no_exact_pair_with_maximal_diagonal_of_bound:
 fixes P Q::"complex poly_operator" and N::nat
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P- op_comp P Q=id"
 and side: "\<forall>e\<in>biv_support(pbw_symbol P). pair_grade e\<le>0"
 and positive: "\<exists>e\<in>biv_support(pbw_symbol Q). 0<pair_grade e"
 and d: "d\<in>biv_support(pbw_symbol P)" and diagonal: "fst d=snd d" and dpos: "0<fst d"
 and maximal: "\<forall>e\<in>biv_support(pbw_symbol P). fst e=snd e \<longrightarrow> snd e\<le>snd d"
 and Pbound: "\<forall>e\<in>biv_support(pbw_symbol P). snd e<N"
 and Qbound: "\<forall>e\<in>biv_support(pbw_symbol Q). snd e<N"
 shows False
proof -
 let ?r="int N" let ?s="1-int N"
 let ?R="leading_form ?r ?s P" let ?F="leading_form ?r ?s Q"
 have support: "biv_support ?R={d}"
   by (rule oneSidedSymbol_maximal_diagonal_singleton_face_of_bound[OF side d diagonal maximal Pbound])
 obtain e where e: "e\<in>biv_support ?F" and ep: "0<pair_grade e"
   using positive_grade_in_diagonal_leading_face[OF Qbound positive] by blast
 have sum: "0<?r+?s" by simp
 have alternatives: "biv_poisson ?F ?R=0 \<or> biv_poisson ?F ?R=1"
   by (rule exactPair_leadingPoisson_zero_or_one[OF P Q sum exact])
 have ne_one: "biv_poisson ?F ?R\<noteq>1"
   using diagonal_singleton_face_poisson_ne_one[OF diagonal support] by blast
 have zero: "biv_poisson ?F ?R=0" using alternatives ne_one by blast
 have dnz: "d\<noteq>(0,0)" using dpos by auto
 have enz: "e\<noteq>(0,0)" using ep by (auto simp: pair_grade_def)
 have Rnonconstant: "\<exists>a\<in>biv_support ?R. a\<noteq>(0,0)" using support dnz by blast
 have Fnonconstant: "\<exists>a\<in>biv_support ?F. a\<noteq>(0,0)" using e enz by blast
 have Rnz: "?R\<noteq>0" using support by auto
 have Fnz: "?F\<noteq>0" using e by auto
 have Rside: "\<forall>a\<in>biv_support ?R. pair_grade a\<le>0"
   by (simp add: support pair_grade_def diagonal)
 have Rhom: "pair_weight ?r ?s a=v_degree ?r ?s P" if "a\<in>biv_support ?R" for a
   using that by (simp add: leading_form_def weighted_component_support)
 have Fhom: "pair_weight ?r ?s a=v_degree ?r ?s Q" if "a\<in>biv_support ?F" for a
   using that by (simp add: leading_form_def weighted_component_support)
 have nonzero: "?r\<noteq>0 \<or> ?s\<noteq>0" by auto
 have Fpositive: "\<exists>a\<in>biv_support ?F. 0<pair_grade a" using e ep by blast
 have ne_zero: "biv_poisson ?R ?F\<noteq>0"
   by (rule poisson_ne_zero_of_homogeneous_faces_grade_separated[OF nonzero Rhom Fhom
     Rnonconstant Fnonconstant Rnz Fnz Rside Fpositive])
 have anti: "biv_poisson ?R ?F= -biv_poisson ?F ?R"
   by (simp add: biv_poisson_def algebra_simps)
 show False using ne_zero zero anti by simp
qed

lemma no_exact_pair_with_maximal_diagonal:
 fixes P Q::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P- op_comp P Q=id"
 and side: "\<forall>e\<in>biv_support(pbw_symbol P). pair_grade e\<le>0"
 and positive: "\<exists>e\<in>biv_support(pbw_symbol Q). 0<pair_grade e"
 and d: "d\<in>biv_support(pbw_symbol P)" and diagonal: "fst d=snd d" and dpos: "0<fst d"
 and maximal: "\<forall>e\<in>biv_support(pbw_symbol P). fst e=snd e \<longrightarrow> snd e\<le>snd d"
 shows False
proof -
 let ?S="biv_support(pbw_symbol P)\<union>biv_support(pbw_symbol Q)"
 let ?N="Suc(Max(snd ` ?S))"
 have bound: "snd e<?N" if "e\<in>?S" for e
 proof -
   have finite: "finite(snd ` ?S)" by simp
   have image: "snd e\<in>snd ` ?S" using that by (rule imageI)
   have "snd e\<le>Max(snd ` ?S)" by (rule Max_ge[OF finite image])
   then show ?thesis by simp
 qed
 have Pb: "\<forall>e\<in>biv_support(pbw_symbol P). snd e<?N" using bound by blast
 have Qb: "\<forall>e\<in>biv_support(pbw_symbol Q). snd e<?N" using bound by blast
 show False by (rule no_exact_pair_with_maximal_diagonal_of_bound[OF P Q exact side positive d diagonal dpos maximal Pb Qb])
qed

lemma oneSided_exact_pair_no_positive_diagonal:
 fixes P Q::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P- op_comp P Q=id"
 and side: "\<forall>e\<in>biv_support(pbw_symbol P). pair_grade e\<le>0"
 and positive: "\<exists>e\<in>biv_support(pbw_symbol Q). 0<pair_grade e"
 shows "\<not>(\<exists>d\<in>biv_support(pbw_symbol P). fst d=snd d \<and> 0<fst d)"
proof
 assume exists: "\<exists>d\<in>biv_support(pbw_symbol P). fst d=snd d \<and> 0<fst d"
 let ?S="{d\<in>biv_support(pbw_symbol P). fst d=snd d \<and> 0<fst d}"
 have finite: "finite ?S" by simp
 have nonempty: "?S\<noteq>{}" using exists by blast
 have max_member: "Max(snd ` ?S)\<in>snd ` ?S" by (rule Max_in) (use finite nonempty in auto)
 obtain d where d: "d\<in>?S" and ds: "snd d=Max(snd ` ?S)" using max_member by auto
 have maximal: "snd e\<le>snd d" if e: "e\<in>biv_support(pbw_symbol P)" and eq: "fst e=snd e" for e
 proof (cases "0<fst e")
   case True
   have member: "e\<in>?S" using e eq True by simp
   show ?thesis unfolding ds by (rule Max_ge) (use finite member in auto)
 next
   case False
   then show ?thesis using eq by arith
 qed
 show False by (rule no_exact_pair_with_maximal_diagonal[OF P Q exact side positive _ _ _])
   (use d maximal in auto)
qed

lemma oneSided_exact_pair_strict_grade:
 fixes P Q::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P- op_comp P Q=id"
 and side: "\<forall>e\<in>biv_support(pbw_symbol P). pair_grade e\<le>0"
 and scalar: "(0,0)\<notin>biv_support(pbw_symbol P)"
 and positive: "\<exists>e\<in>biv_support(pbw_symbol Q). 0<pair_grade e"
 shows "\<forall>e\<in>biv_support(pbw_symbol P). pair_grade e<0"
proof (intro ballI)
 fix e assume e: "e\<in>biv_support(pbw_symbol P)"
 have le: "pair_grade e\<le>0" using side e by blast
 show "pair_grade e<0"
 proof (rule ccontr)
   assume "\<not>pair_grade e<0"
   then have eq: "fst e=snd e" using le by (simp add: pair_grade_def; arith)
   have nonzero: "fst e\<noteq>0"
   proof
     assume zero: "fst e=0"
     have "e=(0,0)" using zero eq by (cases e) auto
     then show False using scalar e by simp
   qed
   have pos: "0<fst e" using nonzero by simp
   have forbidden: "\<not>(\<exists>d\<in>biv_support(pbw_symbol P). fst d=snd d \<and> 0<fst d)"
     by (rule oneSided_exact_pair_no_positive_diagonal[OF P Q exact side positive])
   show False using forbidden e eq pos by blast
 qed
qed

end
