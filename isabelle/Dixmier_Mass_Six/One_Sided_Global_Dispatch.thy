theory One_Sided_Global_Dispatch
 imports One_Sided_Diagonal_Exclusion One_Sided_Crossing_Normalization
   "One_Sided_Integer_Face"
   "HanTan_Face_Exclusion"
begin

lemma global_exact_mate_positive_grade:
 fixes P Q::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P- op_comp P Q=id"
 and side: "\<forall>e\<in>biv_support(pbw_symbol P). pair_grade e\<le>0"
 shows "\<exists>e\<in>biv_support(pbw_symbol Q). 0<pair_grade e"
proof (rule ccontr)
 assume "\<not>(\<exists>e\<in>biv_support(pbw_symbol Q). 0<pair_grade e)"
 then have Qside: "\<forall>e\<in>biv_support(pbw_symbol Q). pair_grade e\<le>0" by auto
 show False using no_exact_pair_both_nonpositive[OF P Q side Qside] exact by blast
qed

lemma oneSided_exact_pair_has_generator:
 fixes P Q::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and pn: "\<exists>d\<in>biv_support(pbw_symbol P). d\<noteq>(0,0)"
 and qn: "\<exists>d\<in>biv_support(pbw_symbol Q). d\<noteq>(0,0)"
 and ps: "(0,0)\<notin>biv_support(pbw_symbol P)" and qs: "(0,0)\<notin>biv_support(pbw_symbol Q)"
 and side: "\<forall>d\<in>biv_support(pbw_symbol P). pair_grade d\<le>0"
 and exact: "op_comp Q P- op_comp P Q=id"
 shows "(0,1)\<in>biv_support(pbw_symbol P)"
proof -
 obtain rho sigma where bracket: "biv_poisson(leading_form rho sigma Q)(leading_form rho sigma P)=1"
   using exists_integer_positive_direction_leading_bracket_one[OF P Q pn qn ps qs side exact] by blast
 show ?thesis using one_sided_leading_bracket_one_forces_generator[OF P Q side bracket] by blast
qed

lemma oneSided_exact_pair_face_dispatch:
 fixes P Q::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P- op_comp P Q=id"
 and side: "\<forall>d\<in>biv_support(pbw_symbol P). pair_grade d\<le>0"
 and pn: "\<exists>d\<in>biv_support(pbw_symbol P). d\<noteq>(0,0)"
 and qn: "\<exists>d\<in>biv_support(pbw_symbol Q). d\<noteq>(0,0)"
 and ps: "(0,0)\<notin>biv_support(pbw_symbol P)" and qs: "(0,0)\<notin>biv_support(pbw_symbol Q)"
 and other: "\<exists>d\<in>biv_support(pbw_symbol P). d\<noteq>(0,1)"
 shows "(\<exists>d\<in>biv_support(leading_form 1 (-1) P). d\<noteq>(0,1) \<and> (0,1)\<in>biv_support(leading_form 1 (-1) P)) \<or>
 (\<exists>rho sigma::int. 0<rho+sigma \<and> (0,1)\<in>biv_support(leading_form rho sigma P) \<and> (\<exists>d\<in>biv_support(leading_form rho sigma P). d\<noteq>(0,1)))"
proof -
 have positive: "\<exists>d\<in>biv_support(pbw_symbol Q). 0<pair_grade d"
   by (rule global_exact_mate_positive_grade[OF P Q exact side])
 have strict: "\<forall>d\<in>biv_support(pbw_symbol P). pair_grade d<0"
   by (rule oneSided_exact_pair_strict_grade[OF P Q exact side ps positive])
 have gen: "(0,1)\<in>biv_support(pbw_symbol P)"
   by (rule oneSided_exact_pair_has_generator[OF P Q pn qn ps qs side exact])
 show ?thesis by (rule one_sided_symbol_face_dispatch[OF strict gen other])
qed

lemma oneSided_exact_pair_grade_boundary_impossible:
 fixes P Q::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P- op_comp P Q=id"
 and gen: "(0,1)\<in>biv_support(leading_form 1 (-1) P)"
 and other: "\<exists>d\<in>biv_support(leading_form 1 (-1) P). d\<noteq>(0,1)"
 shows False
proof -
 have NQ: "-Q\<in>weyl_algebra" by (rule hantan_weyl_neg[OF Q])
 have reverse: "op_comp P (-Q)- op_comp (-Q) P=id"
   using exact by (intro ext) (simp add: op_comp_def hantan_linear_neg_image[OF weyl_linear[OF P]] fun_eq_iff)
 obtain d where d: "d\<in>biv_support(leading_form 1 (-1) P)" and dn: "d\<noteq>(0,1)" using other by blast
 have subset: "{(0,1),d}\<subseteq>biv_support(leading_form 1 (-1) P)" using gen d by blast
 have card: "1<card(biv_support(leading_form 1 (-1) P))"
   using card_mono[OF finite_biv_support subset] dn by auto
 show False by (rule hanTan_case_a2_face_impossible[OF P NQ reverse gen card])
qed

lemma oneSided_exact_pair_strict_face:
 fixes P Q::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P- op_comp P Q=id"
 and side: "\<forall>d\<in>biv_support(pbw_symbol P). pair_grade d\<le>0"
 and pn: "\<exists>d\<in>biv_support(pbw_symbol P). d\<noteq>(0,0)"
 and qn: "\<exists>d\<in>biv_support(pbw_symbol Q). d\<noteq>(0,0)"
 and ps: "(0,0)\<notin>biv_support(pbw_symbol P)" and qs: "(0,0)\<notin>biv_support(pbw_symbol Q)"
 and other: "\<exists>d\<in>biv_support(pbw_symbol P). d\<noteq>(0,1)"
 shows "\<exists>rho sigma::int. 0<rho+sigma \<and> (0,1)\<in>biv_support(leading_form rho sigma P) \<and> (\<exists>d\<in>biv_support(leading_form rho sigma P). d\<noteq>(0,1))"
 using oneSided_exact_pair_face_dispatch[OF P Q exact side pn qn ps qs other]
   oneSided_exact_pair_grade_boundary_impossible[OF P Q exact] by blast

lemma oneSided_exact_pair_strict_negative_face:
 fixes P Q::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P- op_comp P Q=id"
 and side: "\<forall>d\<in>biv_support(pbw_symbol P). pair_grade d\<le>0"
 and pn: "\<exists>d\<in>biv_support(pbw_symbol P). d\<noteq>(0,0)"
 and qn: "\<exists>d\<in>biv_support(pbw_symbol Q). d\<noteq>(0,0)"
 and ps: "(0,0)\<notin>biv_support(pbw_symbol P)" and qs: "(0,0)\<notin>biv_support(pbw_symbol Q)"
 and other: "\<exists>d\<in>biv_support(pbw_symbol P). d\<noteq>(0,1)"
 shows "\<exists>rho sigma::int. 0<rho \<and> sigma\<le>0 \<and> 0<rho+sigma \<and> (0,1)\<in>biv_support(leading_form rho sigma P) \<and>
 (\<exists>d\<in>biv_support(leading_form rho sigma P). d\<noteq>(0,1) \<and> fst d+1<snd d)"
proof -
 obtain rho sigma d where sum: "0<rho+sigma" and gen: "(0,1)\<in>biv_support(leading_form rho sigma P)"
   and d: "d\<in>biv_support(leading_form rho sigma P)" and dn: "d\<noteq>(0,1)"
   using oneSided_exact_pair_strict_face[OF P Q exact side pn qn ps qs other] by blast
 have positive: "\<exists>d\<in>biv_support(pbw_symbol Q). 0<pair_grade d" by (rule global_exact_mate_positive_grade[OF P Q exact side])
 have strict: "\<forall>d\<in>biv_support(pbw_symbol P). pair_grade d<0" by (rule oneSided_exact_pair_strict_grade[OF P Q exact side ps positive])
 have sign: "0<rho \<and> sigma\<le>0 \<and> fst d+1<snd d"
   by (rule one_sided_symbol_face_normal_sign[OF strict sum gen d dn])
 show ?thesis using sign sum gen d dn by blast
qed

lemma oneSided_exact_pair_selected_face_bracket_zero:
 fixes P Q::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P- op_comp P Q=id"
 and side: "\<forall>d\<in>biv_support(pbw_symbol P). pair_grade d\<le>0"
 and pn: "\<exists>d\<in>biv_support(pbw_symbol P). d\<noteq>(0,0)"
 and qn: "\<exists>d\<in>biv_support(pbw_symbol Q). d\<noteq>(0,0)"
 and ps: "(0,0)\<notin>biv_support(pbw_symbol P)" and qs: "(0,0)\<notin>biv_support(pbw_symbol Q)"
 and other: "\<exists>d\<in>biv_support(pbw_symbol P). d\<noteq>(0,1)"
 shows "\<exists>rho sigma::int. 0<rho \<and> sigma\<le>0 \<and> 0<rho+sigma \<and> (0,1)\<in>biv_support(leading_form rho sigma P) \<and>
 1<card(biv_support(leading_form rho sigma P)) \<and> biv_poisson(leading_form rho sigma Q)(leading_form rho sigma P)=0"
proof -
 obtain rho sigma d where rho: "0<rho" and sigma: "sigma\<le>0" and sum: "0<rho+sigma"
 and gen: "(0,1)\<in>biv_support(leading_form rho sigma P)" and d: "d\<in>biv_support(leading_form rho sigma P)" and dn: "d\<noteq>(0,1)"
   using oneSided_exact_pair_strict_negative_face[OF P Q exact side pn qn ps qs other] by blast
 have subset: "{(0,1),d}\<subseteq>biv_support(leading_form rho sigma P)" using gen d by blast
 have card: "1<card(biv_support(leading_form rho sigma P))" using card_mono[OF finite_biv_support subset] dn by auto
 have absent: "(0,0)\<notin>biv_support(leading_form rho sigma P)"
   using ps leading_support_subset[of rho sigma P] by blast
 have scalar: "biv_coeff(leading_form rho sigma P) 0 0=0"
   using absent by (simp add: biv_support_def)
 have zero: "biv_poisson(leading_form rho sigma Q)(leading_form rho sigma P)=0"
   using exactPair_leadingPoisson_zero_or_one[OF P Q sum exact]
     crossing_pair_bracket_one_impossible[OF rho sigma sum gen scalar card] by blast
 show ?thesis using rho sigma sum gen card zero by blast
qed

lemma collinear_exponents_nonpositive_vs_positive_weight:
 fixes rho sigma::int and a b::"nat\<times>nat"
 assumes an: "a\<noteq>(0,0)"
 and collinear: "snd a*fst b=fst a*snd b"
 and aw: "pair_weight rho sigma a\<le>0" and bw: "0<pair_weight rho sigma b"
 shows False
proof -
 have col: "int(snd a)*int(fst b)=int(fst a)*int(snd b)"
   using arg_cong[OF collinear, of int] by (simp only: of_nat_mult)
 have cross_x: "int(snd b)*int(fst a)=int(snd a)*int(fst b)"
   using col by (simp only: mult.commute)
 have cross_y: "int(fst b)*int(snd a)=int(fst a)*int(snd b)"
   using col by (simp only: mult.commute)
 have identity_x: "pair_weight rho sigma b*int(fst a)=pair_weight rho sigma a*int(fst b)"
 proof -
   have "pair_weight rho sigma b*int(fst a)=
     rho*int(fst b)*int(fst a)+sigma*(int(snd b)*int(fst a))"
     by (simp add: pair_weight_def algebra_simps)
   also have "...=rho*int(fst b)*int(fst a)+sigma*(int(snd a)*int(fst b))"
     by (rule arg_cong[OF cross_x])
   also have "...=pair_weight rho sigma a*int(fst b)"
     by (simp add: pair_weight_def algebra_simps)
   finally show ?thesis .
 qed
 have identity_y: "pair_weight rho sigma b*int(snd a)=pair_weight rho sigma a*int(snd b)"
 proof -
   have "pair_weight rho sigma b*int(snd a)=
     rho*(int(fst b)*int(snd a))+sigma*int(snd b)*int(snd a)"
     by (simp add: pair_weight_def algebra_simps)
   also have "...=rho*(int(fst a)*int(snd b))+sigma*int(snd b)*int(snd a)"
     by (rule arg_cong[OF cross_y])
   also have "...=pair_weight rho sigma a*int(snd b)"
     by (simp add: pair_weight_def algebra_simps)
   finally show ?thesis .
 qed
 have either: "0<fst a \<or> 0<snd a" using an by (cases a) auto
 from either show False
 proof
   assume first: "0<fst a"
   have left: "0<pair_weight rho sigma b*int(fst a)" by (rule mult_pos_pos[OF bw]) (use first in simp)
   have right: "pair_weight rho sigma a*int(fst b)\<le>0" by (rule mult_nonpos_nonneg[OF aw]) simp
   show False using identity_x left right by arith
 next
   assume second: "0<snd a"
   have left: "0<pair_weight rho sigma b*int(snd a)" by (rule mult_pos_pos[OF bw]) (use second in simp)
   have right: "pair_weight rho sigma a*int(snd b)\<le>0" by (rule mult_nonpos_nonneg[OF aw]) simp
   show False using identity_y left right by arith
 qed
qed

lemma poisson_ne_zero_of_opposite_face_weight_signs:
 fixes rho sigma m n::int and R F::"complex bivariate"
 assumes weight: "rho\<noteq>0 \<or> sigma\<noteq>0"
 and Rhom: "\<And>a. a\<in>biv_support R \<Longrightarrow> pair_weight rho sigma a=m"
 and Fhom: "\<And>b. b\<in>biv_support F \<Longrightarrow> pair_weight rho sigma b=n"
 and scalar: "(0,0)\<notin>biv_support R" and R: "R\<noteq>0" and F: "F\<noteq>0"
 and m: "m\<le>0" and n: "0<n"
 shows "biv_poisson R F\<noteq>0"
proof
 assume zero: "biv_poisson R F=0"
 obtain a b where a: "a\<in>biv_support R" and b: "b\<in>biv_support F"
 and col: "(of_nat(snd a)::complex)* of_nat(fst b)- of_nat(fst a)* of_nat(snd b)=0"
   using poisson_homogeneous_support_endpoints_collinear[OF weight Rhom Fhom R F zero] by blast
 have cast: "(of_nat(snd a*fst b)::complex)= of_nat(fst a*snd b)" using col by simp
 have colnat: "snd a*fst b=fst a*snd b" using cast by (simp only: of_nat_eq_iff)
 have an: "a\<noteq>(0,0)" using scalar a by blast
 have aw: "pair_weight rho sigma a\<le>0" using Rhom[OF a] m by simp
 have bw: "0<pair_weight rho sigma b" using Fhom[OF b] n by simp
 show False by (rule collinear_exponents_nonpositive_vs_positive_weight[OF an colnat aw bw])
qed

lemma crossing_zero_bracket_impossible_of_mate_positive_grade:
 fixes P Q::"complex poly_operator" and rho sigma::int
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and rho: "0<rho" and sigma: "sigma\<le>0" and sum: "0<rho+sigma"
 and gen: "(0,1)\<in>biv_support(leading_form rho sigma P)"
 and scalar: "(0,0)\<notin>biv_support(pbw_symbol P)"
 and positive: "\<exists>a\<in>biv_support(pbw_symbol Q). 0<pair_grade a"
 and zero: "biv_poisson(leading_form rho sigma Q)(leading_form rho sigma P)=0"
 shows False
proof -
 let ?R="leading_form rho sigma P" let ?F="leading_form rho sigma Q"
 have Pdeg: "v_degree rho sigma P=sigma" using gen by (simp add: leading_form_def weighted_component_support pair_weight_def)
 have Qdeg: "0<v_degree rho sigma Q" by (rule positive_grade_forces_positive_crossing_v_degree[OF rho sum positive])
 have Rhom: "pair_weight rho sigma a=v_degree rho sigma P" if "a\<in>biv_support ?R" for a
   using that by (simp add: leading_form_def weighted_component_support)
 have Fhom: "pair_weight rho sigma a=v_degree rho sigma Q" if "a\<in>biv_support ?F" for a
   using that by (simp add: leading_form_def weighted_component_support)
 have Rs: "(0,0)\<notin>biv_support ?R" using scalar leading_support_subset[of rho sigma P] by blast
 have Rnz: "?R\<noteq>0" using gen by auto
 have Qnz: "pbw_symbol Q\<noteq>0" using positive by auto
 have degree: "weighted_degree rho sigma (pbw_symbol Q)=bot.Value(v_degree rho sigma Q)"
   using Qnz by (cases "weighted_degree rho sigma (pbw_symbol Q)") (simp_all add: v_degree_def)
 have Fnz: "?F\<noteq>0" unfolding leading_form_def by (rule weighted_top_component_nonzero[OF degree])
 have weight: "rho\<noteq>0 \<or> sigma\<noteq>0" using rho by auto
 have Pnonpos: "v_degree rho sigma P\<le>0" using Pdeg sigma by simp
 have ne: "biv_poisson ?R ?F\<noteq>0" by (rule poisson_ne_zero_of_opposite_face_weight_signs[OF weight Rhom Fhom Rs Rnz Fnz Pnonpos Qdeg])
 have anti: "biv_poisson ?R ?F= -biv_poisson ?F ?R" by (simp add: biv_poisson_def algebra_simps)
 show False using zero anti ne by simp
qed

lemma oneSided_exact_pair_nonmonomial_impossible:
 fixes P Q::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P- op_comp P Q=id"
 and side: "\<forall>d\<in>biv_support(pbw_symbol P). pair_grade d\<le>0"
 and pn: "\<exists>d\<in>biv_support(pbw_symbol P). d\<noteq>(0,0)"
 and qn: "\<exists>d\<in>biv_support(pbw_symbol Q). d\<noteq>(0,0)"
 and ps: "(0,0)\<notin>biv_support(pbw_symbol P)" and qs: "(0,0)\<notin>biv_support(pbw_symbol Q)"
 and other: "\<exists>d\<in>biv_support(pbw_symbol P). d\<noteq>(0,1)"
 shows False
proof -
 obtain rho sigma where rho: "0<rho" and sigma: "sigma\<le>0" and sum: "0<rho+sigma"
 and gen: "(0,1)\<in>biv_support(leading_form rho sigma P)"
 and zero: "biv_poisson(leading_form rho sigma Q)(leading_form rho sigma P)=0"
   using oneSided_exact_pair_selected_face_bracket_zero[OF P Q exact side pn qn ps qs other] by blast
 have positive: "\<exists>a\<in>biv_support(pbw_symbol Q). 0<pair_grade a" by (rule global_exact_mate_positive_grade[OF P Q exact side])
 show False by (rule crossing_zero_bracket_impossible_of_mate_positive_grade[OF P Q rho sigma sum gen ps positive zero])
qed
end
