theory One_Sided_Global_Generation
 imports One_Sided_Global_Dispatch
   "Opposite_Grade_Generation"
   "Fourier_Generation"
   "Fourier_Grade_Mass"
begin

lemma global_exact_left_nonzero:
 fixes P Q::"complex poly_operator"
 assumes Q: "Q\<in>weyl_algebra" and exact: "op_comp Q P- op_comp P Q=id"
 shows "P\<noteq>0"
proof
 assume zero: "P=0"
 have "(id::complex poly_operator)=0"
   using exact poly_linear_zero_image[OF weyl_linear[OF Q]]
   by (simp add: zero op_comp_def fun_eq_iff)
 then show False using grade_generation_identity_nonzero by contradiction
qed

lemma global_exact_right_nonzero:
 fixes P Q::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and exact: "op_comp Q P- op_comp P Q=id"
 shows "Q\<noteq>0"
proof
 assume zero: "Q=0"
 have "(id::complex poly_operator)=0"
   using exact poly_linear_zero_image[OF weyl_linear[OF P]]
   by (simp add: zero op_comp_def fun_eq_iff)
 then show False using grade_generation_identity_nonzero by contradiction
qed

lemma global_scalar_free_nonzero_nonconstant:
 fixes P::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and nonzero: "P\<noteq>0"
 and scalar: "(0,0)\<notin>biv_support(pbw_symbol P)"
 shows "\<exists>d\<in>biv_support(pbw_symbol P). d\<noteq>(0,0)"
proof (rule ccontr)
 assume no: "\<not>(\<exists>d\<in>biv_support(pbw_symbol P). d\<noteq>(0,0))"
 have empty: "biv_support(pbw_symbol P)={}"
 proof (rule equals0I)
   fix d
   assume member: "d\<in>biv_support(pbw_symbol P)"
   have equal: "d=(0,0)"
   proof (rule ccontr)
     assume different: "d\<noteq>(0,0)"
     have "\<exists>d\<in>biv_support(pbw_symbol P). d\<noteq>(0,0)"
       by (rule bexI[where x=d]) (rule different, rule member)
     then show False using no by contradiction
   qed
   show False using member scalar equal by simp
 qed
 have symbol: "pbw_symbol P=0" using empty by simp
 have zero_carrier: "(0::complex poly_operator)\<in>weyl_algebra" by (simp add: weyl_algebra_def)
 have symbol_equal: "pbw_symbol P=pbw_symbol (0::complex poly_operator)" using symbol by simp
 have "P=0" by (rule weyl_symbol_injective[OF P zero_carrier symbol_equal])
 then show False using nonzero by contradiction
qed

lemma scalar_free_exact_pair_left_nonconstant:
 fixes P Q::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P- op_comp P Q=id"
 and scalar: "(0,0)\<notin>biv_support(pbw_symbol P)"
 shows "\<exists>d\<in>biv_support(pbw_symbol P). d\<noteq>(0,0)"
 by (rule global_scalar_free_nonzero_nonconstant[OF P global_exact_left_nonzero[OF Q exact] scalar])

lemma scalar_free_exact_pair_right_nonconstant:
 fixes P Q::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P- op_comp P Q=id"
 and scalar: "(0,0)\<notin>biv_support(pbw_symbol Q)"
 shows "\<exists>d\<in>biv_support(pbw_symbol Q). d\<noteq>(0,0)"
 by (rule global_scalar_free_nonzero_nonconstant[OF Q global_exact_right_nonzero[OF P exact] scalar])

lemma oneSided_nonpositive_exact_pair_generates:
 fixes P Q::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P- op_comp P Q=id"
 and side: "\<forall>d\<in>biv_support(pbw_symbol P). pair_grade d\<le>0"
 shows "op_adjoin {P,Q}=weyl_algebra"
proof -
 let ?P="remove_pbw_constant P" let ?Q="remove_pbw_constant Q"
 have Pc: "?P\<in>weyl_algebra" and Qc: "?Q\<in>weyl_algebra"
   by (rule remove_pbw_constant_carrier[OF P], rule remove_pbw_constant_carrier[OF Q])
 have pair: "op_comp ?Q ?P- op_comp ?P ?Q=id" by (rule remove_pbw_constant_exact_pair[OF P Q exact])
 have Pside: "\<forall>d\<in>biv_support(pbw_symbol ?P). pair_grade d\<le>0"
   by (intro ballI; rule remove_pbw_constant_preserves_nonpositive_grades[OF P]) (use side in auto)
 have Ps: "(0,0)\<notin>biv_support(pbw_symbol ?P)" by (rule remove_pbw_constant_scalar_free[OF P])
 have Qs: "(0,0)\<notin>biv_support(pbw_symbol ?Q)" by (rule remove_pbw_constant_scalar_free[OF Q])
 have Pn: "\<exists>d\<in>biv_support(pbw_symbol ?P). d\<noteq>(0,0)" by (rule scalar_free_exact_pair_left_nonconstant[OF Pc Qc pair Ps])
 have Qn: "\<exists>d\<in>biv_support(pbw_symbol ?Q). d\<noteq>(0,0)" by (rule scalar_free_exact_pair_right_nonconstant[OF Pc Qc pair Qs])
 have only: "d=(0,1)" if "d\<in>biv_support(pbw_symbol ?P)" for d
 proof (rule ccontr)
   assume "d\<noteq>(0,1)"
   then have other: "\<exists>d\<in>biv_support(pbw_symbol ?P). d\<noteq>(0,1)" using that by blast
   show False by (rule oneSided_exact_pair_nonmonomial_impossible[OF Pc Qc pair Pside Pn Qn Ps Qs other])
 qed
 have grade: "pair_grade d= -int 1" if "d\<in>biv_support(pbw_symbol ?P)" for d
   by (simp add: only[OF that] pair_grade_def)
 have positive: "0<(1::nat)" by simp
 have generation: "op_adjoin {?P,?Q}=weyl_algebra"
   by (rule pure_negative_grade_exact_pair_generates[OF Pc Qc positive grade pair])
 show ?thesis by (rule generation_of_remove_pbw_constant_generation[OF P Q generation])
qed

lemma oneSided_nonnegative_exact_pair_generates:
 fixes P Q::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P- op_comp P Q=id"
 and side: "\<forall>d\<in>biv_support(pbw_symbol P). 0\<le>pair_grade d"
 shows "op_adjoin {P,Q}=weyl_algebra"
proof -
 have Pc: "fourier_alg_hom P\<in>weyl_algebra" and Qc: "fourier_alg_hom Q\<in>weyl_algebra"
   by (rule fourier_alg_hom_closed[OF P], rule fourier_alg_hom_closed[OF Q])
 have mapped: "op_comp(fourier_alg_hom Q)(fourier_alg_hom P)- op_comp(fourier_alg_hom P)(fourier_alg_hom Q)=id"
 proof -
   have "fourier_alg_hom(op_comp Q P- op_comp P Q)=fourier_alg_hom id" using exact by simp
   then show ?thesis by (simp only: fourier_alg_hom_diff[OF fourier_weyl_comp[OF Q P] fourier_weyl_comp[OF P Q]]
     fourier_alg_hom_comp[OF Q P] fourier_alg_hom_comp[OF P Q] fourier_alg_hom_id)
 qed
 have Pside: "\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom P)). pair_grade d\<le>0"
 proof (intro ballI)
   fix d assume d: "d\<in>biv_support(pbw_symbol(fourier_alg_hom P))"
   have member: "pair_grade d\<in>uminus ` (pair_grade ` biv_support(pbw_symbol P))"
     using fourier_gradeSupport_subset[OF P] d by blast
   obtain e where e: "e\<in>biv_support(pbw_symbol P)" and eq: "pair_grade d= -pair_grade e" using member by auto
   show "pair_grade d\<le>0" using side e by (simp add: eq)
 qed
 have generated: "op_adjoin {fourier_alg_hom P,fourier_alg_hom Q}=weyl_algebra"
   by (rule oneSided_nonpositive_exact_pair_generates[OF Pc Qc mapped Pside])
 show ?thesis using adjoin_fourier_eq_top_iff[OF P Q] generated by blast
qed

lemma hanTanOneSidedGrades_proved:
 "\<forall>P Q::complex poly_operator. P\<in>weyl_algebra \<longrightarrow> Q\<in>weyl_algebra \<longrightarrow>
 op_comp Q P- op_comp P Q=id \<longrightarrow>
 ((\<forall>d\<in>biv_support(pbw_symbol P). 0\<le>pair_grade d) \<or> (\<forall>d\<in>biv_support(pbw_symbol P). pair_grade d\<le>0)) \<longrightarrow>
 op_adjoin {P,Q}=weyl_algebra"
 using oneSided_nonnegative_exact_pair_generates oneSided_nonpositive_exact_pair_generates by blast

lemma ggv_grades_opposite_proved:
 "\<forall>P Q::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
 (\<exists>d\<in>biv_support(pbw_symbol P). 0<pair_grade d) \<and> (\<exists>d\<in>biv_support(pbw_symbol P). pair_grade d<0)"
proof (intro allI impI)
 fix P Q::"complex poly_operator" assume counterexample: "is_counterexample_pair P Q"
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P- op_comp P Q=id" and nongeneration: "op_adjoin {P,Q}\<noteq>weyl_algebra"
   using counterexample by (auto simp: is_counterexample_pair_def)
 have pos: "\<exists>d\<in>biv_support(pbw_symbol P). 0<pair_grade d"
 proof (rule ccontr)
   assume "\<not>(\<exists>d\<in>biv_support(pbw_symbol P). 0<pair_grade d)"
   then have side: "\<forall>d\<in>biv_support(pbw_symbol P). pair_grade d\<le>0" by auto
   show False using oneSided_nonpositive_exact_pair_generates[OF P Q exact side] nongeneration by contradiction
 qed
 have neg: "\<exists>d\<in>biv_support(pbw_symbol P). pair_grade d<0"
 proof (rule ccontr)
   assume "\<not>(\<exists>d\<in>biv_support(pbw_symbol P). pair_grade d<0)"
   then have side: "\<forall>d\<in>biv_support(pbw_symbol P). 0\<le>pair_grade d" by auto
   show False using oneSided_nonnegative_exact_pair_generates[OF P Q exact side] nongeneration by contradiction
 qed
 show "(\<exists>d\<in>biv_support(pbw_symbol P). 0<pair_grade d) \<and> (\<exists>d\<in>biv_support(pbw_symbol P). pair_grade d<0)" using pos neg by blast
qed
end
