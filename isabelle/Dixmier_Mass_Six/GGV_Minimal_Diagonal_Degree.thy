theory GGV_Minimal_Diagonal_Degree
 imports "GGV_Linear_Shear_Minimality"
   "Homogeneous_Cut_Reconstruction"
   "Fourier_Diagonal_Endpoints"
begin

lemma degreeMinimal_full_degree_diagonal_cut_pair:
 fixes P Q::"complex poly_operator"
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
 shows "\<exists>R S. is_degree_minimal_counterexample_pair R S \<and>
   total_degree R=total_degree P \<and> total_degree S=total_degree Q \<and>
   degree(cut_poly 1 1 R)=total_degree R"
proof -
 have pair: "is_counterexample_pair P Q"
   using minimal by (simp add: is_degree_minimal_counterexample_pair_def)
 have nonzero: "cut_poly 1 1 P\<noteq>0" by (rule counterexample_diagonal_cut_ne_zero[OF pair])
 have evaluation: "\<exists>c. poly (cut_poly 1 1 P) c\<noteq>0"
   using nonzero poly_all_0_iff_0[where p="cut_poly 1 1 P"] by blast
 obtain c where c: "poly (cut_poly 1 1 P) c\<noteq>0" using evaluation by blast
 obtain A B where minAB: "is_degree_minimal_counterexample_pair A B"
   and degreeA: "total_degree A=total_degree P" and degreeB: "total_degree B=total_degree Q"
   and translate: "cut_poly 1 1 A=pcompose (cut_poly 1 1 P) [:c,1:]"
   using degreeMinimal_linear_cut_recovers_pair[OF minimal, where c=c] by blast
 have pairAB: "is_counterexample_pair A B"
   using minAB by (simp add: is_degree_minimal_counterexample_pair_def)
 have A: "A\<in>weyl_algebra" and B: "B\<in>weyl_algebra"
   using pairAB by (simp_all add: is_counterexample_pair_def)
 have constant_coefficient: "coeff(cut_poly 1 1 A) 0\<noteq>0"
   using c by (simp add: translate coeff_pcompose_0)
 have weightA: "v_degree 1 1 A=int(total_degree A)"
   by (rule counterexample_diagonal_weight_eq_total_degree[OF pairAB])
 have axis: "(total_degree A,0)\<in>biv_support(leading_form 1 1 A)"
 proof -
   have weight: "pair_weight 1 1 (total_degree A,0)=v_degree 1 1 A"
     by (simp add: pair_weight_def weightA)
   have coefficient: "biv_coeff (leading_form 1 1 A) (total_degree A) 0\<noteq>0"
     using constant_coefficient by (simp only: cutPoly_coeff_at_face_point[OF zero_less_one weight]; simp)
   show ?thesis using coefficient by (simp add: biv_support_def)
 qed
 let ?R="fourier_alg_hom A"
 let ?S="fourier_alg_hom B"
 have minRS: "is_degree_minimal_counterexample_pair ?R ?S"
   by (rule degreeMinimal_fourier_preserved[OF minAB])
 have pairRS: "is_counterexample_pair ?R ?S" by (rule isCounterexamplePair_fourier[OF pairAB])
 have point: "(0,total_degree ?R)\<in>biv_support(leading_form 1 1 ?R)"
   using fourier_diagonal_point_mem[OF A axis] by (simp add: totalDeg_fourier_eq[OF A])
 have weightR: "v_degree 1 1 ?R=int(total_degree ?R)"
   by (rule counterexample_diagonal_weight_eq_total_degree[OF pairRS])
 have weight: "pair_weight 1 1 (0,total_degree ?R)=v_degree 1 1 ?R"
   by (simp add: pair_weight_def weightR)
 have coefficient: "coeff(cut_poly 1 1 ?R)(total_degree ?R)\<noteq>0"
   using point by (simp only: cutPoly_coeff_at_face_point[OF zero_less_one weight])
     (simp add: biv_support_def)
 have full: "degree(cut_poly 1 1 ?R)=total_degree ?R"
   by (rule antisym[OF diagonal_cut_natDegree_le[OF weightR] le_degree[OF coefficient]])
 show ?thesis by (intro exI[of _ ?R] exI[of _ ?S])
   (use minRS degreeA degreeB full in \<open>simp add: totalDeg_fourier_eq[OF A] totalDeg_fourier_eq[OF B]\<close>)
qed

end
