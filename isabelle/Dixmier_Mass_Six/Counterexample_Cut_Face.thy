theory Counterexample_Cut_Face
 imports "Cut_Corner_Normalized_Coordinates"
   "Polynomial_Cut_Common_Weights"
   "Polynomial_Companion_Cut_Grade"
begin

lemma negative_face_cut_degree_and_end:
 fixes P::"complex poly_operator"
 assumes l: "0<l" and rho: "0<rho" and divides: "rho dvd int l" and sum: "0<rho+sigma"
 and negative: "\<exists>e\<in>biv_support(leading_form rho sigma P). pair_grade e<0"
 shows "0<degree(cut_poly rho sigma P) \<and>
   ((int l div rho)*v_degree rho sigma P)-
   (ramified_cut_exponent l rho sigma+int l)*int(degree(cut_poly rho sigma P))<0"
proof -
 obtain i j where point: "(i,j)\<in>biv_support(leading_form rho sigma P)"
   and grade: "int i<int j" using negative by (auto simp: pair_grade_def)
 have weight: "pair_weight rho sigma (i,j)=v_degree rho sigma P"
   by (rule conjunct2[OF polynomialFace_point_source_data[OF point]])
 have coefficient: "coeff(cut_poly rho sigma P)j\<noteq>0"
   using point by (simp only: cutPoly_coeff_at_face_point[OF rho weight] biv_support_def mem_Collect_eq fst_conv snd_conv; blast)
 have bound: "j\<le>degree(cut_poly rho sigma P)" by (rule le_degree[OF coefficient])
 have degree_positive: "0<degree(cut_poly rho sigma P)" using grade bound by arith
 have first: "rho*(int j-int i)>0" by (rule mult_pos_pos[OF rho]) (use grade in arith)
 have second: "0\<le>(rho+sigma)*(int(degree(cut_poly rho sigma P))-int j)"
   by (rule mult_nonneg_nonneg) (use sum bound in auto)
 have identity: "v_degree rho sigma P-(rho+sigma)*int(degree(cut_poly rho sigma P))=
   -rho*(int j-int i)-(rho+sigma)*(int(degree(cut_poly rho sigma P))-int j)"
   using weight by (simp add: pair_weight_def algebra_simps)
 have base: "v_degree rho sigma P-(rho+sigma)*int(degree(cut_poly rho sigma P))<0"
   using identity first second by linarith
 have scaled: "int l*(v_degree rho sigma P-(rho+sigma)*int(degree(cut_poly rho sigma P)))<0"
   by (rule mult_pos_neg) (use l base in auto)
 have cancellation: "rho*(int l div rho)=int l"
   using dvd_mult_div_cancel[OF divides] by (simp only: mult.commute)
 have equality: "rho*(((int l div rho)*v_degree rho sigma P)-
   (ramified_cut_exponent l rho sigma+int l)*int(degree(cut_poly rho sigma P)))=
   int l*(v_degree rho sigma P-(rho+sigma)*int(degree(cut_poly rho sigma P)))"
 proof -
   have expanded: "rho*(((int l div rho)*v_degree rho sigma P)-
     ((int l div rho)*sigma+int l)*int(degree(cut_poly rho sigma P)))=
     (rho*(int l div rho))*v_degree rho sigma P-
     ((rho*(int l div rho))*sigma+rho*int l)*int(degree(cut_poly rho sigma P))"
     by (simp only: right_diff_distrib distrib_left distrib_right mult.assoc)
   show ?thesis
   proof -
     have "rho*(((int l div rho)*v_degree rho sigma P)-
       (ramified_cut_exponent l rho sigma+int l)*int(degree(cut_poly rho sigma P)))=
       (rho*(int l div rho))*v_degree rho sigma P-
       ((rho*(int l div rho))*sigma+rho*int l)*int(degree(cut_poly rho sigma P))"
       by (simp only: ramified_cut_exponent_def expanded)
     also have "...=int l*v_degree rho sigma P-
       (int l*sigma+rho*int l)*int(degree(cut_poly rho sigma P))"
       by (simp only: cancellation)
     also have "...=int l*(v_degree rho sigma P-
       (rho+sigma)*int(degree(cut_poly rho sigma P)))"
       by (simp only: algebra_simps)
     finally show ?thesis .
   qed
 qed
 have endpoint_negative: "((int l div rho)*v_degree rho sigma P)-
   (ramified_cut_exponent l rho sigma+int l)*int(degree(cut_poly rho sigma P))<0"
 proof -
   have product_negative: "rho*(((int l div rho)*v_degree rho sigma P)-
     (ramified_cut_exponent l rho sigma+int l)*int(degree(cut_poly rho sigma P)))<0"
     using scaled by (simp only: equality)
   show ?thesis using product_negative rho by (simp only: mult_less_0_iff; arith)
 qed
 show ?thesis using degree_positive endpoint_negative by blast
qed

lemma counterexample_maxRoot_cut_positive_ratio:
 fixes P Q::"complex poly_operator" and d n::nat
 assumes l: "0<l" and pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 and rho: "0<rho" and divides: "rho dvd int l"
 and Pdir: "in_direction rho sigma P" and Qdir: "in_direction rho sigma Q"
 and threshold: "rho+sigma<v_degree rho sigma P+v_degree rho sigma Q"
 and d: "2\<le>d" and n: "2\<le>n"
 and ratio: "v_degree rho sigma Q*int d=v_degree rho sigma P*int n" and cop: "coprime n d"
 and negative: "\<exists>e\<in>biv_support(leading_form rho sigma P). pair_grade e<0"
 shows "\<exists>c r s. poly(cut_poly rho sigma P)c=0 \<and>
 rootMultiplicity c (cut_poly rho sigma P)=max_root_mult(cut_poly rho sigma P) \<and>
 is_direction r s \<and> 0<r \<and> (sigma\<le>0\<longrightarrow>s<0) \<and>
 (let U=ramified_cut_aut l rho sigma c (polynomial_ramified_lift l P);
      V=ramified_cut_aut l rho sigma c (polynomial_ramified_lift l Q);
      M=rootMultiplicity c (cut_poly rho sigma P); N=rootMultiplicity c (cut_poly rho sigma Q);
      E=((int l div rho)*v_degree rho sigma P-ramified_cut_exponent l rho sigma*int M,M);
      F=((int l div rho)*v_degree rho sigma Q-ramified_cut_exponent l rho sigma*int N,N)
 in ramified_weight l r s E=ramified_weight_deg l r s U \<and>
    ramified_weight l r s F=ramified_weight_deg l r s V \<and>
    0<ramified_weight_deg l r s U \<and> 0<ramified_weight_deg l r s V \<and>
    ramified_weight_deg l r s V*int d=ramified_weight_deg l r s U*int n \<and>
    fst E-int l*int(snd E)<0 \<and> fst F-int l*int(snd F)<0 \<and>
    (\<forall>p\<in>ramified_pbw_support l U. ramified_weight l r s p=ramified_weight_deg l r s U \<longrightarrow>
      fst E-int l*int(snd E)\<le>fst p-int l*int(snd p)) \<and>
    (\<forall>q\<in>ramified_pbw_support l V. ramified_weight l r s q=ramified_weight_deg l r s V \<longrightarrow>
      fst F-int l*int(snd F)\<le>fst q-int l*int(snd q)) \<and>
    (\<exists>BP\<in>ramified_pbw_support l U. snd BP<M \<and> ramified_weight l r s BP=ramified_weight_deg l r s U) \<and>
    (\<exists>BQ\<in>ramified_pbw_support l V. snd BQ<N \<and> ramified_weight l r s BQ=ramified_weight_deg l r s V))"
proof -
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra" and exact: "op_comp Q P-op_comp P Q=id"
   using pair unfolding is_counterexample_pair_def by blast+
 have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have cut: "0<degree(cut_poly rho sigma P)" and old_end: "((int l div rho)*v_degree rho sigma P)-
   (ramified_cut_exponent l rho sigma+int l)*int(degree(cut_poly rho sigma P))<0"
   using negative_face_cut_degree_and_end[OF l rho divides sum negative] by blast+
 have input: "GGVPreliminaryCompanionInput"
   using ggv_preliminary_companion_proved by (simp only: GGVPreliminaryCompanionInput_def)
 have grade: "((int l div rho)*v_degree rho sigma P)-
   (ramified_cut_exponent l rho sigma+int l)*int(max_root_mult(cut_poly rho sigma P))<0"
   by (rule preliminary_companion_maxRoot_cut_grade_negative[OF input l pair direction rho divides Pdir cut old_end])
 have Ppos: "0<v_degree rho sigma P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have Qpos: "0<v_degree rho sigma Q"
   by (rule counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF pair] direction])
 show ?thesis
   using exactPair_maxRoot_cut_exists_common_face_positive_ratio_and_min_grade[
     where l=l and P=P and Q=Q and rho=rho and sigma=sigma and d=d and n=n]
     l P Q direction rho divides Ppos Qpos Pdir Qdir exact threshold d n ratio cop grade
   by (simp only: Let_def; blast)
qed

end
