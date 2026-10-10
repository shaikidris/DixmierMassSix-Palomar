theory Positive_Proportional_Mate_Descent
 imports "Positive_Shear_Mate_Descent"
   "GGV_Singleton_Diagonal_Mate"
begin

lemma preliminary_positive_singleton_finite_descent_both_rows:
 fixes P Q::"complex poly_operator" and sigma a b c d::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and sigma: "1\<le>sigma" and b: "0<b"
   and member: "(a,b)\<in>biv_support(leading_form 1 (int sigma) P)"
   and unique: "\<And>e. e\<in>biv_support(leading_form 1 (int sigma) P) \<Longrightarrow> e=(a,b)"
   and Qbound: "\<And>e. e\<in>biv_support(pbw_symbol Q) \<Longrightarrow> snd e\<le>d"
   and Qpoint: "(c,d)\<in>biv_support(pbw_symbol Q)"
 shows "\<exists>R S. is_counterexample_pair R S \<and> total_degree R=a+b \<and>
   (a,b)\<in>biv_support(pbw_symbol R) \<and>
   (\<forall>e\<in>biv_support(pbw_symbol R). snd e\<le>b) \<and>
   (\<forall>e\<in>biv_support(pbw_symbol S). snd e\<le>d) \<and> (c,d)\<in>biv_support(pbw_symbol S)"
 using pair sigma member unique Qbound Qpoint
proof (induction sigma arbitrary: P Q rule: less_induct)
 case (less sigma)
 show ?case
 proof (cases "\<exists>e\<in>biv_support(pbw_symbol P). a+b<fst e+snd e")
   case True
   obtain tau R S where tau: "1<tau" and smaller: "tau<sigma" and RS: "is_counterexample_pair R S"
     and support: "biv_support(leading_form 1 (int tau) R)={(a,b)}"
     and bound: "\<forall>e\<in>biv_support(pbw_symbol S). snd e\<le>d" and retained: "(c,d)\<in>biv_support(pbw_symbol S)"
     using preliminary_positive_descent_shear_step_with_mate_row[OF source less.prems(1,2) b less.prems(3,4) True less.prems(5,6)] by blast
   have occupied: "(a,b)\<in>biv_support(leading_form 1 (int tau) R)" by (simp add: support)
   have only: "e=(a,b)" if "e\<in>biv_support(leading_form 1 (int tau) R)" for e
     using that by (simp add: support)
   show ?thesis by (rule less.IH[OF smaller RS _ occupied only _ retained]) (use tau bound in auto)
 next
   case False
   have raw: "(a,b)\<in>biv_support(pbw_symbol P)"
     using less.prems(3) by (simp add: leading_form_def weighted_component_support)
   have upper: "fst e+snd e\<le>a+b" if "e\<in>biv_support(pbw_symbol P)" for e using False that by auto
   have degree: "total_degree P=a+b" by (rule totalDeg_eq_of_support_sum_bound[OF raw upper])
   have ybound: "\<forall>e\<in>biv_support(pbw_symbol P). snd e\<le>b"
     by (rule preliminary_positive_last_point_y_bound[OF source less.prems(1,2,3) _ b]) (use less.prems(4) in auto)
   show ?thesis by (intro exI[of _ P] exI[of _ Q]) (use less.prems(1,5,6) degree raw ybound in blast)
 qed
qed

lemma counterexample_proportional_top_rows_mate_totalDeg:
 fixes P Q::"complex poly_operator" and a b c d::nat
 assumes pair: "is_counterexample_pair P Q" and b: "0<b"
   and diagonal: "total_degree P=a+b" and point: "(a,b)\<in>biv_support(pbw_symbol P)"
   and Pbound: "\<And>e. e\<in>biv_support(pbw_symbol P) \<Longrightarrow> snd e\<le>b"
   and Qbound: "\<And>e. e\<in>biv_support(pbw_symbol Q) \<Longrightarrow> snd e\<le>d"
   and Qpoint: "(c,d)\<in>biv_support(pbw_symbol Q)" and proportional: "a*d=b*c"
 shows "total_degree Q=c+d"
proof -
 let ?R="leading_form 1 1 P" let ?S="leading_form 1 1 Q"
 have direction: "is_direction 1 1" by (simp add: is_direction_def)
 have Ppos: "0<v_degree 1 1 P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have Qpos: "0<v_degree 1 1 Q" by (rule counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF pair] direction])
 have Pweight: "v_degree 1 1 P=int(a+b)"
   by (simp only: counterexample_diagonal_weight_eq_total_degree[OF pair] diagonal)
 have facepoint: "(a,b)\<in>biv_support ?R"
   by (rule support_totalDeg_mem_diagonal_leadingForm[OF point]) (simp add: diagonal)
 have Rhom: "pair_weight 1 1 e=v_degree 1 1 P" if "e\<in>biv_support ?R" for e
   using that by (simp add: leading_form_def weighted_component_support)
 have Shom: "pair_weight 1 1 e=v_degree 1 1 Q" if "e\<in>biv_support ?S" for e
   using that by (simp add: leading_form_def weighted_component_support)
 have Rnz: "?R\<noteq>0" by (rule global_leading_form_nonzero_of_positive_degree[OF Ppos])
 have Snz: "?S\<noteq>0" by (rule global_leading_form_nonzero_of_positive_degree[OF Qpos])
 have zero: "biv_poisson ?S ?R=0" by (rule counterexample_leadingPoisson_zero_all_directions[OF pair direction])
 have anti: "biv_poisson ?R ?S= -biv_poisson ?S ?R" by (simp add: biv_poisson_def algebra_simps)
 have bracket: "biv_poisson ?R ?S=0" by (simp only: anti zero minus_zero)
 have weight_nonzero: "(1::int)\<noteq>0 \<or> (1::int)\<noteq>0" by simp
 obtain x y where x: "x\<in>biv_support ?R" and y: "y\<in>biv_support ?S"
   and minimum: "\<forall>e\<in>biv_support ?R. pair_weight 1 (-1) x\<le>pair_weight 1 (-1) e"
   and determinant: "(of_nat(snd x)::complex)* of_nat(fst y)- of_nat(fst x)* of_nat(snd y)=0"
   using poisson_homogeneous_support_endpoints_collinear[OF weight_nonzero Rhom Shom Rnz Snz bracket] by blast
 have sumx: "int(fst x)+int(snd x)=int a+int b"
   using Rhom[OF x] by (simp add: pair_weight_def Pweight)
 have minimum_at_corner: "pair_weight 1 (-1) x\<le>pair_weight 1 (-1) (a,b)"
   by (rule bspec[OF minimum facepoint])
 have perpendicular: "int(fst x)-int(snd x)\<le>int a-int b"
   using minimum_at_corner by (simp add: pair_weight_def)
 have rawx: "x\<in>biv_support(pbw_symbol P)" using x by (simp add: leading_form_def weighted_component_support)
 have xb: "snd x\<le>b" by (rule Pbound[OF rawx])
 have fstx: "fst x=a" and sndx: "snd x=b" using sumx perpendicular xb by arith+
 have cast: "(of_nat(b*fst y)::complex)= of_nat(a*snd y)"
   using determinant by (simp add: fstx sndx)
 have det: "b*fst y=a*snd y" using cast by (simp only: of_nat_eq_iff)
 have sumy: "int(fst y)+int(snd y)=v_degree 1 1 Q"
   using Shom[OF y] by (simp add: pair_weight_def)
 have degreeQ: "total_degree Q=fst y+snd y"
   using sumy counterexample_diagonal_weight_eq_total_degree[OF isCounterexamplePair_swap_neg[OF pair]] by simp
 have rawy: "y\<in>biv_support(pbw_symbol Q)" using y by (simp add: leading_form_def weighted_component_support)
 have yd: "snd y\<le>d" by (rule Qbound[OF rawy])
 have axbound: "a*snd y\<le>a*d" by (rule mult_left_mono[OF yd]) simp
 have productbound: "b*fst y\<le>b*c"
   using axbound by (simp only: det proportional)
 have xc: "fst y\<le>c" using productbound b by simp
 have upper: "total_degree Q\<le>c+d" using degreeQ xc yd by arith
 have lower: "c+d\<le>total_degree Q" using support_total_degree_bound[OF Qpoint] by simp
 show ?thesis by (rule antisym[OF upper lower])
qed

lemma preliminary_positive_proportional_finite_descent_both_degrees:
 fixes P Q::"complex poly_operator" and sigma a b c d::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and sigma: "1\<le>sigma" and b: "0<b"
   and member: "(a,b)\<in>biv_support(leading_form 1 (int sigma) P)"
   and unique: "\<And>e. e\<in>biv_support(leading_form 1 (int sigma) P) \<Longrightarrow> e=(a,b)"
   and Qbound: "\<And>e. e\<in>biv_support(pbw_symbol Q) \<Longrightarrow> snd e\<le>d"
   and Qpoint: "(c,d)\<in>biv_support(pbw_symbol Q)" and proportional: "a*d=b*c"
 shows "\<exists>R S. is_counterexample_pair R S \<and> total_degree R=a+b \<and> total_degree S=c+d"
proof -
 obtain R S where RS: "is_counterexample_pair R S" and Rdegree: "total_degree R=a+b"
   and Rpoint: "(a,b)\<in>biv_support(pbw_symbol R)"
   and Rbound: "\<forall>e\<in>biv_support(pbw_symbol R). snd e\<le>b"
   and Sbound: "\<forall>e\<in>biv_support(pbw_symbol S). snd e\<le>d"
   and Spoint: "(c,d)\<in>biv_support(pbw_symbol S)"
   using preliminary_positive_singleton_finite_descent_both_rows[OF source pair sigma b member unique Qbound Qpoint] by blast
 have Sdegree: "total_degree S=c+d"
   by (rule counterexample_proportional_top_rows_mate_totalDeg[OF RS b Rdegree Rpoint _ _ Spoint proportional])
     (use Rbound Sbound in blast)+
 show ?thesis using RS Rdegree Sdegree by blast
qed

end
