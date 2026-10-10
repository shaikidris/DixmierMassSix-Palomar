theory Ordered_Crossing_Selection
 imports Negative_Face_Grade
   "Subrectangular_Case_Support"
begin

lemma counterexample_diagonal_face_grade_pos:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q" and a: "a\<in>biv_support(leading_form 1 (-1) P)"
 shows "0<pair_grade a"
proof -
 obtain d where d: "d\<in>biv_support(pbw_symbol P)" and positive: "0<pair_grade d"
   using ggv_grades_opposite_proved pair by blast
 have maximal: "rationalNewtonWeight (-1) d\<le>rationalNewtonWeight (-1) a"
   using a d by (simp only: leadingForm_mem_iff_rational_slope[OF zero_less_one]; simp; blast)
 have cast: "(of_int(pair_grade d)::rat)\<le> of_int(pair_grade a)"
   using maximal by (simp add: pair_grade_def rationalNewtonWeight_def)
 have "pair_grade d\<le>pair_grade a" using cast by (simp only: of_int_le_iff)
 then show ?thesis using positive by arith
qed

lemma counterexample_diagonal_face_occupied:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q"
 shows "\<exists>a\<in>biv_support(leading_form 1 (-1) P). 0<pair_grade a"
proof -
 obtain d where d: "d\<in>biv_support(pbw_symbol P)" and positive: "0<pair_grade d"
   using ggv_grades_opposite_proved pair by blast
 have nonempty: "biv_support(pbw_symbol P)\<noteq>{}" using d by blast
 have attained: "Max(pair_grade ` biv_support(pbw_symbol P))\<in>pair_grade ` biv_support(pbw_symbol P)"
   by (rule Max_in) (use nonempty in auto)
 obtain a where a: "a\<in>biv_support(pbw_symbol P)" and ax: "pair_grade a=Max(pair_grade ` biv_support(pbw_symbol P))"
 proof (rule imageE[OF attained])
   fix a assume member: "a\<in>biv_support(pbw_symbol P)"
     and equality: "Max(pair_grade ` biv_support(pbw_symbol P))=pair_grade a"
   show thesis by (rule that[OF member equality[symmetric]])
 qed
 have top: "pair_grade e\<le>pair_grade a" if "e\<in>biv_support(pbw_symbol P)" for e
   unfolding ax by (rule Max_ge) (simp, rule imageI[OF that])
 have bound: "rationalNewtonWeight (-1) e\<le>rationalNewtonWeight (-1) a" if "e\<in>biv_support(pbw_symbol P)" for e
 proof -
   have "(of_int(pair_grade e)::rat)\<le> of_int(pair_grade a)" using top[OF that] by simp
   then show ?thesis by (simp add: pair_grade_def rationalNewtonWeight_def)
 qed
 have face: "a\<in>biv_support(leading_form 1 (-1) P)"
   by (simp only: leadingForm_mem_iff_rational_slope[OF zero_less_one]; simp only: of_int_1 of_int_minus div_by_1; rule conjI[OF a]; use bound in blast)
 show ?thesis using face counterexample_diagonal_face_grade_pos[OF pair face] by blast
qed

lemma counterexample_negative_face_slopes_nonempty_of_horizontal_terminal:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q"
   and terminal: "\<And>e. e\<in>biv_support(leading_form 1 0 P) \<Longrightarrow> pair_grade e<0"
 shows "0<length(ggv_ordered_negative_face_slopes P)"
proof -
 obtain c where c: "c\<in>biv_support(leading_form 1 (-1) P)" using counterexample_diagonal_face_occupied[OF pair] by blast
 have nonempty: "biv_support(leading_form 1 (-1) P)\<noteq>{}" using c by blast
 have attained: "Max(snd ` biv_support(leading_form 1 (-1) P))\<in>snd ` biv_support(leading_form 1 (-1) P)"
   by (rule Max_in) (use nonempty in auto)
 obtain a where a: "a\<in>biv_support(leading_form 1 (-1) P)"
   and ax: "snd a=Max(snd ` biv_support(leading_form 1 (-1) P))"
 proof (rule imageE[OF attained])
   fix a assume member: "a\<in>biv_support(leading_form 1 (-1) P)"
     and equality: "Max(snd ` biv_support(leading_form 1 (-1) P))=snd a"
   show thesis by (rule that[OF member equality[symmetric]])
 qed
 have last: "snd e\<le>snd a" if "e\<in>biv_support(leading_form 1 (-1) P)" for e
   unfolding ax by (rule Max_ge) (simp, rule imageI[OF that])
 have apos: "0<pair_grade a" by (rule counterexample_diagonal_face_grade_pos[OF pair a])
 have horizontal: "is_direction 1 0" by (simp add: is_direction_def)
 have positive: "0<v_degree 1 0 P" by (rule counterexample_vDeg_pos_all_directions[OF pair horizontal])
 have nz: "leading_form 1 0 P\<noteq>0" by (rule global_leading_form_nonzero_of_positive_degree[OF positive])
 obtain b where b: "b\<in>biv_support(leading_form 1 0 P)" using negative_boundary_support_nonempty[OF nz] by blast
 have bneg: "pair_grade b<0" by (rule terminal[OF b])
 have distinct: "a\<noteq>b" using apos bneg by auto
 have slope: "(of_int(-1::int)/ of_int(1::int)::rat)< of_int(0::int)/ of_int(1::int)" by simp
 have order: "snd a\<le>snd b \<and> (snd a=snd b \<longrightarrow> a=b)"
   by (rule leadingFace_points_ordered_by_rational_slope[OF zero_less_one zero_less_one slope a b])
 have higher: "snd a<snd b" using order distinct by auto
 have araw: "a\<in>biv_support(pbw_symbol P)" using a by (simp add: leading_form_def weighted_component_support)
 have braw: "b\<in>biv_support(pbw_symbol P)" and bmax: "\<forall>p\<in>biv_support(pbw_symbol P). rationalNewtonWeight 0 p\<le>rationalNewtonWeight 0 b"
   using b by (simp only: leadingForm_mem_iff_rational_slope[OF zero_less_one]; simp)+
 have above: "\<exists>p\<in>biv_support(pbw_symbol P). snd a<snd p" using braw higher by blast
 obtain t c where left: "-1<t"
   and maximal: "\<forall>p\<in>biv_support(pbw_symbol P). rationalNewtonWeight t p\<le>rationalNewtonWeight t a"
   and c: "c\<in>biv_support(pbw_symbol P)" and higherc: "snd a<snd c"
   and tie: "rationalNewtonWeight t c=rationalNewtonWeight t a"
   using leadingFace_exists_first_upward_tilt[where P=P and rho=1 and sigma="-1", OF zero_less_one a last above] by auto
 have strict_x: "fst a<fst b"
 proof -
   have bound: "fst a\<le>fst b" using bmax araw by (simp add: rationalNewtonWeight_def)
   have unequal: "fst a\<noteq>fst b"
   proof
     assume equal: "fst a=fst b"
     have abmax: "\<forall>p\<in>biv_support(pbw_symbol P). rationalNewtonWeight 0 p\<le>rationalNewtonWeight 0 a"
       using bmax equal by (simp add: rationalNewtonWeight_def)
     have face: "a\<in>biv_support(leading_form 1 0 P)"
       by (simp only: leadingForm_mem_iff_rational_slope[OF zero_less_one]; simp only: of_int_0 div_0; rule conjI[OF araw abmax])
     show False using terminal[OF face] apos by arith
   qed
   show ?thesis using bound unequal by arith
 qed
 have right: "t<0"
 proof (rule ccontr)
   assume "\<not>t<0" then have nonnegative: "0\<le>t" by arith
   have product: "0\<le>t*(of_nat(snd b)- of_nat(snd a))" by (rule mult_nonneg_nonneg) (use nonnegative higher in auto)
   have first: "rationalNewtonWeight t b\<le>rationalNewtonWeight t a" using maximal braw by blast
   have sx: "(of_nat(fst a)::rat)< of_nat(fst b)" using strict_x by simp
   show False using product first sx by (simp add: rationalNewtonWeight_def algebra_simps; linarith)
 qed
 have neq: "a\<noteq>c" using higherc by auto
 have entry: "t\<in>set(ggv_ordered_negative_face_slopes P)"
   using rationalSlope_two_maximizers_mem_ordered_negative_slopes[OF left right araw c _ tie neq] maximal by blast
 show ?thesis using entry by (cases "ggv_ordered_negative_face_slopes P") auto
qed

lemma counterexample_ordered_strict_crossing_of_terminal:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and terminal: "\<And>e. e\<in>biv_support(leading_form 1 0 P) \<Longrightarrow> pair_grade e<0"
 shows "\<exists>j rho s a b. j<length(ggv_ordered_negative_face_slopes P) \<and> 0<rho \<and> 0<s \<and>
   is_direction (int rho) (-int s) \<and>
   ggv_ordered_negative_face_slopes P!j=(of_int(-int s)/ of_int(int rho)::rat) \<and>
   in_direction (int rho) (-int s) P \<and> in_direction (int rho) (-int s) Q \<and>
   a\<in>biv_support(leading_form (int rho) (-int s) P) \<and>
   b\<in>biv_support(leading_form (int rho) (-int s) P) \<and>
   (\<forall>e\<in>biv_support(leading_form (int rho) (-int s) P). snd a\<le>snd e) \<and>
   (\<forall>e\<in>biv_support(leading_form (int rho) (-int s) P). snd e\<le>snd b) \<and>
   0<pair_grade a \<and> pair_grade b<0"
proof -
 let ?L="ggv_ordered_negative_face_slopes P"
 let ?bad="\<lambda>i::nat. \<exists>rho s::nat. \<exists>b. i<length ?L \<and> 0<rho \<and> 0<s \<and>
   is_direction (int rho) (-int s) \<and> ?L!i=(of_int(-int s)/ of_int(int rho)::rat) \<and>
   in_direction (int rho) (-int s) P \<and> b\<in>biv_support(leading_form (int rho) (-int s) P) \<and>
   (\<forall>e\<in>biv_support(leading_form (int rho) (-int s) P). snd e\<le>snd b) \<and> pair_grade b<0"
 have length: "0<length ?L" by (rule counterexample_negative_face_slopes_nonempty_of_horizontal_terminal[OF pair terminal])
 have exists_bad: "\<exists>i. ?bad i"
 proof -
   let ?i="length ?L-1"
   have valid: "?i<length ?L" and last: "?i+1=length ?L" using length by arith+
   have member: "?L!?i\<in>set ?L" by (rule nth_mem[OF valid])
   obtain rho s::nat where rho: "0<rho" and s: "0<s" and direction: "is_direction (int rho) (-int s)"
     and face: "in_direction (int rho) (-int s) P" and entry: "?L!?i=(of_int(-int s)/ of_int(int rho)::rat)"
     using ggv_ordered_negative_entry_nat_face[OF member] by blast
   obtain b where b: "b\<in>biv_support(leading_form (int rho) (-int s) P)"
     and horizontal: "b\<in>biv_support(leading_form 1 0 P)"
     and maximum: "\<forall>e\<in>biv_support(leading_form (int rho) (-int s) P). snd e\<le>snd b"
     using counterexample_last_negative_face_meets_horizontal[OF pair rho s direction last entry face] by blast
   have negative: "pair_grade b<0" by (rule terminal[OF horizontal])
   show ?thesis using valid rho s direction face entry b maximum negative by blast
 qed
 let ?j="LEAST i. ?bad i"
 have least_bad: "?bad ?j" by (rule LeastI_ex[where P="?bad", OF exists_bad])
 obtain rho s::nat and b where index: "?j<length ?L" and rho: "0<rho" and s: "0<s"
   and direction: "is_direction (int rho) (-int s)" and entry: "?L!?j=(of_int(-int s)/ of_int(int rho)::rat)"
   and face: "in_direction (int rho) (-int s) P" and b: "b\<in>biv_support(leading_form (int rho) (-int s) P)"
   and maximum: "\<forall>e\<in>biv_support(leading_form (int rho) (-int s) P). snd e\<le>snd b"
   and negative: "pair_grade b<0" using least_bad by blast
 have faceQ: "in_direction (int rho) (-int s) Q"
   by (rule counterexample_negative_face_direction_of_first[OF pair s direction face])
 have start: "\<exists>a. a\<in>biv_support(leading_form (int rho) (-int s) P) \<and>
   (\<forall>e\<in>biv_support(leading_form (int rho) (-int s) P). snd a\<le>snd e) \<and> 0<pair_grade a"
 proof (cases "?j=0")
   case True
   obtain c where c: "c\<in>biv_support(leading_form 1 (-1) P)" using counterexample_diagonal_face_occupied[OF pair] by blast
   have entry0: "?L!0=(of_int(-int s)/ of_int(int rho)::rat)" using entry True by simp
   obtain a where a: "a\<in>biv_support(leading_form (int rho) (-int s) P)"
     and diagonal: "a\<in>biv_support(leading_form 1 (-1) P)"
     and minimum: "\<forall>e\<in>biv_support(leading_form (int rho) (-int s) P). snd a\<le>snd e"
     using first_negative_face_meets_diagonal[OF rho s length entry0 face c] by blast
   have positive: "0<pair_grade a" by (rule counterexample_diagonal_face_grade_pos[OF pair diagonal])
   show ?thesis using a minimum positive by blast
 next
   case False
   let ?k="?j-1"
   have successor_index: "?k+1=?j" and valid: "?k<length ?L" and earlier: "?k<?j" using False index by arith+
   have member: "?L!?k\<in>set ?L" by (rule nth_mem[OF valid])
   obtain rho0 s0::nat where rho0: "0<rho0" and s0: "0<s0" and direction0: "is_direction (int rho0) (-int s0)"
     and face0: "in_direction (int rho0) (-int s0) P" and entry0: "?L!?k=(of_int(-int s0)/ of_int(int rho0)::rat)"
     using ggv_ordered_negative_entry_nat_face[OF member] by blast
   have memberj: "?L!?j\<in>set ?L" by (rule nth_mem[OF index])
   have left: "-1<(of_int(-int s0)/ of_int(int rho0)::rat)" using ggv_ordered_negative_slope_bounds[OF member] by (simp only: entry0; blast)
   have right: "(of_int(-int s)/ of_int(int rho)::rat)<0" using ggv_ordered_negative_slope_bounds[OF memberj] by (simp only: entry; blast)
   have rp0: "0<int rho0" and rp: "0<int rho" using rho0 rho by simp_all
   have next_valid: "?k+1<length ?L" using successor_index index by simp
   have next_entry: "?L!(?k+1)=(of_int(-int s)/ of_int(int rho)::rat)" using successor_index entry by simp
   obtain a where previous: "a\<in>biv_support(leading_form (int rho0) (-int s0) P)"
     and a: "a\<in>biv_support(leading_form (int rho) (-int s) P)"
     and previous_max: "\<forall>e\<in>biv_support(leading_form (int rho0) (-int s0) P). snd e\<le>snd a"
     and minimum: "\<forall>e\<in>biv_support(leading_form (int rho) (-int s) P). snd a\<le>snd e"
     using leadingFace_successor_shared_endpoint[OF rp0 rp left right next_valid entry0 next_entry face0 face] by blast
   have nz: "pair_grade a\<noteq>0"
     by (rule ggv_preliminary_negative_face_min_y_grade_ne_zero[OF source pair rho s direction a]) (use minimum in blast)
   have positive: "0<pair_grade a"
   proof (rule ccontr)
     assume "\<not>0<pair_grade a"
     then have negative_a: "pair_grade a<0" using nz by arith
     have bad_previous: "?bad ?k" using valid rho0 s0 direction0 entry0 face0 previous previous_max negative_a by blast
     have "?j\<le>?k" by (rule Least_le[where P="?bad" and k="?k", OF bad_previous])
     then show False using earlier by arith
   qed
   show ?thesis using a minimum positive by blast
 qed
 show ?thesis using index rho s direction entry face faceQ b maximum negative start by blast
qed

lemma counterexample_ordered_strict_crossing_of_horizontal_start:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and terminal: "\<exists>a\<in>biv_support(leading_form 1 0 P).
     (\<forall>e\<in>biv_support(leading_form 1 0 P). snd a\<le>snd e) \<and> pair_grade a<0"
 shows "\<exists>j rho s a b. j<length(ggv_ordered_negative_face_slopes P) \<and> 0<rho \<and> 0<s \<and>
   is_direction (int rho) (-int s) \<and>
   ggv_ordered_negative_face_slopes P!j=(of_int(-int s)/ of_int(int rho)::rat) \<and>
   in_direction (int rho) (-int s) P \<and> in_direction (int rho) (-int s) Q \<and>
   a\<in>biv_support(leading_form (int rho) (-int s) P) \<and>
   b\<in>biv_support(leading_form (int rho) (-int s) P) \<and>
   (\<forall>e\<in>biv_support(leading_form (int rho) (-int s) P). snd a\<le>snd e) \<and>
   (\<forall>e\<in>biv_support(leading_form (int rho) (-int s) P). snd e\<le>snd b) \<and>
   0<pair_grade a \<and> pair_grade b<0"
proof -
 obtain a where a: "a\<in>biv_support(leading_form 1 0 P)"
   and minimum: "\<forall>e\<in>biv_support(leading_form 1 0 P). snd a\<le>snd e"
   and negative: "pair_grade a<0" using terminal by blast
 have all: "pair_grade e<0" if "e\<in>biv_support(leading_form 1 0 P)" for e
   by (rule horizontal_min_y_negative_all[OF a _ negative that]) (use minimum in blast)
 show ?thesis by (rule counterexample_ordered_strict_crossing_of_terminal[OF source pair all])
qed
end
