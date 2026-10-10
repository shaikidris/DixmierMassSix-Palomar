theory Negative_Face_Boundaries
 imports Actual_Face_Adjacency First_Downward_Tilt
begin

lemma negative_boundary_support_nonempty:
 fixes F::"complex bivariate"
 assumes F: "F\<noteq>0"
 shows "biv_support F\<noteq>{}"
proof
 assume empty: "biv_support F={}"
 have "F=0" by (rule biv_eqI) (use empty in \<open>auto simp: biv_support_def\<close>)
 then show False using F by contradiction
qed

lemma counterexample_last_negative_face_meets_horizontal:
 fixes P Q::"complex poly_operator" and rho s j::nat
 assumes pair: "is_counterexample_pair P Q" and rho: "0<rho" and s: "0<s"
   and direction: "is_direction (int rho) (-int s)"
   and index: "j+1=length(ggv_ordered_negative_face_slopes P)"
   and entry: "ggv_ordered_negative_face_slopes P!j=(of_int(-int s)/ of_int(int rho)::rat)"
   and face: "in_direction (int rho) (-int s) P"
 shows "\<exists>a. a\<in>biv_support(leading_form (int rho) (-int s) P) \<and>
   a\<in>biv_support(leading_form 1 0 P) \<and>
   (\<forall>p\<in>biv_support(leading_form (int rho) (-int s) P). snd p\<le>snd a)"
proof -
 let ?S="biv_support(leading_form (int rho) (-int s) P)"
 let ?t1="(of_int(-int s)/ of_int(int rho)::rat)"
 have nonempty: "?S\<noteq>{}" using face by (auto simp: in_direction_def)
 have attained: "Max(snd ` ?S)\<in>snd ` ?S" by (rule Max_in) (use nonempty in auto)
 obtain a where a: "a\<in>?S" and ax: "snd a=Max(snd ` ?S)"
 proof (rule imageE[OF attained])
   fix a assume member: "a\<in>?S" and equality: "Max(snd ` ?S)=snd a"
   show thesis by (rule that[OF member equality[symmetric]])
 qed
 have last: "snd p\<le>snd a" if "p\<in>?S" for p unfolding ax by (rule Max_ge) (simp, rule imageI[OF that])
 have horizontal: "is_direction 1 0" by (simp add: is_direction_def)
 have degree: "0<v_degree 1 0 P" by (rule counterexample_vDeg_pos_all_directions[OF pair horizontal])
 have nz: "leading_form 1 0 P\<noteq>0" by (rule global_leading_form_nonzero_of_positive_degree[OF degree])
 obtain b where b: "b\<in>biv_support(leading_form 1 0 P)" using negative_boundary_support_nonempty[OF nz] by blast
 have rho_int: "0<int rho" using rho by simp
 have slope: "?t1<(of_int(0::int)/ of_int(1::int)::rat)" using rho s by simp
 have order: "snd a\<le>snd b \<and> (snd a=snd b \<longrightarrow> a=b)"
   by (rule leadingFace_points_ordered_by_rational_slope[OF rho_int zero_less_one slope a b])
 have ahorizontal: "a\<in>biv_support(leading_form 1 0 P)"
 proof (cases "snd a<snd b")
   case False
   have "a=b" using order False by auto
   then show ?thesis using b by simp
 next
   case True
   have araw: "a\<in>biv_support(pbw_symbol P)" using a by (simp add: leading_form_def weighted_component_support)
   have braw: "b\<in>biv_support(pbw_symbol P)" and bmax: "\<forall>p\<in>biv_support(pbw_symbol P). rationalNewtonWeight 0 p\<le>rationalNewtonWeight 0 b"
     using b by (simp only: leadingForm_mem_iff_rational_slope[OF zero_less_one]; simp)+
   have above: "\<exists>p\<in>biv_support(pbw_symbol P). snd a<snd p" using braw True by blast
   obtain t c where after: "?t1<t"
     and maximal: "\<forall>p\<in>biv_support(pbw_symbol P). rationalNewtonWeight t p\<le>rationalNewtonWeight t a"
     and c: "c\<in>biv_support(pbw_symbol P)" and higher: "snd a<snd c"
     and tie: "rationalNewtonWeight t c=rationalNewtonWeight t a"
     using leadingFace_exists_first_upward_tilt[OF rho_int a last above] by blast
   have before: "t\<le>0"
   proof (rule ccontr)
     assume "\<not>t\<le>0" then have positive: "0<t" by arith
     have later: "rationalNewtonWeight 0 a\<le>rationalNewtonWeight 0 b" using bmax araw by blast
     have first: "rationalNewtonWeight t b\<le>rationalNewtonWeight t a" using maximal braw by blast
     have product: "0<t*(of_nat(snd b)- of_nat(snd a))" by (rule mult_pos_pos) (use positive True in auto)
     show False using first later product by (simp add: rationalNewtonWeight_def algebra_simps; linarith)
   qed
   have valid: "j<length(ggv_ordered_negative_face_slopes P)" using index by arith
   have member: "ggv_ordered_negative_face_slopes P!j\<in>set(ggv_ordered_negative_face_slopes P)" by (rule nth_mem[OF valid])
   have left: "-1<?t1" using ggv_ordered_negative_slope_bounds[OF member] by (simp only: entry; blast)
   have zero: "t=0"
   proof (rule ccontr)
     assume "t\<noteq>0"
     then have right: "t<0" using before by arith
     have lt: "-1<t" using left after by arith
     have distinct: "a\<noteq>c" using higher by auto
     have entry_t: "t\<in>set(ggv_ordered_negative_face_slopes P)"
       using rationalSlope_two_maximizers_mem_ordered_negative_slopes[OF lt right araw c _ tie distinct] maximal by blast
     have "t\<le>ggv_ordered_negative_face_slopes P!j"
       by (rule sortedLT_mem_le_last[OF ggv_ordered_negative_slopes_strict index entry_t])
     then show False using after by (simp only: entry; arith)
   qed
   show ?thesis by (simp only: leadingForm_mem_iff_rational_slope[OF zero_less_one]; simp only: of_int_0 of_int_1 div_0; rule conjI[OF araw]; use maximal zero in blast)
 qed
 show ?thesis using a ahorizontal last by blast
qed

lemma first_negative_face_meets_diagonal:
 fixes P::"complex poly_operator" and rho s::nat
 assumes rho: "0<rho" and s: "0<s"
   and nonempty: "0<length(ggv_ordered_negative_face_slopes P)"
   and entry: "ggv_ordered_negative_face_slopes P!0=(of_int(-int s)/ of_int(int rho)::rat)"
   and face: "in_direction (int rho) (-int s) P"
   and b: "b\<in>biv_support(leading_form 1 (-1) P)"
 shows "\<exists>a. a\<in>biv_support(leading_form (int rho) (-int s) P) \<and>
   a\<in>biv_support(leading_form 1 (-1) P) \<and>
   (\<forall>p\<in>biv_support(leading_form (int rho) (-int s) P). snd a\<le>snd p)"
proof -
 let ?S="biv_support(leading_form (int rho) (-int s) P)" let ?t1="(of_int(-int s)/ of_int(int rho)::rat)"
 have Sne: "?S\<noteq>{}" using face by (auto simp: in_direction_def)
 have attained: "Min(snd ` ?S)\<in>snd ` ?S" by (rule Min_in) (use Sne in auto)
 obtain a where a: "a\<in>?S" and ax: "snd a=Min(snd ` ?S)"
 proof (rule imageE[OF attained])
   fix a assume member: "a\<in>?S" and equality: "Min(snd ` ?S)=snd a"
   show thesis by (rule that[OF member equality[symmetric]])
 qed
 have first: "snd a\<le>snd p" if "p\<in>?S" for p unfolding ax by (rule Min_le) (simp, rule imageI[OF that])
 have member: "ggv_ordered_negative_face_slopes P!0\<in>set(ggv_ordered_negative_face_slopes P)" by (rule nth_mem[OF nonempty])
 have left: "-1<?t1" and right: "?t1<0" using ggv_ordered_negative_slope_bounds[OF member] by (simp only: entry; blast)+
 have rho_int: "0<int rho" using rho by simp
 have slope: "(of_int(-1::int)/ of_int(1::int)::rat)<?t1" using left by simp
 have order: "snd b\<le>snd a \<and> (snd b=snd a \<longrightarrow> b=a)"
   by (rule leadingFace_points_ordered_by_rational_slope[OF zero_less_one rho_int slope b a])
 have adiagonal: "a\<in>biv_support(leading_form 1 (-1) P)"
 proof (cases "snd b<snd a")
   case False
   have "b=a" using order False by auto
   then show ?thesis using b by simp
 next
   case True
   have araw: "a\<in>biv_support(pbw_symbol P)" using a by (simp add: leading_form_def weighted_component_support)
   have braw: "b\<in>biv_support(pbw_symbol P)" and bmax: "\<forall>p\<in>biv_support(pbw_symbol P). rationalNewtonWeight (-1) p\<le>rationalNewtonWeight (-1) b"
     using b by (simp only: leadingForm_mem_iff_rational_slope[OF zero_less_one]; simp)+
   have below: "\<exists>p\<in>biv_support(pbw_symbol P). snd p<snd a" using braw True by blast
   obtain t c where before: "t<?t1"
     and maximal: "\<forall>p\<in>biv_support(pbw_symbol P). rationalNewtonWeight t p\<le>rationalNewtonWeight t a"
     and c: "c\<in>biv_support(pbw_symbol P)" and lower: "snd c<snd a"
     and tie: "rationalNewtonWeight t c=rationalNewtonWeight t a"
     using leadingFace_exists_first_downward_tilt[OF rho_int a first below] by blast
   have after: "-1\<le>t"
   proof (rule ccontr)
     assume "\<not>-1\<le>t" then have less: "t< -1" by arith
     have diagonal: "rationalNewtonWeight (-1) a\<le>rationalNewtonWeight (-1) b" using bmax araw by blast
     have first_bound: "rationalNewtonWeight t b\<le>rationalNewtonWeight t a" using maximal braw by blast
     have product: "0<(-1-t)*(of_nat(snd a)- of_nat(snd b))" by (rule mult_pos_pos) (use less True in auto)
     show False using first_bound diagonal product by (simp add: rationalNewtonWeight_def algebra_simps; linarith)
   qed
   have equal: "t= -1"
   proof (rule ccontr)
     assume "t\<noteq> -1"
     then have lt: "-1<t" using after by arith
     have rt: "t<0" using before right by arith
     have distinct: "a\<noteq>c" using lower by auto
     have entry_t: "t\<in>set(ggv_ordered_negative_face_slopes P)"
       using rationalSlope_two_maximizers_mem_ordered_negative_slopes[OF lt rt araw c _ tie distinct] maximal by blast
     have "ggv_ordered_negative_face_slopes P!0\<le>t"
       by (rule sortedLT_first_le_mem[OF ggv_ordered_negative_slopes_strict nonempty entry_t])
     then show False using before by (simp only: entry; arith)
   qed
   show ?thesis by (simp only: leadingForm_mem_iff_rational_slope[OF zero_less_one]; simp only: of_int_1 of_int_minus div_by_1; rule conjI[OF araw]; use maximal equal in blast)
 qed
 show ?thesis using a adiagonal first by blast
qed
end
