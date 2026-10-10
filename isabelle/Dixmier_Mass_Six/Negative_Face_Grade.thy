theory Negative_Face_Grade
 imports Negative_Face_Boundaries
   "Diagonal_Start_Adapter"
begin

lemma negative_face_min_y_max_grade:
 fixes P::"complex poly_operator" and rho s::nat
 assumes rho: "0<rho" and s: "0<s" and sum: "s<rho"
   and a: "a\<in>biv_support(leading_form (int rho) (-int s) P)"
   and minimum: "\<And>e. e\<in>biv_support(leading_form (int rho) (-int s) P) \<Longrightarrow> snd a\<le>snd e"
 shows "\<forall>e\<in>biv_support(leading_form (int rho) (-int s) P). pair_grade e\<le>pair_grade a"
proof (rule ballI)
 fix e assume e: "e\<in>biv_support(leading_form (int rho) (-int s) P)"
 have weight: "pair_weight (int rho) (-int s) e=pair_weight (int rho) (-int s) a"
   using e a by (simp add: leading_form_def weighted_component_support)
 have product: "0\<le>(int rho-int s)*(int(snd e)-int(snd a))"
   by (rule mult_nonneg_nonneg) (use sum minimum[OF e] in auto)
 have scaled: "int rho*(pair_grade e-pair_grade a)= -(int rho-int s)*(int(snd e)-int(snd a))"
   using weight by (simp add: pair_grade_def pair_weight_def algebra_simps)
 have bound: "int rho*pair_grade e\<le>int rho*pair_grade a"
   using scaled product by (simp add: algebra_simps; linarith)
 have positive: "0<int rho" using rho by simp
 show "pair_grade e\<le>pair_grade a" using bound by (simp only: mult_le_cancel_left_pos[OF positive])
qed

lemma ggv_preliminary_negative_face_min_y_grade_ne_zero:
 fixes P Q::"complex poly_operator" and rho s::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and rho: "0<rho" and s: "0<s" and direction: "is_direction (int rho) (-int s)"
   and a: "a\<in>biv_support(leading_form (int rho) (-int s) P)"
   and minimum: "\<And>e. e\<in>biv_support(leading_form (int rho) (-int s) P) \<Longrightarrow> snd a\<le>snd e"
 shows "pair_grade a\<noteq>0"
proof
 assume zero: "pair_grade a=0"
 have sum: "s<rho" using direction by (simp add: is_direction_def; arith)
 have diagonal: "fst a=snd a" using zero by (simp add: pair_grade_def)
 have degree: "0<v_degree (int rho) (-int s) P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have weight: "pair_weight (int rho) (-int s) a=v_degree (int rho) (-int s) P"
   using a by (simp add: leading_form_def weighted_component_support)
 have positive: "0<fst a"
 proof (rule ccontr)
   assume "\<not>0<fst a" then have x: "fst a=0" by arith
   have y: "snd a=0" using diagonal x by simp
   show False using weight degree by (simp add: pair_weight_def x y)
 qed
 have maximal: "pair_grade e\<le>pair_grade a" if "e\<in>biv_support(leading_form (int rho) (-int s) P)" for e
   using negative_face_min_y_max_grade[OF rho s sum a minimum] that by blast
 show False by (rule ggv_preliminary_no_diagonal_leading_top[OF source pair direction a maximal diagonal positive])
qed
end
