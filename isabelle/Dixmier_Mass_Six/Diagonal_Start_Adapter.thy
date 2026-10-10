theory Diagonal_Start_Adapter
 imports "GGV_Case_Field_Adapter"
   "Poisson_Diagonal_Start"
begin

lemma ggv_preliminary_no_diagonal_leading_top:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and direction: "is_direction rho sigma"
   and d: "d\<in>biv_support(leading_form rho sigma P)"
   and maximal: "\<And>x. x\<in>biv_support(leading_form rho sigma P) \<Longrightarrow> pair_grade x\<le>pair_grade d"
   and diagonal: "fst d=snd d" and positive: "0<fst d"
 shows False
proof -
 obtain F where homogeneous: "weighted_homogeneous rho sigma (rho+sigma) F"
   and companion: "biv_poisson (leading_form rho sigma P) F=leading_form rho sigma P"
   using source pair direction unfolding GGVPreliminaryCompanionInput_def by blast
 have Rhom: "pair_weight rho sigma x=v_degree rho sigma P"
   if "x\<in>biv_support(leading_form rho sigma P)" for x
   using that by (simp add: leading_form_def weighted_component_support)
 have Fhom: "pair_weight rho sigma x=rho+sigma" if "x\<in>biv_support F" for x
   using homogeneous that unfolding weighted_homogeneous_def by blast
 have sum: "rho+sigma\<noteq>0" using direction by (simp add: is_direction_def)
 show False by (rule poisson_companion_no_diagonal_homogeneous_max[OF sum Rhom Fhom companion d maximal diagonal positive])
qed

lemma preliminary_horizontal_nonpositive_is_negative:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and nonpositive: "\<And>e. e\<in>biv_support(leading_form 1 0 P) \<Longrightarrow> pair_grade e\<le>0"
   and e: "e\<in>biv_support(leading_form 1 0 P)"
 shows "pair_grade e<0"
proof (rule ccontr)
 assume bad: "\<not>pair_grade e<0"
 have zero: "pair_grade e=0" using bad nonpositive[OF e] by arith
 have diagonal: "fst e=snd e" using zero by (simp add: pair_grade_def)
 have weight: "pair_weight 1 0 e=v_degree 1 0 P"
   using e by (simp add: leading_form_def weighted_component_support)
 have direction: "is_direction 1 0" by (simp add: is_direction_def)
 have degree: "0<v_degree 1 0 P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have positive: "0<fst e" using weight degree by (simp add: pair_weight_def)
 have maximal: "pair_grade x\<le>pair_grade e" if "x\<in>biv_support(leading_form 1 0 P)" for x
   using nonpositive[OF that] by (simp only: zero)
 show False by (rule ggv_preliminary_no_diagonal_leading_top[OF source pair direction e maximal diagonal positive])
qed

end
