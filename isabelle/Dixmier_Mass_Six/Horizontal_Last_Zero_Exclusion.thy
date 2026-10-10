theory Horizontal_Last_Zero_Exclusion
 imports "Fourier_Boundary_Occupancy"
   "Diagonal_Start_Adapter"
   "Counterexample_Positive_Weight"
begin

lemma preliminary_horizontal_max_y_grade_ne_zero:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
 and e: "e\<in>biv_support(leading_form 1 0 P)"
 and maximal: "\<And>d. d\<in>biv_support(leading_form 1 0 P) \<Longrightarrow> snd d\<le>snd e"
 shows "pair_grade e\<noteq>0"
proof
 assume zero: "pair_grade e=0"
 have diagonal: "fst e=snd e" using zero by (simp add: pair_grade_def)
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have raw: "e\<in>biv_support(pbw_symbol P)" and weight: "pair_weight 1 0 e=v_degree 1 0 P"
   using e by (auto simp: leading_form_def weighted_component_support)
 have nonempty: "biv_support(pbw_symbol P)\<noteq>{}" using raw by blast
 have bound: "pair_weight 1 0 d\<le>pair_weight 1 0 e" if d: "d\<in>biv_support(pbw_symbol P)" for d
 proof -
   have "pair_weight 1 0 d\<le>Max(pair_weight 1 0 ` biv_support(pbw_symbol P))"
     by (rule Max_ge) (simp, rule imageI[OF d])
   then show ?thesis using weight nonempty by (simp add: v_degree_def weighted_degree_def)
 qed
 have hx: "fst d\<le>fst e" if "d\<in>biv_support(pbw_symbol P)" for d
   using bound[OF that] by (simp add: pair_weight_def)
 have hy: "snd d\<le>snd e" if d: "d\<in>biv_support(pbw_symbol P)" and equal: "fst d=fst e" for d
 proof -
   have dw: "pair_weight 1 0 d=v_degree 1 0 P" using equal weight by (simp add: pair_weight_def)
   have df: "d\<in>biv_support(leading_form 1 0 P)"
     using d dw by (simp add: leading_form_def weighted_component_support)
   show ?thesis by (rule maximal[OF df])
 qed
 have direction: "is_direction 1 0" by (simp add: is_direction_def)
 have positive: "0<v_degree 1 0 P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have ep: "0<fst e" using positive weight by (simp add: pair_weight_def)
 let ?T="fourier_alg_hom P"
 let ?z="(snd e,fst e)"
 have point: "?z\<in>biv_support(pbw_symbol ?T)"
   by (rule fourier_rightmost_column_endpoint_mem[OF P ep]) (use raw hx hy in \<open>auto simp: prod.collapse\<close>)
 have bounds: "(\<forall>d\<in>biv_support(pbw_symbol ?T). snd d\<le>fst e) \<and>
   (\<forall>d\<in>biv_support(pbw_symbol ?T). snd d=fst e \<longrightarrow> fst d\<le>snd e)"
   by (rule fourier_rightmost_column_boundary_bounds[OF P hx hy])
 have Tnonempty: "biv_support(pbw_symbol ?T)\<noteq>{}" using point by blast
 have maximal_weight: "Max(pair_weight 0 1 ` biv_support(pbw_symbol ?T))=int(fst e)"
   by (rule Max_eqI) (simp, use bounds in \<open>auto simp: pair_weight_def\<close>, use point in \<open>auto simp: pair_weight_def intro!: image_eqI\<close>)
 have zweight: "pair_weight 0 1 ?z=v_degree 0 1 ?T"
   using maximal_weight Tnonempty by (simp add: pair_weight_def v_degree_def weighted_degree_def)
 have zface: "?z\<in>biv_support(leading_form 0 1 ?T)"
   using point zweight by (simp add: leading_form_def weighted_component_support)
 have zgmax: "pair_grade d\<le>pair_grade ?z" if df: "d\<in>biv_support(leading_form 0 1 ?T)" for d
 proof -
   have dr: "d\<in>biv_support(pbw_symbol ?T)" and dw: "pair_weight 0 1 d=v_degree 0 1 ?T"
     using df by (auto simp: leading_form_def weighted_component_support)
   have dy: "snd d=fst e" using dw zweight by (simp add: pair_weight_def)
   have dx: "fst d\<le>snd e" using bounds dr dy by blast
   show ?thesis using dx by (simp add: pair_grade_def dy)
 qed
 have Fpair: "is_counterexample_pair ?T (fourier_alg_hom Q)" by (rule isCounterexamplePair_fourier[OF pair])
 have vertical_direction: "is_direction 0 1" by (simp add: is_direction_def)
 show False by (rule ggv_preliminary_no_diagonal_leading_top[OF source Fpair vertical_direction zface zgmax])
   (use diagonal ep in auto)
qed

end
