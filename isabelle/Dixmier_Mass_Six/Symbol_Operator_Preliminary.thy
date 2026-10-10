theory Symbol_Operator_Preliminary
 imports "GGV_Companion_Proved"
begin

lemma symbolLinearMap_surjective:
 fixes F::"complex bivariate"
 shows "\<exists>T::complex poly_operator. T\<in>weyl_algebra \<and> pbw_symbol T=F"
proof -
 let ?T="finite_normal_sum (biv_support F) (\<lambda>u. biv_coeff F (fst u)(snd u))"
 have carrier: "?T\<in>weyl_algebra" by (rule finite_normal_sum_in_weyl[OF finite_biv_support])
 have symbol: "pbw_symbol ?T=F"
   by (simp only: pbw_symbol_finite_normal_sum[OF finite_biv_support] biv_reconstruct)
 show ?thesis by (intro exI[of _ ?T] conjI carrier symbol)
qed

lemma native_weighted_homogeneous_degree:
 assumes hom: "weighted_homogeneous rho sigma m F" and nz: "F\<noteq>0"
 shows "weighted_degree rho sigma F=bot.Value m"
proof -
 have nonempty: "biv_support F\<noteq>{}" using nz by (simp only: biv_support_empty_iff not_False_eq_True)
 obtain u where member: "u\<in>biv_support F" using nonempty by blast
 have constant_weight: "pair_weight rho sigma u=m" using hom member unfolding weighted_homogeneous_def by blast
 have attained: "m\<in>pair_weight rho sigma`biv_support F"
   by (simp only: constant_weight[symmetric]; rule imageI[OF member])
 have subset: "pair_weight rho sigma`biv_support F\<subseteq>{m}"
   using hom unfolding weighted_homogeneous_def by auto
 have weights: "pair_weight rho sigma`biv_support F={m}"
   by (rule subset_antisym[OF subset]) (use attained in auto)
 show ?thesis by (simp only: weighted_degree_def; simp add: nz nonempty weights)
qed

lemma native_homogeneous_component_self:
 assumes hom: "weighted_homogeneous rho sigma m F"
 shows "weighted_component rho sigma m F=F"
proof (rule biv_eqI)
 fix i j
 show "biv_coeff(weighted_component rho sigma m F)i j=biv_coeff F i j"
   using hom by (auto simp: weighted_component_coeff weighted_homogeneous_def biv_support_def)
qed

lemma weightedHomogeneous_symbol_has_operator:
 fixes F::"complex bivariate"
 assumes hom: "weighted_homogeneous rho sigma m F" and nz: "F\<noteq>0"
 shows "\<exists>T::complex poly_operator. T\<in>weyl_algebra \<and> pbw_symbol T=F \<and> v_degree rho sigma T=m"
proof -
 obtain T where carrier: "T\<in>weyl_algebra" and symbol: "pbw_symbol T=F"
   using symbolLinearMap_surjective[of F] by blast
 have degree: "weighted_degree rho sigma (pbw_symbol T)=bot.Value m"
   by (simp only: symbol; rule native_weighted_homogeneous_degree[OF hom nz])
 have v: "v_degree rho sigma T=m" by (simp only: v_degree_def degree; simp)
 show ?thesis by (intro exI[of _ T]) (use carrier symbol v in blast)
qed

definition GGVOperatorPreliminaryInput::bool where
 "GGVOperatorPreliminaryInput \<longleftrightarrow>
 (\<forall>P Q::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
 (\<forall>rho sigma::int. is_direction rho sigma \<longrightarrow>
 (\<exists>T::complex poly_operator. T\<in>weyl_algebra \<and> v_degree rho sigma T=rho+sigma \<and>
 weighted_homogeneous rho sigma (rho+sigma)(pbw_symbol T) \<and>
 weighted_component rho sigma (v_degree rho sigma P+v_degree rho sigma T-(rho+sigma))
   (pbw_symbol(op_comp P T-op_comp T P))=leading_form rho sigma P)))"

lemma ggv_operator_preliminary_of_symbol_input:
 assumes source: "GGVPreliminaryCompanionInput"
 shows "GGVOperatorPreliminaryInput"
 unfolding GGVOperatorPreliminaryInput_def
proof (intro allI impI)
 fix P Q::"complex poly_operator" and rho sigma::int
 assume pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 obtain F where hom: "weighted_homogeneous rho sigma (rho+sigma) F"
 and fixed: "biv_poisson(leading_form rho sigma P)F=leading_form rho sigma P"
   using source pair direction unfolding GGVPreliminaryCompanionInput_def by blast
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have positive: "0<v_degree rho sigma P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have Pnz: "leading_form rho sigma P\<noteq>0" by (rule global_leading_form_nonzero_of_positive_degree[OF positive])
 have Fnz: "F\<noteq>0" using fixed Pnz by (auto simp: biv_poisson_def)
 obtain T where T: "T\<in>weyl_algebra" and symbol: "pbw_symbol T=F" and Tdegree: "v_degree rho sigma T=rho+sigma"
   using weightedHomogeneous_symbol_has_operator[OF hom Fnz] by blast
 have Tface: "leading_form rho sigma T=F"
   by (simp only: leading_form_def Tdegree symbol native_homogeneous_component_self[OF hom])
 have bracket: "biv_poisson(leading_form rho sigma P)(leading_form rho sigma T)\<noteq>0"
   by (simp only: Tface fixed Pnz not_False_eq_True)
 have result: "v_degree rho sigma (op_comp P T-op_comp T P)=v_degree rho sigma P \<and>
   leading_form rho sigma (op_comp P T-op_comp T P)=leading_form rho sigma P"
   using leading_form_commutator[OF T P sum bracket] by (simp add: Tdegree Tface fixed)
 have component: "weighted_component rho sigma (v_degree rho sigma P+v_degree rho sigma T-(rho+sigma))
   (pbw_symbol(op_comp P T-op_comp T P))=leading_form rho sigma P"
   using result by (simp only: leading_form_def Tdegree; simp)
 show "\<exists>T::complex poly_operator. T\<in>weyl_algebra \<and> v_degree rho sigma T=rho+sigma \<and>
 weighted_homogeneous rho sigma (rho+sigma)(pbw_symbol T) \<and>
 weighted_component rho sigma (v_degree rho sigma P+v_degree rho sigma T-(rho+sigma))
   (pbw_symbol(op_comp P T-op_comp T P))=leading_form rho sigma P"
   by (intro exI[of _ T]) (use T Tdegree hom symbol component in blast)
qed

end
