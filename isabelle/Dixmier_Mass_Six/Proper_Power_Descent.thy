theory Proper_Power_Descent
 imports Mate_Descent Leading_Powers
begin

lemma weightedDegree_eq_coe_of_vDeg_pos:
 assumes "0<v_degree rho sigma T"
 shows "weighted_degree rho sigma (pbw_symbol T)=bot.Value(v_degree rho sigma T)"
 using assms by (cases "weighted_degree rho sigma (pbw_symbol T)") (simp_all add: v_degree_def)

lemma zero_poisson_mate_power_of_no_proper_power:
 fixes P T::"complex poly_operator"
 assumes direction: "is_direction rho sigma" and pair: "is_counterexample_pair P T"
 and zero: "biv_poisson(leading_form rho sigma T)(leading_form rho sigma P)=0"
 and no_power: "\<And>d S mu. 1<d \<Longrightarrow> mu\<noteq>0 \<Longrightarrow> leading_form rho sigma P\<noteq>[:[:mu:]:]*S^d"
 shows "\<exists>nu::complex. \<exists>n::nat. nu\<noteq>0 \<and>
 v_degree rho sigma T=int(Suc n)*v_degree rho sigma P \<and>
 leading_form rho sigma T=smult [:nu:] ((leading_form rho sigma P)^Suc n)"
proof -
 have Ppos: "0<v_degree rho sigma P"
   by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have Tpos: "0<v_degree rho sigma T"
   by (rule counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF pair] direction])
 let ?m="nat(v_degree rho sigma P)" let ?omega="nat(v_degree rho sigma T)"
 have m: "0<?m" and omega: "0<?omega" using Ppos Tpos by simp_all
 have mc: "int ?m=v_degree rho sigma P" and oc: "int ?omega=v_degree rho sigma T"
   using Ppos Tpos by simp_all
 have Phom: "weighted_homogeneous rho sigma (int ?m) (leading_form rho sigma P)"
   unfolding mc leading_form_def by (rule weighted_component_homogeneous)
 have Thom: "weighted_homogeneous rho sigma (int ?omega) (leading_form rho sigma T)"
   unfolding oc leading_form_def by (rule weighted_component_homogeneous)
 have Pnz: "leading_form rho sigma P\<noteq>0"
   by (rule global_leading_form_nonzero_of_positive_degree) (use m mc in simp)
 have Tnz: "leading_form rho sigma T\<noteq>0"
   by (rule global_leading_form_nonzero_of_positive_degree) (use omega oc in simp)
 obtain c where c: "c\<noteq>0"
 and power: "(leading_form rho sigma T)^?m=[:[:c:]:]*(leading_form rho sigma P)^?omega"
   using homogeneous_poisson_power_ratio[OF m omega Tnz Pnz Thom Phom zero] by auto
 obtain nu k where nu: "nu\<noteq>0" and exponent: "?omega=?m*k"
 and shape: "leading_form rho sigma T=[:[:nu:]:]*(leading_form rho sigma P)^k"
   using scalar_power_of_no_proper_power[OF m Tnz Pnz c power no_power] by auto
 have k: "0<k" using omega exponent by (cases k) auto
 obtain n where kn: "k=Suc n" using k by (cases k) auto
 have weight: "v_degree rho sigma T=int(Suc n)*v_degree rho sigma P"
   using mc oc exponent by (simp add: kn algebra_simps)
 have face: "leading_form rho sigma T=smult [:nu:] ((leading_form rho sigma P)^Suc n)"
   using shape by (simp add: kn)
 show ?thesis by (intro exI[of _ nu] exI[of _ n]) (use nu weight face in blast)
qed

lemma counterexample_impossible_of_power_face_descent:
 fixes P Q::"complex poly_operator"
 assumes direction: "is_direction rho sigma" and pair: "is_counterexample_pair P Q"
 and one: "\<And>T. is_counterexample_pair P T \<Longrightarrow>
 biv_poisson(leading_form rho sigma T)(leading_form rho sigma P)\<noteq>1"
 and zero_power: "\<And>T. is_counterexample_pair P T \<Longrightarrow>
 biv_poisson(leading_form rho sigma T)(leading_form rho sigma P)=0 \<Longrightarrow>
 \<exists>c::complex. \<exists>n::nat. c\<noteq>0 \<and> v_degree rho sigma T=int(Suc n)*v_degree rho sigma P \<and>
 leading_form rho sigma T=smult [:c:] ((leading_form rho sigma P)^Suc n)"
 shows False
proof -
 have induction: "\<forall>T::complex poly_operator. nat(v_degree rho sigma T)=n \<longrightarrow> is_counterexample_pair P T \<longrightarrow> False" for n::nat
 proof (induction n rule: less_induct)
   case (less n)
   show ?case
   proof (intro allI impI)
     fix T::"complex poly_operator"
     assume measure: "nat(v_degree rho sigma T)=n" and counterexample: "is_counterexample_pair P T"
     have P: "P\<in>weyl_algebra" and T: "T\<in>weyl_algebra"
     and exact: "op_comp T P- op_comp P T=id"
       using counterexample by (auto simp: is_counterexample_pair_def)
     have Ppos: "0<v_degree rho sigma P"
       by (rule counterexample_vDeg_pos_all_directions[OF counterexample direction])
     have Tpos: "0<v_degree rho sigma T"
       by (rule counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF counterexample] direction])
     have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
     have alternatives: "biv_poisson(leading_form rho sigma T)(leading_form rho sigma P)=0 \<or>
       biv_poisson(leading_form rho sigma T)(leading_form rho sigma P)=1"
       by (rule exactPair_leadingPoisson_zero_or_one[OF P T sum exact])
     have zero: "biv_poisson(leading_form rho sigma T)(leading_form rho sigma P)=0"
       using alternatives one[OF counterexample] by blast
     obtain c k where c: "c\<noteq>0" and weight: "v_degree rho sigma T=int(Suc k)*v_degree rho sigma P"
     and face: "leading_form rho sigma T=smult [:c:] ((leading_form rho sigma P)^Suc k)"
       using zero_power[OF counterexample zero] by auto
     let ?T'="T-(\<lambda>p. smult c ((P ^^ Suc k) p))"
     have successor: "is_counterexample_pair P ?T'"
       by (rule isCounterexamplePair_mateSubtraction[OF counterexample])
     have next_positive: "0<v_degree rho sigma ?T'"
       by (rule counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF successor] direction])
     have Pdegree: "weighted_degree rho sigma (pbw_symbol P)=bot.Value(v_degree rho sigma P)"
       by (rule weightedDegree_eq_coe_of_vDeg_pos[OF Ppos])
     have Tdegree: "weighted_degree rho sigma (pbw_symbol T)=bot.Value(int(Suc k)*v_degree rho sigma P)"
       using weightedDegree_eq_coe_of_vDeg_pos[OF Tpos] by (simp only: weight)
     have positive: "0<int(Suc k)*v_degree rho sigma P" using Tpos by (simp only: weight)
     have drop: "v_degree rho sigma ?T'<v_degree rho sigma T"
       using mateSubtraction_weight_drop_of_power_face[OF P T c sum positive Pdegree Tdegree face]
       by (simp only: weight)
     have nonnegative: "0\<le>v_degree rho sigma ?T'" using next_positive by arith
     have nat_drop: "nat(v_degree rho sigma ?T')<nat(v_degree rho sigma T)"
       using drop by (simp only: nat_less_eq_zless[OF nonnegative])
     have smaller: "nat(v_degree rho sigma ?T')<n" using nat_drop by (simp only: measure)
     have previous: "\<forall>U::complex poly_operator. nat(v_degree rho sigma U)=nat(v_degree rho sigma ?T') \<longrightarrow>
       is_counterexample_pair P U \<longrightarrow> False"
       by (rule less.IH[OF smaller])
     show False using previous[rule_format, of ?T'] successor by simp
   qed
 qed
 have initial: "\<forall>T::complex poly_operator. nat(v_degree rho sigma T)=nat(v_degree rho sigma Q) \<longrightarrow>
   is_counterexample_pair P T \<longrightarrow> False"
   by (rule induction)
 show False using initial[rule_format, of Q] pair by simp
qed

lemma counterexample_face_is_scalar_proper_power_of_bracket_one_exclusion:
 fixes P Q::"complex poly_operator"
 assumes direction: "is_direction rho sigma" and pair: "is_counterexample_pair P Q"
 and one: "\<And>T. is_counterexample_pair P T \<Longrightarrow>
 biv_poisson(leading_form rho sigma T)(leading_form rho sigma P)\<noteq>1"
 shows "\<exists>d::nat. \<exists>S mu. 1<d \<and> mu\<noteq>0 \<and> leading_form rho sigma P=[:[:mu:]:]*S^d"
proof (rule ccontr)
 assume absent: "\<not>(\<exists>d::nat. \<exists>S mu. 1<d \<and> mu\<noteq>0 \<and> leading_form rho sigma P=[:[:mu:]:]*S^d)"
 have no_power: "leading_form rho sigma P\<noteq>[:[:mu:]:]*S^d" if "1<d" "mu\<noteq>0" for d S mu
   using absent that by blast
 show False
 proof (rule counterexample_impossible_of_power_face_descent[OF direction pair one])
   fix T assume counterexample: "is_counterexample_pair P T"
     and zero: "biv_poisson(leading_form rho sigma T)(leading_form rho sigma P)=0"
   show "\<exists>c::complex. \<exists>n::nat. c\<noteq>0 \<and> v_degree rho sigma T=int(Suc n)*v_degree rho sigma P \<and>
     leading_form rho sigma T=smult [:c:] ((leading_form rho sigma P)^Suc n)"
     by (rule zero_poisson_mate_power_of_no_proper_power[OF direction counterexample zero no_power])
 qed
qed

lemma ggv_proper_power_of_local_bracket_one_exclusion:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 and one: "\<And>T. is_counterexample_pair P T \<Longrightarrow>
 biv_poisson(leading_form rho sigma T)(leading_form rho sigma P)\<noteq>1"
 shows "\<exists>mu::complex. \<exists>k::nat. \<exists>R::complex bivariate. \<exists>m::int.
 mu\<noteq>0 \<and> 2\<le>k \<and> R\<noteq>0 \<and> weighted_homogeneous rho sigma m R \<and>
 leading_form rho sigma P=[:[:mu:]:]*R^k"
proof -
 obtain k R mu where k: "1<k" and mu: "mu\<noteq>0"
 and shape: "leading_form rho sigma P=[:[:mu:]:]*R^k"
   using counterexample_face_is_scalar_proper_power_of_bracket_one_exclusion[OF direction pair one] by auto
 have Ppos: "0<v_degree rho sigma P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have Pnz: "leading_form rho sigma P\<noteq>0" by (rule global_leading_form_nonzero_of_positive_degree[OF Ppos])
 have Rnz: "R\<noteq>0" using Pnz shape k by auto
 have support: "biv_support(leading_form rho sigma P)=biv_support(R^k)"
   by (simp add: shape biv_support_def biv_coeff_def mu)
 have Phom: "weighted_homogeneous rho sigma (v_degree rho sigma P) (leading_form rho sigma P)"
   unfolding leading_form_def by (rule weighted_component_homogeneous)
 have powerhom: "weighted_homogeneous rho sigma (v_degree rho sigma P) (R^k)"
   using Phom support by (simp only: weighted_homogeneous_def)
 have positive: "0<k" using k by arith
 obtain m where hom: "weighted_homogeneous rho sigma m R"
   using weighted_homogeneous_root_of_power[OF Rnz positive powerhom] by auto
 show ?thesis by (intro exI[of _ mu] exI[of _ k] exI[of _ R] exI[of _ m])
   (use mu k Rnz hom shape in auto)
qed

lemma ggv_proper_power_input_proved:
 "\<forall>P Q::complex poly_operator. is_counterexample_pair P Q \<longrightarrow>
 (\<forall>rho sigma::int. is_direction rho sigma \<longrightarrow>
 (\<exists>mu::complex. \<exists>k::nat. \<exists>R::complex bivariate. \<exists>m::int.
 mu\<noteq>0 \<and> 2\<le>k \<and> R\<noteq>0 \<and> weighted_homogeneous rho sigma m R \<and>
 leading_form rho sigma P=[:[:mu:]:]*R^k))"
proof (intro allI impI)
 fix P Q::"complex poly_operator" and rho sigma::int
 assume pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 show "\<exists>mu::complex. \<exists>k::nat. \<exists>R::complex bivariate. \<exists>m::int.
 mu\<noteq>0 \<and> 2\<le>k \<and> R\<noteq>0 \<and> weighted_homogeneous rho sigma m R \<and>
 leading_form rho sigma P=[:[:mu:]:]*R^k"
 proof (rule ggv_proper_power_of_local_bracket_one_exclusion[OF pair direction])
   fix T assume counterexample: "is_counterexample_pair P T"
   show "biv_poisson(leading_form rho sigma T)(leading_form rho sigma P)\<noteq>1"
     by (rule ggv_bracket_one_input_proved[OF counterexample direction])
 qed
qed

end
