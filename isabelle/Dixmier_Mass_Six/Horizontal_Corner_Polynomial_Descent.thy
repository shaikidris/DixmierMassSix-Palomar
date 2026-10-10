theory Horizontal_Corner_Polynomial_Descent
 imports "Horizontal_Corner_Full_Root"
   "Polynomial_Cut_Common_Weights"
   "Polynomial_Lift_Face_Transport"
begin

lemma lifted_two_top_orders_InDir:
 fixes T::"complex poly_operator" and E B::"int\<times>nat"
 assumes T: "T\<in>weyl_algebra" and positive: "0<v_degree rho sigma T"
 and E: "E\<in>ramified_pbw_support 1 (polynomial_ramified_lift 1 T)"
 and B: "B\<in>ramified_pbw_support 1 (polynomial_ramified_lift 1 T)"
 and Et: "ramified_weight 1 rho sigma E=ramified_weight_deg 1 rho sigma (polynomial_ramified_lift 1 T)"
 and Bt: "ramified_weight 1 rho sigma B=ramified_weight_deg 1 rho sigma (polynomial_ramified_lift 1 T)"
 and order: "snd B<snd E"
 shows "in_direction rho sigma T"
proof -
 have one: "0<(1::nat)" by simp
 obtain i where i: "fst E=int i"
   using polynomialRamifiedLift_support_iff_symbol[OF one T, where k="fst E" and j="snd E"] E
   by (auto simp: prod.collapse)
 obtain j where j: "fst B=int j"
   using polynomialRamifiedLift_support_iff_symbol[OF one T, where k="fst B" and j="snd B"] B
   by (auto simp: prod.collapse)
 have e: "(i,snd E)\<in>biv_support (leading_form rho sigma T)"
   using E Et polynomialRamifiedLift_leading_support_iff[OF one T positive, where i=i and j="snd E"]
   by (simp add: i[symmetric] prod.collapse)
 have b: "(j,snd B)\<in>biv_support (leading_form rho sigma T)"
   using B Bt polynomialRamifiedLift_leading_support_iff[OF one T positive, where i=j and j="snd B"]
   by (simp add: j[symmetric] prod.collapse)
 have distinct: "(i,snd E)\<noteq>(j,snd B)" using order by auto
 have subset: "{(i,snd E),(j,snd B)}\<subseteq>biv_support (leading_form rho sigma T)"
   using e b by auto
 have card: "card {(i,snd E),(j,snd B)}\<le>card(biv_support (leading_form rho sigma T))"
   by (rule card_mono[OF finite_biv_support subset])
 show ?thesis using card distinct by (simp add: in_direction_def)
qed

lemma horizontal_corner_polynomial_descent:
 fixes P Q::"complex poly_operator" and a b d n h::nat
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction 1 0"
 and Pdir: "in_direction 1 0 P" and Qdir: "in_direction 1 0 Q"
 and d: "1<d" and n: "1<n" and h: "2\<le>h"
 and a: "a=d*(h-1)" and b: "b=d*h"
 and endpt: "(a,b)\<in>biv_support (leading_form 1 0 P)"
 and minimum: "\<And>e. e\<in>biv_support (leading_form 1 0 P) \<Longrightarrow> pair_grade(a,b)\<le>pair_grade e"
 and weights: "v_degree 1 0 Q*int d=v_degree 1 0 P*int n" and cop: "coprime n d"
 shows "\<exists>c R S r s. is_counterexample_pair R S \<and> is_direction r s \<and> 0<r \<and> s<0 \<and>
   polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 P) \<and>
   polynomial_ramified_lift 1 S=ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 Q) \<and>
   in_direction r s R \<and> in_direction r s S \<and>
   (a,b)\<in>biv_support (leading_form r s R) \<and>
   (\<forall>e\<in>biv_support (leading_form r s R). pair_grade(a,b)\<le>pair_grade e) \<and>
   0<v_degree r s R \<and> 0<v_degree r s S \<and>
   v_degree r s S*int d=v_degree r s R*int n"
proof -
 have one: "0<(1::nat)" by simp
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
   using pair unfolding is_counterexample_pair_def by blast+
 have exact: "op_comp Q P-op_comp P Q=id"
   using pair unfolding is_counterexample_pair_def by blast
 have Ppos: "0<v_degree 1 0 P"
   by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have Qpos: "0<v_degree 1 0 Q"
   by (rule counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF pair] direction])
 have sum: "1<v_degree 1 0 P+v_degree 1 0 Q" using Ppos Qpos by arith
 have hom: "weighted_homogeneous 1 0 (v_degree 1 0 P) (leading_form 1 0 P)"
   unfolding leading_form_def by (rule weighted_component_homogeneous)
 have endpoint_weight: "pair_weight 1 0 (a,b)=v_degree 1 0 P"
   using hom endpt unfolding weighted_homogeneous_def by blast
 have weight: "v_degree 1 0 P=int a"
   using endpoint_weight by (simp only: pair_weight_def fst_conv snd_conv mult_1_left mult_zero_left add_0_right)
 have maximum: "max_root_mult(cut_poly 1 0 P)=b"
   by (rule horizontal_corner_maxRoot_eq_degree[OF pair direction Pdir Qdir d n h a b endpt minimum weights cop])
 have ab: "a<b" using a b d h by simp
 have negative: "((int 1 div 1)*v_degree 1 0 P)-
   (ramified_cut_exponent 1 1 0+int 1)*int(max_root_mult(cut_poly 1 0 P))<0"
   using ab by (simp add: ramified_cut_exponent_def maximum weight)
 obtain c r s BP BQ where selected: "rootMultiplicity c (cut_poly 1 0 P)=max_root_mult(cut_poly 1 0 P)"
 and newdir: "is_direction r s" and r: "0<r" and s: "s<0"
 and Et: "ramified_weight 1 r s (v_degree 1 0 P,rootMultiplicity c (cut_poly 1 0 P))=
   ramified_weight_deg 1 r s (ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 P))"
 and Ft: "ramified_weight 1 r s (v_degree 1 0 Q,rootMultiplicity c (cut_poly 1 0 Q))=
   ramified_weight_deg 1 r s (ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 Q))"
 and ratio: "ramified_weight_deg 1 r s (ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 Q))*int d=
   ramified_weight_deg 1 r s (ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 P))*int n"
 and BP: "BP\<in>ramified_pbw_support 1 (ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 P))"
 and BPlow: "snd BP<rootMultiplicity c (cut_poly 1 0 P)"
 and BPt: "ramified_weight 1 r s BP=ramified_weight_deg 1 r s (ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 P))"
 and BQ: "BQ\<in>ramified_pbw_support 1 (ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 Q))"
 and BQlow: "snd BQ<rootMultiplicity c (cut_poly 1 0 Q)"
 and BQt: "ramified_weight 1 r s BQ=ramified_weight_deg 1 r s (ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 Q))"
   using exactPair_maxRoot_cut_exists_common_face_positive_ratio[where l=1 and P=P and Q=Q and rho=1 and sigma=0 and d=d and n=n]
     one P Q direction Ppos Qpos Pdir Qdir exact sum d n weights cop negative
   by (auto simp: Let_def ramified_cut_exponent_def)
 obtain R S where newpair: "is_counterexample_pair R S"
 and liftR: "polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 P)"
 and liftS: "polynomial_ramified_lift 1 S=ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 Q)"
   using horizontal_cut_recovers_polynomial_counterexample[OF pair, where c=c] by blast
 have R: "R\<in>weyl_algebra" and S: "S\<in>weyl_algebra"
   using newpair unfolding is_counterexample_pair_def by blast+
 have Rpos: "0<v_degree r s R"
   by (rule counterexample_vDeg_pos_all_directions[OF newpair newdir])
 have Spos: "0<v_degree r s S"
   by (rule counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF newpair] newdir])
 have cut_endpointP: "(int a,b)\<in>ramified_pbw_support 1
   (ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 P))"
   using polynomialRamifiedCut_root_start_on_old_face[where l=1 and P=P and rho=1 and sigma=0 and i=a and j=b and c=c, simplified]
     one P endpt by (auto simp: ramified_cut_exponent_def selected maximum weight)
 have endpointP: "(int a,b)\<in>ramified_pbw_support 1 (polynomial_ramified_lift 1 R)"
   using cut_endpointP by (simp only: liftR)
 have nonemptyQ: "biv_support (leading_form 1 0 Q)\<noteq>{}"
   using Qdir by (auto simp: in_direction_def)
 obtain i j where Qend: "(i,j)\<in>biv_support (leading_form 1 0 Q)"
   using nonemptyQ by (metis all_not_in_conv prod.exhaust)
 have cut_endpointQ: "(v_degree 1 0 Q,rootMultiplicity c (cut_poly 1 0 Q))
   \<in>ramified_pbw_support 1 (ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 Q))"
   using polynomialRamifiedCut_root_start_on_old_face[where l=1 and P=Q and rho=1 and sigma=0 and i=i and j=j and c=c, simplified]
     one Q Qend by (auto simp: ramified_cut_exponent_def)
 have endpointQ: "(v_degree 1 0 Q,rootMultiplicity c (cut_poly 1 0 Q))
   \<in>ramified_pbw_support 1 (polynomial_ramified_lift 1 S)"
   using cut_endpointQ by (simp only: liftS)
 have EPtop: "ramified_weight 1 r s (int a,b)=ramified_weight_deg 1 r s (polynomial_ramified_lift 1 R)"
   using Et by (simp only: selected maximum weight liftR)
 have EQtop: "ramified_weight 1 r s (v_degree 1 0 Q,rootMultiplicity c (cut_poly 1 0 Q))=
   ramified_weight_deg 1 r s (polynomial_ramified_lift 1 S)"
   using Ft by (simp only: liftS)
 have BP': "BP\<in>ramified_pbw_support 1 (polynomial_ramified_lift 1 R)"
   using BP by (simp only: liftR)
 have BPt': "ramified_weight 1 r s BP=ramified_weight_deg 1 r s (polynomial_ramified_lift 1 R)"
   using BPt by (simp only: liftR)
 have BQ': "BQ\<in>ramified_pbw_support 1 (polynomial_ramified_lift 1 S)"
   using BQ by (simp only: liftS)
 have BQt': "ramified_weight 1 r s BQ=ramified_weight_deg 1 r s (polynomial_ramified_lift 1 S)"
   using BQt by (simp only: liftS)
 have endpoint: "(a,b)\<in>biv_support (leading_form r s R)"
   using polynomialRamifiedLift_leading_support_iff[OF one R Rpos, where i=a and j=b] endpointP EPtop by simp
 have Rdir: "in_direction r s R"
   by (rule lifted_two_top_orders_InDir[OF R Rpos endpointP BP' EPtop BPt'])
      (use BPlow in \<open>simp add: selected maximum\<close>)
 have Sdir: "in_direction r s S"
   by (rule lifted_two_top_orders_InDir[OF S Spos endpointQ BQ' EQtop BQt']) (use BQlow in simp)
 have oldupper: "ramified_weight 1 1 0 (u,j)\<le>int a"
   if "(u,j)\<in>ramified_pbw_support 1 (polynomial_ramified_lift 1 P)" for u j
   using polynomialRamifiedLift_weight_le_scaled_vDeg[OF one P, where rho=1 and sigma=0 and u=u and n=j] that
   by (simp add: weight)
 have upper: "u\<le>int a" if "(u,j)\<in>ramified_pbw_support 1 (polynomial_ramified_lift 1 R)" for u j
 proof -
   have member: "(u,j)\<in>ramified_pbw_support 1 (ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 P))"
     using that by (simp only: liftR)
   have "ramified_weight 1 1 0 (u,j)\<le>1*int a"
     by (rule ramified_cut_aut_weight_upper[where r="int a", OF one polynomial_ramified_lift_carrier _ _ _ _ member])
        (use oldupper in auto)
   then show ?thesis by (simp add: ramified_weight_def)
 qed
 have sumnew: "0<r+s" using newdir by (simp add: is_direction_def)
 have minnew: "pair_grade(a,b)\<le>pair_grade e" if e: "e\<in>biv_support (leading_form r s R)" for e
 proof -
   have bridge: "(int(fst e),snd e)\<in>ramified_pbw_support 1 (polynomial_ramified_lift 1 R) \<and>
     ramified_weight 1 r s (int(fst e),snd e)=ramified_weight_deg 1 r s (polynomial_ramified_lift 1 R)"
     using polynomialRamifiedLift_leading_support_iff[OF one R Rpos, where i="fst e" and j="snd e"] e
     by (simp add: prod.collapse)
   have x: "int(fst e)\<le>int a" by (rule upper[OF conjunct1[OF bridge]])
   have same: "r*(int(fst e)-int a)+s*(int(snd e)-int b)=0"
     using conjunct2[OF bridge] EPtop by (simp add: ramified_weight_def algebra_simps; linarith)
   have y: "int(snd e)\<le>int b"
   proof (rule ccontr)
     assume "\<not>int(snd e)\<le>int b"
     then have delta: "0<int(snd e)-int b" by arith
     have negative: "s*(int(snd e)-int b)<0" by (rule mult_neg_pos[OF s delta])
     have nonpositive: "r*(int(fst e)-int a)\<le>0"
       by (rule mult_nonneg_nonpos) (use r x in auto)
     show False using same negative nonpositive by arith
   qed
   have nonnegative: "0\<le>(r+s)*(int b-int(snd e))"
     by (rule mult_nonneg_nonneg) (use sumnew y in auto)
   have identity: "r*((int(fst e)-int(snd e))-(int a-int b))=
     (r+s)*(int b-int(snd e))"
     using same by (simp add: algebra_simps; linarith)
   have grade: "int a-int b\<le>int(fst e)-int(snd e)"
   proof (rule ccontr)
     assume "\<not>int a-int b\<le>int(fst e)-int(snd e)"
     then have delta: "(int(fst e)-int(snd e))-(int a-int b)<0" by arith
     have "r*((int(fst e)-int(snd e))-(int a-int b))<0" by (rule mult_pos_neg[OF r delta])
     then show False using identity nonnegative by arith
   qed
   show ?thesis using grade by (simp add: pair_grade_def)
 qed
 have ratioNew: "v_degree r s S*int d=v_degree r s R*int n"
   using ratio by (simp only: liftR[symmetric] liftS[symmetric]
     polynomialRamifiedLift_weightDeg_scaled_of_pos[OF one R Rpos]
     polynomialRamifiedLift_weightDeg_scaled_of_pos[OF one S Spos]; simp)
 have minimum_new: "\<forall>e\<in>biv_support (leading_form r s R). pair_grade(a,b)\<le>pair_grade e"
   by (intro ballI, rule minnew, assumption)
 show ?thesis
   apply (rule exI[where x=c])
   apply (rule exI[where x=R])
   apply (rule exI[where x=S])
   apply (rule exI[where x=r])
   apply (rule exI[where x=s])
   apply (intro conjI)
               apply (rule newpair)
              apply (rule newdir)
             apply (rule r)
            apply (rule s)
           apply (rule liftR)
          apply (rule liftS)
         apply (rule Rdir)
        apply (rule Sdir)
       apply (rule endpoint)
      apply (rule minimum_new)
     apply (rule Rpos)
    apply (rule Spos)
   apply (rule ratioNew)
   done
qed

end
