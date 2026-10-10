theory Horizontal_Corner_Full_Root
 imports "Polynomial_Constant_Cut_Recovery"
   "Polynomial_Cut_Mate_Alignment"
   "Polynomial_Companion_Cut_Grade"
begin

lemma horizontal_face_cut_coefficient:
 fixes P::"complex poly_operator"
 assumes endpt: "(a,b)\<in>biv_support (leading_form 1 0 P)"
 shows "coeff (cut_poly 1 0 P) j=biv_coeff (leading_form 1 0 P) a j"
proof -
 have homogeneous: "weighted_homogeneous 1 0 (v_degree 1 0 P) (leading_form 1 0 P)"
   unfolding leading_form_def by (rule weighted_component_homogeneous)
 have endpoint_weight: "pair_weight 1 0 (a,b)=v_degree 1 0 P"
   using homogeneous endpt unfolding weighted_homogeneous_def by blast
 have weight: "v_degree 1 0 P=int a"
   using endpoint_weight by (simp only: pair_weight_def fst_conv snd_conv mult_1_left mult_zero_left add_0_right)
 have row: "coeff (leading_form 1 0 P) j=monom (biv_coeff (leading_form 1 0 P) a j) a"
 proof (rule poly_eqI)
   fix i
   show "coeff (coeff (leading_form 1 0 P) j) i=
     coeff (monom (biv_coeff (leading_form 1 0 P) a j) a) i"
   proof (cases "i=a")
     case True then show ?thesis by (simp add: biv_coeff_def)
   next
     case False
     have zero: "biv_coeff (leading_form 1 0 P) i j=0"
     proof (rule ccontr)
       assume nonzero: "biv_coeff (leading_form 1 0 P) i j\<noteq>0"
       have member: "(i,j)\<in>biv_support (leading_form 1 0 P)"
         using nonzero by (simp add: biv_support_def)
       have member_weight: "pair_weight 1 0 (i,j)=v_degree 1 0 P"
         using homogeneous member unfolding weighted_homogeneous_def by blast
       have equality: "int i=int a"
         using member_weight by (simp only: weight pair_weight_def fst_conv snd_conv
           mult_1_left mult_zero_left add_0_right)
       show False using equality False by (simp only: of_nat_eq_iff)
     qed
     show ?thesis using False zero by (simp add: biv_coeff_def)
   qed
 qed
 show ?thesis by (simp only: cut_poly_coeff row poly_monom; simp)
qed

lemma horizontal_cut_degree_of_min_grade_endpoint:
 fixes P::"complex poly_operator"
 assumes endpt: "(a,b)\<in>biv_support (leading_form 1 0 P)"
 and minimum: "\<And>e. e\<in>biv_support (leading_form 1 0 P) \<Longrightarrow> pair_grade(a,b)\<le>pair_grade e"
 shows "degree (cut_poly 1 0 P)=b"
proof (rule antisym)
 show "degree (cut_poly 1 0 P)\<le>b"
 proof (rule degree_le, intro allI impI)
   fix j assume greater: "b<j"
   show "coeff (cut_poly 1 0 P) j=0"
   proof (rule ccontr)
     assume nonzero: "coeff (cut_poly 1 0 P) j\<noteq>0"
     have member: "(a,j)\<in>biv_support (leading_form 1 0 P)"
       using nonzero by (simp add: horizontal_face_cut_coefficient[OF endpt] biv_support_def)
     show False using minimum[OF member] greater by (simp add: pair_grade_def)
   qed
 qed
 show "b\<le>degree (cut_poly 1 0 P)"
   by (rule le_degree) (use endpt in \<open>simp add: horizontal_face_cut_coefficient[OF endpt] biv_support_def\<close>)
qed

lemma horizontal_corner_cutPoly_natDegree:
 fixes P::"complex poly_operator"
 assumes endpt: "(d,2*d)\<in>biv_support (leading_form 1 0 P)"
 and minimum: "\<And>e. e\<in>biv_support (leading_form 1 0 P) \<Longrightarrow> pair_grade(d,2*d)\<le>pair_grade e"
 shows "degree (cut_poly 1 0 P)=2*d"
 by (rule horizontal_cut_degree_of_min_grade_endpoint[OF endpt minimum])

lemma horizontal_normalized_full_root_arithmetic:
 fixes a b d h M::nat
 assumes d: "0<d" and h: "2\<le>h" and a: "a=d*(h-1)" and b: "b=d*h"
 and divisible: "d dvd M" and negative: "a<M" and bound: "M\<le>b"
 shows "M=b"
proof -
 obtain k where M: "M=d*k" using divisible by (elim dvdE)
 have lower: "h-1<k" using negative by (simp only: a M mult_less_cancel1 d)
 have upper: "k\<le>h" using bound by (simp only: b M mult_le_cancel1 d)
 have equal: "k=h" using lower upper h by arith
 show ?thesis by (simp only: M b equal)
qed

lemma horizontal_corner_maxRoot_eq_degree:
 fixes P Q::"complex poly_operator" and a b d n h::nat
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction 1 0"
 and Pdir: "in_direction 1 0 P" and Qdir: "in_direction 1 0 Q"
 and d: "1<d" and n: "1<n" and h: "2\<le>h"
 and a: "a=d*(h-1)" and b: "b=d*h"
 and endpt: "(a,b)\<in>biv_support (leading_form 1 0 P)"
 and minimum: "\<And>e. e\<in>biv_support (leading_form 1 0 P) \<Longrightarrow> pair_grade(a,b)\<le>pair_grade e"
 and weights: "v_degree 1 0 Q*int d=v_degree 1 0 P*int n" and cop: "coprime n d"
 shows "max_root_mult (cut_poly 1 0 P)=b"
proof -
 have positive: "0<(1::nat)" by simp
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
   using pair unfolding is_counterexample_pair_def by blast+
 have exact: "op_comp Q P-op_comp P Q=id"
   using pair unfolding is_counterexample_pair_def by blast
 have Ppos: "0<v_degree 1 0 P"
   by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have Qpos: "0<v_degree 1 0 Q"
   by (rule counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF pair] direction])
 have degree: "degree(cut_poly 1 0 P)=b"
   by (rule horizontal_cut_degree_of_min_grade_endpoint[OF endpt minimum])
 have bp: "0<b" using b d h by simp
 have ab: "a<b" using a b d h by simp
 have hom: "weighted_homogeneous 1 0 (v_degree 1 0 P) (leading_form 1 0 P)"
   unfolding leading_form_def by (rule weighted_component_homogeneous)
 have endpoint_weight: "pair_weight 1 0 (a,b)=v_degree 1 0 P"
   using hom endpt unfolding weighted_homogeneous_def by blast
 have weight: "v_degree 1 0 P=int a"
   using endpoint_weight by (simp only: pair_weight_def fst_conv snd_conv mult_1_left mult_zero_left add_0_right)
 have sum: "1<v_degree 1 0 P+v_degree 1 0 Q" using Ppos Qpos by arith
 obtain c where selected: "rootMultiplicity c (cut_poly 1 0 P)=max_root_mult(cut_poly 1 0 P)"
 and rootsNat: "nat(v_degree 1 0 Q)*max_root_mult(cut_poly 1 0 P)=
   nat(v_degree 1 0 P)*rootMultiplicity c (cut_poly 1 0 Q)"
   using exactPair_maxRoot_cut_mate_oldFace_endpoints[where l=1 and P=P and Q=Q and rho=1 and sigma=0, simplified]
     positive P Q direction Ppos Qpos Pdir Qdir exact sum by (auto simp: ramified_cut_exponent_def)
 have roots: "v_degree 1 0 Q*int(max_root_mult(cut_poly 1 0 P))=
   v_degree 1 0 P*int(rootMultiplicity c (cut_poly 1 0 Q))"
   using arg_cong[OF rootsNat, of int] Ppos Qpos by simp
 have divisible: "d dvd max_root_mult(cut_poly 1 0 P)"
   using reduced_ratio_root_orders_divide[OF Ppos weights roots cop] by (rule conjunct1)
 have input: "GGVPreliminaryCompanionInput"
   using ggv_preliminary_companion_proved by (simp only: GGVPreliminaryCompanionInput_def)
 have nonmonomial: "1<card(biv_support(leading_form 1 0 P))"
   using Pdir by (simp only: in_direction_def)
 have degreepos: "0<degree(cut_poly 1 0 P)" using degree bp by simp
 have oldnegative: "((int 1 div 1)*v_degree 1 0 P)-
   (ramified_cut_exponent 1 1 0+int 1)*int(degree(cut_poly 1 0 P))<0"
   using ab by (simp add: ramified_cut_exponent_def degree weight)
 have negative: "((int 1 div 1)*v_degree 1 0 P)-
   (ramified_cut_exponent 1 1 0+int 1)*int(max_root_mult(cut_poly 1 0 P))<0"
   by (rule preliminary_companion_maxRoot_cut_grade_negative[where l=1 and P=P and Q=Q and rho=1 and sigma=0,
     OF input positive pair direction _ _ Pdir degreepos oldnegative]) simp_all
 have lower: "a<max_root_mult(cut_poly 1 0 P)"
   using negative by (simp add: ramified_cut_exponent_def weight)
 have bound: "max_root_mult(cut_poly 1 0 P)\<le>b"
   using max_root_mult_degree_bound[of "cut_poly 1 0 P"] by (simp only: degree)
 show ?thesis by (rule horizontal_normalized_full_root_arithmetic[OF _ h a b divisible lower bound])
   (use d in arith)
qed

end
