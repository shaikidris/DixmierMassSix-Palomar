theory GGV_Horizontal_Standard_Cut
 imports "Horizontal_Corner_Full_Root"
   "Subrectangular_Case_Support"
begin

lemma subrectangular_horizontal_weight_and_cut_degree:
 fixes P::"complex poly_operator"
 assumes rectangle: "is_subrectangular_at P a b"
 shows "v_degree 1 0 P=int a \<and> degree(cut_poly 1 0 P)=b"
proof -
 have weight: "v_degree 1 0 P=int a" using subrectangular_v_degree[OF rectangle] by blast
 have corner: "(a,b)\<in>biv_support(leading_form 1 0 P)"
   by (rule subrectangular_corner_mem_horizontal[OF rectangle])
 have minimum: "pair_grade(a,b)\<le>pair_grade e"
   if member: "e\<in>biv_support(leading_form 1 0 P)" for e
 proof -
   have source: "e\<in>biv_support(pbw_symbol P)"
     using member by (auto simp: leading_form_def weighted_component_support)
   have homogeneous: "weighted_homogeneous 1 0 (v_degree 1 0 P) (leading_form 1 0 P)"
     unfolding leading_form_def by (rule weighted_component_homogeneous)
   have x: "fst e=a" using homogeneous member
     by (simp add: weighted_homogeneous_def pair_weight_def weight)
   have y: "snd e\<le>b" using rectangle source by (simp add: is_subrectangular_at_def)
   show ?thesis using y by (simp add: pair_grade_def x)
 qed
 show ?thesis using weight horizontal_cut_degree_of_min_grade_endpoint[OF corner minimum] by blast
qed

lemma preliminary_horizontal_maxRoot_above_corner:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and rectangle: "is_subrectangular_at P a b" and orientation: "a<b"
   and face: "in_direction 1 0 P"
 shows "a<max_root_mult(cut_poly 1 0 P)"
proof -
 have weight: "v_degree 1 0 P=int a" and degree: "degree(cut_poly 1 0 P)=b"
   using subrectangular_horizontal_weight_and_cut_degree[OF rectangle] by blast+
 have positive: "0<degree(cut_poly 1 0 P)" using orientation by (simp only: degree; arith)
 have old: "((int 1 div 1)*v_degree 1 0 P)-
   (ramified_cut_exponent 1 1 0+int 1)*int(degree(cut_poly 1 0 P))<0"
   using orientation by (simp add: weight degree ramified_cut_exponent_def)
 have direction: "is_direction 1 0" by (simp add: is_direction_def)
 have negative: "((int 1 div 1)*v_degree 1 0 P)-
   (ramified_cut_exponent 1 1 0+int 1)*int(max_root_mult(cut_poly 1 0 P))<0"
   by (rule preliminary_companion_maxRoot_cut_grade_negative[OF source zero_less_one pair direction zero_less_one _ face positive old]) simp
 show ?thesis using negative by (simp add: weight ramified_cut_exponent_def)
qed

lemma preliminary_horizontal_cut_negative_old_face_exact_pair:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and rectangle: "is_subrectangular_at P a b" and orientation: "a<b"
   and face: "in_direction 1 0 P"
 shows "\<exists>c. poly(cut_poly 1 0 P)c=0 \<and>
   rootMultiplicity c(cut_poly 1 0 P)=max_root_mult(cut_poly 1 0 P) \<and>
   (int a,max_root_mult(cut_poly 1 0 P))\<in>ramified_pbw_support 1
     (ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P)) \<and>
   (\<forall>u n. (u,n)\<in>ramified_pbw_support 1(ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P)) \<longrightarrow>
     ramified_weight 1 1 0(u,n)=int a \<longrightarrow> max_root_mult(cut_poly 1 0 P)\<le>n \<and> u-int n<0) \<and>
   laurent_comp (ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 Q))
     (ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P))-
   laurent_comp (ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P))
     (ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 Q))=id"
proof -
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra" and bracket: "op_comp Q P-op_comp P Q=id"
   using pair by (auto simp: is_counterexample_pair_def)
 have weight: "v_degree 1 0 P=int a" using subrectangular_horizontal_weight_and_cut_degree[OF rectangle] by blast
 have beyond: "a<max_root_mult(cut_poly 1 0 P)"
   by (rule preliminary_horizontal_maxRoot_above_corner[OF source pair rectangle orientation face])
 obtain c where root: "poly(cut_poly 1 0 P)c=0" and maximum: "rootMultiplicity c(cut_poly 1 0 P)=max_root_mult(cut_poly 1 0 P)"
   using cutPoly_exists_maxRoot_of_InDir[OF zero_less_one face] by blast
 have corner: "(a,b)\<in>biv_support(leading_form 1 0 P)" by (rule subrectangular_corner_mem_horizontal[OF rectangle])
 have data: "(int a,max_root_mult(cut_poly 1 0 P))\<in>ramified_pbw_support 1(ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P)) \<and>
   (\<forall>u n. (u,n)\<in>ramified_pbw_support 1(ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P)) \<longrightarrow>
     ramified_weight 1 1 0(u,n)=int a \<longrightarrow> max_root_mult(cut_poly 1 0 P)\<le>n)"
   using polynomialRamifiedCut_root_start_on_old_face[OF zero_less_one P zero_less_one _ _ corner, where c=c]
   by (simp add: maximum weight ramified_cut_exponent_def)
 have negative: "max_root_mult(cut_poly 1 0 P)\<le>n \<and> u-int n<0"
   if support: "(u,n)\<in>ramified_pbw_support 1(ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P))"
     and top: "ramified_weight 1 1 0(u,n)=int a" for u n
 proof -
   have lower: "max_root_mult(cut_poly 1 0 P)\<le>n" using data support top by blast
   have x: "u=int a" using top by (simp add: ramified_weight_def)
   show ?thesis using lower beyond by (simp only: x; arith)
 qed
 have exact: "laurent_comp (ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 Q))
     (ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P))-
   laurent_comp (ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P))
     (ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 Q))=id"
   by (rule ramified_cut_aut_exact_pair[OF zero_less_one polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier
     polynomial_ramified_lift_bracket_one[OF zero_less_one P Q bracket]])
 show ?thesis by (intro exI[of _ c]) (use root maximum data negative exact in blast)
qed

end
