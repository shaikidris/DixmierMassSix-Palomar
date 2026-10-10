theory Polynomial_Horizontal_Cut_Rectangle
 imports "Polynomial_Shear_Top_Row"
   "Subrectangular_Case_Support"
   "Positive_Shear_Finite_Descent"
begin

lemma polynomial_horizontal_cut_preserves_subrectangular:
 fixes P R::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and R: "R\<in>weyl_algebra"
   and rectangle: "is_subrectangular_at P a b"
   and recover: "polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P)"
 shows "is_subrectangular_at R a b"
proof -
 have point: "(a,b)\<in>biv_support(pbw_symbol P)" and ybound: "\<And>e. e\<in>biv_support(pbw_symbol P) \<Longrightarrow> snd e\<le>b"
   using rectangle by (auto simp: is_subrectangular_at_def)
 have pointR: "(a,b)\<in>biv_support(pbw_symbol R)"
   by (rule polynomial_cut_preserves_top_row_point[OF P R ybound point recover])
 have yR: "\<forall>e\<in>biv_support(pbw_symbol R). snd e\<le>b"
   using polynomial_cut_preserves_y_bound_and_top_row[OF P R ybound recover] by blast
 have weight: "v_degree 1 0 P=int a" using subrectangular_v_degree[OF rectangle] by blast
 have oldupper: "ramified_weight 1 1 0(u,n)\<le>int a"
   if support: "(u,n)\<in>ramified_pbw_support 1(polynomial_ramified_lift 1 P)" for u n
   using polynomialRamifiedLift_weight_le_scaled_vDeg[OF zero_less_one P, where rho=1 and sigma=0 and u=u and n=n] support
   by (simp add: weight)
 have xR: "fst e\<le>a" if member: "e\<in>biv_support(pbw_symbol R)" for e
 proof -
   have lifted: "(int(fst e),snd e)\<in>ramified_pbw_support 1(polynomial_ramified_lift 1 R)"
     using polynomialRamifiedLift_support_iff_symbol[OF zero_less_one R, where k="int(fst e)" and j="snd e"] member
     by (auto simp: prod.collapse)
   have cutmember: "(int(fst e),snd e)\<in>ramified_pbw_support 1(ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P))"
     using lifted by (simp only: recover)
   have upper: "ramified_weight 1 1 0(int(fst e),snd e)\<le>1*int a"
     by (rule ramified_cut_aut_weight_upper[where r="int a", OF zero_less_one polynomial_ramified_lift_carrier _ _ _ _ cutmember])
       (use oldupper in auto)
   show ?thesis using upper by (simp add: ramified_weight_def)
 qed
 show ?thesis using pointR yR xR by (auto simp: is_subrectangular_at_def)
qed

lemma subrectangular_totalDeg_eq:
 fixes P::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and rectangle: "is_subrectangular_at P a b"
 shows "total_degree P=a+b"
proof -
 have rectangle_data: "(a,b)\<in>biv_support(pbw_symbol P) \<and>
   (\<forall>e\<in>biv_support(pbw_symbol P). fst e\<le>a \<and> snd e\<le>b)"
   using rectangle by (simp only: is_subrectangular_at_def; blast)
 have point: "(a,b)\<in>biv_support(pbw_symbol P)" by (rule conjunct1[OF rectangle_data])
 have bound: "fst e+snd e\<le>a+b" if member: "e\<in>biv_support(pbw_symbol P)" for e
 proof -
   have coordinates: "fst e\<le>a \<and> snd e\<le>b"
     by (rule bspec[OF conjunct2[OF rectangle_data] member])
   show ?thesis using coordinates by arith
 qed
 show ?thesis by (rule totalDeg_eq_of_support_sum_bound[OF point bound])
qed

lemma polynomial_horizontal_cut_preserves_totalDeg:
 fixes P R::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and R: "R\<in>weyl_algebra"
   and rectangle: "is_subrectangular_at P a b"
   and recover: "polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P)"
 shows "total_degree R=total_degree P"
 by (simp only: subrectangular_totalDeg_eq[OF R polynomial_horizontal_cut_preserves_subrectangular[OF P R rectangle recover]]
   subrectangular_totalDeg_eq[OF P rectangle])

end
