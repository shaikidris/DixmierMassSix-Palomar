theory GGV_Horizontal_Minimality
 imports "Polynomial_Horizontal_Cut_Rectangle"
   "GGV_Horizontal_Standard_Cut"
   "GGV_Linear_Shear_Minimality"
begin

lemma degreeMinimal_horizontal_cut_preserved:
 fixes P Q R S::"complex poly_operator"
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
   and rectangleP: "is_subrectangular_at P a b" and rectangleQ: "is_subrectangular_at Q u v"
   and pairRS: "is_counterexample_pair R S"
   and recoverR: "polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P)"
   and recoverS: "polynomial_ramified_lift 1 S=ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 Q)"
 shows "is_degree_minimal_counterexample_pair R S"
proof -
 have pairPQ: "is_counterexample_pair P Q" using minimal by (simp add: is_degree_minimal_counterexample_pair_def)
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra" using pairPQ by (auto simp: is_counterexample_pair_def)
 have R: "R\<in>weyl_algebra" and S: "S\<in>weyl_algebra" using pairRS by (auto simp: is_counterexample_pair_def)
 have Rd: "total_degree R=total_degree P" by (rule polynomial_horizontal_cut_preserves_totalDeg[OF P R rectangleP recoverR])
 have Sd: "total_degree S=total_degree Q" by (rule polynomial_horizontal_cut_preserves_totalDeg[OF Q S rectangleQ recoverS])
 show ?thesis by (rule degreeMinimal_pair_of_same_total_degrees[OF minimal pairRS Rd Sd])
qed

lemma degreeMinimal_horizontal_cut_recovers_pair:
 fixes P Q::"complex poly_operator"
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
   and rectangleP: "is_subrectangular_at P a b" and rectangleQ: "is_subrectangular_at Q u v"
 shows "\<exists>R S. is_degree_minimal_counterexample_pair R S \<and> is_subrectangular_at R a b \<and> is_subrectangular_at S u v \<and>
   polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P) \<and>
   polynomial_ramified_lift 1 S=ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 Q)"
proof -
 have pairPQ: "is_counterexample_pair P Q" using minimal by (simp add: is_degree_minimal_counterexample_pair_def)
 obtain R S where pairRS: "is_counterexample_pair R S"
   and recoverR: "polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P)"
   and recoverS: "polynomial_ramified_lift 1 S=ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 Q)"
   using horizontal_cut_recovers_polynomial_counterexample[OF pairPQ, where c=c] by blast
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra" using pairPQ by (auto simp: is_counterexample_pair_def)
 have R: "R\<in>weyl_algebra" and S: "S\<in>weyl_algebra" using pairRS by (auto simp: is_counterexample_pair_def)
 show ?thesis by (rule exI[of _ R], rule exI[of _ S])
   (use degreeMinimal_horizontal_cut_preserved[OF minimal rectangleP rectangleQ pairRS recoverR recoverS]
     polynomial_horizontal_cut_preserves_subrectangular[OF P R rectangleP recoverR]
     polynomial_horizontal_cut_preserves_subrectangular[OF Q S rectangleQ recoverS] recoverR recoverS in blast)
qed

lemma preliminary_degreeMinimal_horizontal_standardization:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and minimal: "is_degree_minimal_counterexample_pair P Q"
   and rectangleP: "is_subrectangular_at P a b" and rectangleQ: "is_subrectangular_at Q u v"
   and orientation: "a<b" and face: "in_direction 1 0 P"
 shows "\<exists>R S. is_degree_minimal_counterexample_pair R S \<and> is_subrectangular_at R a b \<and> is_subrectangular_at S u v \<and>
   (\<forall>e\<in>biv_support(leading_form 1 0 R). pair_grade e<0)"
proof -
 have pairPQ: "is_counterexample_pair P Q" using minimal by (simp add: is_degree_minimal_counterexample_pair_def)
 obtain c where negative: "\<forall>k n. (k,n)\<in>ramified_pbw_support 1(ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P)) \<longrightarrow>
     ramified_weight 1 1 0(k,n)=int a \<longrightarrow> max_root_mult(cut_poly 1 0 P)\<le>n \<and> k-int n<0"
   using preliminary_horizontal_cut_negative_old_face_exact_pair[OF source pairPQ rectangleP orientation face] by blast
 obtain R S where minRS: "is_degree_minimal_counterexample_pair R S"
   and rectR: "is_subrectangular_at R a b" and rectS: "is_subrectangular_at S u v"
   and recover: "polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P)"
   using degreeMinimal_horizontal_cut_recovers_pair[OF minimal rectangleP rectangleQ, where c=c] by blast
 have pairRS: "is_counterexample_pair R S" using minRS by (simp add: is_degree_minimal_counterexample_pair_def)
 have R: "R\<in>weyl_algebra" using pairRS by (simp add: is_counterexample_pair_def)
 have allnegative: "pair_grade e<0" if member: "e\<in>biv_support(leading_form 1 0 R)" for e
 proof -
   have sourceR: "e\<in>biv_support(pbw_symbol R)" and ew: "pair_weight 1 0 e=v_degree 1 0 R"
     using member by (auto simp: leading_form_def weighted_component_support)
   have weight: "v_degree 1 0 R=int a" using subrectangular_v_degree[OF rectR] by blast
   have x: "fst e=a" using ew by (simp add: pair_weight_def weight)
   have lifted: "(int(fst e),snd e)\<in>ramified_pbw_support 1(polynomial_ramified_lift 1 R)"
     using polynomialRamifiedLift_support_iff_symbol[OF zero_less_one R, where k="int(fst e)" and j="snd e"] sourceR
     by (auto simp: prod.collapse)
   have cutmember: "(int(fst e),snd e)\<in>ramified_pbw_support 1(ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P))"
     using lifted by (simp only: recover)
   have top: "ramified_weight 1 1 0(int(fst e),snd e)=int a" by (simp add: ramified_weight_def x)
   have negative_at: "(int(fst e),snd e)\<in>ramified_pbw_support 1
     (ramified_cut_aut 1 1 0 c(polynomial_ramified_lift 1 P)) \<longrightarrow>
     ramified_weight 1 1 0(int(fst e),snd e)=int a \<longrightarrow>
     max_root_mult(cut_poly 1 0 P)\<le>snd e \<and> int(fst e)-int(snd e)<0"
     by (rule spec[OF spec[OF negative, of "int(fst e)"], of "snd e"])
   have point_bound: "max_root_mult(cut_poly 1 0 P)\<le>snd e \<and> int(fst e)-int(snd e)<0"
     by (rule mp[OF mp[OF negative_at cutmember] top])
   show ?thesis using conjunct2[OF point_bound] by (simp only: pair_grade_def)
 qed
 show ?thesis by (rule exI[of _ R], rule exI[of _ S]) (use minRS rectR rectS allnegative in blast)
qed

end
