theory GGV_Minimal_Crossing_Pair
 imports "GGV_Minimal_Standardization"
   "GGV_Horizontal_Minimality"
   "Ordered_Crossing_Selection"
begin

lemma subrectangular_horizontal_negative_of_no_dir:
 fixes P::"complex poly_operator"
 assumes rectangle: "is_subrectangular_at P a b" and orientation: "a<b"
   and noface: "\<not>in_direction 1 0 P"
   and member: "e\<in>biv_support(leading_form 1 0 P)"
 shows "pair_grade e<0"
proof -
 have corner: "(a,b)\<in>biv_support(leading_form 1 0 P)" by (rule subrectangular_corner_mem_horizontal[OF rectangle])
 have card: "card(biv_support(leading_form 1 0 P))\<le>1" using noface by (simp add: in_direction_def)
 have equal: "e=(a,b)"
 proof (rule ccontr)
   assume distinct: "e\<noteq>(a,b)"
   have subset: "{e,(a,b)}\<subseteq>biv_support(leading_form 1 0 P)" using member corner by auto
   have "card {e,(a,b)}\<le>card(biv_support(leading_form 1 0 P))" by (rule card_mono[OF finite_biv_support subset])
   then show False using card distinct by simp
 qed
 show ?thesis using orientation by (simp add: equal pair_grade_def)
qed

lemma degreeMinimal_negative_horizontal_pair:
 fixes P Q::"complex poly_operator"
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
 shows "\<exists>R S a b u v. is_degree_minimal_counterexample_pair R S \<and>
   total_degree R=total_degree P \<and> total_degree S=total_degree Q \<and>
   0<a \<and> a<b \<and> 0<u \<and> 0<v \<and> is_subrectangular_at R a b \<and>
   is_subrectangular_at S u v \<and> a*v=b*u \<and>
   (\<forall>e\<in>biv_support(leading_form 1 0 R). pair_grade e<0)"
proof -
 obtain T U a b u v where minTU: "is_degree_minimal_counterexample_pair T U"
   and Td: "total_degree T=total_degree P" and Ud: "total_degree U=total_degree Q"
   and ap: "0<a" and orient: "a<b" and up: "0<u" and vp: "0<v"
   and rectT: "is_subrectangular_at T a b" and rectU: "is_subrectangular_at U u v" and proportional: "a*v=b*u"
   using degreeMinimal_oriented_subrectangular_pair[OF minimal] by blast
 show ?thesis
 proof (cases "in_direction 1 0 T")
   case True
   obtain R S where minRS: "is_degree_minimal_counterexample_pair R S"
     and rectR: "is_subrectangular_at R a b" and rectS: "is_subrectangular_at S u v"
     and terminal: "\<forall>e\<in>biv_support(leading_form 1 0 R). pair_grade e<0"
     using preliminary_degreeMinimal_horizontal_standardization[OF preliminary_companion_from_actual_GGV_companion minTU rectT rectU orient True] by blast
   have pairTU: "is_counterexample_pair T U" and pairRS: "is_counterexample_pair R S"
     using minTU minRS by (simp_all add: is_degree_minimal_counterexample_pair_def)
   have T: "T\<in>weyl_algebra" and U: "U\<in>weyl_algebra" and R: "R\<in>weyl_algebra" and S: "S\<in>weyl_algebra"
     using pairTU pairRS by (auto simp: is_counterexample_pair_def)
   have Rd: "total_degree R=total_degree P"
     by (simp only: subrectangular_totalDeg_eq[OF R rectR] subrectangular_totalDeg_eq[OF T rectT, symmetric] Td)
   have Sd: "total_degree S=total_degree Q"
     by (simp only: subrectangular_totalDeg_eq[OF S rectS] subrectangular_totalDeg_eq[OF U rectU, symmetric] Ud)
   show ?thesis by (rule exI[of _ R], rule exI[of _ S], rule exI[of _ a], rule exI[of _ b], rule exI[of _ u], rule exI[of _ v])
     (use minRS Rd Sd ap orient up vp rectR rectS proportional terminal in blast)
 next
   case False
   have terminal: "\<forall>e\<in>biv_support(leading_form 1 0 T). pair_grade e<0"
     by (intro ballI) (rule subrectangular_horizontal_negative_of_no_dir[OF rectT orient False])
   show ?thesis by (rule exI[of _ T], rule exI[of _ U], rule exI[of _ a], rule exI[of _ b], rule exI[of _ u], rule exI[of _ v])
     (use minTU Td Ud ap orient up vp rectT rectU proportional terminal in blast)
 qed
qed

lemma degreeMinimal_strict_crossing_pair:
 fixes P Q::"complex poly_operator"
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
 shows "\<exists>R S a b u v j rho s e f. is_degree_minimal_counterexample_pair R S \<and>
   total_degree R=total_degree P \<and> total_degree S=total_degree Q \<and>
   0<a \<and> a<b \<and> 0<u \<and> 0<v \<and> is_subrectangular_at R a b \<and> is_subrectangular_at S u v \<and> a*v=b*u \<and>
   (\<forall>x\<in>biv_support(leading_form 1 0 R). pair_grade x<0) \<and>
   j<length(ggv_ordered_negative_face_slopes R) \<and> 0<rho \<and> 0<s \<and>
   is_direction (int rho) (-int s) \<and> ggv_ordered_negative_face_slopes R!j=(of_int(-int s)/ of_int(int rho)::rat) \<and>
   in_direction (int rho) (-int s) R \<and> in_direction (int rho) (-int s) S \<and>
   e\<in>biv_support(leading_form (int rho) (-int s) R) \<and> f\<in>biv_support(leading_form (int rho) (-int s) R) \<and>
   (\<forall>x\<in>biv_support(leading_form (int rho) (-int s) R). snd e\<le>snd x) \<and>
   (\<forall>x\<in>biv_support(leading_form (int rho) (-int s) R). snd x\<le>snd f) \<and> 0<pair_grade e \<and> pair_grade f<0"
proof -
 obtain R S a b u v where minRS: "is_degree_minimal_counterexample_pair R S"
   and Rd: "total_degree R=total_degree P" and Sd: "total_degree S=total_degree Q"
   and ap: "0<a" and orient: "a<b" and up: "0<u" and vp: "0<v"
   and rectR: "is_subrectangular_at R a b" and rectS: "is_subrectangular_at S u v" and proportional: "a*v=b*u"
   and terminal: "\<forall>x\<in>biv_support(leading_form 1 0 R). pair_grade x<0"
   using degreeMinimal_negative_horizontal_pair[OF minimal] by blast
 have pairRS: "is_counterexample_pair R S" using minRS by (simp add: is_degree_minimal_counterexample_pair_def)
 have negative: "pair_grade x<0" if "x\<in>biv_support(leading_form 1 0 R)" for x using terminal that by blast
 have crossing: "\<exists>j rho s e f. j<length(ggv_ordered_negative_face_slopes R) \<and> 0<rho \<and> 0<s \<and>
   is_direction (int rho) (-int s) \<and> ggv_ordered_negative_face_slopes R!j=(of_int(-int s)/ of_int(int rho)::rat) \<and>
   in_direction (int rho) (-int s) R \<and> in_direction (int rho) (-int s) S \<and>
   e\<in>biv_support(leading_form (int rho) (-int s) R) \<and> f\<in>biv_support(leading_form (int rho) (-int s) R) \<and>
   (\<forall>x\<in>biv_support(leading_form (int rho) (-int s) R). snd e\<le>snd x) \<and>
   (\<forall>x\<in>biv_support(leading_form (int rho) (-int s) R). snd x\<le>snd f) \<and> 0<pair_grade e \<and> pair_grade f<0"
   by (rule counterexample_ordered_strict_crossing_of_terminal[OF preliminary_companion_from_actual_GGV_companion pairRS negative])
 show ?thesis by (rule exI[of _ R], rule exI[of _ S], rule exI[of _ a], rule exI[of _ b], rule exI[of _ u], rule exI[of _ v])
   (use minRS Rd Sd ap orient up vp rectR rectS proportional terminal crossing in blast)
qed

end
