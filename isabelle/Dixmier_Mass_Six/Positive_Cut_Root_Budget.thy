theory Positive_Cut_Root_Budget
 imports "Polynomial_Companion_Cut_Grade"
   "Homogeneous_Cut_Reconstruction"
begin

lemma native_positive_companion_cut_degree_le_one:
 fixes T::"complex poly_operator" and sigma::nat
 assumes sigma: "1<sigma" and weight: "v_degree 1 (int sigma) T=1+int sigma"
 shows "degree(cut_poly 1 (int sigma) T)\<le>1"
proof (rule degree_le, intro allI impI)
 fix j::nat assume above: "1<j"
 have homogeneous: "weighted_homogeneous 1 (int sigma) (1+int sigma) (leading_form 1 (int sigma) T)"
   unfolding weight[symmetric] leading_form_def by (rule weighted_component_homogeneous)
 have zero: "biv_coeff (leading_form 1 (int sigma) T) i j=0" for i::nat
 proof (rule ccontr)
   assume nz: "\<not>biv_coeff (leading_form 1 (int sigma) T) i j=0"
   have member: "(i,j)\<in>biv_support(leading_form 1 (int sigma) T)"
     using nz by (simp add: biv_support_def)
   have all_weights: "\<forall>u\<in>biv_support(leading_form 1 (int sigma) T). pair_weight 1 (int sigma) u=1+int sigma"
     using homogeneous by (simp only: weighted_homogeneous_def)
   have point_weight: "pair_weight 1 (int sigma) (i,j)=1+int sigma"
     by (rule bspec[OF all_weights member])
   have eq: "int i+int sigma*int j=1+int sigma"
     using point_weight by (simp only: pair_weight_def fst_conv snd_conv mult_1_left mult.commute)
   have jp: "2\<le>int j" using above by simp
   have sp: "0<int sigma" using sigma by simp
   have lower: "2*int sigma\<le>int sigma*int j"
     using mult_left_mono[OF jp, of "int sigma"] sp by simp
   show False using eq lower sigma by linarith
 qed
 have rowzero: "coeff (leading_form 1 (int sigma) T) j=0"
   by (rule poly_eqI) (simp only: coeff_0 biv_coeff_def[symmetric] zero)
 show "coeff(cut_poly 1 (int sigma) T) j=0" by (simp add: cut_poly_coeff rowzero)
qed

lemma polynomialRamified_positive_companion_cut_natDegree_le_one:
 fixes T::"complex poly_operator" and sigma::nat
 assumes T: "T\<in>weyl_algebra" and sigma: "1<sigma"
 and weight: "ramified_weight_deg 1 1 (int sigma) (polynomial_ramified_lift 1 T)=1+int sigma"
 shows "degree(ramified_top_face_polynomial 1 1 (int sigma) (polynomial_ramified_lift 1 T))\<le>1"
proof -
 have one: "0<(1::nat)" by simp
 have rho: "0<(1::int)" by simp
 have divides: "(1::int) dvd int(1::nat)" by simp
 have tw: "v_degree 1 (int sigma) T=1+int sigma"
   using weight by (simp only: polynomial_ramified_lift_weight_degree[OF one T]; simp)
 have face: "ramified_top_face_polynomial 1 1 (int sigma) (polynomial_ramified_lift 1 T)=cut_poly 1 (int sigma) T"
   by (rule polynomial_ramified_lift_top_face[OF one T rho divides])
 show ?thesis by (simp only: face; rule native_positive_companion_cut_degree_le_one[OF sigma tw])
qed

lemma preliminary_positive_cut_distinct_roots_le_one:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q" and sigma: "1<sigma"
 shows "card(set_mset(proots(cut_poly 1 (int sigma) P)))\<le>1"
proof -
 have one: "0<(1::nat)" by simp
 have rho: "0<(1::int)" by simp
 have sum: "0<(1::int)+int sigma" using sigma by simp
 have divides: "(1::int) dvd int(1::nat)" by simp
 have direction: "is_direction 1 (int sigma)" using sigma by (simp add: is_direction_def)
 obtain T where T: "T\<in>weyl_algebra" and Tnz: "T\<noteq>0"
   and Tweight: "ramified_weight_deg 1 1 (int sigma) (polynomial_ramified_lift 1 T)=int 1*(1+int sigma)"
   and degree: "ramified_weight_deg 1 1 (int sigma)
    (laurent_comp (polynomial_ramified_lift 1 P)(polynomial_ramified_lift 1 T)-
      laurent_comp (polynomial_ramified_lift 1 T)(polynomial_ramified_lift 1 P))=
    ramified_weight_deg 1 1 (int sigma) (polynomial_ramified_lift 1 P)"
   and face: "ramified_top_face_polynomial 1 1 (int sigma)
    (laurent_comp (polynomial_ramified_lift 1 P)(polynomial_ramified_lift 1 T)-
      laurent_comp (polynomial_ramified_lift 1 T)(polynomial_ramified_lift 1 P))=
    ramified_top_face_polynomial 1 1 (int sigma) (polynomial_ramified_lift 1 P)"
   using preliminary_companion_has_polynomial_cut_witness[OF source one pair direction rho divides] by blast
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have Ppos: "0<v_degree 1 (int sigma) P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have Pnz: "P\<noteq>0" using Ppos by auto
 have LPnz: "polynomial_ramified_lift 1 P\<noteq>0"
   using polynomial_ramified_lift_injective[OF one P, where Q=0] Pnz
   by (auto simp: weyl_algebra_def)
 have LTnz: "polynomial_ramified_lift 1 T\<noteq>0"
   using polynomial_ramified_lift_injective[OF one T, where Q=0] Tnz
   by (auto simp: weyl_algebra_def)
 have budget: "card(set_mset(proots(ramified_top_face_polynomial 1 1 (int sigma)
   (polynomial_ramified_lift 1 P))))\<le>degree(ramified_top_face_polynomial 1 1 (int sigma)
   (-polynomial_ramified_lift 1 T))"
   by (rule ramified_source_companion_top_face_root_count[OF one rho sum
     polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier LPnz LTnz degree face Tweight])
 have negT: "-T\<in>weyl_algebra"
   using op_adjoin.diff[OF op_adjoin_zero T[unfolded weyl_algebra_def]] by (simp add: weyl_algebra_def)
 have negative_lift: "polynomial_ramified_lift 1 (-T)= -polynomial_ramified_lift 1 T"
   using polynomial_ramified_lift_diff[OF one, where P=0 and Q=T] T
   by (simp add: weyl_algebra_def)
 have negative_weight: "ramified_weight_deg 1 1 (int sigma) (polynomial_ramified_lift 1 (-T))=1+int sigma"
   by (simp only: negative_lift ramifiedWeightDeg_neg[OF one polynomial_ramified_lift_carrier] Tweight; simp)
 have bound: "degree(ramified_top_face_polynomial 1 1 (int sigma) (polynomial_ramified_lift 1 (-T)))\<le>1"
   by (rule polynomialRamified_positive_companion_cut_natDegree_le_one[OF negT sigma negative_weight])
 have actual_face: "ramified_top_face_polynomial 1 1 (int sigma) (polynomial_ramified_lift 1 P)=cut_poly 1 (int sigma) P"
   by (rule polynomial_ramified_lift_top_face[OF one P rho divides])
 have actual_budget: "card(set_mset(proots(cut_poly 1 (int sigma) P)))\<le>
   degree(ramified_top_face_polynomial 1 1 (int sigma) (polynomial_ramified_lift 1 (-T)))"
   using budget by (simp only: actual_face negative_lift)
 show ?thesis by (rule order_trans[OF actual_budget bound])
qed

end
