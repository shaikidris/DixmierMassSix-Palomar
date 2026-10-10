theory GGV_Diagonal_Root_Budget
 imports "Polynomial_Companion_Cut_Grade"
   "Homogeneous_Cut_Reconstruction"
   "Diagonal_Cut_Factorization"
begin

text \<open>Actual GGVDiagonalRootBudget source composition. All witnesses are
produced by the native preliminary companion theorem; none are assumptions.
Source 61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff.\<close>

lemma polynomialRamified_diagonal_topFace_natDegree_le:
 fixes T::"complex poly_operator" and n::nat
 assumes T: "T\<in>weyl_algebra"
   and weight: "ramified_weight_deg 1 1 1 (polynomial_ramified_lift 1 T)=int n"
 shows "degree(ramified_top_face_polynomial 1 1 1 (polynomial_ramified_lift 1 T))\<le>n"
proof -
 have one: "0<(1::nat)" by simp
 have rho: "0<(1::int)" by simp
 have divides: "(1::int) dvd int(1::nat)" by simp
 have degree: "v_degree 1 1 T=int n"
   using weight by (simp only: polynomial_ramified_lift_weight_degree[OF one T]; simp)
 have face: "ramified_top_face_polynomial 1 1 1 (polynomial_ramified_lift 1 T)=cut_poly 1 1 T"
   by (rule polynomial_ramified_lift_top_face[OF one T rho divides])
 show ?thesis by (simp only: face; rule diagonal_cut_natDegree_le[OF degree])
qed

lemma preliminary_diagonal_cut_distinct_roots_le_two:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
 shows "card(set_mset(proots(cut_poly 1 1 P)))\<le>2"
proof -
 have one: "0<(1::nat)" by simp
 have rho: "0<(1::int)" by simp
 have sum: "0<(1::int)+1" by simp
 have divides: "(1::int) dvd int(1::nat)" by simp
 have direction: "is_direction 1 1" by (simp add: is_direction_def)
 obtain T where T: "T\<in>weyl_algebra" and Tnz: "T\<noteq>0"
   and Tweight: "ramified_weight_deg 1 1 1 (polynomial_ramified_lift 1 T)=int 1*(1+1)"
   and degree: "ramified_weight_deg 1 1 1
    (laurent_comp (polynomial_ramified_lift 1 P)(polynomial_ramified_lift 1 T)-
      laurent_comp (polynomial_ramified_lift 1 T)(polynomial_ramified_lift 1 P))=
    ramified_weight_deg 1 1 1 (polynomial_ramified_lift 1 P)"
   and face: "ramified_top_face_polynomial 1 1 1
    (laurent_comp (polynomial_ramified_lift 1 P)(polynomial_ramified_lift 1 T)-
      laurent_comp (polynomial_ramified_lift 1 T)(polynomial_ramified_lift 1 P))=
    ramified_top_face_polynomial 1 1 1 (polynomial_ramified_lift 1 P)"
   using preliminary_companion_has_polynomial_cut_witness[OF source one pair direction rho divides] by blast
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have Ppos: "0<v_degree 1 1 P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have Pnz: "P\<noteq>0" using Ppos by auto
 have LPnz: "polynomial_ramified_lift 1 P\<noteq>0"
   using polynomial_ramified_lift_injective[OF one P, where Q=0] Pnz
   by (auto simp: weyl_algebra_def)
 have LTnz: "polynomial_ramified_lift 1 T\<noteq>0"
   using polynomial_ramified_lift_injective[OF one T, where Q=0] Tnz
   by (auto simp: weyl_algebra_def)
 have budget: "card(set_mset(proots(ramified_top_face_polynomial 1 1 1
   (polynomial_ramified_lift 1 P))))\<le>degree(ramified_top_face_polynomial 1 1 1
   (-polynomial_ramified_lift 1 T))"
   by (rule ramified_source_companion_top_face_root_count[OF one rho sum
     polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier LPnz LTnz degree face Tweight])
 have negT: "-T\<in>weyl_algebra"
   using op_adjoin.diff[OF op_adjoin_zero T[unfolded weyl_algebra_def]] by (simp add: weyl_algebra_def)
 have negative_lift: "polynomial_ramified_lift 1 (-T)= -polynomial_ramified_lift 1 T"
   using polynomial_ramified_lift_diff[OF one, where P=0 and Q=T] T
   by (simp add: weyl_algebra_def)
 have negative_weight: "ramified_weight_deg 1 1 1 (polynomial_ramified_lift 1 (-T))=int(2::nat)"
   by (simp only: negative_lift ramifiedWeightDeg_neg[OF one polynomial_ramified_lift_carrier] Tweight; simp)
 have bound: "degree(ramified_top_face_polynomial 1 1 1 (polynomial_ramified_lift 1 (-T)))\<le>2"
   by (rule polynomialRamified_diagonal_topFace_natDegree_le[OF negT negative_weight])
 have actual_face: "ramified_top_face_polynomial 1 1 1 (polynomial_ramified_lift 1 P)=cut_poly 1 1 P"
   by (rule polynomial_ramified_lift_top_face[OF one P rho divides])
 have actual_budget: "card(set_mset(proots(cut_poly 1 1 P)))\<le>
   degree(ramified_top_face_polynomial 1 1 1 (polynomial_ramified_lift 1 (-T)))"
   using budget by (simp only: actual_face negative_lift)
 show ?thesis by (rule order_trans[OF actual_budget bound])
qed

lemma preliminary_diagonal_two_roots_exhaust_weight:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and roots: "2\<le>card(set_mset(proots(cut_poly 1 1 P)))"
 shows "v_degree 1 1 P=int(degree(cut_poly 1 1 P))"
proof -
 have one: "0<(1::nat)" by simp
 have rho: "0<(1::int)" by simp
 have sum: "0<(1::int)+1" by simp
 have divides: "(1::int) dvd int(1::nat)" by simp
 have direction: "is_direction 1 1" by (simp add: is_direction_def)
 obtain T where T: "T\<in>weyl_algebra" and Tnz: "T\<noteq>0"
   and Tweight: "ramified_weight_deg 1 1 1 (polynomial_ramified_lift 1 T)=int 1*(1+1)"
   and degree: "ramified_weight_deg 1 1 1
    (laurent_comp (polynomial_ramified_lift 1 P)(polynomial_ramified_lift 1 T)-
      laurent_comp (polynomial_ramified_lift 1 T)(polynomial_ramified_lift 1 P))=
    ramified_weight_deg 1 1 1 (polynomial_ramified_lift 1 P)"
   and face: "ramified_top_face_polynomial 1 1 1
    (laurent_comp (polynomial_ramified_lift 1 P)(polynomial_ramified_lift 1 T)-
      laurent_comp (polynomial_ramified_lift 1 T)(polynomial_ramified_lift 1 P))=
    ramified_top_face_polynomial 1 1 1 (polynomial_ramified_lift 1 P)"
   using preliminary_companion_has_polynomial_cut_witness[OF source one pair direction rho divides] by blast
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have Ppos: "0<v_degree 1 1 P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have Pnz: "P\<noteq>0" using Ppos by auto
 have LPnz: "polynomial_ramified_lift 1 P\<noteq>0"
   using polynomial_ramified_lift_injective[OF one P, where Q=0] Pnz
   by (auto simp: weyl_algebra_def)
 have LTnz: "polynomial_ramified_lift 1 T\<noteq>0"
   using polynomial_ramified_lift_injective[OF one T, where Q=0] Tnz
   by (auto simp: weyl_algebra_def)
 have budget: "card(set_mset(proots(ramified_top_face_polynomial 1 1 1
   (polynomial_ramified_lift 1 P))))\<le>degree(ramified_top_face_polynomial 1 1 1
   (-polynomial_ramified_lift 1 T))"
   by (rule ramified_source_companion_top_face_root_count[OF one rho sum
     polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier LPnz LTnz degree face Tweight])
 have negT: "-T\<in>weyl_algebra"
   using op_adjoin.diff[OF op_adjoin_zero T[unfolded weyl_algebra_def]] by (simp add: weyl_algebra_def)
 have negative_lift: "polynomial_ramified_lift 1 (-T)= -polynomial_ramified_lift 1 T"
   using polynomial_ramified_lift_diff[OF one, where P=0 and Q=T] T
   by (simp add: weyl_algebra_def)
 have negative_weight: "ramified_weight_deg 1 1 1 (polynomial_ramified_lift 1 (-T))=int(2::nat)"
   by (simp only: negative_lift ramifiedWeightDeg_neg[OF one polynomial_ramified_lift_carrier] Tweight; simp)
 have bound: "degree(ramified_top_face_polynomial 1 1 1 (polynomial_ramified_lift 1 (-T)))\<le>2"
   by (rule polynomialRamified_diagonal_topFace_natDegree_le[OF negT negative_weight])
 have actual_face: "ramified_top_face_polynomial 1 1 1 (polynomial_ramified_lift 1 P)=cut_poly 1 1 P"
   by (rule polynomial_ramified_lift_top_face[OF one P rho divides])
 have actual_budget: "card(set_mset(proots(cut_poly 1 1 P)))\<le>
   degree(ramified_top_face_polynomial 1 1 1 (polynomial_ramified_lift 1 (-T)))"
   using budget by (simp only: actual_face negative_lift)

 have Ftwo: "degree(ramified_top_face_polynomial 1 1 1 (polynomial_ramified_lift 1 (-T)))=2"
   using roots actual_budget bound by arith
 have cut_nonzero: "cut_poly 1 1 P\<noteq>0" by (rule counterexample_diagonal_cut_ne_zero[OF pair])
 have roots_bound: "card(set_mset(proots(cut_poly 1 1 P)))\<le>degree(cut_poly 1 1 P)"
   using card_poly_roots_bound[OF cut_nonzero] by (simp only: set_count_proots[OF cut_nonzero])
 have Pdegree: "0<degree(ramified_top_face_polynomial 1 1 1 (polynomial_ramified_lift 1 P))"
   using roots roots_bound by (simp only: actual_face; arith)
 have Fdegree: "2\<le>degree(ramified_top_face_polynomial 1 1 1 (-polynomial_ramified_lift 1 T))"
   by (simp only: negative_lift[symmetric] Ftwo)
 have weight: "ramified_weight_deg 1 1 1 (polynomial_ramified_lift 1 P)=1*v_degree 1 1 P"
   by (simp only: polynomial_ramified_lift_weight_degree[OF one P]; simp)
 have identity: "v_degree 1 1 P*int(degree(ramified_top_face_polynomial 1 1 1 (-polynomial_ramified_lift 1 T)))=
   (int 1+ramified_cut_exponent 1 1 1)*int(degree(ramified_top_face_polynomial 1 1 1 (polynomial_ramified_lift 1 P)))"
   by (rule ramified_source_companion_endpoint_degree_identity[OF one rho divides sum
     polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier LPnz LTnz weight degree face Tweight Pdegree Fdegree])
 have negative_degree: "degree(ramified_top_face_polynomial 1 1 1 (-polynomial_ramified_lift 1 T))=2"
   using arg_cong[where f="\<lambda>S. degree(ramified_top_face_polynomial 1 1 1 S)", OF negative_lift[symmetric]]
   by (simp only: Ftwo)
 have exponent_value: "ramified_cut_exponent 1 1 1=1" by (simp add: ramified_cut_exponent_def)
 have scaled_identity: "v_degree 1 1 P*2=2*int(degree(cut_poly 1 1 P))"
   using identity by (simp only: negative_degree actual_face exponent_value of_nat_1 of_nat_numeral; simp)
 show ?thesis using scaled_identity by linarith
qed

lemma preliminary_diagonal_cut_factorization:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
 shows "(\<exists>lam::complex. lam\<noteq>0 \<and> cut_poly 1 1 P=[:lam:]) \<or>
 (\<exists>lam alpha::complex. \<exists>k::nat. lam\<noteq>0 \<and> 1\<le>k \<and>
 cut_poly 1 1 P=[:lam:]*[:-alpha,1:]^k) \<or>
 (\<exists>lam alpha beta::complex. \<exists>u v::nat.
 lam\<noteq>0 \<and> alpha\<noteq>beta \<and> 1\<le>u \<and> 1\<le>v \<and>
 cut_poly 1 1 P=[:lam:]*[:-alpha,1:]^u*[:-beta,1:]^v)"
 by (rule complex_polynomial_two_root_factorization[OF counterexample_diagonal_cut_ne_zero[OF pair]
   preliminary_diagonal_cut_distinct_roots_le_two[OF source pair]])

lemma preliminary_two_root_cut_face:
 fixes P Q::"complex poly_operator" and lam alpha beta::complex and u v::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and lam: "lam\<noteq>0" and distinct: "alpha\<noteq>beta" and u: "1\<le>u" and v: "1\<le>v"
   and cut: "cut_poly 1 1 P=[:lam:]*[:-alpha,1:]^u*[:-beta,1:]^v"
 shows "leading_form 1 1 P=[:[:lam:]:]*
   (biv_monom 1 0 1-[:[:alpha:]:]*biv_monom 1 1 0)^u*
   (biv_monom 1 0 1-[:[:beta:]:]*biv_monom 1 1 0)^v"
proof -
 let ?p="cut_poly 1 1 P"
 have nonzero: "?p\<noteq>0" by (rule counterexample_diagonal_cut_ne_zero[OF pair])
 have upos: "0<u" using u by arith
 have vpos: "0<v" using v by arith
 have alpha_zero: "poly ?p alpha=0"
   by (simp add: cut poly_mult poly_power zero_power[OF upos])
 have beta_zero: "poly ?p beta=0"
   by (simp add: cut poly_mult poly_power zero_power[OF vpos])
 have alpha: "alpha\<in>set_mset(proots ?p)" using alpha_zero nonzero by simp
 have beta: "beta\<in>set_mset(proots ?p)" using beta_zero nonzero by simp
 have subset: "{alpha,beta}\<subseteq>set_mset(proots ?p)" using alpha beta by blast
 have cardinal: "card {alpha,beta}\<le>card(set_mset(proots ?p))"
   by (rule card_mono) (simp, rule subset)
 have roots: "2\<le>card(set_mset(proots ?p))" using cardinal distinct by simp
 have weight: "v_degree 1 1 P=int(degree ?p)"
   by (rule preliminary_diagonal_two_roots_exhaust_weight[OF source pair roots])
 have degree: "degree ?p=u+v"
   by (simp add: cut degree_mult_eq degree_power_eq lam)
 have whole: "v_degree 1 1 P=int(0+u+v)" using weight by (simp only: degree; simp)
 show ?thesis using diagonal_face_eq_of_factored_cut[OF whole cut] by simp
qed

end
