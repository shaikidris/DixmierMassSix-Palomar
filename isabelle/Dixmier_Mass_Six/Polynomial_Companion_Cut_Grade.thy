theory Polynomial_Companion_Cut_Grade
 imports Symbol_Operator_Preliminary
   "Polynomial_Cut_Mate_Alignment"
   "Ramified_Cut_Companion_Strict_Grade"
begin

lemma native_preliminary_actual_operator:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput"
 and pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 shows "\<exists>T::complex poly_operator. T\<in>weyl_algebra \<and> T\<noteq>0 \<and>
 v_degree rho sigma T=rho+sigma \<and> weighted_homogeneous rho sigma (rho+sigma)(pbw_symbol T) \<and>
 v_degree rho sigma (op_comp P T-op_comp T P)=v_degree rho sigma P \<and>
 leading_form rho sigma (op_comp P T-op_comp T P)=leading_form rho sigma P"
proof -
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
 have Tnz: "T\<noteq>0" using symbol Fnz by auto
 have Tface: "leading_form rho sigma T=F"
   by (simp only: leading_form_def Tdegree symbol native_homogeneous_component_self[OF hom])
 have bracket: "biv_poisson(leading_form rho sigma P)(leading_form rho sigma T)\<noteq>0"
   by (simp only: Tface fixed Pnz not_False_eq_True)
 have result: "v_degree rho sigma (op_comp P T-op_comp T P)=v_degree rho sigma P \<and>
   leading_form rho sigma (op_comp P T-op_comp T P)=leading_form rho sigma P"
   using leading_form_commutator[OF T P sum bracket] by (simp add: Tdegree Tface fixed)
 show ?thesis by (intro exI[of _ T]) (use T Tnz Tdegree hom symbol result in blast)
qed

lemma polynomialRamifiedLift_weightDeg_eq_of_pos:
 fixes P::"complex poly_operator"
 assumes "0<l" "P\<in>(weyl_algebra::complex poly_operator set)" "0<rho" "rho dvd int l" "0<v_degree rho sigma P"
 shows "ramified_weight_deg l rho sigma (polynomial_ramified_lift l P)=int l*v_degree rho sigma P"
 by (rule polynomial_ramified_lift_weight_degree[OF assms(1,2)])

lemma polynomialRamifiedLift_topFace_eq_cutPoly_of_pos:
 fixes P::"complex poly_operator"
 assumes "0<l" "P\<in>(weyl_algebra::complex poly_operator set)" "0<rho" "rho dvd int l" "0<v_degree rho sigma P"
 shows "ramified_top_face_polynomial l rho sigma (polynomial_ramified_lift l P)=cut_poly rho sigma P"
 by (rule polynomial_ramified_lift_top_face[OF assms(1,2,3,4)])

lemma preliminary_companion_has_polynomial_cut_witness:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and l: "0<l"
 and pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 and rho: "0<rho" and div: "rho dvd int l"
 shows "\<exists>T::complex poly_operator. T\<in>weyl_algebra \<and> T\<noteq>0 \<and>
 ramified_weight_deg l rho sigma (polynomial_ramified_lift l T)=int l*(rho+sigma) \<and>
 ramified_weight_deg l rho sigma (laurent_comp (polynomial_ramified_lift l P)(polynomial_ramified_lift l T)-
   laurent_comp (polynomial_ramified_lift l T)(polynomial_ramified_lift l P))=
   ramified_weight_deg l rho sigma (polynomial_ramified_lift l P) \<and>
 ramified_top_face_polynomial l rho sigma (laurent_comp (polynomial_ramified_lift l P)(polynomial_ramified_lift l T)-
   laurent_comp (polynomial_ramified_lift l T)(polynomial_ramified_lift l P))=
   ramified_top_face_polynomial l rho sigma (polynomial_ramified_lift l P)"
proof -
 obtain T where T: "T\<in>weyl_algebra" and Tnz: "T\<noteq>0"
 and Tdegree: "v_degree rho sigma T=rho+sigma"
 and Hdegree: "v_degree rho sigma (op_comp P T-op_comp T P)=v_degree rho sigma P"
 and Hface: "leading_form rho sigma (op_comp P T-op_comp T P)=leading_form rho sigma P"
   using native_preliminary_actual_operator[OF source pair direction] by blast
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 let ?H="op_comp P T-op_comp T P"
 have H: "?H\<in>weyl_algebra" using P T
   by (auto simp: weyl_algebra_def intro: op_adjoin.comp op_adjoin.diff)
 have comm: "laurent_comp (polynomial_ramified_lift l P)(polynomial_ramified_lift l T)-
   laurent_comp (polynomial_ramified_lift l T)(polynomial_ramified_lift l P)=polynomial_ramified_lift l ?H"
   by (rule polynomial_ramified_lift_commutator[OF l T P, symmetric])
 have weight: "ramified_weight_deg l rho sigma (polynomial_ramified_lift l T)=int l*(rho+sigma)"
   by (simp only: polynomial_ramified_lift_weight_degree[OF l T] Tdegree)
 have degree: "ramified_weight_deg l rho sigma (polynomial_ramified_lift l ?H)=
   ramified_weight_deg l rho sigma (polynomial_ramified_lift l P)"
   by (simp only: polynomial_ramified_lift_weight_degree[OF l H] polynomial_ramified_lift_weight_degree[OF l P] Hdegree)
 have cut: "cut_poly rho sigma ?H=cut_poly rho sigma P" by (simp only: cut_poly_def Hface)
 have face: "ramified_top_face_polynomial l rho sigma (polynomial_ramified_lift l ?H)=
   ramified_top_face_polynomial l rho sigma (polynomial_ramified_lift l P)"
   by (simp only: polynomial_ramified_lift_top_face[OF l H rho div] polynomial_ramified_lift_top_face[OF l P rho div] cut)
 show ?thesis by (intro exI[of _ T]) (use T Tnz weight degree face in \<open>simp only: comm; blast\<close>)
qed

lemma preliminary_companion_has_ramified_cut_witness:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and l: "0<l"
 and pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 and rho: "0<rho" and div: "rho dvd int l"
 shows "\<exists>F. F\<in>ramified_operator_algebra l \<and> F\<noteq>0 \<and>
 ramified_weight_deg l rho sigma F=int l*(rho+sigma) \<and>
 ramified_weight_deg l rho sigma (laurent_comp (polynomial_ramified_lift l P) F-laurent_comp F (polynomial_ramified_lift l P))=
   ramified_weight_deg l rho sigma (polynomial_ramified_lift l P) \<and>
 ramified_top_face_polynomial l rho sigma (laurent_comp (polynomial_ramified_lift l P) F-laurent_comp F (polynomial_ramified_lift l P))=
   ramified_top_face_polynomial l rho sigma (polynomial_ramified_lift l P)"
proof -
 obtain T where T: "T\<in>weyl_algebra" and Tnz: "T\<noteq>0"
 and weight: "ramified_weight_deg l rho sigma (polynomial_ramified_lift l T)=int l*(rho+sigma)"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp (polynomial_ramified_lift l P)(polynomial_ramified_lift l T)-
   laurent_comp (polynomial_ramified_lift l T)(polynomial_ramified_lift l P))=ramified_weight_deg l rho sigma (polynomial_ramified_lift l P)"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp (polynomial_ramified_lift l P)(polynomial_ramified_lift l T)-
   laurent_comp (polynomial_ramified_lift l T)(polynomial_ramified_lift l P))=ramified_top_face_polynomial l rho sigma (polynomial_ramified_lift l P)"
   using preliminary_companion_has_polynomial_cut_witness[OF source l pair direction rho div] by blast
 have zero: "(0::complex poly_operator)\<in>weyl_algebra" by (simp add: weyl_algebra_def)
 have nonzero: "polynomial_ramified_lift l T\<noteq>0"
 proof
   assume equal_zero: "polynomial_ramified_lift l T=0"
   have equal: "polynomial_ramified_lift l T=polynomial_ramified_lift l (0::complex poly_operator)" using equal_zero by simp
   have "T=0" by (rule polynomial_ramified_lift_injective[OF l T zero equal])
   then show False using Tnz by contradiction
 qed
 show ?thesis by (intro exI[of _ "polynomial_ramified_lift l T"])
   (use polynomial_ramified_lift_carrier nonzero weight degree face in blast)
qed

lemma preliminary_companion_maxRoot_cut_grade_negative:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and l: "0<l"
 and pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 and rho: "0<rho" and div: "rho dvd int l" and Pface: "in_direction rho sigma P"
 and cut_degree: "0<degree(cut_poly rho sigma P)"
 and old_end: "((int l div rho)*v_degree rho sigma P)-
   (ramified_cut_exponent l rho sigma+int l)*int(degree(cut_poly rho sigma P))<0"
 shows "((int l div rho)*v_degree rho sigma P)-
   (ramified_cut_exponent l rho sigma+int l)*int(max_root_mult(cut_poly rho sigma P))<0"
proof -
 let ?LP="polynomial_ramified_lift l P"
 let ?LQ="polynomial_ramified_lift l Q"
 let ?r="(int l div rho)*v_degree rho sigma P"
 let ?k="ramified_cut_exponent l rho sigma"
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P-op_comp P Q=id" using pair by (auto simp: is_counterexample_pair_def)
 have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have Ppositive: "0<v_degree rho sigma P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 obtain F where F: "F\<in>ramified_operator_algebra l" and Fnz: "F\<noteq>0"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp ?LP F-laurent_comp F ?LP)=ramified_weight_deg l rho sigma ?LP"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp ?LP F-laurent_comp F ?LP)=ramified_top_face_polynomial l rho sigma ?LP"
   using preliminary_companion_has_ramified_cut_witness[OF source l pair direction rho div] by blast
 have LP: "?LP\<in>ramified_operator_algebra l" by (rule polynomial_ramified_lift_carrier)
 have LQ: "?LQ\<in>ramified_operator_algebra l" by (rule polynomial_ramified_lift_carrier)
 have comm: "laurent_comp ?LQ ?LP-laurent_comp ?LP ?LQ=id"
   by (rule polynomial_ramified_lift_bracket_one[OF l P Q exact])
 have leading_nonzero: "leading_form rho sigma P\<noteq>0"
   by (rule global_leading_form_nonzero_of_positive_degree[OF Ppositive])
 have support: "biv_support(leading_form rho sigma P)\<noteq>{}"
   using leading_nonzero by (simp only: biv_support_empty_iff not_False_eq_True)
 have exists_point: "\<exists>u. u\<in>biv_support(leading_form rho sigma P)"
   using support by (simp only: ex_in_conv not_False_eq_True)
 obtain u where u: "u\<in>biv_support(leading_form rho sigma P)" by (rule exE[OF exists_point]) assumption
 obtain i j where coordinates: "u=(i,j)" by (cases u) simp
 have point: "(i,j)\<in>biv_support(leading_form rho sigma P)"
   using u by (simp only: coordinates)
 have point_data: "(int l*int i,j)\<in>ramified_pbw_support l ?LP \<and>
   ramified_weight l rho sigma (int l*int i,j)=rho*?r"
   by (rule polynomialRamifiedLift_face_point[OF l P div point])
 have member: "(int l*int i,j)\<in>ramified_pbw_support l ?LP" using point_data by blast
 have top: "ramified_weight l rho sigma (int l*int i,j)=rho*?r" using point_data by blast
 have scale: "rho*(int l div rho)=int l" using div by (simp add: dvd_mult_div_cancel mult.commute)
 have positive: "0<rho*?r" by (simp only: mult.assoc[symmetric] scale; use l Ppositive in simp)
 have LPweight: "ramified_weight_deg l rho sigma ?LP=rho*?r"
   by (simp only: polynomial_ramified_lift_weight_degree[OF l P] mult.assoc[symmetric] scale)
 have upper: "ramified_weight l rho sigma (u,n)\<le>rho*?r" if "(u,n)\<in>ramified_pbw_support l ?LP" for u n
   using ramified_weight_deg_upper[OF that, where rho=rho and sigma=sigma] by (simp only: LPweight)
 have LPnz: "?LP\<noteq>0" using member l by (auto simp: ramified_pbw_support_def ramified_pbw_coeffs_zero)
 have top_face: "ramified_top_face_polynomial l rho sigma ?LP=cut_poly rho sigma P"
   by (rule polynomial_ramified_lift_top_face[OF l P rho div])
 have cut_face: "ramified_face_polynomial l ?LP ?r ?k=cut_poly rho sigma P"
   by (rule polynomialRamifiedFace_eq_cutPoly[OF l P rho div])
 have Pdegree: "0<degree(ramified_top_face_polynomial l rho sigma ?LP)" by (simp only: top_face cut_degree)
 have old_end_lift: "?r-(?k+int l)*int(degree(ramified_face_polynomial l ?LP ?r ?k))<0"
   by (simp only: cut_face old_end)
 obtain c where negative: "?r-(?k+int l)*int(max_root_mult(ramified_face_polynomial l ?LP ?r ?k))<0"
   using ramifiedCutAut_exists_maxRoot_negative_grade_of_source_companion[OF l rho div sum positive LP LQ F comm LPnz Fnz
     member top upper degree face Fweight Pdegree old_end_lift] by blast
 show ?thesis using negative by (simp only: cut_face)
qed

end
