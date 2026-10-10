theory Ramified_Diagonal_Cut_Certificate
 imports Ramified_Companion_Positive_Threshold
   "Ramified_Mate_Root_Alignment"
begin

lemma ramified_exact_pair_full_degree_root_mate_of_reverse_commutator:
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0" and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and Ppos: "0<ramified_weight_deg l rho sigma P" and Qpos: "0<ramified_weight_deg l rho sigma Q"
 and threshold: "0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
 and full: "rootMultiplicity c (ramified_top_face_polynomial l rho sigma P)=degree(ramified_top_face_polynomial l rho sigma P)"
 shows "rootMultiplicity c (ramified_top_face_polynomial l rho sigma Q)=degree(ramified_top_face_polynomial l rho sigma Q)"
proof -
 have threshold': "0<ramified_weight_deg l rho sigma Q+ramified_weight_deg l rho sigma P-int l*(rho+sigma)" using threshold by arith
 note root = ramified_exact_pair_top_face_rootMultiplicity_ratio[where a=c, OF l rho sum Q P Qnz Pnz exact Qpos Ppos threshold']
 note degree = ramified_exact_pair_top_face_degree_ratio[OF l rho sum Q P Qnz Pnz exact Qpos Ppos threshold']
 have scaled: "nat(ramified_weight_deg l rho sigma P)*rootMultiplicity c (ramified_top_face_polynomial l rho sigma Q)=
   nat(ramified_weight_deg l rho sigma P)*degree(ramified_top_face_polynomial l rho sigma Q)"
   using root degree by (simp only: full)
 have nz: "nat(ramified_weight_deg l rho sigma P)\<noteq>0" using Ppos by simp
 show ?thesis by (rule iffD1[OF mult_left_cancel[OF nz] scaled])
qed

lemma ramified_diagonal_companion_exact_pair_cut_certificate:
 assumes l: "0<l" and rho: "0<rho" and direction: "is_direction rho sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0" and Fnz: "F\<noteq>0" and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and Ppos: "0<ramified_weight_deg l rho sigma P" and Qpos: "0<ramified_weight_deg l rho sigma Q"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and linear: "degree(ramified_top_face_polynomial l rho sigma (-F))=1"
 and Pdegree: "2\<le>degree(ramified_top_face_polynomial l rho sigma P)"
 and member: "j\<in>polynomial_support(ramified_top_face_polynomial l rho sigma P)"
 and distinct: "j\<noteq>degree(ramified_top_face_polynomial l rho sigma P)"
 shows "rho dvd int l \<and>
   0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma) \<and>
   (\<exists>c::complex. c\<noteq>0 \<and> poly(ramified_top_face_polynomial l rho sigma P)c=0 \<and>
     rootMultiplicity c (ramified_top_face_polynomial l rho sigma P)=degree(ramified_top_face_polynomial l rho sigma P) \<and>
     rootMultiplicity c (ramified_top_face_polynomial l rho sigma Q)=degree(ramified_top_face_polynomial l rho sigma Q))"
proof -
 have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have gap: "degree(ramified_top_face_polynomial l rho sigma (-F))<degree(ramified_top_face_polynomial l rho sigma P)" using linear Pdegree by arith
 have threshold: "0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
   by (rule ramified_exact_pair_positive_threshold_of_source_companion_degree_gap[OF l rho sum P Q F Pnz Qnz Fnz exact Ppos Qpos degree face Fweight gap])
 obtain c where divides: "rho dvd int l" and cnz: "c\<noteq>0"
 and root: "poly(ramified_top_face_polynomial l rho sigma P)c=0"
 and full: "rootMultiplicity c (ramified_top_face_polynomial l rho sigma P)=degree(ramified_top_face_polynomial l rho sigma P)"
   using ramified_linear_source_companion_admissible_full_root[OF l rho direction P F Pnz Fnz degree face Fweight linear member distinct] by blast
 have mate: "rootMultiplicity c (ramified_top_face_polynomial l rho sigma Q)=degree(ramified_top_face_polynomial l rho sigma Q)"
   by (rule ramified_exact_pair_full_degree_root_mate_of_reverse_commutator[OF l rho sum P Q Pnz Qnz exact Ppos Qpos threshold full])
 show ?thesis by (intro conjI[OF divides] conjI[OF threshold] exI[of _ c]) (use cnz root full mate in auto)
qed

end
