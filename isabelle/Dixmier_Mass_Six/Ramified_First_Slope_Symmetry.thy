theory Ramified_First_Slope_Symmetry
 imports Ramified_First_Slope_Alignment
begin

lemma ramifiedPBWCoeffs_neg:
 assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
 shows "ramified_pbw_coeffs l (-T)=-ramified_pbw_coeffs l T"
proof -
 have neg: "-T=normal_smult (-1) T" by (simp only: normal_smult_minus_one)
 show ?thesis by (rule poly_mapping_eqI, rule poly_mapping_eqI)
   (simp add: neg ramified_pbw_coeffs_smult[OF l T] laurent_smult_lookup)
qed

lemma ramifiedPBWSupport_neg:
 assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
 shows "ramified_pbw_support l (-T)=ramified_pbw_support l T"
 by (auto simp: ramified_pbw_support_def ramifiedPBWCoeffs_neg[OF l T] Poly_Mapping.in_keys_iff)

lemma ramified_exact_pair_no_later_first_slope:
 fixes E F B::"int\<times>nat" and tP tQ::rat
 assumes l: "0<l" and rho: "0<rho"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and positive: "0<tQ" and early: "tQ<of_nat l*of_int(rho+sigma)" and before: "tQ<tP"
 and order: "2\<le>snd E" and old: "int(snd E)*fst F=int(snd F)*fst E"
 and EP: "E\<in>ramified_pbw_support l P" and FQ: "F\<in>ramified_pbw_support l Q"
 and BQ: "B\<in>ramified_pbw_support l Q" and lower: "snd B<snd F"
 and Eold: "ramified_weight l rho sigma E=VP" and Fold: "ramified_weight l rho sigma F=VQ"
 and Qfirst: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>
 of_int(ramified_weight l rho sigma q)-tQ*of_nat(snd q)\<le>of_int VQ-tQ*of_nat(snd F)"
 and Btie: "of_int(ramified_weight l rho sigma B)-tQ*of_nat(snd B)=of_int VQ-tQ*of_nat(snd F)"
 and Pold: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>ramified_weight l rho sigma p\<le>VP"
 and Pfirst: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>
 of_int(ramified_weight l rho sigma p)-tP*of_nat(snd p)\<le>of_int VP-tP*of_nat(snd E)"
 shows False
proof -
 have minusP: "-P\<in>ramified_operator_algebra l"
   using ramified_algebra_smult[OF P, where c="-1"] by (simp only: normal_smult_minus_one)
 have Qlinear: "laurent_linear Q" by (rule ramified_operator_algebra_linear[OF Q])
 have reverse: "laurent_comp (-P) Q-laurent_comp Q (-P)=id"
 proof -
   have left: "laurent_comp (-P) Q= -laurent_comp P Q"
     using laurent_comp_smult_left[where c="-1" and T=P and U=Q]
     by (simp only: normal_smult_minus_one)
   have right: "laurent_comp Q (-P)= -laurent_comp Q P"
     using laurent_comp_smult_right[OF Qlinear, where c="-1" and U=P]
     by (simp only: normal_smult_minus_one)
   have "laurent_comp (-P) Q-laurent_comp Q (-P)=laurent_comp Q P-laurent_comp P Q"
     by (simp only: left right) (simp add: algebra_simps)
   then show ?thesis using exact by simp
 qed
 have support: "ramified_pbw_support l (-P)=ramified_pbw_support l P"
   by (rule ramifiedPBWSupport_neg[OF l P])
 have Eneg: "E\<in>ramified_pbw_support l (-P)" using EP by (simp only: support)
 have oldReverse: "int(snd F)*fst E=int(snd E)*fst F" using old by simp
 have negOld: "\<And>p. p\<in>ramified_pbw_support l (-P) \<Longrightarrow>ramified_weight l rho sigma p\<le>VP"
   using Pold by (simp only: support)
 have negFirst: "\<And>p. p\<in>ramified_pbw_support l (-P) \<Longrightarrow>
 of_int(ramified_weight l rho sigma p)-tP*of_nat(snd p)\<le>of_int VP-tP*of_nat(snd E)"
   using Pfirst by (simp only: support)
 show False by (rule ramified_exact_pair_no_earlier_first_slope[OF l rho Q minusP reverse
 positive early before order oldReverse FQ Eneg BQ lower Fold Eold Qfirst Btie negOld negFirst])
qed
end
