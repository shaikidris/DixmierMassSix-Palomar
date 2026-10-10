theory Ramified_First_Slope_Alignment
 imports Ramified_Unequal_Face_Exclusion Ramified_Rational_Tilt_Direction
begin

lemma ramified_exact_pair_no_earlier_first_slope:
 fixes E F B::"int\<times>nat" and tP tQ::rat
 assumes l: "0<l" and rho: "0<rho"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and positive: "0<tP" and early: "tP<of_nat l*of_int(rho+sigma)" and before: "tP<tQ"
 and order: "2\<le>snd F" and old: "int(snd E)*fst F=int(snd F)*fst E"
 and EP: "E\<in>ramified_pbw_support l P" and FQ: "F\<in>ramified_pbw_support l Q"
 and BP: "B\<in>ramified_pbw_support l P" and lower: "snd B<snd E"
 and Eold: "ramified_weight l rho sigma E=VP" and Fold: "ramified_weight l rho sigma F=VQ"
 and Pfirst: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>
 of_int(ramified_weight l rho sigma p)-tP*of_nat(snd p)\<le>of_int VP-tP*of_nat(snd E)"
 and Btie: "of_int(ramified_weight l rho sigma B)-tP*of_nat(snd B)=of_int VP-tP*of_nat(snd E)"
 and Qold: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>ramified_weight l rho sigma q\<le>VQ"
 and Qfirst: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>
 of_int(ramified_weight l rho sigma q)-tQ*of_nat(snd q)\<le>of_int VQ-tQ*of_nat(snd F)"
 shows False
proof -
 let ?r="rationalTiltRho l rho tP" let ?s="rationalTiltSigma l sigma tP"
 have rpos: "0<?r" by (rule rationalTilt_rho_pos[OF l rho])
 have sumpos: "0<?r+?s" by (rule rationalTilt_sum_pos[OF early])
 have Ptilt: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>
 of_int(ramified_weight l rho sigma p)-tP*of_nat(snd p)\<le>
 of_int(ramified_weight l rho sigma E)-tP*of_nat(snd E)"
   using Pfirst Eold by simp
 have nonneg: "0\<le>tP" and le: "tP\<le>tQ" using positive before by simp_all
 have Qtilt: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>
 of_int(ramified_weight l rho sigma q)-tP*of_nat(snd q)\<le>
 of_int(ramified_weight l rho sigma F)-tP*of_nat(snd F)"
   using finiteSupport_before_first_slope_bound[where S="ramified_pbw_support l Q"
 and w="ramified_weight l rho sigma" and V=VQ and M="snd F" and t=tP and tFirst=tQ,
 OF nonneg le Qold Qfirst] Fold by simp
 have Pu: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l ?r ?s p\<le>ramified_weight l ?r ?s E"
   by (rule rationalTilt_support_bound[OF l Ptilt])
 have Qu: "\<forall>q\<in>ramified_pbw_support l Q. ramified_weight l ?r ?s q\<le>ramified_weight l ?r ?s F"
   by (rule rationalTilt_support_bound[OF l Qtilt])
 have Et: "ramified_weight l ?r ?s E=ramified_weight_deg l ?r ?s P"
   by (rule sym, rule ramified_weight_deg_eq_of_attained_upper) (use EP Pu in auto)
 have Ft: "ramified_weight l ?r ?s F=ramified_weight_deg l ?r ?s Q"
   by (rule sym, rule ramified_weight_deg_eq_of_attained_upper) (use FQ Qu in auto)
 have Bt: "ramified_weight l ?r ?s B=ramified_weight_deg l ?r ?s P"
 proof -
   have cast: "(of_int(ramified_weight l ?r ?s B)::rat)=of_int(ramified_weight l ?r ?s E)"
     by (simp only: rationalTilt_weight_scale Eold Btie)
   have "ramified_weight l ?r ?s B=ramified_weight l ?r ?s E" using cast by simp
   then show ?thesis using Et by simp
 qed
 have Pdegree: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l ?r ?s p\<le>ramified_weight_deg l ?r ?s P"
   using Pu Et by simp
 have canonical: "snd B\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P) \<and>
 ramified_weight l ?r ?s(ramified_pbw_top_laurent l P(snd B),snd B)=ramified_weight_deg l ?r ?s P"
   using ramified_face_point_top_laurent_at_order[OF rpos BP Bt Pdegree] by blast
 have singleton: "\<And>u. u\<in>ramified_pbw_support l Q \<Longrightarrow>
 ramified_weight l ?r ?s u=ramified_weight_deg l ?r ?s Q \<Longrightarrow>u=F"
 proof -
   fix u assume u: "u\<in>ramified_pbw_support l Q"
     and top: "ramified_weight l ?r ?s u=ramified_weight_deg l ?r ?s Q"
   have tie: "ramified_weight l ?r ?s u=ramified_weight l ?r ?s F" using top Ft by simp
   show "u=F" by (rule rationalTilt_before_first_slope_singleton[OF l rho positive before Fold Qold Qfirst u tie])
 qed
 show False by (rule ramified_exact_pair_no_unequal_first_face[OF l rpos sumpos P Q exact order old Et Ft _ _ lower singleton])
   (use canonical in blast)+
qed
end
