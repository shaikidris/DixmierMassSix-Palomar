theory Ramified_Common_First_Tilt
 imports Ramified_Common_Integral_Face
begin

lemma ramified_common_first_tilt_primitive_face:
 fixes E F BP BQ::"int\<times>nat" and t::rat
 assumes l: "0<l" and rho: "0<rho"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and t: "0<t" and early: "t<of_nat l*of_int(rho+sigma)"
 and E: "E\<in>ramified_pbw_support l P" and F: "F\<in>ramified_pbw_support l Q"
 and BP: "BP\<in>ramified_pbw_support l P" and BQ: "BQ\<in>ramified_pbw_support l Q"
 and Ew: "ramified_weight l rho sigma E=VP" and Fw: "ramified_weight l rho sigma F=VQ"
 and Pold: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>ramified_weight l rho sigma p\<le>VP"
 and Qold: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>ramified_weight l rho sigma q\<le>VQ"
 and Pfirst: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>
 of_int(ramified_weight l rho sigma p)-t*of_nat(snd p)\<le>of_int VP-t*of_nat(snd E)"
 and Qfirst: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>
 of_int(ramified_weight l rho sigma q)-t*of_nat(snd q)\<le>of_int VQ-t*of_nat(snd F)"
 and Ptie: "of_int(ramified_weight l rho sigma BP)-t*of_nat(snd BP)=of_int VP-t*of_nat(snd E)"
 and Qtie: "of_int(ramified_weight l rho sigma BQ)-t*of_nat(snd BQ)=of_int VQ-t*of_nat(snd F)"
 shows "\<exists>r s::int. is_direction r s \<and>0<r \<and>(sigma\<le>0 \<longrightarrow>s<0) \<and>
 ramified_weight l r s E=ramified_weight_deg l r s P \<and>
 ramified_weight l r s F=ramified_weight_deg l r s Q \<and>
 ramified_weight l r s BP=ramified_weight_deg l r s P \<and>
 ramified_weight l r s BQ=ramified_weight_deg l r s Q \<and>
 (\<forall>p\<in>ramified_pbw_support l P. ramified_weight l r s p=ramified_weight_deg l r s P \<longrightarrow>
 fst E-int l*int(snd E)\<le>fst p-int l*int(snd p)) \<and>
 (\<forall>q\<in>ramified_pbw_support l Q. ramified_weight l r s q=ramified_weight_deg l r s Q \<longrightarrow>
 fst F-int l*int(snd F)\<le>fst q-int l*int(snd q))"
proof -
 obtain R S where Rd: "R=rationalTiltRho l rho t" and Sd: "S=rationalTiltSigma l sigma t"
 and R: "0<R" and sum: "0<R+S"
 and Pu: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l R S p\<le>ramified_weight l R S E"
 and Qu: "\<forall>q\<in>ramified_pbw_support l Q. ramified_weight l R S q\<le>ramified_weight l R S F"
 and EtR: "ramified_weight l R S E=ramified_weight_deg l R S P"
 and FtR: "ramified_weight l R S F=ramified_weight_deg l R S Q"
 and BPtR: "ramified_weight l R S BP=ramified_weight_deg l R S P"
 and BQtR: "ramified_weight l R S BQ=ramified_weight_deg l R S Q"
   using ramified_common_rational_tilt_integral_face[OF l rho P Q early E F BP BQ Ew Fw Pfirst Qfirst Ptie Qtie] by blast
 have Pur: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>ramified_weight l R S p\<le>ramified_weight l R S E" using Pu by blast
 have Qur: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>ramified_weight l R S q\<le>ramified_weight l R S F" using Qu by blast
 have Pt: "ramified_weight l R S BP=ramified_weight l R S E" using BPtR EtR by simp
 have Qt: "ramified_weight l R S BQ=ramified_weight l R S F" using BQtR FtR by simp
 obtain r s g where g: "0<g" and Rg: "R=g*r" and Sg: "S=g*s"
 and direction: "is_direction r s" and r: "0<r"
 and Et: "ramified_weight l r s E=ramified_weight_deg l r s P"
 and Ft: "ramified_weight l r s F=ramified_weight_deg l r s Q"
 and BPt: "ramified_weight l r s BP=ramified_weight_deg l r s P"
 and BQt: "ramified_weight l r s BQ=ramified_weight_deg l r s Q"
   using ramified_common_integral_face_primitive[OF l R sum P Q E F Pur Qur Pt Qt] by blast
 have RR: "rationalTiltRho l rho t=g*r" using Rd Rg by simp
 have SS: "rationalTiltSigma l sigma t=g*s" using Sd Sg by simp
 have sNeg: "s<0" if sigma: "sigma\<le>0"
 proof -
   obtain a b where quotient: "quotient_of t=(a,b)" by (cases "quotient_of t") auto
   have b: "0<b" by (rule quotient_of_denom_pos[OF quotient])
   have fraction: "t=of_int a/of_int b" by (rule quotient_of_div[OF quotient])
   have a: "0<a" using t b by (simp add: fraction zero_less_divide_iff)
   have product: "sigma*int l*b\<le>0" using sigma l b by (simp add: mult_le_0_iff)
   have Sneg: "S<0" using product a Sd by (simp add: rationalTiltSigma_def quotient)
   show ?thesis using Sneg Sg g by (simp add: mult_less_0_iff)
 qed
 have sumrs: "0<r+s" using direction by (simp add: is_direction_def)
 note Pmin = ramified_first_tilt_old_start_min_grade[OF l P t Ew Pold g RR SS r sumrs Et]
 note Qmin = ramified_first_tilt_old_start_min_grade[OF l Q t Fw Qold g RR SS r sumrs Ft]
 have negative: "sigma\<le>0 \<longrightarrow>s<0" using sNeg by blast
 show ?thesis
 proof (rule exI[where x=r], rule exI[where x=s], intro conjI)
   show "is_direction r s" by (rule direction)
   show "0<r" by (rule r)
   show "sigma\<le>0 \<longrightarrow>s<0" by (rule negative)
   show "ramified_weight l r s E=ramified_weight_deg l r s P" by (rule Et)
   show "ramified_weight l r s F=ramified_weight_deg l r s Q" by (rule Ft)
   show "ramified_weight l r s BP=ramified_weight_deg l r s P" by (rule BPt)
   show "ramified_weight l r s BQ=ramified_weight_deg l r s Q" by (rule BQt)
   show "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l r s p=ramified_weight_deg l r s P \<longrightarrow>
     fst E-int l*int(snd E)\<le>fst p-int l*int(snd p)" by (rule Pmin)
   show "\<forall>q\<in>ramified_pbw_support l Q. ramified_weight l r s q=ramified_weight_deg l r s Q \<longrightarrow>
     fst F-int l*int(snd F)\<le>fst q-int l*int(snd q)" by (rule Qmin)
 qed
qed
end
