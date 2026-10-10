theory Ramified_Common_First_Slope
 imports Ramified_First_Slope_Symmetry
begin

lemma ramified_exact_pair_first_slopes_equal_of_one_early:
 fixes E F BP BQ::"int\<times>nat" and tP tQ::rat
 assumes l: "0<l" and rho: "0<rho"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and tP: "0<tP" and tQ: "0<tQ"
 and early: "tP<of_nat l*of_int(rho+sigma) \<or>tQ<of_nat l*of_int(rho+sigma)"
 and Eorder: "2\<le>snd E" and Forder: "2\<le>snd F"
 and old: "int(snd E)*fst F=int(snd F)*fst E"
 and EP: "E\<in>ramified_pbw_support l P" and FQ: "F\<in>ramified_pbw_support l Q"
 and BP: "BP\<in>ramified_pbw_support l P" and BQ: "BQ\<in>ramified_pbw_support l Q"
 and Plower: "snd BP<snd E" and Qlower: "snd BQ<snd F"
 and Eold: "ramified_weight l rho sigma E=VP" and Fold: "ramified_weight l rho sigma F=VQ"
 and Pold: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>ramified_weight l rho sigma p\<le>VP"
 and Qold: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>ramified_weight l rho sigma q\<le>VQ"
 and Pfirst: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>
 of_int(ramified_weight l rho sigma p)-tP*of_nat(snd p)\<le>of_int VP-tP*of_nat(snd E)"
 and Qfirst: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>
 of_int(ramified_weight l rho sigma q)-tQ*of_nat(snd q)\<le>of_int VQ-tQ*of_nat(snd F)"
 and Ptie: "of_int(ramified_weight l rho sigma BP)-tP*of_nat(snd BP)=of_int VP-tP*of_nat(snd E)"
 and Qtie: "of_int(ramified_weight l rho sigma BQ)-tQ*of_nat(snd BQ)=of_int VQ-tQ*of_nat(snd F)"
 shows "tP=tQ"
proof (rule ccontr)
 assume ne: "tP\<noteq>tQ"
 consider (less) "tP<tQ" | (greater) "tQ<tP" using ne by arith
 then show False
 proof cases
   case less
   have earlyP: "tP<of_nat l*of_int(rho+sigma)" using early less by auto
   show False by (rule ramified_exact_pair_no_earlier_first_slope[OF l rho P Q exact
     tP earlyP less Forder old EP FQ BP Plower Eold Fold Pfirst Ptie Qold Qfirst])
 next
   case greater
   have earlyQ: "tQ<of_nat l*of_int(rho+sigma)" using early greater by auto
   show False by (rule ramified_exact_pair_no_later_first_slope[OF l rho P Q exact
     tQ earlyQ greater Eorder old EP FQ BQ Qlower Eold Fold Qfirst Qtie Pold Pfirst])
 qed
qed

lemma ramified_exact_pair_first_slopes_equal:
 fixes E F BP BQ::"int\<times>nat" and tP tQ::rat
 assumes l: "0<l" and rho: "0<rho"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and tP: "0<tP" and tQ: "0<tQ"
 and earlyP: "tP<of_nat l*of_int(rho+sigma)" and earlyQ: "tQ<of_nat l*of_int(rho+sigma)"
 and Eorder: "2\<le>snd E" and Forder: "2\<le>snd F"
 and old: "int(snd E)*fst F=int(snd F)*fst E"
 and EP: "E\<in>ramified_pbw_support l P" and FQ: "F\<in>ramified_pbw_support l Q"
 and BP: "BP\<in>ramified_pbw_support l P" and BQ: "BQ\<in>ramified_pbw_support l Q"
 and Plower: "snd BP<snd E" and Qlower: "snd BQ<snd F"
 and Eold: "ramified_weight l rho sigma E=VP" and Fold: "ramified_weight l rho sigma F=VQ"
 and Pold: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>ramified_weight l rho sigma p\<le>VP"
 and Qold: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>ramified_weight l rho sigma q\<le>VQ"
 and Pfirst: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>
 of_int(ramified_weight l rho sigma p)-tP*of_nat(snd p)\<le>of_int VP-tP*of_nat(snd E)"
 and Qfirst: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>
 of_int(ramified_weight l rho sigma q)-tQ*of_nat(snd q)\<le>of_int VQ-tQ*of_nat(snd F)"
 and Ptie: "of_int(ramified_weight l rho sigma BP)-tP*of_nat(snd BP)=of_int VP-tP*of_nat(snd E)"
 and Qtie: "of_int(ramified_weight l rho sigma BQ)-tQ*of_nat(snd BQ)=of_int VQ-tQ*of_nat(snd F)"
 shows "tP=tQ"
 by (rule ramified_exact_pair_first_slopes_equal_of_one_early[OF l rho P Q exact tP tQ _
 Eorder Forder old EP FQ BP BQ Plower Qlower Eold Fold Pold Qold Pfirst Qfirst Ptie Qtie])
   (use earlyP in blast)
end
