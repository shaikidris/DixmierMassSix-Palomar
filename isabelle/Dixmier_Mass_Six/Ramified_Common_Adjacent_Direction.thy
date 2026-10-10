theory Ramified_Common_Adjacent_Direction
 imports Ramified_One_Sided_First_Slope
begin

lemma ramified_exact_pair_exists_common_early_adjacent_face:
 fixes E F::"int\<times>nat"
 assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and EP: "E\<in>ramified_pbw_support l P" and FQ: "F\<in>ramified_pbw_support l Q"
 and Eweight: "ramified_weight l rho sigma E=VP" and Fweight: "ramified_weight l rho sigma F=VQ"
 and Egrade: "fst E-int l*int(snd E)<0" and Fgrade: "fst F-int l*int(snd F)<0"
 and Eorder: "2\<le>snd E" and Forder: "2\<le>snd F"
 and old: "int(snd E)*fst F=int(snd F)*fst E"
 and Ptop: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>ramified_weight l rho sigma p\<le>VP"
 and Qtop: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>ramified_weight l rho sigma q\<le>VQ"
 and Pstart: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>ramified_weight l rho sigma p=VP \<Longrightarrow>snd E\<le>snd p"
 and Qstart: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>ramified_weight l rho sigma q=VQ \<Longrightarrow>snd F\<le>snd q"
 shows "\<exists>t::rat. 0<t \<and>t<of_nat l*of_int(rho+sigma) \<and>
 (\<forall>p\<in>ramified_pbw_support l P. of_int(ramified_weight l rho sigma p)-t*of_nat(snd p)\<le>of_int VP-t*of_nat(snd E)) \<and>
 (\<forall>q\<in>ramified_pbw_support l Q. of_int(ramified_weight l rho sigma q)-t*of_nat(snd q)\<le>of_int VQ-t*of_nat(snd F)) \<and>
 (\<exists>BP\<in>ramified_pbw_support l P. snd BP<snd E \<and>of_int(ramified_weight l rho sigma BP)-t*of_nat(snd BP)=of_int VP-t*of_nat(snd E)) \<and>
 (\<exists>BQ\<in>ramified_pbw_support l Q. snd BQ<snd F \<and>of_int(ramified_weight l rho sigma BQ)-t*of_nat(snd BQ)=of_int VQ-t*of_nat(snd F))"
proof -
 let ?earlyP = "\<exists>t::rat. 0<t \<and>t<of_nat l*of_int(rho+sigma) \<and>
   (\<forall>p\<in>ramified_pbw_support l P. of_int(ramified_weight l rho sigma p)-t*of_nat(snd p)\<le>of_int VP-t*of_nat(snd E)) \<and>
   (\<exists>C\<in>ramified_pbw_support l P. snd C<snd E \<and>of_int(ramified_weight l rho sigma C)-t*of_nat(snd C)=of_int VP-t*of_nat(snd E))"
 let ?earlyQ = "\<exists>t::rat. 0<t \<and>t<of_nat l*of_int(rho+sigma) \<and>
   (\<forall>q\<in>ramified_pbw_support l Q. of_int(ramified_weight l rho sigma q)-t*of_nat(snd q)\<le>of_int VQ-t*of_nat(snd F)) \<and>
   (\<exists>C\<in>ramified_pbw_support l Q. snd C<snd F \<and>of_int(ramified_weight l rho sigma C)-t*of_nat(snd C)=of_int VQ-t*of_nat(snd F))"
 have first: "?earlyP \<or> ?earlyQ"
   by (rule ramified_exact_pair_exists_early_adjacent_slope[where EP=E and EQ=F and VP=VP and VQ=VQ,
     OF l rho positive P Q exact Eweight Fweight Egrade Fgrade Ptop Qtop Pstart Qstart])
 from first show ?thesis
 proof (elim disjE)
   assume earlyPdata: "?earlyP"
   from earlyPdata obtain tP :: rat and BP :: "int\<times>nat" where tP: "0<tP" and earlyP: "tP<of_nat l*of_int(rho+sigma)"
   and Pfirst: "\<forall>p\<in>ramified_pbw_support l P. of_int(ramified_weight l rho sigma p)-tP*of_nat(snd p)\<le>of_int VP-tP*of_nat(snd E)"
   and BP: "BP\<in>ramified_pbw_support l P" and Plower: "snd BP<snd E"
   and Ptie: "of_int(ramified_weight l rho sigma BP)-tP*of_nat(snd BP)=of_int VP-tP*of_nat(snd E)" by blast
   have PfirstRule: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>
   of_int(ramified_weight l rho sigma p)-tP*of_nat(snd p)\<le>of_int VP-tP*of_nat(snd E)" using Pfirst by blast
   have belowQ: "\<exists>b\<in>ramified_pbw_support l Q. snd b<snd F"
     by (rule ramified_exact_pair_first_slope_forces_mate_lower_order[OF l rho P Q exact tP earlyP
       Forder old EP FQ BP Plower Eweight Fweight PfirstRule Ptie Qtop])
   obtain tQ :: rat and BQ :: "int\<times>nat" where tQ: "0<tQ"
   and Qfirst: "\<forall>q\<in>ramified_pbw_support l Q. of_int(ramified_weight l rho sigma q)-tQ*of_nat(snd q)\<le>of_int VQ-tQ*of_nat(snd F)"
   and BQ: "BQ\<in>ramified_pbw_support l Q" and Qlower: "snd BQ<snd F"
   and Qtie: "of_int(ramified_weight l rho sigma BQ)-tQ*of_nat(snd BQ)=of_int VQ-tQ*of_nat(snd F)"
     using finiteSupport_exists_adjacent_rational_slope[where S="ramified_pbw_support l Q"
 and w="ramified_weight l rho sigma" and V=VQ and M="snd F",
 OF ramified_pbw_support_finite Qtop Qstart belowQ] by blast
   have QfirstRule: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>
   of_int(ramified_weight l rho sigma q)-tQ*of_nat(snd q)\<le>of_int VQ-tQ*of_nat(snd F)" using Qfirst by blast
   have early: "tP<of_nat l*of_int(rho+sigma) \<or>tQ<of_nat l*of_int(rho+sigma)" using earlyP by blast
   have equal: "tP=tQ" by (rule ramified_exact_pair_first_slopes_equal_of_one_early[OF l rho P Q exact
      tP tQ early Eorder Forder old EP FQ BP BQ Plower Qlower Eweight Fweight Ptop Qtop PfirstRule QfirstRule Ptie Qtie])
   have QfirstP: "\<forall>q\<in>ramified_pbw_support l Q.
   of_int(ramified_weight l rho sigma q)-tP*of_nat(snd q)\<le>of_int VQ-tP*of_nat(snd F)"
     using Qfirst by (simp only: equal)
   have QtieP: "of_int(ramified_weight l rho sigma BQ)-tP*of_nat(snd BQ)=of_int VQ-tP*of_nat(snd F)"
     using Qtie by (simp only: equal)
   have Poccupied: "\<exists>b\<in>ramified_pbw_support l P. snd b<snd E \<and>
   of_int(ramified_weight l rho sigma b)-tP*of_nat(snd b)=of_int VP-tP*of_nat(snd E)"
   proof (rule bexI[where x=BP])
     show "snd BP<snd E \<and>
       of_int(ramified_weight l rho sigma BP)-tP*of_nat(snd BP)=of_int VP-tP*of_nat(snd E)"
       by (rule conjI[OF Plower Ptie])
     show "BP\<in>ramified_pbw_support l P" by (rule BP)
   qed
   have Qoccupied: "\<exists>b\<in>ramified_pbw_support l Q. snd b<snd F \<and>
   of_int(ramified_weight l rho sigma b)-tP*of_nat(snd b)=of_int VQ-tP*of_nat(snd F)"
   proof (rule bexI[where x=BQ])
     show "snd BQ<snd F \<and>
       of_int(ramified_weight l rho sigma BQ)-tP*of_nat(snd BQ)=of_int VQ-tP*of_nat(snd F)"
       by (rule conjI[OF Qlower QtieP])
     show "BQ\<in>ramified_pbw_support l Q" by (rule BQ)
   qed
   show ?thesis by (rule exI[where x=tP], rule conjI[OF tP conjI[OF earlyP conjI[OF Pfirst conjI[OF QfirstP conjI[OF Poccupied Qoccupied]]]]])
 next
   assume earlyQdata: "?earlyQ"
   from earlyQdata obtain tQ :: rat and BQ :: "int\<times>nat" where tQ: "0<tQ" and earlyQ: "tQ<of_nat l*of_int(rho+sigma)"
   and Qfirst: "\<forall>q\<in>ramified_pbw_support l Q. of_int(ramified_weight l rho sigma q)-tQ*of_nat(snd q)\<le>of_int VQ-tQ*of_nat(snd F)"
   and BQ: "BQ\<in>ramified_pbw_support l Q" and Qlower: "snd BQ<snd F"
   and Qtie: "of_int(ramified_weight l rho sigma BQ)-tQ*of_nat(snd BQ)=of_int VQ-tQ*of_nat(snd F)" by blast
   have QfirstRule: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>
   of_int(ramified_weight l rho sigma q)-tQ*of_nat(snd q)\<le>of_int VQ-tQ*of_nat(snd F)" using Qfirst by blast
   have belowP: "\<exists>b\<in>ramified_pbw_support l P. snd b<snd E"
     by (rule ramified_exact_pair_mate_first_slope_forces_lower_order[OF l rho P Q exact tQ earlyQ
       Eorder old EP FQ BQ Qlower Eweight Fweight QfirstRule Qtie Ptop])
   obtain tP :: rat and BP :: "int\<times>nat" where tP: "0<tP"
   and Pfirst: "\<forall>p\<in>ramified_pbw_support l P. of_int(ramified_weight l rho sigma p)-tP*of_nat(snd p)\<le>of_int VP-tP*of_nat(snd E)"
   and BP: "BP\<in>ramified_pbw_support l P" and Plower: "snd BP<snd E"
   and Ptie: "of_int(ramified_weight l rho sigma BP)-tP*of_nat(snd BP)=of_int VP-tP*of_nat(snd E)"
     using finiteSupport_exists_adjacent_rational_slope[where S="ramified_pbw_support l P"
 and w="ramified_weight l rho sigma" and V=VP and M="snd E",
 OF ramified_pbw_support_finite Ptop Pstart belowP] by blast
   have PfirstRule: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>
   of_int(ramified_weight l rho sigma p)-tP*of_nat(snd p)\<le>of_int VP-tP*of_nat(snd E)" using Pfirst by blast
   have early: "tP<of_nat l*of_int(rho+sigma) \<or>tQ<of_nat l*of_int(rho+sigma)" using earlyQ by blast
   have equal: "tP=tQ" by (rule ramified_exact_pair_first_slopes_equal_of_one_early[OF l rho P Q exact
      tP tQ early Eorder Forder old EP FQ BP BQ Plower Qlower Eweight Fweight Ptop Qtop PfirstRule QfirstRule Ptie Qtie])
   have PfirstQ: "\<forall>p\<in>ramified_pbw_support l P.
   of_int(ramified_weight l rho sigma p)-tQ*of_nat(snd p)\<le>of_int VP-tQ*of_nat(snd E)"
     using Pfirst by (simp only: equal)
   have PtieQ: "of_int(ramified_weight l rho sigma BP)-tQ*of_nat(snd BP)=of_int VP-tQ*of_nat(snd E)"
     using Ptie by (simp only: equal)
   have Poccupied: "\<exists>b\<in>ramified_pbw_support l P. snd b<snd E \<and>
   of_int(ramified_weight l rho sigma b)-tQ*of_nat(snd b)=of_int VP-tQ*of_nat(snd E)"
   proof (rule bexI[where x=BP])
     show "snd BP<snd E \<and>
       of_int(ramified_weight l rho sigma BP)-tQ*of_nat(snd BP)=of_int VP-tQ*of_nat(snd E)"
       by (rule conjI[OF Plower PtieQ])
     show "BP\<in>ramified_pbw_support l P" by (rule BP)
   qed
   have Qoccupied: "\<exists>b\<in>ramified_pbw_support l Q. snd b<snd F \<and>
   of_int(ramified_weight l rho sigma b)-tQ*of_nat(snd b)=of_int VQ-tQ*of_nat(snd F)"
   proof (rule bexI[where x=BQ])
     show "snd BQ<snd F \<and>
       of_int(ramified_weight l rho sigma BQ)-tQ*of_nat(snd BQ)=of_int VQ-tQ*of_nat(snd F)"
       by (rule conjI[OF Qlower Qtie])
     show "BQ\<in>ramified_pbw_support l Q" by (rule BQ)
   qed
   show ?thesis by (rule exI[where x=tQ], rule conjI[OF tQ conjI[OF earlyQ conjI[OF PfirstQ conjI[OF Qfirst conjI[OF Poccupied Qoccupied]]]]])
 qed
qed
end
