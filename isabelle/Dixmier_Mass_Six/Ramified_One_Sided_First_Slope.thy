theory Ramified_One_Sided_First_Slope
 imports Ramified_Common_First_Slope
begin

lemma ramified_exact_pair_first_slope_forces_mate_lower_order:
 fixes E F B::"int\<times>nat" and tP::rat
 assumes l: "0<l" and rho: "0<rho"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and positive: "0<tP" and early: "tP<of_nat l*of_int(rho+sigma)"
 and order: "2\<le>snd F" and old: "int(snd E)*fst F=int(snd F)*fst E"
 and EP: "E\<in>ramified_pbw_support l P" and FQ: "F\<in>ramified_pbw_support l Q"
 and BP: "B\<in>ramified_pbw_support l P" and lower: "snd B<snd E"
 and Eold: "ramified_weight l rho sigma E=VP" and Fold: "ramified_weight l rho sigma F=VQ"
 and Pfirst: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>
 of_int(ramified_weight l rho sigma p)-tP*of_nat(snd p)\<le>of_int VP-tP*of_nat(snd E)"
 and Btie: "of_int(ramified_weight l rho sigma B)-tP*of_nat(snd B)=of_int VP-tP*of_nat(snd E)"
 and Qold: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>ramified_weight l rho sigma q\<le>VQ"

 shows "\<exists>b\<in>ramified_pbw_support l Q. snd b<snd F"
proof (rule ccontr)
 assume none: "\<not>(\<exists>b\<in>ramified_pbw_support l Q. snd b<snd F)"
 have allOrder: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>snd F\<le>snd q"
   using none by auto
 let ?tQ="tP+1"
 have before: "tP<?tQ" by simp
 have nonneg: "0\<le>?tQ" using positive by arith
 have Qfirst: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>
 of_int(ramified_weight l rho sigma q)-?tQ*of_nat(snd q)\<le>of_int VQ-?tQ*of_nat(snd F)"
 proof -
   fix q assume q: "q\<in>ramified_pbw_support l Q"
   have weight: "(of_int(ramified_weight l rho sigma q)::rat)\<le>of_int VQ" using Qold[OF q] by simp
   have order: "(of_nat(snd F)::rat)\<le>of_nat(snd q)" using allOrder[OF q] by simp
   have product: "?tQ*of_nat(snd F)\<le>?tQ*of_nat(snd q)" by (rule mult_left_mono[OF order nonneg])
   show "of_int(ramified_weight l rho sigma q)-?tQ*of_nat(snd q)\<le>of_int VQ-?tQ*of_nat(snd F)"
     using weight product by linarith
 qed
 show False by (rule ramified_exact_pair_no_earlier_first_slope[OF l rho P Q exact positive early
 before order old EP FQ BP lower Eold Fold Pfirst Btie Qold Qfirst])
qed

lemma ramified_exact_pair_mate_first_slope_forces_lower_order:
 fixes E F B::"int\<times>nat" and tQ::rat
 assumes l: "0<l" and rho: "0<rho"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and positive: "0<tQ" and early: "tQ<of_nat l*of_int(rho+sigma)"
 and order: "2\<le>snd E" and old: "int(snd E)*fst F=int(snd F)*fst E"
 and EP: "E\<in>ramified_pbw_support l P" and FQ: "F\<in>ramified_pbw_support l Q"
 and BQ: "B\<in>ramified_pbw_support l Q" and lower: "snd B<snd F"
 and Eold: "ramified_weight l rho sigma E=VP" and Fold: "ramified_weight l rho sigma F=VQ"
 and Qfirst: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow>
 of_int(ramified_weight l rho sigma q)-tQ*of_nat(snd q)\<le>of_int VQ-tQ*of_nat(snd F)"
 and Btie: "of_int(ramified_weight l rho sigma B)-tQ*of_nat(snd B)=of_int VQ-tQ*of_nat(snd F)"
 and Pold: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow>ramified_weight l rho sigma p\<le>VP"

 shows "\<exists>b\<in>ramified_pbw_support l P. snd b<snd E"
proof (rule ccontr)
 assume none: "\<not>(\<exists>b\<in>ramified_pbw_support l P. snd b<snd E)"
 have allOrder: "\<And>q. q\<in>ramified_pbw_support l P \<Longrightarrow>snd E\<le>snd q"
   using none by auto
 let ?tP="tQ+1"
 have before: "tQ<?tP" by simp
 have nonneg: "0\<le>?tP" using positive by arith
 have Pfirst: "\<And>q. q\<in>ramified_pbw_support l P \<Longrightarrow>
 of_int(ramified_weight l rho sigma q)-?tP*of_nat(snd q)\<le>of_int VP-?tP*of_nat(snd E)"
 proof -
   fix q assume q: "q\<in>ramified_pbw_support l P"
   have weight: "(of_int(ramified_weight l rho sigma q)::rat)\<le>of_int VP" using Pold[OF q] by simp
   have order: "(of_nat(snd E)::rat)\<le>of_nat(snd q)" using allOrder[OF q] by simp
   have product: "?tP*of_nat(snd E)\<le>?tP*of_nat(snd q)" by (rule mult_left_mono[OF order nonneg])
   show "of_int(ramified_weight l rho sigma q)-?tP*of_nat(snd q)\<le>of_int VP-?tP*of_nat(snd E)"
     using weight product by linarith
 qed
 show False by (rule ramified_exact_pair_no_later_first_slope[OF l rho P Q exact positive early
 before order old EP FQ BQ lower Eold Fold Qfirst Btie Pold Pfirst])
qed

end
