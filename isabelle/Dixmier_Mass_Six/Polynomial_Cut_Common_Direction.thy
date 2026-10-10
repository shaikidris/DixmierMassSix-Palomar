theory Polynomial_Cut_Common_Direction
 imports Polynomial_Cut_Source_Endpoints Ramified_Common_First_Tilt
begin

lemma polynomial_cut_old_face_data:
 fixes c::complex
 assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
 and rho: "0<rho" and divides: "rho dvd int l" and positive: "0<rho+sigma"
 and face: "in_direction rho sigma P"
 defines "r\<equiv>(int l div rho)*v_degree rho sigma P"
 and "k\<equiv>ramified_cut_exponent l rho sigma"
 and "M\<equiv>rootMultiplicity c(cut_poly rho sigma P)"
 and "U\<equiv>ramified_cut_aut l rho sigma c(polynomial_ramified_lift l P)"
 shows "U\<in>ramified_operator_algebra l \<and>
 (r-k*int M,M)\<in>ramified_pbw_support l U \<and>
 ramified_weight l rho sigma(r-k*int M,M)=rho*r \<and>
 (\<forall>p\<in>ramified_pbw_support l U. ramified_weight l rho sigma p\<le>rho*r) \<and>
 (\<forall>p\<in>ramified_pbw_support l U. ramified_weight l rho sigma p=rho*r \<longrightarrow>M\<le>snd p)"
proof -
 have nonempty: "biv_support(leading_form rho sigma P)\<noteq>{}" using face by (auto simp: in_direction_def)
 obtain u where u: "u\<in>biv_support(leading_form rho sigma P)" using nonempty by blast
 have pair: "(fst u,snd u)\<in>biv_support(leading_form rho sigma P)" using u by simp
 have rootStart: "((r-k*int M,M)\<in>ramified_pbw_support l U \<and>
 ramified_weight l rho sigma(r-k*int M,M)=rho*r) \<and>
 (\<forall>a j. (a,j)\<in>ramified_pbw_support l U \<longrightarrow>ramified_weight l rho sigma(a,j)=rho*r \<longrightarrow>M\<le>j)"
 using polynomialRamifiedCut_root_start_on_old_face[where c=c,
 OF l P rho divides positive pair] by (simp add: r_def k_def M_def U_def)
 have sourceBound: "\<And>a j. (a,j)\<in>ramified_pbw_support l(polynomial_ramified_lift l P) \<Longrightarrow>
 ramified_weight l rho sigma(a,j)\<le>rho*r"
   unfolding r_def by (rule polynomialRamifiedLift_weight_le_scaled_vDeg[OF l P divides])
 have cutBound: "\<And>a j. (a,j)\<in>ramified_pbw_support l U \<Longrightarrow>ramified_weight l rho sigma(a,j)\<le>rho*r"
   unfolding U_def by (rule ramified_cut_aut_weight_upper[OF l polynomial_ramified_lift_carrier rho divides positive sourceBound])
 have carrier: "U\<in>ramified_operator_algebra l"
   unfolding U_def by (rule ramified_cut_aut_mem[OF l polynomial_ramified_lift_carrier])
 have fullBound: "\<forall>p\<in>ramified_pbw_support l U. ramified_weight l rho sigma p\<le>rho*r"
 proof (intro ballI)
   fix p assume p: "p\<in>ramified_pbw_support l U"
   obtain a j where peq: "p=(a,j)" by (cases p) auto
   show "ramified_weight l rho sigma p\<le>rho*r" using cutBound p by (simp only: peq)
 qed
 have fullStart: "\<forall>p\<in>ramified_pbw_support l U. ramified_weight l rho sigma p=rho*r \<longrightarrow>M\<le>snd p"
 proof (intro ballI impI)
   fix p assume p: "p\<in>ramified_pbw_support l U" and w: "ramified_weight l rho sigma p=rho*r"
   obtain a j where peq: "p=(a,j)" by (cases p) auto
   show "M\<le>snd p" using rootStart p w by (auto simp: peq)
 qed
 show ?thesis using carrier rootStart fullBound fullStart by blast
qed

lemma exactPair_maxRoot_cut_exists_common_early_adjacent_face:
 assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
 and direction: "is_direction rho sigma" and rho: "0<rho" and divides: "rho dvd int l"
 and Ppos: "0<v_degree rho sigma P" and Qpos: "0<v_degree rho sigma Q"
 and Pface: "in_direction rho sigma P" and Qface: "in_direction rho sigma Q"
 and exact: "op_comp Q P-op_comp P Q=id"
 and threshold: "rho+sigma<v_degree rho sigma P+v_degree rho sigma Q"
 and d: "2\<le>d" and n: "2\<le>n"
 and weights: "v_degree rho sigma Q*int d=v_degree rho sigma P*int n" and cop: "coprime n d"
 and grade: "(int l div rho)*v_degree rho sigma P-(ramified_cut_exponent l rho sigma+int l)*
 int(max_root_mult(cut_poly rho sigma P))<0"
 shows "\<exists>c. poly(cut_poly rho sigma P)c=0 \<and>
 rootMultiplicity c(cut_poly rho sigma P)=max_root_mult(cut_poly rho sigma P) \<and>
 (let U=ramified_cut_aut l rho sigma c(polynomial_ramified_lift l P);
 V=ramified_cut_aut l rho sigma c(polynomial_ramified_lift l Q);
 rP=(int l div rho)*v_degree rho sigma P; rQ=(int l div rho)*v_degree rho sigma Q;
 M=rootMultiplicity c(cut_poly rho sigma P); N=rootMultiplicity c(cut_poly rho sigma Q)
 in \<exists>t::rat. 0<t \<and>t<of_nat l*of_int(rho+sigma) \<and>
 (\<forall>p\<in>ramified_pbw_support l U. of_int(ramified_weight l rho sigma p)-t*of_nat(snd p)\<le>of_int(rho*rP)-t*of_nat M) \<and>
 (\<forall>q\<in>ramified_pbw_support l V. of_int(ramified_weight l rho sigma q)-t*of_nat(snd q)\<le>of_int(rho*rQ)-t*of_nat N) \<and>
 (\<exists>BP\<in>ramified_pbw_support l U. snd BP<M \<and>of_int(ramified_weight l rho sigma BP)-t*of_nat(snd BP)=of_int(rho*rP)-t*of_nat M) \<and>
 (\<exists>BQ\<in>ramified_pbw_support l V. snd BQ<N \<and>of_int(ramified_weight l rho sigma BQ)-t*of_nat(snd BQ)=of_int(rho*rQ)-t*of_nat N))"
proof -
 let ?rP="(int l div rho)*v_degree rho sigma P" let ?rQ="(int l div rho)*v_degree rho sigma Q"
 let ?k="ramified_cut_exponent l rho sigma"
 obtain c M N where root: "poly(cut_poly rho sigma P)c=0"
 and maximum: "M=max_root_mult(cut_poly rho sigma P)"
 and MP: "M=rootMultiplicity c(cut_poly rho sigma P)" and NQ: "N=rootMultiplicity c(cut_poly rho sigma Q)"
 and M2: "2\<le>M" and N2: "2\<le>N"
 and pointP: "(?rP-?k*int M,M)\<in>ramified_pbw_support l(ramified_cut_aut l rho sigma c(polynomial_ramified_lift l P))"
 and pointQ: "(?rQ-?k*int N,N)\<in>ramified_pbw_support l(ramified_cut_aut l rho sigma c(polynomial_ramified_lift l Q))"
 and parallel: "int M*(?rQ-?k*int N)=int N*(?rP-?k*int M)"
 and cutExact: "laurent_comp(ramified_cut_aut l rho sigma c(polynomial_ramified_lift l Q))
 (ramified_cut_aut l rho sigma c(polynomial_ramified_lift l P))-
 laurent_comp(ramified_cut_aut l rho sigma c(polynomial_ramified_lift l P))
 (ramified_cut_aut l rho sigma c(polynomial_ramified_lift l Q))=id"
   using exactPair_maxRoot_cut_parallel_endpoints_and_orders[OF l P Q direction rho divides Ppos Qpos Pface Qface exact threshold d n weights cop] by blast
 let ?U="ramified_cut_aut l rho sigma c(polynomial_ramified_lift l P)"
 let ?V="ramified_cut_aut l rho sigma c(polynomial_ramified_lift l Q)"
 let ?E="(?rP-?k*int M,M)" let ?F="(?rQ-?k*int N,N)"
 have positive: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have Ed: "fst ?E-int l*int(snd ?E)<0" using grade maximum by (simp add: algebra_simps)
 have scale: "int M*(fst ?F-int l*int N)=int N*(fst ?E-int l*int M)"
   using parallel by (simp add: algebra_simps)
 have Mpos: "0<int M" and Npos: "0<int N" using M2 N2 by arith+
 have neg: "int N*(fst ?E-int l*int M)<0" by (rule mult_pos_neg[OF Npos]) (use Ed in simp)
 have scaled_negative: "int M*(fst ?F-int l*int N)<0" using neg by (simp only: scale)
 have Fd: "fst ?F-int l*int(snd ?F)<0"
   using scaled_negative Mpos by (simp only: snd_conv mult_less_0_iff; arith)
 note Pdata = polynomial_cut_old_face_data[where c=c,
 OF l P rho divides positive Pface]
 note Qdata = polynomial_cut_old_face_data[where c=c,
 OF l Q rho divides positive Qface]
 have Pc: "?U\<in>ramified_operator_algebra l" and Qc: "?V\<in>ramified_operator_algebra l"
 and Ew: "ramified_weight l rho sigma ?E=rho*?rP" and Fw: "ramified_weight l rho sigma ?F=rho*?rQ"
 and Pt: "\<And>p. p\<in>ramified_pbw_support l ?U \<Longrightarrow>ramified_weight l rho sigma p\<le>rho*?rP"
 and Qt: "\<And>q. q\<in>ramified_pbw_support l ?V \<Longrightarrow>ramified_weight l rho sigma q\<le>rho*?rQ"
 and Ps: "\<And>p. p\<in>ramified_pbw_support l ?U \<Longrightarrow>ramified_weight l rho sigma p=rho*?rP \<Longrightarrow>M\<le>snd p"
 and Qs: "\<And>q. q\<in>ramified_pbw_support l ?V \<Longrightarrow>ramified_weight l rho sigma q=rho*?rQ \<Longrightarrow>N\<le>snd q"
   using Pdata Qdata MP NQ by auto
 have Eorder: "2\<le>snd ?E" using M2 by (simp only: snd_conv)
 have Forder: "2\<le>snd ?F" using N2 by (simp only: snd_conv)
 have old_parallel: "int(snd ?E)*fst ?F=int(snd ?F)*fst ?E"
   using parallel by (simp only: fst_conv snd_conv)
 have Pstart: "\<And>p. p\<in>ramified_pbw_support l ?U \<Longrightarrow>
   ramified_weight l rho sigma p=rho*?rP \<Longrightarrow>snd ?E\<le>snd p"
   using Ps by (simp only: snd_conv)
 have Qstart: "\<And>q. q\<in>ramified_pbw_support l ?V \<Longrightarrow>
   ramified_weight l rho sigma q=rho*?rQ \<Longrightarrow>snd ?F\<le>snd q"
   using Qs by (simp only: snd_conv)
 note common = ramified_exact_pair_exists_common_early_adjacent_face[
   where l=l and rho=rho and sigma=sigma and P="?U" and Q="?V"
   and E="?E" and F="?F" and VP="rho*?rP" and VQ="rho*?rQ",
   OF l rho positive Pc Qc cutExact pointP pointQ Ew Fw Ed Fd
     Eorder Forder old_parallel Pt Qt Pstart Qstart]
 have selected_maximum: "rootMultiplicity c(cut_poly rho sigma P)=max_root_mult(cut_poly rho sigma P)"
   by (rule trans[OF MP[symmetric] maximum])
 show ?thesis
   apply (rule exI[where x=c])
   apply (rule conjI[OF root])
   apply (rule conjI[OF selected_maximum])
   apply (simp only: Let_def)
   apply (use common in \<open>simp only: snd_conv MP NQ\<close>)
   done
qed

lemma exactPair_maxRoot_cut_exists_primitive_common_face:
 assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
 and direction: "is_direction rho sigma" and rho: "0<rho" and divides: "rho dvd int l"
 and Ppos: "0<v_degree rho sigma P" and Qpos: "0<v_degree rho sigma Q"
 and Pface: "in_direction rho sigma P" and Qface: "in_direction rho sigma Q"
 and exact: "op_comp Q P-op_comp P Q=id"
 and threshold: "rho+sigma<v_degree rho sigma P+v_degree rho sigma Q"
 and d: "2\<le>d" and n: "2\<le>n"
 and weights: "v_degree rho sigma Q*int d=v_degree rho sigma P*int n" and cop: "coprime n d"
 and grade: "(int l div rho)*v_degree rho sigma P-(ramified_cut_exponent l rho sigma+int l)*
 int(max_root_mult(cut_poly rho sigma P))<0"

 shows "\<exists>c r s. poly(cut_poly rho sigma P)c=0 \<and>
 rootMultiplicity c(cut_poly rho sigma P)=max_root_mult(cut_poly rho sigma P) \<and>
 is_direction r s \<and>0<r \<and>(sigma\<le>0 \<longrightarrow>s<0) \<and>
 (let U=ramified_cut_aut l rho sigma c(polynomial_ramified_lift l P);
 V=ramified_cut_aut l rho sigma c(polynomial_ramified_lift l Q);
 M=rootMultiplicity c(cut_poly rho sigma P); N=rootMultiplicity c(cut_poly rho sigma Q);
 E=((int l div rho)*v_degree rho sigma P-ramified_cut_exponent l rho sigma*int M,M);
 F=((int l div rho)*v_degree rho sigma Q-ramified_cut_exponent l rho sigma*int N,N)
 in ramified_weight l r s E=ramified_weight_deg l r s U \<and>
 ramified_weight l r s F=ramified_weight_deg l r s V \<and>
 (\<forall>p\<in>ramified_pbw_support l U. ramified_weight l r s p=ramified_weight_deg l r s U \<longrightarrow>
 fst E-int l*int(snd E)\<le>fst p-int l*int(snd p)) \<and>
 (\<forall>q\<in>ramified_pbw_support l V. ramified_weight l r s q=ramified_weight_deg l r s V \<longrightarrow>
 fst F-int l*int(snd F)\<le>fst q-int l*int(snd q)) \<and>
 (\<exists>BP\<in>ramified_pbw_support l U. snd BP<M \<and>ramified_weight l r s BP=ramified_weight_deg l r s U) \<and>
 (\<exists>BQ\<in>ramified_pbw_support l V. snd BQ<N \<and>ramified_weight l r s BQ=ramified_weight_deg l r s V))"
proof -
 let ?LP="polynomial_ramified_lift l P" let ?LQ="polynomial_ramified_lift l Q"
 let ?rP="(int l div rho)*v_degree rho sigma P" let ?rQ="(int l div rho)*v_degree rho sigma Q"
 let ?k="ramified_cut_exponent l rho sigma"
 obtain c::complex and t::rat and BP BQ::"int\<times>nat" where root: "poly(cut_poly rho sigma P)c=0"
 and maximum: "rootMultiplicity c(cut_poly rho sigma P)=max_root_mult(cut_poly rho sigma P)"
 and t: "0<t" and early: "t<of_nat l*of_int(rho+sigma)"
 and Pfirst: "\<forall>p\<in>ramified_pbw_support l(ramified_cut_aut l rho sigma c ?LP).
 of_int(ramified_weight l rho sigma p)-t*of_nat(snd p)\<le>of_int(rho*?rP)-t*of_nat(rootMultiplicity c(cut_poly rho sigma P))"
 and Qfirst: "\<forall>q\<in>ramified_pbw_support l(ramified_cut_aut l rho sigma c ?LQ).
 of_int(ramified_weight l rho sigma q)-t*of_nat(snd q)\<le>of_int(rho*?rQ)-t*of_nat(rootMultiplicity c(cut_poly rho sigma Q))"
 and BP: "BP\<in>ramified_pbw_support l(ramified_cut_aut l rho sigma c ?LP)"
 and BQ: "BQ\<in>ramified_pbw_support l(ramified_cut_aut l rho sigma c ?LQ)"
 and Plower: "snd BP<rootMultiplicity c(cut_poly rho sigma P)"
 and Qlower: "snd BQ<rootMultiplicity c(cut_poly rho sigma Q)"
 and Ptie: "of_int(ramified_weight l rho sigma BP)-t*of_nat(snd BP)=of_int(rho*?rP)-t*of_nat(rootMultiplicity c(cut_poly rho sigma P))"
 and Qtie: "of_int(ramified_weight l rho sigma BQ)-t*of_nat(snd BQ)=of_int(rho*?rQ)-t*of_nat(rootMultiplicity c(cut_poly rho sigma Q))"
 using exactPair_maxRoot_cut_exists_common_early_adjacent_face[OF l P Q direction rho divides Ppos Qpos Pface Qface exact threshold d n weights cop grade]
 unfolding Let_def by blast
 let ?U="ramified_cut_aut l rho sigma c ?LP" let ?V="ramified_cut_aut l rho sigma c ?LQ"
 let ?M="rootMultiplicity c(cut_poly rho sigma P)" let ?N="rootMultiplicity c(cut_poly rho sigma Q)"
 let ?E="(?rP-?k*int ?M,?M)" let ?F="(?rQ-?k*int ?N,?N)"
 have positive: "0<rho+sigma" using direction by (simp add: is_direction_def)
 note Pdata = polynomial_cut_old_face_data[where c=c, OF l P rho divides positive Pface]
 note Qdata = polynomial_cut_old_face_data[where c=c, OF l Q rho divides positive Qface]
 have Pc: "?U\<in>ramified_operator_algebra l" and Qc: "?V\<in>ramified_operator_algebra l"
 and EP: "?E\<in>ramified_pbw_support l ?U" and FQ: "?F\<in>ramified_pbw_support l ?V"
 and Ew: "ramified_weight l rho sigma ?E=rho*?rP" and Fw: "ramified_weight l rho sigma ?F=rho*?rQ"
 and Pold: "\<And>p. p\<in>ramified_pbw_support l ?U \<Longrightarrow>ramified_weight l rho sigma p\<le>rho*?rP"
 and Qold: "\<And>q. q\<in>ramified_pbw_support l ?V \<Longrightarrow>ramified_weight l rho sigma q\<le>rho*?rQ"
 using Pdata Qdata by auto
 have Pf: "\<And>p. p\<in>ramified_pbw_support l ?U \<Longrightarrow>
 of_int(ramified_weight l rho sigma p)-t*of_nat(snd p)\<le>of_int(rho*?rP)-t*of_nat(snd ?E)" using Pfirst by auto
 have Qf: "\<And>q. q\<in>ramified_pbw_support l ?V \<Longrightarrow>
 of_int(ramified_weight l rho sigma q)-t*of_nat(snd q)\<le>of_int(rho*?rQ)-t*of_nat(snd ?F)" using Qfirst by auto
 have Ptie_projected: "of_int(ramified_weight l rho sigma BP)-t*of_nat(snd BP)=
   of_int(rho*?rP)-t*of_nat(snd ?E)"
   using Ptie by (simp only: snd_conv)
 have Qtie_projected: "of_int(ramified_weight l rho sigma BQ)-t*of_nat(snd BQ)=
   of_int(rho*?rQ)-t*of_nat(snd ?F)"
   using Qtie by (simp only: snd_conv)
 note primitive = ramified_common_first_tilt_primitive_face[
   where l=l and rho=rho and sigma=sigma and P="?U" and Q="?V"
   and t=t and E="?E" and F="?F" and BP=BP and BQ=BQ
   and VP="rho*?rP" and VQ="rho*?rQ",
   OF l rho Pc Qc t early EP FQ BP BQ Ew Fw Pold Qold Pf Qf
     Ptie_projected Qtie_projected]
 show ?thesis by (rule exI[where x=c])
   (simp only: Let_def; use primitive root maximum Plower Qlower BP BQ in \<open>blast\<close>)
qed

end
