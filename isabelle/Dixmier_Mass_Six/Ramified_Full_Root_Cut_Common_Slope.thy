theory Ramified_Full_Root_Cut_Common_Slope
 imports Ramified_Lower_Face_Ending_Point
   "Ramified_Full_Root_Corner_Preservation"
   "Ramified_Common_Integral_Face"
   "Ramified_Common_Adjacent_Direction"
begin

lemma ramified_full_root_cut_exists_common_early_slope:
 assumes l: "0<l" and rho: "0<rho" and div: "rho dvd int l" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0" and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and fullP: "rootMultiplicity c (ramified_top_face_polynomial l rho sigma P)=degree(ramified_top_face_polynomial l rho sigma P)"
 and fullQ: "rootMultiplicity c (ramified_top_face_polynomial l rho sigma Q)=degree(ramified_top_face_polynomial l rho sigma Q)"
 and E: "E=(ramified_pbw_top_laurent l P(degree(ramified_top_face_polynomial l rho sigma P)),degree(ramified_top_face_polynomial l rho sigma P))"
 and F: "F=(ramified_pbw_top_laurent l Q(degree(ramified_top_face_polynomial l rho sigma Q)),degree(ramified_top_face_polynomial l rho sigma Q))"
 and Egrade: "fst E-int l*int(snd E)<0" and Fgrade: "fst F-int l*int(snd F)<0"
 and Eorder: "2\<le>snd E" and Forder: "2\<le>snd F" and parallel: "int(snd E)*fst F=int(snd F)*fst E"
 shows "\<exists>t::rat. 0<t \<and> t< of_nat l* of_int(rho+sigma) \<and>
   (\<forall>p\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c P). of_int(ramified_weight l rho sigma p)-t* of_nat(snd p)\<le> of_int(ramified_weight_deg l rho sigma P)-t* of_nat(snd E)) \<and>
   (\<forall>q\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c Q). of_int(ramified_weight l rho sigma q)-t* of_nat(snd q)\<le> of_int(ramified_weight_deg l rho sigma Q)-t* of_nat(snd F)) \<and>
   (\<exists>BP\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c P). snd BP<snd E \<and> of_int(ramified_weight l rho sigma BP)-t* of_nat(snd BP)= of_int(ramified_weight_deg l rho sigma P)-t* of_nat(snd E)) \<and>
   (\<exists>BQ\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c Q). snd BQ<snd F \<and> of_int(ramified_weight l rho sigma BQ)-t* of_nat(snd BQ)= of_int(ramified_weight_deg l rho sigma Q)-t* of_nat(snd F))"
proof -
 let ?C="ramified_cut_aut l rho sigma c"
 let ?VP="ramified_weight_deg l rho sigma P" let ?VQ="ramified_weight_deg l rho sigma Q"
 have PC: "?C P\<in>ramified_operator_algebra l" by (rule ramified_cut_aut_mem[OF l P])
 have QC: "?C Q\<in>ramified_operator_algebra l" by (rule ramified_cut_aut_mem[OF l Q])
 note Ps = ramified_full_degree_root_cut_preserves_canonical_endpoint[OF l P rho div sum Pnz fullP]
 note Qs = ramified_full_degree_root_cut_preserves_canonical_endpoint[OF l Q rho div sum Qnz fullQ]
 have EP: "E\<in>ramified_pbw_support l (?C P)" and Et: "ramified_weight l rho sigma E=?VP"
 and Estart: "\<And>p. p\<in>ramified_pbw_support l (?C P) \<Longrightarrow> ramified_weight l rho sigma p=?VP \<Longrightarrow> snd E\<le>snd p"
   using Ps by (auto simp only: E fst_conv snd_conv split_beta prod.collapse)
 have FQ: "F\<in>ramified_pbw_support l (?C Q)" and Ft: "ramified_weight l rho sigma F=?VQ"
 and Fstart: "\<And>p. p\<in>ramified_pbw_support l (?C Q) \<Longrightarrow> ramified_weight l rho sigma p=?VQ \<Longrightarrow> snd F\<le>snd p"
   using Qs by (auto simp only: F fst_conv snd_conv split_beta prod.collapse)
 have Pw: "ramified_weight_deg l rho sigma (?C P)=?VP" by (rule ramified_cut_aut_weight_deg_eq[OF l P rho div sum Pnz])
 have Qw: "ramified_weight_deg l rho sigma (?C Q)=?VQ" by (rule ramified_cut_aut_weight_deg_eq[OF l Q rho div sum Qnz])
 have cutexact: "laurent_comp (?C Q)(?C P)-laurent_comp (?C P)(?C Q)=id" by (rule ramified_cut_aut_exact_pair[OF l P Q exact])
 have Pupper: "\<And>p. p\<in>ramified_pbw_support l (?C P) \<Longrightarrow> ramified_weight l rho sigma p\<le>?VP" using ramified_weight_deg_upper[where l=l and T="?C P" and rho=rho and sigma=sigma] by (simp only: Pw)
 have Qupper: "\<And>p. p\<in>ramified_pbw_support l (?C Q) \<Longrightarrow> ramified_weight l rho sigma p\<le>?VQ" using ramified_weight_deg_upper[where l=l and T="?C Q" and rho=rho and sigma=sigma] by (simp only: Qw)
 show ?thesis by (rule ramified_exact_pair_exists_common_early_adjacent_face[OF l rho sum PC QC cutexact EP FQ Et Ft Egrade Fgrade Eorder Forder parallel Pupper Qupper Estart Fstart])
qed

lemma ramified_full_root_cut_exists_primitive_common_face:
 assumes l: "0<l" and rho: "0<rho" and div: "rho dvd int l" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0" and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and fullP: "rootMultiplicity c (ramified_top_face_polynomial l rho sigma P)=degree(ramified_top_face_polynomial l rho sigma P)"
 and fullQ: "rootMultiplicity c (ramified_top_face_polynomial l rho sigma Q)=degree(ramified_top_face_polynomial l rho sigma Q)"
 and E: "E=(ramified_pbw_top_laurent l P(degree(ramified_top_face_polynomial l rho sigma P)),degree(ramified_top_face_polynomial l rho sigma P))"
 and F: "F=(ramified_pbw_top_laurent l Q(degree(ramified_top_face_polynomial l rho sigma Q)),degree(ramified_top_face_polynomial l rho sigma Q))"
 and Egrade: "fst E-int l*int(snd E)<0" and Fgrade: "fst F-int l*int(snd F)<0"
 and Eorder: "2\<le>snd E" and Forder: "2\<le>snd F" and parallel: "int(snd E)*fst F=int(snd F)*fst E"
 shows "\<exists>r s::int. is_direction r s \<and> 0<r \<and>
   ramified_weight l r s E=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c P) \<and>
   ramified_weight l r s F=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c Q) \<and>
   (\<exists>BP\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c P). snd BP<snd E \<and> ramified_weight l r s BP=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c P)) \<and>
   (\<exists>BQ\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c Q). snd BQ<snd F \<and> ramified_weight l r s BQ=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c Q))"
proof -
 let ?C="ramified_cut_aut l rho sigma c"
 let ?VP="ramified_weight_deg l rho sigma P" let ?VQ="ramified_weight_deg l rho sigma Q"
 have PC: "?C P\<in>ramified_operator_algebra l" by (rule ramified_cut_aut_mem[OF l P])
 have QC: "?C Q\<in>ramified_operator_algebra l" by (rule ramified_cut_aut_mem[OF l Q])
 note Ps = ramified_full_degree_root_cut_preserves_canonical_endpoint[OF l P rho div sum Pnz fullP]
 note Qs = ramified_full_degree_root_cut_preserves_canonical_endpoint[OF l Q rho div sum Qnz fullQ]
 have EP: "E\<in>ramified_pbw_support l (?C P)" and Et: "ramified_weight l rho sigma E=?VP"
 and Estart: "\<And>p. p\<in>ramified_pbw_support l (?C P) \<Longrightarrow> ramified_weight l rho sigma p=?VP \<Longrightarrow> snd E\<le>snd p"
   using Ps by (auto simp only: E fst_conv snd_conv split_beta prod.collapse)
 have FQ: "F\<in>ramified_pbw_support l (?C Q)" and Ft: "ramified_weight l rho sigma F=?VQ"
 and Fstart: "\<And>p. p\<in>ramified_pbw_support l (?C Q) \<Longrightarrow> ramified_weight l rho sigma p=?VQ \<Longrightarrow> snd F\<le>snd p"
   using Qs by (auto simp only: F fst_conv snd_conv split_beta prod.collapse)
 have Pw: "ramified_weight_deg l rho sigma (?C P)=?VP" by (rule ramified_cut_aut_weight_deg_eq[OF l P rho div sum Pnz])
 have Qw: "ramified_weight_deg l rho sigma (?C Q)=?VQ" by (rule ramified_cut_aut_weight_deg_eq[OF l Q rho div sum Qnz])
 have cutexact: "laurent_comp (?C Q)(?C P)-laurent_comp (?C P)(?C Q)=id" by (rule ramified_cut_aut_exact_pair[OF l P Q exact])
 have Pupper: "\<And>p. p\<in>ramified_pbw_support l (?C P) \<Longrightarrow> ramified_weight l rho sigma p\<le>?VP" using ramified_weight_deg_upper[where l=l and T="?C P" and rho=rho and sigma=sigma] by (simp only: Pw)
 have Qupper: "\<And>p. p\<in>ramified_pbw_support l (?C Q) \<Longrightarrow> ramified_weight l rho sigma p\<le>?VQ" using ramified_weight_deg_upper[where l=l and T="?C Q" and rho=rho and sigma=sigma] by (simp only: Qw)
 obtain t BP BQ where early: "t<(of_nat l* of_int(rho+sigma)::rat)"
 and Pfirst: "\<forall>p\<in>ramified_pbw_support l (?C P). of_int(ramified_weight l rho sigma p)-t* of_nat(snd p)\<le> of_int ?VP-t* of_nat(snd E)"
 and Qfirst: "\<forall>q\<in>ramified_pbw_support l (?C Q). of_int(ramified_weight l rho sigma q)-t* of_nat(snd q)\<le> of_int ?VQ-t* of_nat(snd F)"
 and BP: "BP\<in>ramified_pbw_support l (?C P)" and BPlow: "snd BP<snd E"
 and BPtie: "of_int(ramified_weight l rho sigma BP)-t* of_nat(snd BP)= of_int ?VP-t* of_nat(snd E)"
 and BQ: "BQ\<in>ramified_pbw_support l (?C Q)" and BQlow: "snd BQ<snd F"
 and BQtie: "of_int(ramified_weight l rho sigma BQ)-t* of_nat(snd BQ)= of_int ?VQ-t* of_nat(snd F)"
   using ramified_full_root_cut_exists_common_early_slope[OF l rho div sum P Q Pnz Qnz exact fullP fullQ E F Egrade Fgrade Eorder Forder parallel] by blast
 have Pu: "\<And>p. p\<in>ramified_pbw_support l (?C P) \<Longrightarrow> of_int(ramified_weight l rho sigma p)-t* of_nat(snd p)\<le> of_int ?VP-t* of_nat(snd E)" using Pfirst by blast
 have Qu: "\<And>q. q\<in>ramified_pbw_support l (?C Q) \<Longrightarrow> of_int(ramified_weight l rho sigma q)-t* of_nat(snd q)\<le> of_int ?VQ-t* of_nat(snd F)" using Qfirst by blast
 obtain r s where direction: "is_direction r s" and rpos: "0<r"
 and Etop: "ramified_weight l r s E=ramified_weight_deg l r s (?C P)"
 and Ftop: "ramified_weight l r s F=ramified_weight_deg l r s (?C Q)"
 and BPtop: "ramified_weight l r s BP=ramified_weight_deg l r s (?C P)"
 and BQtop: "ramified_weight l r s BQ=ramified_weight_deg l r s (?C Q)"
   using ramified_common_rational_tilt_primitive_face[OF l rho PC QC early EP FQ BP BQ Et Ft Pu Qu BPtie BQtie] by blast
 show ?thesis by (intro exI[of _ r] exI[of _ s]) (use direction rpos Etop Ftop BP BPlow BPtop BQ BQlow BQtop in blast)
qed

lemma ramified_full_root_cut_exists_strict_lower_common_face:
 assumes l: "0<l" and rho: "0<rho" and div: "rho dvd int l" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0" and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and fullP: "rootMultiplicity c (ramified_top_face_polynomial l rho sigma P)=degree(ramified_top_face_polynomial l rho sigma P)"
 and fullQ: "rootMultiplicity c (ramified_top_face_polynomial l rho sigma Q)=degree(ramified_top_face_polynomial l rho sigma Q)"
 and E: "E=(ramified_pbw_top_laurent l P(degree(ramified_top_face_polynomial l rho sigma P)),degree(ramified_top_face_polynomial l rho sigma P))"
 and F: "F=(ramified_pbw_top_laurent l Q(degree(ramified_top_face_polynomial l rho sigma Q)),degree(ramified_top_face_polynomial l rho sigma Q))"
 and Egrade: "fst E-int l*int(snd E)<0" and Fgrade: "fst F-int l*int(snd F)<0"
 and Eorder: "2\<le>snd E" and Forder: "2\<le>snd F" and parallel: "int(snd E)*fst F=int(snd F)*fst E"
 shows "\<exists>r s::int. is_direction r s \<and> 0<r \<and> rho*s<r*sigma \<and>
   ramified_weight l r s E=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c P) \<and>
   ramified_weight l r s F=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c Q) \<and>
   (\<exists>BP\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c P). snd BP<snd E \<and> ramified_weight l r s BP=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c P)) \<and>
   (\<exists>BQ\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c Q). snd BQ<snd F \<and> ramified_weight l r s BQ=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c Q))"
proof -
 let ?C="ramified_cut_aut l rho sigma c"
 let ?VP="ramified_weight_deg l rho sigma P" let ?VQ="ramified_weight_deg l rho sigma Q"
 have PC: "?C P\<in>ramified_operator_algebra l" by (rule ramified_cut_aut_mem[OF l P])
 have QC: "?C Q\<in>ramified_operator_algebra l" by (rule ramified_cut_aut_mem[OF l Q])
 note Ps = ramified_full_degree_root_cut_preserves_canonical_endpoint[OF l P rho div sum Pnz fullP]
 note Qs = ramified_full_degree_root_cut_preserves_canonical_endpoint[OF l Q rho div sum Qnz fullQ]
 have EP: "E\<in>ramified_pbw_support l (?C P)" and Et: "ramified_weight l rho sigma E=?VP"
 and Estart: "\<And>p. p\<in>ramified_pbw_support l (?C P) \<Longrightarrow> ramified_weight l rho sigma p=?VP \<Longrightarrow> snd E\<le>snd p"
   using Ps by (auto simp only: E fst_conv snd_conv split_beta prod.collapse)
 have FQ: "F\<in>ramified_pbw_support l (?C Q)" and Ft: "ramified_weight l rho sigma F=?VQ"
 and Fstart: "\<And>p. p\<in>ramified_pbw_support l (?C Q) \<Longrightarrow> ramified_weight l rho sigma p=?VQ \<Longrightarrow> snd F\<le>snd p"
   using Qs by (auto simp only: F fst_conv snd_conv split_beta prod.collapse)
 have Pw: "ramified_weight_deg l rho sigma (?C P)=?VP" by (rule ramified_cut_aut_weight_deg_eq[OF l P rho div sum Pnz])
 have Qw: "ramified_weight_deg l rho sigma (?C Q)=?VQ" by (rule ramified_cut_aut_weight_deg_eq[OF l Q rho div sum Qnz])
 have cutexact: "laurent_comp (?C Q)(?C P)-laurent_comp (?C P)(?C Q)=id" by (rule ramified_cut_aut_exact_pair[OF l P Q exact])
 have Pupper: "\<And>p. p\<in>ramified_pbw_support l (?C P) \<Longrightarrow> ramified_weight l rho sigma p\<le>?VP" using ramified_weight_deg_upper[where l=l and T="?C P" and rho=rho and sigma=sigma] by (simp only: Pw)
 have Qupper: "\<And>p. p\<in>ramified_pbw_support l (?C Q) \<Longrightarrow> ramified_weight l rho sigma p\<le>?VQ" using ramified_weight_deg_upper[where l=l and T="?C Q" and rho=rho and sigma=sigma] by (simp only: Qw)
 obtain r s BP BQ where direction: "is_direction r s" and rpos: "0<r"
 and Etop: "ramified_weight l r s E=ramified_weight_deg l r s (?C P)"
 and Ftop: "ramified_weight l r s F=ramified_weight_deg l r s (?C Q)"
 and BP: "BP\<in>ramified_pbw_support l (?C P)" and BPlow: "snd BP<snd E"
 and BPtop: "ramified_weight l r s BP=ramified_weight_deg l r s (?C P)"
 and BQ: "BQ\<in>ramified_pbw_support l (?C Q)" and BQlow: "snd BQ<snd F"
 and BQtop: "ramified_weight l r s BQ=ramified_weight_deg l r s (?C Q)"
   using ramified_full_root_cut_exists_primitive_common_face[OF l rho div sum P Q Pnz Qnz exact fullP fullQ E F Egrade Fgrade Eorder Forder parallel] by blast
 have topold: "ramified_weight l rho sigma E=ramified_weight_deg l rho sigma (?C P)" by (simp only: Pw Et)
 have start: "\<And>p. p\<in>ramified_pbw_support l (?C P) \<Longrightarrow> ramified_weight l rho sigma p=ramified_weight_deg l rho sigma (?C P) \<Longrightarrow> snd E\<le>snd p" by (simp only: Pw; rule Estart)
 have tie: "ramified_weight l r s BP=ramified_weight l r s E" using BPtop Etop by simp
 have strict: "rho*s<r*sigma" by (rule ramified_old_face_min_order_new_tie_strict_decrease[OF l rpos PC BP topold start BPlow tie])
 show ?thesis by (intro exI[of _ r] exI[of _ s]) (use direction rpos strict Etop Ftop BP BPlow BPtop BQ BQlow BQtop in blast)
qed

end
