theory Ramified_Normalized_Corner_Geometry
 imports Ramified_Full_Root_Cut_Common_Slope
   "Ramified_Canonical_End_Proportion"
begin

lemma ramified_normalized_corner_pair_geometry:
 fixes l d n h::nat
 assumes d: "2\<le>d" and n: "2\<le>n" and h: "2\<le>h"
 and E: "E=(int d*(int l*int h-1),d*h)" and F: "F=(int n*(int l*int h-1),n*h)"
 shows "fst E-int l*int(snd E)<0 \<and> fst F-int l*int(snd F)<0 \<and>
   2\<le>snd E \<and> 2\<le>snd F \<and> int(snd E)*fst F=int(snd F)*fst E"
proof -
 have eg: "fst E-int l*int(snd E)=-int d" by (simp only: E fst_conv snd_conv of_nat_mult; algebra)
 have fg: "fst F-int l*int(snd F)=-int n" by (simp only: F fst_conv snd_conv of_nat_mult; algebra)
 have ep: "fst E-int l*int(snd E)<0" using d by (simp only: eg; simp)
 have fp: "fst F-int l*int(snd F)<0" using n by (simp only: fg; simp)
 have eo: "2\<le>snd E"
 proof -
   have "1*2\<le>d*h" by (rule mult_le_mono) (use d h in auto)
   then show ?thesis by (simp only: E snd_conv mult_1_left)
 qed
 have fo: "2\<le>snd F"
 proof -
   have "1*2\<le>n*h" by (rule mult_le_mono) (use n h in auto)
   then show ?thesis by (simp only: F snd_conv mult_1_left)
 qed
 have par: "int(snd E)*fst F=int(snd F)*fst E" by (simp only: E F fst_conv snd_conv of_nat_mult; algebra)
 show ?thesis using ep fp eo fo par by blast
qed

lemma ramified_normalized_corner_full_root_cut_lower_face:
 assumes l: "0<l" and rho: "0<rho" and div: "rho dvd int l" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0" and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and fullP: "rootMultiplicity c (ramified_top_face_polynomial l rho sigma P)=degree(ramified_top_face_polynomial l rho sigma P)"
 and fullQ: "rootMultiplicity c (ramified_top_face_polynomial l rho sigma Q)=degree(ramified_top_face_polynomial l rho sigma Q)"
 and E: "E=(ramified_pbw_top_laurent l P(degree(ramified_top_face_polynomial l rho sigma P)),degree(ramified_top_face_polynomial l rho sigma P))"
 and F: "F=(ramified_pbw_top_laurent l Q(degree(ramified_top_face_polynomial l rho sigma Q)),degree(ramified_top_face_polynomial l rho sigma Q))"
 and d: "2\<le>d" and n: "2\<le>n" and h: "2\<le>h"
 and Ppos: "0<ramified_weight_deg l rho sigma P" and Qpos: "0<ramified_weight_deg l rho sigma Q"
 and threshold: "0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
 and ratio: "ramified_weight_deg l rho sigma Q*int d=ramified_weight_deg l rho sigma P*int n"
 and corner: "E=(int d*(int l*int h-1),d*h)"
 shows "\<exists>r s::int. is_direction r s \<and> 0<r \<and> rho*s<r*sigma \<and>
   ramified_weight l r s E=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c P) \<and>
   ramified_weight l r s F=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c Q) \<and>
   (\<exists>BP\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c P). snd BP<snd E \<and> ramified_weight l r s BP=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c P)) \<and>
   (\<exists>BQ\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c Q). snd BQ<snd F \<and> ramified_weight l r s BQ=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c Q))"
proof -
 let ?C="ramified_cut_aut l rho sigma c"
 note proportion = ramified_exact_pair_canonical_ends_proportional[OF l rho sum P Q Pnz Qnz exact Ppos Qpos threshold ratio]
 have x: "int n*fst E=int d*fst F" and y: "n*snd E=d*snd F" using proportion by (simp_all only: E F fst_conv snd_conv)
 have dpos: "0<d" using d by arith
 have cx: "fst E=int d*(int l*int h-1)" and cy: "snd E=d*h" by (simp_all only: corner fst_conv snd_conv)
 note mate = ramified_normalized_corner_proportion_mate_coordinates[OF dpos x y cx cy]
 have Fcorner: "F=(int n*(int l*int h-1),n*h)" using mate by (cases F) auto
 note geometry = ramified_normalized_corner_pair_geometry[OF d n h corner Fcorner]
 have eg: "fst E-int l*int(snd E)<0" and fg: "fst F-int l*int(snd F)<0"
 and eo: "2\<le>snd E" and fo: "2\<le>snd F" and parallel: "int(snd E)*fst F=int(snd F)*fst E" using geometry by auto
 show ?thesis by (rule ramified_full_root_cut_exists_strict_lower_common_face[OF l rho div sum P Q Pnz Qnz exact fullP fullQ E F eg fg eo fo parallel])
qed

end
