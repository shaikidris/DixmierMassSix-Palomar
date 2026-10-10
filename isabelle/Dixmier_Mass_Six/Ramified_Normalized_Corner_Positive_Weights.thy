theory Ramified_Normalized_Corner_Positive_Weights
 imports Ramified_Normalized_Corner_Geometry
   "Ramified_Common_Face_Ratio"
begin

lemma ramified_exact_pair_normalized_top_corners_positive_ratio:
 fixes l d n h::nat
 assumes l: "0<l" and r: "0<r" and sum: "0<r+s"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and d: "0<d" and n: "0<n" and h: "0<h"
 and Ptop: "ramified_weight l r s (int d*(int l*int h-1),d*h)=ramified_weight_deg l r s P"
 and Qtop: "ramified_weight l r s (int n*(int l*int h-1),n*h)=ramified_weight_deg l r s Q"
 shows "0<ramified_weight_deg l r s P \<and> 0<ramified_weight_deg l r s Q \<and>
   ramified_weight_deg l r s Q*int d=ramified_weight_deg l r s P*int n"
proof -
 let ?E="(int d*(int l*int h-1),d*h)" let ?F="(int n*(int l*int h-1),n*h)"
 have order: "0<snd ?E" using d h by simp
 have parallel: "int(snd ?E)*fst ?F=int(snd ?F)*fst ?E" by (simp only: fst_conv snd_conv of_nat_mult; algebra)
 have ratio: "int(snd ?E)*int n=int(snd ?F)*int d" by (simp add: mult_ac)
 show ?thesis by (rule ramified_exact_pair_parallel_top_weights_positive_ratio[OF l r sum P Q exact order parallel Ptop Qtop d n ratio])
qed

lemma ramified_normalized_corner_full_root_cut_positive_lower_face:
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
   0<ramified_weight_deg l r s (ramified_cut_aut l rho sigma c P) \<and>
   0<ramified_weight_deg l r s (ramified_cut_aut l rho sigma c Q) \<and>
   ramified_weight_deg l r s (ramified_cut_aut l rho sigma c Q)*int d=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c P)*int n \<and>
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
 obtain r s BP BQ where direction: "is_direction r s" and rpos: "0<r" and strict: "rho*s<r*sigma"
 and Etop: "ramified_weight l r s E=ramified_weight_deg l r s (?C P)"
 and Ftop: "ramified_weight l r s F=ramified_weight_deg l r s (?C Q)"
 and BP: "BP\<in>ramified_pbw_support l (?C P)" and BPlow: "snd BP<snd E" and BPtop: "ramified_weight l r s BP=ramified_weight_deg l r s (?C P)"
 and BQ: "BQ\<in>ramified_pbw_support l (?C Q)" and BQlow: "snd BQ<snd F" and BQtop: "ramified_weight l r s BQ=ramified_weight_deg l r s (?C Q)"
   using ramified_normalized_corner_full_root_cut_lower_face[OF l rho div sum P Q Pnz Qnz exact fullP fullQ E F d n h Ppos Qpos threshold ratio corner] by blast
 have PC: "?C P\<in>ramified_operator_algebra l" by (rule ramified_cut_aut_mem[OF l P])
 have QC: "?C Q\<in>ramified_operator_algebra l" by (rule ramified_cut_aut_mem[OF l Q])
 have cutexact: "laurent_comp (?C Q)(?C P)-laurent_comp (?C P)(?C Q)=id" by (rule ramified_cut_aut_exact_pair[OF l P Q exact])
 have newsum: "0<r+s" using direction by (simp add: is_direction_def)
 have npos: "0<n" and hpos: "0<h" using n h by auto
 have Pt: "ramified_weight l r s (int d*(int l*int h-1),d*h)=ramified_weight_deg l r s (?C P)" using Etop by (simp only: corner)
 have Qt: "ramified_weight l r s (int n*(int l*int h-1),n*h)=ramified_weight_deg l r s (?C Q)" using Ftop by (simp only: Fcorner)
 note positive = ramified_exact_pair_normalized_top_corners_positive_ratio[OF l rpos newsum PC QC cutexact dpos npos hpos Pt Qt]
 show ?thesis by (intro exI[of _ r] exI[of _ s]) (use direction rpos strict positive Etop Ftop BP BPlow BPtop BQ BQlow BQtop in blast)
qed

end
