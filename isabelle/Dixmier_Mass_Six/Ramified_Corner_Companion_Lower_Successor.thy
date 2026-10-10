theory Ramified_Corner_Companion_Lower_Successor
 imports Ramified_Normalized_Corner_Positive_Weights
begin

lemma ramified_source_companion_normalized_corner_lower_successor:
 assumes l: "0<l" and rho: "0<rho" and direction: "is_direction rho sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0" and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and E: "E=(ramified_pbw_top_laurent l P(degree(ramified_top_face_polynomial l rho sigma P)),degree(ramified_top_face_polynomial l rho sigma P))"
 and F: "F=(ramified_pbw_top_laurent l Q(degree(ramified_top_face_polynomial l rho sigma Q)),degree(ramified_top_face_polynomial l rho sigma Q))"
 and d: "2\<le>d" and n: "2\<le>n" and h: "2\<le>h" and cop: "coprime d n"
 and Ppos: "0<ramified_weight_deg l rho sigma P" and Qpos: "0<ramified_weight_deg l rho sigma Q"
 and ratio: "ramified_weight_deg l rho sigma Q*int d=ramified_weight_deg l rho sigma P*int n"
 and corner: "E=(int d*(int l*int h-1),d*h)"
 and G: "G\<in>ramified_operator_algebra l" and Gnz: "G\<noteq>0"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P G-laurent_comp G P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P G-laurent_comp G P)=ramified_top_face_polynomial l rho sigma P"
 and Gweight: "ramified_weight_deg l rho sigma G=int l*(rho+sigma)"
 and member: "j\<in>polynomial_support(ramified_top_face_polynomial l rho sigma P)"
 and distinct: "j\<noteq>degree(ramified_top_face_polynomial l rho sigma P)"
 shows "\<exists>c::complex. c\<noteq>0 \<and> rho dvd int l \<and> (\<exists>r::int. \<exists>s::int. is_direction r s \<and> 0<r \<and> rho*s<r*sigma \<and>
   0<ramified_weight_deg l r s (ramified_cut_aut l rho sigma c P) \<and>
   0<ramified_weight_deg l r s (ramified_cut_aut l rho sigma c Q) \<and>
   ramified_weight_deg l r s (ramified_cut_aut l rho sigma c Q)*int d=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c P)*int n \<and>
   ramified_weight l r s E=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c P) \<and>
   ramified_weight l r s F=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c Q) \<and>
   (\<exists>BP\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c P). snd BP<snd E \<and> ramified_weight l r s BP=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c P)) \<and>
   (\<exists>BQ\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c Q). snd BQ<snd F \<and> ramified_weight l r s BQ=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c Q)) \<and>
   (degree(ramified_top_face_polynomial l r s (ramified_cut_aut l rho sigma c P))=snd E \<and> ramified_pbw_top_laurent l (ramified_cut_aut l rho sigma c P)(snd E)=fst E) \<and>
   (degree(ramified_top_face_polynomial l r s (ramified_cut_aut l rho sigma c Q))=snd F \<and> ramified_pbw_top_laurent l (ramified_cut_aut l rho sigma c Q)(snd F)=fst F))"
proof -
 let ?p="ramified_top_face_polynomial l rho sigma P"
 have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have dpos: "0<d" and npos: "0<n" using d n by auto
 have Pdegree: "degree ?p=d*h" using arg_cong[where f=snd, OF E] arg_cong[where f=snd, OF corner] by simp
 have Pcoord: "ramified_pbw_top_laurent l P(d*h)=int d*(int l*int h-1)"
   using arg_cong[where f=fst, OF E] arg_cong[where f=fst, OF corner] by (simp only: Pdegree fst_conv)
 have nonzero: "?p\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l P rho Pnz])
 have ending: "rho*ramified_pbw_top_laurent l P(degree ?p)+int l*sigma*int(degree ?p)=ramified_weight_deg l rho sigma P"
   by (rule native_ramified_top_face_degree_weight[OF nonzero])
 have Ptop: "ramified_weight l rho sigma (int d*(int l*int h-1),d*h)=ramified_weight_deg l rho sigma P"
   using ending by (simp only: ramified_weight_def fst_conv snd_conv Pdegree Pcoord)
 have scaled: "int d*ramified_weight l rho sigma (int n*(int l*int h-1),n*h)=int d*ramified_weight_deg l rho sigma Q"
 proof -
   have "int d*ramified_weight l rho sigma (int n*(int l*int h-1),n*h)=
     ramified_weight l rho sigma (int d*(int l*int h-1),d*h)*int n"
     by (simp only: ramified_weight_def fst_conv snd_conv of_nat_mult; algebra)
   also have "...=ramified_weight_deg l rho sigma P*int n" by (simp only: Ptop)
   also have "...=int d*ramified_weight_deg l rho sigma Q" using ratio by (simp only: mult.commute)
   finally show ?thesis .
 qed
 have dne: "int d\<noteq>0" using dpos by simp
 have Qtop: "ramified_weight l rho sigma (int n*(int l*int h-1),n*h)=ramified_weight_deg l rho sigma Q"
   by (rule iffD1[OF mult_left_cancel[OF dne] scaled])
 obtain c where cnz: "c\<noteq>0" and div: "rho dvd int l"
 and threshold: "0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
 and fullP: "rootMultiplicity c ?p=degree ?p"
 and fullQ: "rootMultiplicity c (ramified_top_face_polynomial l rho sigma Q)=degree(ramified_top_face_polynomial l rho sigma Q)"
   using ramified_normalized_corner_source_companion_full_root_certificate[OF l rho direction P Q G Pnz Qnz Gnz exact Ppos Qpos degree face Gweight dpos npos h cop ratio Pdegree Pcoord Qtop member distinct] by blast
 let ?C="ramified_cut_aut l rho sigma c"
 obtain r s BP BQ where direction': "is_direction r s" and rpos: "0<r" and strict: "rho*s<r*sigma"
 and positiveP: "0<ramified_weight_deg l r s (?C P)" and positiveQ: "0<ramified_weight_deg l r s (?C Q)"
 and ratio': "ramified_weight_deg l r s (?C Q)*int d=ramified_weight_deg l r s (?C P)*int n"
 and Etop: "ramified_weight l r s E=ramified_weight_deg l r s (?C P)"
 and Ftop: "ramified_weight l r s F=ramified_weight_deg l r s (?C Q)"
 and BP: "BP\<in>ramified_pbw_support l (?C P)" and BPlow: "snd BP<snd E" and BPtop: "ramified_weight l r s BP=ramified_weight_deg l r s (?C P)"
 and BQ: "BQ\<in>ramified_pbw_support l (?C Q)" and BQlow: "snd BQ<snd F" and BQtop: "ramified_weight l r s BQ=ramified_weight_deg l r s (?C Q)"
   using ramified_normalized_corner_full_root_cut_positive_lower_face[OF l rho div sum P Q Pnz Qnz exact fullP fullQ E F d n h Ppos Qpos threshold ratio corner] by blast
 have PC: "?C P\<in>ramified_operator_algebra l" by (rule ramified_cut_aut_mem[OF l P])
 have QC: "?C Q\<in>ramified_operator_algebra l" by (rule ramified_cut_aut_mem[OF l Q])
 note Ps = ramified_full_degree_root_cut_preserves_canonical_endpoint[OF l P rho div sum Pnz fullP]
 note Qs = ramified_full_degree_root_cut_preserves_canonical_endpoint[OF l Q rho div sum Qnz fullQ]
 have EP: "E\<in>ramified_pbw_support l (?C P)" and Eold: "ramified_weight l rho sigma E=ramified_weight_deg l rho sigma P" using Ps by (auto simp only: E)
 have FQ: "F\<in>ramified_pbw_support l (?C Q)" and Fold: "ramified_weight l rho sigma F=ramified_weight_deg l rho sigma Q" using Qs by (auto simp only: F)
 have Pw: "ramified_weight_deg l rho sigma (?C P)=ramified_weight_deg l rho sigma P" by (rule ramified_cut_aut_weight_deg_eq[OF l P rho div sum Pnz])
 have Qw: "ramified_weight_deg l rho sigma (?C Q)=ramified_weight_deg l rho sigma Q" by (rule ramified_cut_aut_weight_deg_eq[OF l Q rho div sum Qnz])
 have Pupper: "\<And>p. p\<in>ramified_pbw_support l (?C P) \<Longrightarrow> ramified_weight l rho sigma p\<le>ramified_weight l rho sigma E"
   using ramified_weight_deg_upper[where l=l and T="?C P" and rho=rho and sigma=sigma] by (simp only: Pw Eold)
 have Qupper: "\<And>q. q\<in>ramified_pbw_support l (?C Q) \<Longrightarrow> ramified_weight l rho sigma q\<le>ramified_weight l rho sigma F"
   using ramified_weight_deg_upper[where l=l and T="?C Q" and rho=rho and sigma=sigma] by (simp only: Qw Fold)
 have endingP: "degree(ramified_top_face_polynomial l r s (?C P))=snd E \<and> ramified_pbw_top_laurent l (?C P)(snd E)=fst E"
   by (rule Ramified_Lower_Face_Ending_Point.ramified_strict_lower_face_canonical_degree_at_preserved_point[OF l rpos strict PC EP Etop Pupper])
 have endingQ: "degree(ramified_top_face_polynomial l r s (?C Q))=snd F \<and> ramified_pbw_top_laurent l (?C Q)(snd F)=fst F"
   by (rule Ramified_Lower_Face_Ending_Point.ramified_strict_lower_face_canonical_degree_at_preserved_point[OF l rpos strict QC FQ Ftop Qupper])
 show ?thesis by (intro exI[of _ c] conjI[OF cnz] conjI[OF div] exI[of _ r] exI[of _ s])
   (use direction' rpos strict positiveP positiveQ ratio' Etop Ftop BP BPlow BPtop BQ BQlow BQtop endingP endingQ in blast)
qed

end
