theory Ramified_Corner_Companion_Full_Root
 imports Ramified_Parallel_Companion_Full_Root
begin

lemma ramified_normalized_corner_source_companion_full_root_certificate:
 fixes n d h j::nat
 assumes l: "0<l" and rho: "0<rho" and direction: "is_direction rho sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0" and Fnz: "F\<noteq>0"
 and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and Ppos: "0<ramified_weight_deg l rho sigma P" and Qpos: "0<ramified_weight_deg l rho sigma Q"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and d: "0<d" and n: "0<n" and h: "2\<le>h" and cop: "coprime d n"
 and ratio: "ramified_weight_deg l rho sigma Q*int d=ramified_weight_deg l rho sigma P*int n"
 and Pdegree: "degree(ramified_top_face_polynomial l rho sigma P)=d*h"
 and Pcoord: "ramified_pbw_top_laurent l P(d*h)=int d*(int l*int h-1)"
 and Qtop: "ramified_weight l rho sigma (int n*(int l*int h-1),n*h)=ramified_weight_deg l rho sigma Q"
 and member: "j\<in>polynomial_support(ramified_top_face_polynomial l rho sigma P)"
 and distinct: "j\<noteq>degree(ramified_top_face_polynomial l rho sigma P)"
 shows "rho dvd int l \<and>
   0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma) \<and>
   (\<exists>c::complex. c\<noteq>0 \<and> poly(ramified_top_face_polynomial l rho sigma P)c=0 \<and>
     rootMultiplicity c (ramified_top_face_polynomial l rho sigma P)=degree(ramified_top_face_polynomial l rho sigma P) \<and>
     rootMultiplicity c (ramified_top_face_polynomial l rho sigma Q)=degree(ramified_top_face_polynomial l rho sigma Q))"
proof -
 let ?p="ramified_top_face_polynomial l rho sigma P"
 let ?f="ramified_top_face_polynomial l rho sigma (-F)"
 have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have divides: "rho dvd int l"
   by (rule ramified_normalized_corner_source_companion_rho_dvd_index[OF l rho direction P Q F Pnz Qnz Fnz exact Ppos Qpos degree face Fweight d n h cop ratio Pdegree Pcoord Qtop member distinct])
 have cases: "(degree ?f=1 \<and> rho dvd int l) \<or>
   (degree ?f=2 \<and> ramified_pbw_top_laurent l (-F)2=int l*2-1 \<and> h=2 \<and> rho=int l \<and> sigma=1-int l \<and>
    0\<in>polynomial_support ?p \<and> ramified_pbw_top_laurent l P 0=int d)"
   by (rule ramified_normalized_corner_source_companion_endpoint_cases[OF l rho direction P Q F Pnz Qnz Fnz exact Ppos Qpos degree face Fweight d n h cop ratio Pdegree Pcoord Qtop member distinct])
 have Pnonzero: "?p\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l P rho Pnz])
 have ending: "rho*ramified_pbw_top_laurent l P(degree ?p)+int l*sigma*int(degree ?p)=ramified_weight_deg l rho sigma P"
   by (rule native_ramified_top_face_degree_weight[OF Pnonzero])
 have Ptop: "ramified_weight l rho sigma (int d*(int l*int h-1),d*h)=ramified_weight_deg l rho sigma P"
   using ending by (simp only: ramified_weight_def fst_conv snd_conv Pdegree Pcoord)
 have threshold: "0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
   by (rule ramified_exact_pair_normalized_corners_positive_threshold[OF l rho sum P Q Pnz Qnz exact d n h Ppos Qpos Ptop Qtop])
 have witness: "\<exists>c::complex. c\<noteq>0 \<and> poly ?p c=0 \<and>
   rootMultiplicity c ?p=degree ?p \<and> rootMultiplicity c (ramified_top_face_polynomial l rho sigma Q)=degree(ramified_top_face_polynomial l rho sigma Q)"
 proof (cases "degree ?f=1")
   case True
   have two: "2\<le>degree ?p"
   proof -
     have "1*2\<le>d*h" by (rule mult_le_mono) (use d h in auto)
     then show ?thesis by (simp only: Pdegree mult_1_left)
   qed
   show ?thesis using ramified_diagonal_companion_exact_pair_cut_certificate[OF l rho direction P Q F Pnz Qnz Fnz exact Ppos Qpos degree face Fweight True two member distinct] by blast
 next
   case False
   have rr: "rho=int l" and ss: "sigma=1-int l" and hh: "h=2"
   and zero: "0\<in>polynomial_support ?p" and coord: "ramified_pbw_top_laurent l P 0=int d"
     using cases False by auto
   have sumone: "rho+sigma=1" by (simp only: rr ss; arith)
   have deg: "degree ?p=2*d" by (simp only: Pdegree hh mult.commute)
   show ?thesis by (rule ramified_parallel_corner_companion_full_root[OF l rho rr sumone P Q F Pnz Qnz Fnz exact Ppos Qpos degree face Fweight d cop ratio deg zero coord])
 qed
 show ?thesis by (intro conjI[OF divides] conjI[OF threshold] witness)
qed

end
