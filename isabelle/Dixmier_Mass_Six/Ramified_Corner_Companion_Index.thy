theory Ramified_Corner_Companion_Index
 imports Ramified_Linear_Companion_Full_Root
begin

lemma ramified_normalized_corner_source_companion_rho_dvd_index:
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
 shows "rho dvd int l"
proof -
 let ?p="ramified_top_face_polynomial l rho sigma P"
 let ?f="ramified_top_face_polynomial l rho sigma (-F)"
 let ?M="degree ?f" let ?v="ramified_pbw_top_laurent l (-F) ?M"
 have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have Pnonzero: "?p\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l P rho Pnz])
 have ending: "rho*ramified_pbw_top_laurent l P(degree ?p)+int l*sigma*int(degree ?p)=ramified_weight_deg l rho sigma P"
   by (rule native_ramified_top_face_degree_weight[OF Pnonzero])
 have Ptop: "ramified_weight l rho sigma (int d*(int l*int h-1),d*h)=ramified_weight_deg l rho sigma P"
   using ending by (simp only: ramified_weight_def fst_conv snd_conv Pdegree Pcoord)
 have threshold: "0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
   by (rule ramified_exact_pair_normalized_corners_positive_threshold[OF l rho sum P Q Pnz Qnz exact d n h Ppos Qpos Ptop Qtop])
 have hpos: "0<h" using h by arith
 have positive: "0<degree ?p" by (simp only: Pdegree) (rule mult_pos_pos[OF d hpos])
 have dichotomy: "(?M=1 \<and> ?v=int l) \<or>
   ramified_pbw_top_laurent l P(degree ?p)*int ?M=?v*int(degree ?p)"
   by (rule ramified_source_companion_canonical_endpoint_dichotomy[OF l rho sum P F Pnz Fnz degree face Fweight positive])
 then show ?thesis
 proof
   assume linear: "?M=1 \<and> ?v=int l"
   have Mone: "?M=1" using linear by blast
   show ?thesis using ramified_linear_source_companion_admissible_full_root[OF l rho direction P F Pnz Fnz degree face Fweight Mone member distinct] by blast
 next
   assume parallel: "ramified_pbw_top_laurent l P(degree ?p)*int ?M=?v*int(degree ?p)"
   obtain a where amem: "a\<in>ramified_pbw_support l P"
   and atop: "ramified_weight l rho sigma a=ramified_weight_deg l rho sigma P"
   and amin: "\<forall>b\<in>ramified_pbw_support l P. ramified_weight l rho sigma b=ramified_weight_deg l rho sigma P \<longrightarrow> snd a\<le>snd b"
     using ramified_exists_top_face_min_order_point[where sigma=sigma, OF l rho P Pnz] by blast
   obtain b where bmem: "b\<in>ramified_pbw_support l Q"
   and btop: "ramified_weight l rho sigma b=ramified_weight_deg l rho sigma Q"
   and bmin: "\<forall>a\<in>ramified_pbw_support l Q. ramified_weight l rho sigma a=ramified_weight_deg l rho sigma Q \<longrightarrow> snd b\<le>snd a"
     using ramified_exists_top_face_min_order_point[where sigma=sigma, OF l rho Q Qnz] by blast
   have minP: "\<And>b. b\<in>ramified_pbw_support l P \<Longrightarrow> ramified_weight l rho sigma b=ramified_weight_deg l rho sigma P \<Longrightarrow> snd a\<le>snd b" using amin by blast
   have minQ: "\<And>a. a\<in>ramified_pbw_support l Q \<Longrightarrow> ramified_weight l rho sigma a=ramified_weight_deg l rho sigma Q \<Longrightarrow> snd b\<le>snd a" using bmin by blast
   have jindex: "j\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P)"
   and jtop: "rho*ramified_pbw_top_laurent l P j+int l*sigma*int j=ramified_weight_deg l rho sigma P"
     using member by (simp_all add: ramified_top_face_polynomial_mem_support_iff)
   have jmem: "(ramified_pbw_top_laurent l P j,j)\<in>ramified_pbw_support l P" by (rule ramified_pbw_top_laurent_support[OF jindex])
   have jweight: "ramified_weight l rho sigma (ramified_pbw_top_laurent l P j,j)=ramified_weight_deg l rho sigma P"
     using jtop by (simp only: ramified_weight_def fst_conv snd_conv)
   have jle: "j\<le>degree ?p" using member by (auto simp: polynomial_support_def intro: le_degree)
   have jlt: "j<d*h" using jle distinct Pdegree by arith
   have corner: "ramified_weight l rho sigma (int d*(int h*int l-1),d*h)=ramified_weight_deg l rho sigma P"
     using Ptop by (simp only: mult.commute)
   have jlower: "snd(ramified_pbw_top_laurent l P j,j)<d*h" using jlt by (simp only: snd_conv)
   obtain i k where grade: "0<i-int l*int k"
   and point: "rho*i+int l*sigma*int k=rho*(int l*int h-1)+int l*sigma*int h"
     using ramified_corner_exists_positive_primitive_first_point[where p=a and q=b and B="(ramified_pbw_top_laurent l P j,j)" and n=n and d=d and h=h, OF l rho sum P Q F Pnz Qnz exact Ppos Qpos threshold Fnz Fweight degree face amem bmem atop btop minP minQ d cop ratio corner jmem jweight jlower] by blast
   have scaled: "int d*(?v*int h)=int d*(int ?M*(int l*int h-1))"
     using parallel by (simp only: Pdegree Pcoord of_nat_mult; simp only: algebra_simps; linarith)
   have dne: "int d\<noteq>0" using d by simp
   have primitive: "?v*int h=int ?M*(int l*int h-1)"
     by (rule iffD1[OF mult_left_cancel[OF dne] scaled])
   have Mpositive: "0<?M" by (rule ramified_source_companion_top_face_degree_pos[OF l rho sum P F Pnz Fnz degree face Fweight positive])
   have Fnonzero: "?f\<noteq>0" using Mpositive by auto
   have Ftop: "rho*?v+int l*sigma*int ?M=int l*(rho+sigma)"
     using native_ramified_top_face_degree_weight[OF Fnonzero] by (simp only: ramifiedWeightDeg_neg[OF l F] Fweight)
   have rigid: "?M=2 \<and> ?v=int l*2-1 \<and> h=2 \<and> rho=int l \<and> sigma=1-int l"
     by (rule ramified_corner_parallel_endpoint_rigid[OF l h direction rho primitive Ftop point grade])
   have equality: "rho=int l" using rigid by blast
   show ?thesis by (simp only: equality dvd_refl)
 qed
qed

end
