theory Ramified_Lower_Face_Ending_Point
 imports Ramified_Corner_Companion_Full_Root
   "Ramified_Adjacent_Strict_Decrease"
begin

lemma ramified_strict_lower_face_order_le_preserved_point:
 assumes l: "0<l" and r: "0<r" and strict: "rho*s<r*sigma"
 and old: "ramified_weight l rho sigma p\<le>ramified_weight l rho sigma E"
 and tie: "ramified_weight l r s p=ramified_weight l r s E"
 shows "snd p\<le>snd E"
proof -
 have scaledtie: "rho*ramified_weight l r s p=rho*ramified_weight l r s E" by (rule arg_cong[OF tie])
 have identity: "r*(ramified_weight l rho sigma p-ramified_weight l rho sigma E)=
   (int l*(r*sigma-rho*s))*(int(snd p)-int(snd E))"
   using scaledtie by (simp only: ramified_weight_def fst_conv snd_conv split_beta algebra_simps; linarith)
 have factor: "0<int l*(r*sigma-rho*s)" using l strict by simp
 have product: "r*(ramified_weight l rho sigma p-ramified_weight l rho sigma E)\<le>0"
   by (rule mult_nonneg_nonpos) (use r old in auto)
 have bound: "(int l*(r*sigma-rho*s))*(int(snd p)-int(snd E))\<le>(int l*(r*sigma-rho*s))*0"
   using product by (simp only: identity mult_0_right)
 have "int(snd p)-int(snd E)\<le>0" by (rule iffD1[OF mult_le_cancel_left_pos[OF factor] bound])
 then show ?thesis by simp
qed

lemma ramified_strict_lower_face_preserved_point_min_grade:
 assumes l: "0<l" and r: "0<r" and sum: "0<r+s" and strict: "rho*s<r*sigma"
 and old: "ramified_weight l rho sigma p\<le>ramified_weight l rho sigma E"
 and tie: "ramified_weight l r s p=ramified_weight l r s E"
 shows "fst E-int l*int(snd E)\<le>fst p-int l*int(snd p)"
proof -
 have order: "snd p\<le>snd E" by (rule ramified_strict_lower_face_order_le_preserved_point[OF l r strict old tie])
 have identity: "r*((fst p-int l*int(snd p))-(fst E-int l*int(snd E)))=
   (int l*(r+s))*(int(snd E)-int(snd p))"
   using tie by (simp only: ramified_weight_def fst_conv snd_conv split_beta algebra_simps; linarith)
 have product: "0\<le>(int l*(r+s))*(int(snd E)-int(snd p))" using l sum order by simp
 have bound: "r*0\<le>r*((fst p-int l*int(snd p))-(fst E-int l*int(snd E)))"
   using product by (simp only: identity mult_0_right)
 have "0\<le>(fst p-int l*int(snd p))-(fst E-int l*int(snd E))" by (rule iffD1[OF mult_le_cancel_left_pos[OF r] bound])
 then show ?thesis by arith
qed

lemma ramified_strict_lower_face_canonical_degree_at_preserved_point:
 assumes l: "0<l" and r: "0<r" and strict: "rho*s<r*sigma"
 and P: "P\<in>ramified_operator_algebra l" and member: "E\<in>ramified_pbw_support l P"
 and top: "ramified_weight l r s E=ramified_weight_deg l r s P"
 and old: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow> ramified_weight l rho sigma p\<le>ramified_weight l rho sigma E"
 shows "degree(ramified_top_face_polynomial l r s P)=snd E \<and> ramified_pbw_top_laurent l P(snd E)=fst E"
proof -
 have upper: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l r s p\<le>ramified_weight_deg l r s P" using ramified_weight_deg_upper by blast
 note data = ramified_face_point_top_laurent_at_order[OF r member top upper]
 have index: "snd E\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P)" and coord: "ramified_pbw_top_laurent l P(snd E)=fst E"
 and ending: "ramified_weight l r s (ramified_pbw_top_laurent l P(snd E),snd E)=ramified_weight_deg l r s P" using data by auto
 have largest: "j\<le>snd E" if index: "j\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P)"
 and tie: "ramified_weight l r s (ramified_pbw_top_laurent l P j,j)=ramified_weight_deg l r s P" for j
 proof -
   have member: "(ramified_pbw_top_laurent l P j,j)\<in>ramified_pbw_support l P" by (rule ramified_pbw_top_laurent_support[OF index])
   have oldbound: "ramified_weight l rho sigma (ramified_pbw_top_laurent l P j,j)\<le>ramified_weight l rho sigma E" by (rule old[OF member])
   have weight: "ramified_weight l r s (ramified_pbw_top_laurent l P j,j)=ramified_weight l r s E" using tie top by simp
   show ?thesis using ramified_strict_lower_face_order_le_preserved_point[OF l r strict oldbound weight] by simp
 qed
 have endingraw: "r*ramified_pbw_top_laurent l P(snd E)+int l*s*int(snd E)=ramified_weight_deg l r s P"
   using ending by (simp only: ramified_weight_def fst_conv snd_conv)
 have largestset: "\<forall>j\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P). r*ramified_pbw_top_laurent l P j+int l*s*int j=ramified_weight_deg l r s P \<longrightarrow> j\<le>snd E"
   using largest by (auto simp: ramified_weight_def)
 have degree: "degree(ramified_top_face_polynomial l r s P)=snd E"
   by (rule ramified_top_face_polynomial_nat_degree_of_endpoint[OF index endingraw largestset])
 show ?thesis by (rule conjI[OF degree coord])
qed

lemma ramified_normalized_corner_new_face_weight_ratio:
 fixes l d n h::nat
 assumes l: "0<l" and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and Ptop: "ramified_weight l r s (int d*(int l*int h-1),d*h)=ramified_weight_deg l r s P"
 and Qtop: "ramified_weight l r s (int n*(int l*int h-1),n*h)=ramified_weight_deg l r s Q"
 shows "ramified_weight_deg l r s Q*int d=ramified_weight_deg l r s P*int n"
proof -
 have normalized: "ramified_weight l r s (int n*(int l*int h-1),n*h)*int d=
   ramified_weight l r s (int d*(int l*int h-1),d*h)*int n"
   by (simp only: ramified_weight_def fst_conv snd_conv of_nat_mult; algebra)
 show ?thesis using normalized by (simp only: Ptop Qtop)
qed

end
