theory Ramified_Corner_Companion_Endpoints
 imports "Ramified_Cut_Companion_Strict_Grade"
begin

lemma native_ramified_top_face_degree_weight:
 assumes nonzero: "ramified_top_face_polynomial l rho sigma P\<noteq>0"
 shows "rho*ramified_pbw_top_laurent l P(degree(ramified_top_face_polynomial l rho sigma P))+
   int l*sigma*int(degree(ramified_top_face_polynomial l rho sigma P))=ramified_weight_deg l rho sigma P"
proof -
 have occupied: "degree(ramified_top_face_polynomial l rho sigma P)\<in>
   polynomial_support(ramified_top_face_polynomial l rho sigma P)"
   using nonzero by (simp add: polynomial_support_def)
 show ?thesis using occupied by (simp only: ramified_top_face_polynomial_mem_support_iff; blast)
qed

lemma ramified_exists_top_face_min_order_point:
 assumes l: "0<l" and rho: "0<rho" and P: "P\<in>ramified_operator_algebra l" and Pnz: "P\<noteq>0"
 shows "\<exists>p\<in>ramified_pbw_support l P. ramified_weight l rho sigma p=ramified_weight_deg l rho sigma P \<and>
   (\<forall>q\<in>ramified_pbw_support l P. ramified_weight l rho sigma q=ramified_weight_deg l rho sigma P \<longrightarrow> snd p\<le>snd q)"
proof -
 let ?f="ramified_top_face_polynomial l rho sigma P"
 let ?S="polynomial_support ?f"
 let ?N="Min ?S"
 let ?p="(ramified_pbw_top_laurent l P ?N,?N)"
 have nonzero: "?f\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l P rho Pnz])
 have top_coeff: "coeff ?f (degree ?f)\<noteq>0" using nonzero by simp
 have occupied: "degree ?f\<in>?S" using top_coeff by (simp only: polynomial_support_def mem_Collect_eq not_False_eq_True)
 have nonempty: "?S\<noteq>{}"
 proof
   assume empty: "?S={}"
   show False using occupied by (simp only: empty empty_iff)
 qed
 have member: "?N\<in>?S" by (rule Min_in[OF polynomial_support_finite nonempty])
 have data: "?N\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P) \<and>
   ramified_weight l rho sigma ?p=ramified_weight_deg l rho sigma P"
   using member by (simp add: ramified_top_face_polynomial_mem_support_iff ramified_weight_def)
 have atom: "?p\<in>ramified_pbw_support l P"
   by (rule ramified_pbw_top_laurent_support) (use data in blast)
 have least: "?N\<le>snd q" if q: "q\<in>ramified_pbw_support l P"
   and qt: "ramified_weight l rho sigma q=ramified_weight_deg l rho sigma P" for q
 proof -
   have upper: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l rho sigma p\<le>ramified_weight_deg l rho sigma P"
     using ramified_weight_deg_upper by blast
   have dataq: "snd q\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P) \<and>
     ramified_weight l rho sigma (ramified_pbw_top_laurent l P(snd q),snd q)=ramified_weight_deg l rho sigma P"
     using ramified_face_point_top_laurent_at_order[OF rho q qt upper] by blast
   have memberq: "snd q\<in>?S"
     using dataq by (simp add: ramified_top_face_polynomial_mem_support_iff ramified_weight_def)
   show ?thesis by (rule Min_le[OF polynomial_support_finite memberq])
 qed
 show ?thesis by (intro bexI[of _ ?p]) (use atom data least in auto)
qed

lemma ramified_source_companion_weight_degree_balance:
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Fnz: "F\<noteq>0"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and Pdegree: "0<degree(ramified_top_face_polynomial l rho sigma P)"
 and Fdegree: "2\<le>degree(ramified_top_face_polynomial l rho sigma (-F))"
 shows "ramified_weight_deg l rho sigma P*int(degree(ramified_top_face_polynomial l rho sigma (-F)))=
   int l*(rho+sigma)*int(degree(ramified_top_face_polynomial l rho sigma P))"
proof -
 let ?g="ramified_top_face_polynomial l rho sigma P"
 let ?f="ramified_top_face_polynomial l rho sigma (-F)"
 let ?den="of_nat l* of_int rho::complex"
 let ?A="of_int(ramified_weight_deg l rho sigma P)/?den"
 let ?B="of_int(ramified_weight_deg l rho sigma (-F))/?den"
 have scalar: "[:?A:]*(pderiv ?f*?g)-[:?B:]*(?f*pderiv ?g)=?g"
   by (rule native_ramified_source_bracket_scalar[OF l rho sum P F Pnz Fnz degree face Fweight])
 have balance: "?A* of_nat(degree ?f)=?B* of_nat(degree ?g)"
   by (rule derivative_bracket_top_degree_balance[OF Pdegree Fdegree scalar])
 have den: "?den\<noteq>0" using l rho by simp
 have scaled: "(?A* of_nat(degree ?f))*?den=(?B* of_nat(degree ?g))*?den" by (rule arg_cong[OF balance])
 have raw: "(of_int(ramified_weight_deg l rho sigma P)::complex)* of_nat(degree ?f)=
   of_int(ramified_weight_deg l rho sigma (-F))* of_nat(degree ?g)"
   using scaled den by (simp add: divide_inverse mult_ac)
 have cast_nat: "(of_int(int n)::complex)= of_nat n" for n by simp
 have grouped: "(of_int(ramified_weight_deg l rho sigma P*int(degree ?f))::complex)=
   of_int(ramified_weight_deg l rho sigma (-F)*int(degree ?g))"
   using raw by (simp only: of_int_mult cast_nat)
 have integers: "ramified_weight_deg l rho sigma P*int(degree ?f)=
   ramified_weight_deg l rho sigma (-F)*int(degree ?g)"
   using grouped by (simp only: of_int_eq_iff)
 show ?thesis using integers by (simp only: ramifiedWeightDeg_neg[OF l F] Fweight)
qed

lemma ramified_source_companion_canonical_endpoint_dichotomy:
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Fnz: "F\<noteq>0"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and Pdegree: "0<degree(ramified_top_face_polynomial l rho sigma P)"
 shows "(degree(ramified_top_face_polynomial l rho sigma (-F))=1 \<and>
   ramified_pbw_top_laurent l (-F)(degree(ramified_top_face_polynomial l rho sigma (-F)))=int l) \<or>
   ramified_pbw_top_laurent l P(degree(ramified_top_face_polynomial l rho sigma P))*
     int(degree(ramified_top_face_polynomial l rho sigma (-F)))=
   ramified_pbw_top_laurent l (-F)(degree(ramified_top_face_polynomial l rho sigma (-F)))*
     int(degree(ramified_top_face_polynomial l rho sigma P))"
proof -
 let ?g="ramified_top_face_polynomial l rho sigma P"
 let ?f="ramified_top_face_polynomial l rho sigma (-F)"
 let ?N="degree ?g" let ?M="degree ?f"
 let ?u="ramified_pbw_top_laurent l P ?N" let ?v="ramified_pbw_top_laurent l (-F) ?M"
 have M: "0<?M" by (rule ramified_source_companion_top_face_degree_pos[OF l rho sum P F Pnz Fnz degree face Fweight Pdegree])
 have gnz: "?g\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l P rho Pnz])
 have fnz: "?f\<noteq>0" using M by auto
 have Nmember: "?N\<in>polynomial_support ?g" using gnz by (simp add: polynomial_support_def)
 have Mmember: "?M\<in>polynomial_support ?f" using fnz by (simp add: polynomial_support_def)
 have Ptop: "rho*?u+int l*sigma*int ?N=ramified_weight_deg l rho sigma P"
   using Nmember by (simp add: ramified_top_face_polynomial_mem_support_iff)
 have Ftop: "rho*?v+int l*sigma*int ?M=int l*(rho+sigma)"
   using Mmember by (simp add: ramified_top_face_polynomial_mem_support_iff ramifiedWeightDeg_neg[OF l F] Fweight)
 show ?thesis
 proof (cases "?M=1")
   case True
   have vertexfactor: "rho*?v=rho*int l" using Ftop by (simp only: True of_nat_1; simp only: algebra_simps; linarith)
   have rhonz: "rho\<noteq>0" using rho by arith
   have vertex: "?v=int l" by (rule iffD1[OF mult_left_cancel[OF rhonz] vertexfactor])
   show ?thesis by (intro disjI1 conjI True vertex)
 next
   case False
   have two: "2\<le>?M" using M False by arith
   have balance: "ramified_weight_deg l rho sigma P*int ?M=int l*(rho+sigma)*int ?N"
     by (rule ramified_source_companion_weight_degree_balance[OF l rho sum P F Pnz Fnz degree face Fweight Pdegree two])
   have left: "(rho*?u+int l*sigma*int ?N)*int ?M=ramified_weight_deg l rho sigma P*int ?M"
     by (rule arg_cong[OF Ptop])
   have right: "(rho*?v+int l*sigma*int ?M)*int ?N=(int l*(rho+sigma))*int ?N"
     by (rule arg_cong[OF Ftop])
   have cancellation: "rho*(?u*int ?M)=rho*(?v*int ?N)" using left right balance by (simp only: algebra_simps; linarith)
   have rhonz: "rho\<noteq>0" using rho by arith
   have parallel: "?u*int ?M=?v*int ?N" by (rule iffD1[OF mult_left_cancel[OF rhonz] cancellation])
   show ?thesis by (rule disjI2[OF parallel])
 qed
qed

end
