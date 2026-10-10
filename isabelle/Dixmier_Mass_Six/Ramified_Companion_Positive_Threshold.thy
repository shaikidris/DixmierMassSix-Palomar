theory Ramified_Companion_Positive_Threshold
 imports Ramified_Corner_Companion_Index
begin

lemma constant_derivative_bracket_maxRoot_le_one:
 fixes f g::"complex poly" and A B::complex
 assumes g: "g\<noteq>0" and bracket: "[:A:]*(pderiv f*g)-[:B:]*(f*pderiv g)=1"
 shows "max_root_mult g\<le>1"
proof -
 have bound: "count(proots g)c\<le>1" if member: "c\<in>set_mset(proots g)" for c
 proof (rule ccontr)
   assume bad: "\<not>count(proots g)c\<le>1"
   have root: "poly g c=0" using member g by simp
   have multiplicity: "1<Polynomial.order c g" using bad by (simp add: rootMultiplicity_eq_count_proots[symmetric] rootMultiplicity_eq_order[OF g])
   have derivative: "poly(pderiv g)c=0"
   proof (cases "pderiv g=0")
     case True
     show ?thesis by (simp only: True poly_0)
   next
     case False
     have order: "0<Polynomial.order c (pderiv g)" using order_pderiv[OF g root] multiplicity by arith
     show ?thesis using order_gt_0_iff[OF False] order by simp
   qed
   have "(0::complex)=1" using arg_cong[where f="\<lambda>p. poly p c", OF bracket]
     by (simp add: root derivative)
   then show False by simp
 qed
 show ?thesis unfolding max_root_mult_def
   by (rule Max.boundedI) (use bound in auto)
qed

lemma ramified_exact_pair_positive_threshold_of_source_companion_degree_gap:
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0" and Fnz: "F\<noteq>0"
 and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and Ppos: "0<ramified_weight_deg l rho sigma P" and Qpos: "0<ramified_weight_deg l rho sigma Q"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and gap: "degree(ramified_top_face_polynomial l rho sigma (-F))<degree(ramified_top_face_polynomial l rho sigma P)"
 shows "0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
proof (rule ccontr)
 let ?p="ramified_top_face_polynomial l rho sigma P"
 let ?f="ramified_top_face_polynomial l rho sigma (-F)"
 assume bad: "\<not>0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
 note lower = ramified_exact_pair_weightDeg_sum_lower[OF l rho sum Q P exact]
 have zero: "ramified_weight_deg l rho sigma Q+ramified_weight_deg l rho sigma P-int l*(rho+sigma)=0"
   using bad lower by arith
 note bracket = ramified_exact_pair_top_face_bracket_eq_one_of_threshold_zero[OF l rho sum Q P Qnz Pnz exact zero]
 have nonzero: "?p\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l P rho Pnz])
 have simple: "max_root_mult ?p\<le>1" by (rule constant_derivative_bracket_maxRoot_le_one[OF nonzero bracket])
 have count: "card(set_mset(proots ?p))\<le>degree ?f"
   by (rule ramified_source_companion_top_face_root_count[OF l rho sum P F Pnz Fnz degree face Fweight])
 have budget: "degree ?p\<le>degree ?f*max_root_mult ?p" by (rule complex_polynomial_companion_root_budget[OF count])
 have upper: "degree ?f*max_root_mult ?p\<le>degree ?f*1" by (rule mult_le_mono2[OF simple])
 show False using budget upper gap by arith
qed

end
