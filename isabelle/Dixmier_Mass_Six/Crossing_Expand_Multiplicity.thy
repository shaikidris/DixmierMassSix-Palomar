theory Crossing_Expand_Multiplicity
 imports "General_Companion"
begin

lemma native_expand_power:
 "pcompose (p^k) q=(pcompose p q)^k" for p q::"complex poly"
 by (induction k) (simp_all add: pcompose_mult pcompose_1)

lemma native_rootMultiplicity_mult:
 assumes "p*q\<noteq>0"
 shows "rootMultiplicity a (p*q)=rootMultiplicity a p+rootMultiplicity a q"
 using assms by (simp add: rootMultiplicity_eq_order order_mult)

lemma native_rootMultiplicity_power:
 "rootMultiplicity a (p^k)=k*rootMultiplicity a p"
 by (simp add: rootMultiplicity_eq_count_proots proots_power)

lemma X_pow_sub_C_rootMultiplicity_one_at_nonzero:
 fixes rho::nat and c::complex
 assumes rho: "0<rho" and c: "c\<noteq>0"
 shows "rootMultiplicity c ([:0,1:]^rho-[:c^rho:])=1"
proof -
 let ?p="[:0,1:]^rho-[:c^rho:]"
 have degree: "degree (?p::complex poly)=rho"
   using degree_add_eq_left[where p="[:0,1:]^rho::complex poly" and q="-[:c^rho:]"] rho
   by (simp add: degree_power_eq diff_conv_add_uminus)
 have pnz: "?p\<noteq>0" using degree rho by auto
 have root: "poly ?p c=0" by simp
 have derivative: "poly (pderiv ?p) c=of_nat rho*c^(rho-1)"
   by (simp add: pderiv_diff pderiv_power pderiv_pCons)
 have dnz: "poly (pderiv ?p) c\<noteq>0" using rho c by (simp add: derivative)
 have dpnz: "pderiv ?p\<noteq>0" using dnz by auto
 have orderzero: "order c (pderiv ?p)=0" by (simp add: order_eq_0_iff[OF dpnz] dnz)
 have order: "order c ?p=1" using order_pderiv[OF pnz root] by (simp only: orderzero)
 show ?thesis by (simp only: rootMultiplicity_eq_order[OF pnz] order)
qed

lemma rootMultiplicity_expand_at_nonzero:
 fixes rho::nat and r::"complex poly" and c::complex
 assumes rho: "0<rho" and c: "c\<noteq>0" and r: "r\<noteq>0"
 shows "rootMultiplicity c (pcompose r ([:0,1:]^rho))=rootMultiplicity (c^rho) r"
proof -
 let ?j="order (c^rho) r"
 let ?B="[:0,1:]^rho-[:c^rho:]"
 obtain u where factor: "r=[:-(c^rho),1:]^?j*u" and und: "\<not>[:-(c^rho),1:] dvd u"
   using order_decomp[OF r, of "c^rho"] by blast
 have unz: "poly u (c^rho)\<noteq>0" using und by (simp add: poly_eq_0_iff_dvd)
 have expand_eval: "poly (pcompose u ([:0,1:]^rho)) c\<noteq>0" using unz by (simp add: poly_pcompose)
 have expand_nz: "pcompose u ([:0,1:]^rho)\<noteq>0" using expand_eval by auto
 have composed: "pcompose r ([:0,1:]^rho)=pcompose ([:-(c^rho),1:]^?j*u) ([:0,1:]^rho)"
   by (rule arg_cong[OF factor])
 have linear_substitution: "pcompose [:-(c^rho),1:] ([:0,1:]^rho)=?B"
   by (simp add: pcompose_pCons one_pCons diff_conv_add_uminus minus_pCons add.commute)
 have factor_expand: "pcompose r ([:0,1:]^rho)=?B^?j*pcompose u ([:0,1:]^rho)"
   by (simp only: composed pcompose_mult native_expand_power linear_substitution)
 have Bdegree: "degree (?B::complex poly)=rho"
   using degree_add_eq_left[where p="[:0,1:]^rho::complex poly" and q="-[:c^rho:]"] rho
   by (simp add: degree_power_eq diff_conv_add_uminus)
 have Bnz: "?B\<noteq>0" using Bdegree rho by auto
 have product: "?B^?j*pcompose u ([:0,1:]^rho)\<noteq>0" using Bnz expand_nz by simp
 have uzero: "rootMultiplicity c (pcompose u ([:0,1:]^rho))=0"
   by (simp add: rootMultiplicity_eq_order[OF expand_nz] order_eq_0_iff[OF expand_nz] expand_eval)
 show ?thesis by (simp only: factor_expand native_rootMultiplicity_mult[OF product]
   native_rootMultiplicity_power X_pow_sub_C_rootMultiplicity_one_at_nonzero[OF rho c]
   uzero rootMultiplicity_eq_order[OF r]; simp)
qed

end
