theory Crossing_Cut_Multiplicity
 imports "Crossing_Expand_Multiplicity"
   "Crossing_Cut_Formula"
   "Complex_Root_Budget"
begin

lemma crossingFace_general_cutPoly_nonzero_rootMultiplicity:
 fixes T::"complex poly_operator" and mu c::complex and r::"complex poly"
 assumes mu: "mu\<noteq>0" and rho: "0<rho" and r0: "coeff r 0=1" and c: "c\<noteq>0"
 and face: "leading_form (int rho) (-int s) T=
   [:[:mu:]:]*(biv_monom 1 a b*biv_univariate_eval r (biv_monom 1 s rho))^k"
 shows "rootMultiplicity c (cut_poly (int rho) (-int s) T)=k*rootMultiplicity (c^rho) r"
proof -
 let ?g="[:mu:]*[:0,1:]^(b*k)"
 let ?e="pcompose r ([:0,1:]^rho)"
 have r: "r\<noteq>0" using r0 by auto
 have ev: "poly ?g c\<noteq>0" using mu c by simp
 have g: "?g\<noteq>0" using ev by auto
 have positive: "0<degree ([:0,1:]^rho::complex poly)" using rho by (simp add: degree_power_eq)
 have e: "?e\<noteq>0" using r by (simp only: pcompose_eq_0_iff[OF positive] not_False_eq_True)
 have product: "?g*?e^k\<noteq>0" using g e by simp
 have order_zero: "Polynomial.order c ?g=0" by (rule iffD2[OF Polynomial.order_eq_0_iff[OF g] ev])
 have gzero: "rootMultiplicity c ?g=0" by (simp only: rootMultiplicity_eq_order[OF g] order_zero)
 have shape: "cut_poly (int rho) (-int s) T=?g*?e^k"
   by (simp only: crossingFace_general_cutPoly[OF face] native_expand_power)
 show ?thesis by (simp only: shape native_rootMultiplicity_mult[OF product]
   native_rootMultiplicity_power rootMultiplicity_expand_at_nonzero[OF rho c r] gzero add_0_left)
qed

lemma crossingFace_general_cutPoly_zero_rootMultiplicity:
 fixes T::"complex poly_operator" and mu::complex and r::"complex poly"
 assumes mu: "mu\<noteq>0" and rho: "0<rho" and r0: "coeff r 0=1"
 and face: "leading_form (int rho) (-int s) T=
   [:[:mu:]:]*(biv_monom 1 a b*biv_univariate_eval r (biv_monom 1 s rho))^k"
 shows "rootMultiplicity 0 (cut_poly (int rho) (-int s) T)=b*k"
proof -
 let ?g="[:mu:]*pcompose (r^k) ([:0,1:]^rho)"
 have rzero: "poly r 0=1" using r0 by (simp only: poly_0_coeff_0)
 have zero_power: "(0::complex)^rho=0" by (rule zero_power[OF rho])
 have eval: "poly ?g 0\<noteq>0" using mu rzero by (simp add: poly_pcompose zero_power)
 have g: "?g\<noteq>0" using eval by auto
 have product: "?g*[:0,1:]^(b*k)\<noteq>0" using g by simp
 have order_zero: "Polynomial.order 0 ?g=0" by (rule iffD2[OF Polynomial.order_eq_0_iff[OF g] eval])
 have gzero: "rootMultiplicity 0 ?g=0" by (simp only: rootMultiplicity_eq_order[OF g] order_zero)
 have shape: "cut_poly (int rho) (-int s) T=?g*[:0,1:]^(b*k)"
   by (simp only: crossingFace_general_cutPoly[OF face] mult_ac)
 have mono_nonzero: "([:0,1:]^(b*k)::complex poly)\<noteq>0" by simp
 have mono_order: "Polynomial.order (0::complex) ([:0,1:]^(b*k))=b*k"
   using Polynomial.order_power_n_n[where a="0::complex" and n="b*k"] by (simp only: minus_zero)
 have mono: "rootMultiplicity (0::complex) ([:0,1:]^(b*k))=b*k"
   by (simp only: rootMultiplicity_eq_order[OF mono_nonzero] mono_order)
 show ?thesis by (simp only: shape native_rootMultiplicity_mult[OF product] gzero mono add_0_left)
qed

lemma crossingFace_general_cutPoly_maxRootMult_of_full_scalar_root:
 fixes T::"complex poly_operator" and mu alpha::complex and p::"complex poly"
 assumes mu: "mu\<noteq>0" and rho: "0<rho" and k: "0<k" and p0: "coeff p 0=1"
 and alpha: "alpha\<noteq>0" and multiplicity: "rootMultiplicity alpha p=degree p"
 and degree: "0<degree p" and base: "b\<le>degree p"
 and face: "leading_form (int rho) (-int s) T=
   [:[:mu:]:]*(biv_monom 1 a b*biv_univariate_eval p (biv_monom 1 s rho))^k"
 shows "max_root_mult (cut_poly (int rho) (-int s) T)=k*degree p"
proof -
 let ?S="cut_poly (int rho) (-int s) T"
 have pnz: "p\<noteq>0" using degree by auto
 have positive: "0<degree ([:0,1:]^rho::complex poly)" using rho by (simp add: degree_power_eq)
 have en: "pcompose (p^k) ([:0,1:]^rho)\<noteq>0"
   using pnz by (simp only: pcompose_eq_0_iff[OF positive]; simp)
 have Snz: "?S\<noteq>0" using mu en by (simp only: crossingFace_general_cutPoly[OF face]; simp)
 have upper: "rootMultiplicity z ?S\<le>k*degree p" for z
 proof (cases "z=0")
   case True
   show ?thesis using mult_le_mono2[OF base, of k]
     by (simp only: True crossingFace_general_cutPoly_zero_rootMultiplicity[OF mu rho p0 face] mult.commute)
 next
   case False
   have bound: "rootMultiplicity (z^rho) p\<le>degree p"
     by (simp only: rootMultiplicity_eq_order[OF pnz]; rule Polynomial.order_degree[OF pnz])
   show ?thesis by (simp only: crossingFace_general_cutPoly_nonzero_rootMultiplicity[OF mu rho p0 False face]; rule mult_le_mono2[OF bound])
 qed
 have maximum_upper: "max_root_mult ?S\<le>k*degree p"
   unfolding max_root_mult_def rootMultiplicity_eq_count_proots[symmetric]
   by (rule Max.boundedI) (use upper in auto)
 let ?B="[:0,1:]^rho-[:alpha:]"
 have Bdegree: "degree (?B::complex poly)=rho"
   using degree_add_eq_left[where p="[:0,1:]^rho::complex poly" and q="-[:alpha:]"] rho
   by (simp add: degree_power_eq diff_conv_add_uminus)
 have Bpositive: "0<degree ?B" using rho by (simp only: Bdegree)
 obtain z where root: "poly ?B z=0"
   using native_complex_polynomial_max_root_exists[where p="?B", OF Bpositive] by blast
 have power: "z^rho=alpha" using root by simp
 have z: "z\<noteq>0" using power alpha rho by auto
 have value_at_z: "rootMultiplicity z ?S=k*degree p"
   by (simp only: crossingFace_general_cutPoly_nonzero_rootMultiplicity[OF mu rho p0 z face] power multiplicity)
 have order_positive: "0<Polynomial.order z ?S" using value_at_z k degree
   by (simp only: rootMultiplicity_eq_order[OF Snz]; simp)
 have rootS: "poly ?S z=0" using order_positive by (simp add: Polynomial.order_root)
 have membership: "z\<in>set_mset(proots ?S)" using rootS Snz by simp
 let ?W="insert 0 ((\<lambda>z. count(proots ?S) z)`set_mset(proots ?S))"
 have finiteW: "finite ?W" by simp
 have count_member: "count(proots ?S)z\<in>?W"
   by (rule insertI2, rule imageI[OF membership])
 have count_bound: "count(proots ?S)z\<le>Max ?W" by (rule Max_ge[OF finiteW count_member])
 have count_value: "count(proots ?S)z=k*degree p"
   using value_at_z by (simp only: rootMultiplicity_eq_count_proots)
 have maximum_lower: "k*degree p\<le>max_root_mult ?S"
   using count_bound by (simp only: count_value max_root_mult_def)
 show ?thesis using maximum_upper maximum_lower by arith
qed

end
