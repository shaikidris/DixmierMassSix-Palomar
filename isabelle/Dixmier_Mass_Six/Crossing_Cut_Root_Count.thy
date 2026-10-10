theory Crossing_Cut_Root_Count
 imports "General_Root_Degree"
   "Crossing_Cut_Multiplicity"
   "Crossing_Poisson_Scalar"
begin

lemma crossing_companion_specialization_degree:
 fixes f::"complex poly" and rho::nat
 assumes rho: "0<rho" and constant_term: "poly f 0\<noteq>0"
 shows "degree ([:0,1:]*pcompose f ([:0,1:]^rho))=1+rho*degree f"
proof -
 have eval: "poly(pcompose f ([:0,1:]^rho))0\<noteq>0"
   using constant_term by (simp add: poly_pcompose zero_power[OF rho])
 have nz: "pcompose f ([:0,1:]^rho)\<noteq>0" using eval by auto
 have Xnz: "([:0,1:]::complex poly)\<noteq>0" by simp
 have Xdegree: "degree([:0,1:]::complex poly)=1" by simp
 have power_degree: "degree([:0,1:]^rho::complex poly)=rho" by (simp add: degree_power_eq)
 show ?thesis by (simp only: degree_mult_eq[OF Xnz nz] Xdegree degree_pcompose power_degree mult.commute)
qed

lemma crossing_homogeneous_companion_specialization_degree:
 fixes F::"complex bivariate" and f::"complex poly" and rho s::nat
 assumes rho: "0<rho" and constant_term: "poly f 0\<noteq>0"
 and shape: "F=biv_monom 1 1 1*biv_univariate_eval f (biv_monom 1 s rho)"
 shows "degree(map_poly (\<lambda>q. poly q 1) F)=1+rho*degree f"
proof -
 have mult: "map_poly (\<lambda>q. poly q 1)(A*B)=map_poly (\<lambda>q. poly q 1) A*map_poly (\<lambda>q. poly q 1) B" for A B::"complex bivariate"
   using cut_specialize_hom unfolding coefficient_hom_def by blast
 have map: "map_poly (\<lambda>q. poly q 1) F=[:0,1:]*pcompose f ([:0,1:]^rho)"
   by (simp only: shape crossing_cut_specialize_mult crossing_cut_specialize_monom
     crossing_substitution_eval power_one power_one_right pCons_one mult_1_left)
 show ?thesis by (simp only: map crossing_companion_specialization_degree[OF rho constant_term])
qed

lemma crossing_homogeneous_companion_degreeOf_Y:
 fixes F::"complex bivariate" and f::"complex poly" and rho s::nat
 assumes rho: "0<rho" and constant_term: "poly f 0\<noteq>0"
 and homogeneous: "weighted_homogeneous (int rho) (-int s) (int rho-int s) F"
 and shape: "F=biv_monom 1 1 1*biv_univariate_eval f (biv_monom 1 s rho)"
 shows "degree F=1+rho*degree f"
proof -
 have rpos: "0<(int rho)" using rho by simp
 show ?thesis using homogeneous_specialization_natDegree_eq_degreeOf_Y[OF rpos homogeneous]
   crossing_homogeneous_companion_specialization_degree[OF rho constant_term shape] by simp
qed

lemma crossing_power_face_cutPoly:
 fixes P::"complex poly_operator" and mu::complex and r::"complex poly"
 assumes face: "leading_form (int rho) (-int s) P=
   [:[:mu:]:]*(biv_monom 1 a b*biv_univariate_eval r (biv_monom 1 s rho))^k"
 shows "cut_poly (int rho) (-int s) P=[:mu:]*[:0,1:]^(b*k)*(pcompose r ([:0,1:]^rho))^k"
 by (simp only: crossingFace_general_cutPoly[OF face] native_expand_power)

lemma crossing_power_face_cutPoly_root_count:
 fixes P::"complex poly_operator" and mu::complex and r f::"complex poly"
 assumes direction: "s<rho" and base: "b<a" and r0: "coeff r 0=1"
 and cut: "cut_poly (int rho) (-int s) P\<noteq>0"
 and face: "leading_form (int rho) (-int s) P=
   [:[:mu:]:]*(biv_monom 1 a b*biv_univariate_eval r (biv_monom 1 s rho))^k"
 and scalar: "[:of_nat rho- of_nat s:]*[:0,1:]*f*pderiv r-
 (([:of_nat a- of_nat b:]*f+[:of_nat rho* of_nat a- of_nat s* of_nat b:]*[:0,1:]*pderiv f+1)*r)=0"
 shows "card(set_mset(proots(cut_poly (int rho) (-int s) P)))\<le>1+rho*degree f"
proof -
 have gen: "GenComp (rho-s)(a-b)(rho*a-s*b) r f"
   by (rule crossing_scalar_to_GenComp[OF direction base scalar])
 have rzero: "poly r 0=1" using r0 by (simp only: poly_0_coeff_0)
 have fnz: "f\<noteq>0" using GenComp_constant_relation[OF gen rzero] by auto
 have delta: "0<rho-s" using direction by arith
 have rho: "0<rho" using direction by arith
 show ?thesis by (rule GenComp_powered_face_root_count[OF gen delta rzero fnz rho cut crossing_power_face_cutPoly[OF face]])
qed

lemma crossing_power_face_cutPoly_roots_le_companion_degree:
 fixes P::"complex poly_operator" and F::"complex bivariate" and mu::complex and r f::"complex poly"
 assumes direction: "s<rho" and base: "b<a" and r0: "coeff r 0=1"
 and cut: "cut_poly (int rho) (-int s) P\<noteq>0"
 and face: "leading_form (int rho) (-int s) P=
   [:[:mu:]:]*(biv_monom 1 a b*biv_univariate_eval r (biv_monom 1 s rho))^k"
 and shape: "F=biv_monom 1 1 1*biv_univariate_eval f (biv_monom 1 s rho)"
 and scalar: "[:of_nat rho- of_nat s:]*[:0,1:]*f*pderiv r-
 (([:of_nat a- of_nat b:]*f+[:of_nat rho* of_nat a- of_nat s* of_nat b:]*[:0,1:]*pderiv f+1)*r)=0"
 shows "card(set_mset(proots(cut_poly (int rho) (-int s) P)))\<le>degree(map_poly (\<lambda>q. poly q 1) F)"
proof -
 have gen: "GenComp (rho-s)(a-b)(rho*a-s*b) r f"
   by (rule crossing_scalar_to_GenComp[OF direction base scalar])
 have rzero: "poly r 0=1" using r0 by (simp only: poly_0_coeff_0)
 have fzero: "poly f 0\<noteq>0" using GenComp_constant_relation[OF gen rzero] by auto
 have rho: "0<rho" using direction by arith
 have degree: "degree(map_poly (\<lambda>q. poly q 1) F)=1+rho*degree f"
   by (rule crossing_homogeneous_companion_specialization_degree[OF rho fzero shape])
 show ?thesis by (simp only: degree; rule crossing_power_face_cutPoly_root_count[OF direction base r0 cut face scalar])
qed

lemma crossing_power_face_cutPoly_roots_le_companion_endpoint_Y:
 fixes P::"complex poly_operator" and F::"complex bivariate" and mu::complex and r f::"complex poly"
 assumes direction: "s<rho" and base: "b<a" and r0: "coeff r 0=1"
 and cut: "cut_poly (int rho) (-int s) P\<noteq>0"
 and face: "leading_form (int rho) (-int s) P=
   [:[:mu:]:]*(biv_monom 1 a b*biv_univariate_eval r (biv_monom 1 s rho))^k"
 and homogeneous: "weighted_homogeneous (int rho) (-int s) (int rho-int s) F"
 and shape: "F=biv_monom 1 1 1*biv_univariate_eval f (biv_monom 1 s rho)"
 and scalar: "[:of_nat rho- of_nat s:]*[:0,1:]*f*pderiv r-
 (([:of_nat a- of_nat b:]*f+[:of_nat rho* of_nat a- of_nat s* of_nat b:]*[:0,1:]*pderiv f+1)*r)=0"
 shows "card(set_mset(proots(cut_poly (int rho) (-int s) P)))\<le>degree F"
proof -
 have gen: "GenComp (rho-s)(a-b)(rho*a-s*b) r f"
   by (rule crossing_scalar_to_GenComp[OF direction base scalar])
 have rzero: "poly r 0=1" using r0 by (simp only: poly_0_coeff_0)
 have fzero: "poly f 0\<noteq>0" using GenComp_constant_relation[OF gen rzero] by auto
 have rho: "0<rho" using direction by arith
 have degree: "degree F=1+rho*degree f"
   by (rule crossing_homogeneous_companion_degreeOf_Y[OF rho fzero homogeneous shape])
 show ?thesis by (simp only: degree; rule crossing_power_face_cutPoly_root_count[OF direction base r0 cut face scalar])
qed

end
