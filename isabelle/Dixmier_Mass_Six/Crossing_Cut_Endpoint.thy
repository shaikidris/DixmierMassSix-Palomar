theory Crossing_Cut_Endpoint
 imports "Crossing_Cut_Root_Count"
   "Poisson_Fixed_Point_Weight"
   "Ramified_Cut_Setup"
begin

lemma crossing_monomial_weight_bound:
 fixes s rho a b::nat
 assumes direction: "s<rho" and base: "b<a"
 shows "s*b\<le>rho*a"
proof -
 have one: "s*b\<le>s*a" by (rule mult_le_mono2) (use base in arith)
 have two: "s*a\<le>rho*a" by (rule mult_le_mono1) (use direction in arith)
 show ?thesis using one two by arith
qed

lemma crossing_parameter_delta_le_W:
 fixes s rho a b::nat
 assumes direction: "s<rho" and base: "b<a"
 shows "rho-s\<le>rho*a-s*b"
proof -
 have one: "rho*(b+1)\<le>rho*a" by (rule mult_le_mono2) (use base in arith)
 have two: "s*b\<le>rho*b" by (rule mult_le_mono1) (use direction in arith)
 show ?thesis using one two by (simp only: distrib_left mult_1_right; arith)
qed

lemma crossing_scalar_degree_cut_endpoint_identity:
 fixes rho s a b e L::nat
 assumes direction: "s<rho" and base: "b<a"
 and identity: "(rho-s)*e=(a-b)+(rho*a-s*b)*L"
 shows "(rho*a-s*b)*(1+rho*L)=(rho-s)*(b+rho*e)"
proof -
 have bound: "s*b\<le>rho*a" by (rule crossing_monomial_weight_bound[OF direction base])
 have dz: "(int rho-int s)*int e=(int a-int b)+(int rho*int a-int s*int b)*int L"
   using arg_cong[where f=int, OF identity] direction base bound
   by (simp add: of_nat_diff)
 have scaled: "int rho*((int rho-int s)*int e)=
   int rho*((int a-int b)+(int rho*int a-int s*int b)*int L)"
   by (rule arg_cong[OF dz])
 have calculation: "(int rho*int a-int s*int b)*(1+int rho*int L)-
   (int rho-int s)*(int b+int rho*int e)=
   int rho*((int a-int b)+(int rho*int a-int s*int b)*int L)-
   int rho*((int rho-int s)*int e)" by (simp add: algebra_simps)
 have equality: "(int rho*int a-int s*int b)*(1+int rho*int L)=
   (int rho-int s)*(int b+int rho*int e)" using scaled calculation by arith
 have cast_natural: "int((rho*a-s*b)*(1+rho*L))=int((rho-s)*(b+rho*e))"
   using equality
   by (simp only: of_nat_mult of_nat_add of_nat_diff[OF bound]
     of_nat_diff[OF less_imp_le[OF direction]] of_nat_1)
 show ?thesis by (rule of_nat_eq_iff[where 'a=int, THEN iffD1, OF cast_natural])
qed

lemma crossing_general_scalar_facts:
 fixes rho s a b::nat and r f::"complex poly"
 assumes direction: "s<rho" and base: "b<a" and r0: "coeff r 0=1" and r: "0<degree r"
 and scalar: "[:of_nat rho- of_nat s:]*[:0,1:]*f*pderiv r-
 (([:of_nat a- of_nat b:]*f+[:of_nat rho* of_nat a- of_nat s* of_nat b:]*[:0,1:]*pderiv f+1)*r)=0"
 shows "0<degree f \<and> degree f<degree r \<and>
   (rho-s)*degree r=(a-b)+(rho*a-s*b)*degree f \<and>
   (\<forall>alpha. poly r alpha=0 \<longrightarrow> poly f alpha=0 \<and>
    alpha*poly(pderiv f)alpha*(of_nat(rho-s)* of_nat(rootMultiplicity alpha r)- of_nat(rho*a-s*b))=1)"
proof -
 have gen: "GenComp(rho-s)(a-b)(rho*a-s*b) r f"
   by (rule crossing_scalar_to_GenComp[OF direction base scalar])
 have delta: "0<rho-s" using direction by arith
 have H: "0<a-b" using base by arith
 have bound: "rho-s\<le>rho*a-s*b" by (rule crossing_parameter_delta_le_W[OF direction base])
 have zero: "poly r 0=1" using r0 by (simp only: poly_0_coeff_0)
 have f: "0<degree f" by (rule GenComp_natDegree_f_pos[OF gen delta zero r])
 show ?thesis using f GenComp_natDegree_f_lt[OF gen H bound r f]
   GenComp_degree_identity[OF gen r f] GenComp_root_slope[OF gen delta zero] by blast
qed

lemma crossingFace_general_cutPoly_natDegree:
 fixes T::"complex poly_operator" and mu::complex and r::"complex poly"
 assumes mu: "mu\<noteq>0" and rho: "0<rho" and r0: "coeff r 0=1"
 and face: "leading_form (int rho) (-int s) T=
   [:[:mu:]:]*(biv_monom 1 a b*biv_univariate_eval r (biv_monom 1 s rho))^k"
 shows "degree(cut_poly (int rho) (-int s) T)=b*k+rho*k*degree r"
proof -
 have r: "r\<noteq>0" using r0 by auto
 have positive: "0<degree ([:0,1:]^rho::complex poly)" using rho by (simp add: degree_power_eq)
 have expanded: "pcompose r ([:0,1:]^rho)\<noteq>0"
   using r by (simp only: pcompose_eq_0_iff[OF positive] not_False_eq_True)
 show ?thesis using mu expanded
   by (simp add: crossing_power_face_cutPoly[OF face] degree_mult_eq degree_power_eq degree_pcompose mult_ac)
qed

lemma native_fixedPointEuler_constant:
 "fixedPointEuler rho sigma [:[:c:]:]=0"
 for c::complex
 by (simp add: fixedPointEuler_def biv_dx_def biv_dy_def map_poly_pCons pderiv_pCons)

lemma native_fixedPointEuler_power:
 "fixedPointEuler rho sigma (F^k)=[:[:of_nat k:]:]*F^(k-1)*fixedPointEuler rho sigma F"
 for F::"complex bivariate"
proof -
 have successor: "fixedPointEuler rho sigma (F^(Suc n))=
   of_nat(Suc n)*F^n*fixedPointEuler rho sigma F" for n
 proof (induction n)
  case 0 show ?case by (simp only: One_nat_def[symmetric] power_one_right power_0 of_nat_1 mult_1_left mult_1_right)
 next
  case (Suc n)
  have step: "fixedPointEuler rho sigma (F^(Suc(Suc n)))=
    fixedPointEuler rho sigma F*F^(Suc n)+F*fixedPointEuler rho sigma(F^(Suc n))"
    by (subst power_Suc; rule fixedPointEuler_mul)
  show ?case
    by (rule trans[OF step]; simp only: Suc.IH; simp only: power_Suc of_nat_Suc; simp only: algebra_simps mult_1_left)
 qed
 show ?thesis
 proof (cases k)
  case 0 show ?thesis by (simp add: 0 one_pCons native_fixedPointEuler_constant)
 next
  case (Suc n)
  show ?thesis by (simp only: Suc successor diff_Suc_1 of_nat_poly[symmetric])
 qed
qed

lemma crossing_general_scalar_substitution_homogeneous:
 "weighted_homogeneous (int rho) (-int s) 0 (biv_univariate_eval r (biv_monom 1 s rho))"
 for r::"complex poly"
proof -
 let ?E="biv_univariate_eval r (biv_monom 1 s rho)"
 have dx: "biv_monom 1 1 0*biv_dx ?E=
   [:[:of_nat s:]:]*biv_monom 1 s rho*biv_univariate_eval(pderiv r)(biv_monom 1 s rho)"
   using euler_crossing_x[where a=0 and b=0 and A=r and s=s and rho=rho]
   by (simp add: biv_monom_def monom_0; simp only: crossing_inner_unit smult_1_left)
 have dy: "biv_monom 1 0 1*biv_dy ?E=
   [:[:of_nat rho:]:]*biv_monom 1 s rho*biv_univariate_eval(pderiv r)(biv_monom 1 s rho)"
   using euler_crossing_y[where a=0 and b=0 and A=r and s=s and rho=rho]
   by (simp add: biv_monom_def monom_0; simp only: crossing_inner_unit smult_1_left)
 have negative_constant: "[:[:-(of_nat s::complex):]:]=-[:[:of_nat s:]:]"
   by (simp only: minus_pCons minus_zero)
 have constant_negative: "[:-(c::complex):]=-[:c:]" for c
   by (simp only: minus_pCons minus_zero)
 have eq: "fixedPointEuler (int rho) (-int s) ?E=0"
   by (simp only: fixedPointEuler_def dx dy joseph_smult_constant
     of_int_of_nat_eq of_int_minus negative_constant; simp add: algebra_simps;
     simp only: constant_negative smult_minus_left right_minus)
 show ?thesis by (rule homogeneous_of_fixedPointEuler) (simp only: eq of_int_0 pCons_0_0 smult_0_left)
qed

lemma crossingFace_general_weight:
 fixes P::"complex poly_operator" and mu::complex and r::"complex poly"
 assumes direction: "s<rho" and base: "b<a"
 and cut: "cut_poly (int rho) (-int s) P\<noteq>0"
 and face: "leading_form (int rho) (-int s) P=
   [:[:mu:]:]*(biv_monom 1 a b*biv_univariate_eval r (biv_monom 1 s rho))^k"
 shows "v_degree (int rho) (-int s) P=int k*int(rho*a-s*b)"
proof -
 let ?W="int(rho*a-s*b)"
 let ?B="biv_monom 1 a b*biv_univariate_eval r (biv_monom 1 s rho)"
 have bound: "s*b\<le>rho*a" by (rule crossing_monomial_weight_bound[OF direction base])
 have monomial: "weighted_homogeneous (int rho) (-int s) ?W (biv_monom (1::complex) a b)"
   using bound by (auto simp: weighted_homogeneous_def weighted_support_monom pair_weight_def of_nat_diff)
 have monomial_euler: "fixedPointEuler (int rho) (-int s) (biv_monom (1::complex) a b)=smult [:of_int ?W:] (biv_monom 1 a b)"
   by (rule fixedPointEuler_of_homogeneous[OF monomial])
 have scalar_euler: "fixedPointEuler (int rho) (-int s) (biv_univariate_eval r(biv_monom 1 s rho))=0"
   using fixedPointEuler_of_homogeneous[OF crossing_general_scalar_substitution_homogeneous[of rho s r]] by simp
 have base_euler: "fixedPointEuler (int rho) (-int s) ?B=[:[:of_int ?W:]:]*?B"
   by (simp only: fixedPointEuler_mul monomial_euler scalar_euler joseph_smult_constant mult_zero_right add_0_right mult.assoc)
 have scalar_constant: "fixedPointEuler (int rho) (-int s) [:[:mu:]:]=0"
   by (rule native_fixedPointEuler_constant)
 have eq: "fixedPointEuler (int rho) (-int s) (leading_form (int rho) (-int s) P)=
   smult [:of_int(int k*?W):] (leading_form (int rho) (-int s) P)"
 proof -
  have product: "fixedPointEuler (int rho) (-int s) (leading_form (int rho) (-int s) P)=
    fixedPointEuler (int rho) (-int s) [:[:mu:]:]*?B^k+
    [:[:mu:]:]*fixedPointEuler (int rho) (-int s) (?B^k)"
    by (simp only: face; rule fixedPointEuler_mul)
  have derivative: "fixedPointEuler (int rho) (-int s) (leading_form (int rho) (-int s) P)=
    [:[:mu:]:]*([:[:of_nat k:]:]*?B^(k-1)*([:[:of_int ?W:]:]*?B))"
    by (simp only: product scalar_constant native_fixedPointEuler_power
      base_euler mult_zero_left add_0_left)
  have constant_mult: "[:[:(x::complex)*y:]:]=[:[:x:]:]*[:[:y:]:]" for x y
    by simp
  show ?thesis
    by (rule trans[OF derivative];
      simp only: face joseph_smult_constant of_int_mult of_int_of_nat_eq
      constant_mult of_nat_poly[symmetric] of_int_poly[symmetric]; cases k;
      simp only: of_nat_0 of_nat_Suc power_0 power_Suc diff_Suc_1
        pCons_0_0 mult_zero_left mult_zero_right;
      simp only: algebra_simps)
 qed
 have hom: "weighted_homogeneous (int rho) (-int s) (int k*?W) (leading_form (int rho) (-int s) P)"
   by (rule homogeneous_of_fixedPointEuler[OF eq])
 have lead: "weighted_homogeneous (int rho) (-int s) (v_degree (int rho) (-int s) P) (leading_form (int rho) (-int s) P)"
   unfolding leading_form_def by (rule weighted_component_homogeneous)
 have nonzero: "leading_form (int rho) (-int s) P\<noteq>0" using cut by (auto simp: cut_poly_def)
 have nonempty: "biv_support(leading_form (int rho) (-int s) P)\<noteq>{}"
   using nonzero by (simp only: biv_support_empty_iff not_False_eq_True)
 obtain u::"nat\<times>nat" where u: "u\<in>biv_support(leading_form (int rho) (-int s) P)"
   using nonempty by blast
 have hweight: "pair_weight (int rho) (-int s) u=int k*?W"
   by (rule bspec[OF hom[unfolded weighted_homogeneous_def] u])
 have lweight: "pair_weight (int rho) (-int s) u=v_degree (int rho) (-int s) P"
   by (rule bspec[OF lead[unfolded weighted_homogeneous_def] u])
 show ?thesis by (rule trans[OF sym[OF lweight] hweight])
qed


lemma crossing_power_face_cutPoly_companion_degree_identity:
 fixes P::"complex poly_operator" and mu::complex and r f::"complex poly"
 assumes direction: "s<rho" and base: "b<a" and mu: "mu\<noteq>0"
 and r0: "coeff r 0=1" and r: "0<degree r"
 and face: "leading_form (int rho) (-int s) P=
   [:[:mu:]:]*(biv_monom 1 a b*biv_univariate_eval r (biv_monom 1 s rho))^k"
 and cut: "cut_poly (int rho) (-int s) P\<noteq>0"
 and scalar: "[:of_nat rho- of_nat s:]*[:0,1:]*f*pderiv r-
 (([:of_nat a- of_nat b:]*f+[:of_nat rho* of_nat a- of_nat s* of_nat b:]*[:0,1:]*pderiv f+1)*r)=0"
 shows "v_degree (int rho) (-int s) P*int(1+rho*degree f)=
   (int rho+ramified_cut_exponent rho (int rho) (-int s))*int(degree(cut_poly (int rho) (-int s) P))"
proof -
 have rho: "0<rho" using direction by arith
 have facts: "(rho-s)*degree r=(a-b)+(rho*a-s*b)*degree f"
   using crossing_general_scalar_facts[OF direction base r0 r scalar] by blast
 have numeric: "(rho*a-s*b)*(1+rho*degree f)=(rho-s)*(b+rho*degree r)"
   by (rule crossing_scalar_degree_cut_endpoint_identity[OF direction base facts])
 have degree: "degree(cut_poly (int rho) (-int s) P)=b*k+rho*k*degree r"
   by (rule crossingFace_general_cutPoly_natDegree[OF mu rho r0 face])
 have weight: "v_degree (int rho) (-int s) P=int k*int(rho*a-s*b)"
   by (rule crossingFace_general_weight[OF direction base cut face])
 have exponent: "ramified_cut_exponent rho (int rho) (-int s)=-int s"
   using rho by (simp add: ramified_cut_exponent_def)
 have cast: "int(rho*a-s*b)*int(1+rho*degree f)=(int rho-int s)*int(b+rho*degree r)"
   using arg_cong[where f=int, OF numeric]
   by (simp only: of_nat_mult of_nat_diff[OF less_imp_le[OF direction]])
 have scaled: "int k*(int(rho*a-s*b)*int(1+rho*degree f))=
   int k*((int rho-int s)*int(b+rho*degree r))" by (rule arg_cong[OF cast])
 have regroup: "int k*((int rho-int s)*int(b+rho*degree r))=
   (int rho-int s)*int(b*k+rho*k*degree r)"
   by (simp add: of_nat_add of_nat_mult algebra_simps)
 have final: "(int k*int(rho*a-s*b))*int(1+rho*degree f)=
   (int rho-int s)*int(b*k+rho*k*degree r)"
   using trans[OF scaled regroup] by (simp only: mult.assoc)
 show ?thesis using final by (simp only: weight degree exponent diff_conv_add_uminus)
qed

end
