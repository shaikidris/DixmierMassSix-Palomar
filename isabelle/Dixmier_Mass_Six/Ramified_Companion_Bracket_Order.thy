theory Ramified_Companion_Bracket_Order
 imports "Ramified_Shear_Top_Face"
   "Ramified_Leading_Poisson"
begin

lemma native_ramified_zero_carrier: "0\<in>ramified_operator_algebra l"
 using laurent_adjoin.scalar[where c="0::complex"]
 by (simp add: ramified_operator_algebra_def laurent_scalar_zero)

lemma native_ramified_neg_carrier:
 "T\<in>ramified_operator_algebra l \<Longrightarrow> -T\<in>ramified_operator_algebra l"
 using ramified_algebra_diff[OF native_ramified_zero_carrier, of T] by simp

lemma native_ramified_pbw_neg:
 assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
 shows "ramified_pbw_coeffs l (-T)=-ramified_pbw_coeffs l T"
 using ramified_pbw_coeffs_diff[OF l native_ramified_zero_carrier T]
 by (simp add: ramified_pbw_coeffs_zero[OF l])

lemma native_ramified_support_neg:
 assumes "0<l" "T\<in>ramified_operator_algebra l"
 shows "ramified_pbw_support l (-T)=ramified_pbw_support l T"
 using native_ramified_pbw_neg[OF assms]
 by (auto simp: ramified_pbw_support_def Poly_Mapping.in_keys_iff)

lemma ramifiedWeightDeg_neg:
 assumes "0<l" "T\<in>ramified_operator_algebra l"
 shows "ramified_weight_deg l rho sigma (-T)=ramified_weight_deg l rho sigma T"
 by (simp only: ramified_weight_deg_def native_ramified_support_neg[OF assms])

lemma native_ramified_top_laurent_neg:
 assumes "0<l" "T\<in>ramified_operator_algebra l"
 shows "ramified_pbw_top_laurent l (-T) j=ramified_pbw_top_laurent l T j"
 by (simp add: ramified_pbw_top_laurent_def laurent_top_exponent_def
   native_ramified_pbw_neg[OF assms] Poly_Mapping.in_keys_iff)

lemma native_ramified_top_face_neg:
 assumes "0<l" "T\<in>ramified_operator_algebra l"
 shows "ramified_top_face_polynomial l rho sigma (-T)=-ramified_top_face_polynomial l rho sigma T"
 by (rule poly_eqI)
   (simp add: ramified_top_face_polynomial_coeff ramifiedWeightDeg_neg[OF assms]
     native_ramified_top_laurent_neg[OF assms] native_ramified_pbw_neg[OF assms]
     ramified_pbw_coeff_def Poly_Mapping.in_keys_iff)

lemma ramified_top_face_coeff_of_weight:
 assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
 and rho: "0<rho"
 and weight: "ramified_weight l rho sigma (v,j)=ramified_weight_deg l rho sigma T"
 shows "coeff(ramified_top_face_polynomial l rho sigma T) j=ramified_pbw_coeff l T v j"
proof (cases "ramified_pbw_coeff l T v j=0")
 case False
 have point: "(v,j)\<in>ramified_pbw_support l T"
   using False by (simp only: ramified_pbw_support_mem_iff[OF l T] not_False_eq_True)
 have upper: "\<forall>p\<in>ramified_pbw_support l T.
   ramified_weight l rho sigma p\<le>ramified_weight_deg l rho sigma T"
   using ramified_weight_deg_upper by blast
 have data: "j\<in>Poly_Mapping.keys(ramified_pbw_coeffs l T) \<and>
   ramified_pbw_top_laurent l T j=v"
   using ramified_face_point_top_laurent_at_order[OF rho point weight upper] by simp
 show ?thesis using data weight
   by (simp add: ramified_top_face_polynomial_coeff ramified_weight_def)
next
 case True
 have zero: "coeff(ramified_top_face_polynomial l rho sigma T) j=0"
 proof (rule ccontr)
   assume nonzero: "coeff(ramified_top_face_polynomial l rho sigma T) j\<noteq>0"
   have member: "j\<in>polynomial_support(ramified_top_face_polynomial l rho sigma T)"
     using nonzero by (simp only: polynomial_support_def mem_Collect_eq not_False_eq_True)
   have top: "rho*ramified_pbw_top_laurent l T j+int l*sigma*int j=
     ramified_weight_deg l rho sigma T"
     using member by (simp add: ramified_top_face_polynomial_mem_support_iff)
   have product: "rho*ramified_pbw_top_laurent l T j=rho*v"
     using top weight by (simp only: ramified_weight_def fst_conv snd_conv; arith)
   have rho_ne: "rho\<noteq>0" using rho by arith
   have index: "ramified_pbw_top_laurent l T j=v"
     using product by (simp only: mult_left_cancel[OF rho_ne])
   have "coeff(ramified_top_face_polynomial l rho sigma T) j=0"
     using ramified_top_face_polynomial_coeff_of_mem_support[OF member] True
     by (simp only: index)
   then show False using nonzero by contradiction
 qed
 show ?thesis by (simp only: zero True)
qed

lemma ramified_source_leading_bracket_coeffs:
 assumes l: "0<l" and rho: "0<rho"
 and P: "P\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=
   ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=
   ramified_top_face_polynomial l rho sigma P"
 and weight: "ramified_weight l rho sigma (v,j)=ramified_weight_deg l rho sigma P"
 shows "ramified_pbw_coeff l (laurent_comp P F-laurent_comp F P) v j=
   ramified_pbw_coeff l P v j"
proof -
 let ?H="laurent_comp P F-laurent_comp F P"
 have H: "?H\<in>ramified_operator_algebra l"
   by (intro ramified_algebra_diff ramified_algebra_comp) (rule P F)+
 have Hw: "ramified_weight l rho sigma (v,j)=ramified_weight_deg l rho sigma ?H"
   by (simp only: degree weight)
 have "ramified_pbw_coeff l ?H v j=coeff(ramified_top_face_polynomial l rho sigma ?H) j"
   by (rule ramified_top_face_coeff_of_weight[OF l H rho Hw, symmetric])
 also have "...=coeff(ramified_top_face_polynomial l rho sigma P) j"
   by (simp only: face)
 also have "...=ramified_pbw_coeff l P v j"
   by (rule ramified_top_face_coeff_of_weight[OF l P rho weight])
 finally show ?thesis .
qed

lemma ramified_first_face_coeff_of_bracket_coeffs:
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and R: "R\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Rnz: "R\<noteq>0"
 and bracket: "\<And>j v. ramified_weight l rho sigma (v,j)=ramified_weight_deg l rho sigma P \<Longrightarrow>
   ramified_pbw_coeff l (laurent_comp R P-laurent_comp P R) v j=ramified_pbw_coeff l P v j"
 and Rweight: "ramified_weight_deg l rho sigma R=int l*(rho+sigma)"
 and member: "j\<in>polynomial_support(ramified_top_face_polynomial l rho sigma P)"
 shows "coeff ([:of_int(ramified_weight_deg l rho sigma P)/(of_nat l*of_int rho):]*
   (pderiv(ramified_top_face_polynomial l rho sigma R)*ramified_top_face_polynomial l rho sigma P)-
   [:of_int(ramified_weight_deg l rho sigma R)/(of_nat l*of_int rho):]*
   (ramified_top_face_polynomial l rho sigma R*pderiv(ramified_top_face_polynomial l rho sigma P))) j=
   coeff(ramified_top_face_polynomial l rho sigma P) j"
proof -
 let ?v="ramified_pbw_top_laurent l P j"
 have top: "ramified_weight l rho sigma (?v,j)=ramified_weight_deg l rho sigma P"
   using member by (simp add: ramified_top_face_polynomial_mem_support_iff ramified_weight_def)
 have first: "ramified_weight l rho sigma (?v,j)=ramified_weight_deg l rho sigma R+
   ramified_weight_deg l rho sigma P-int l*(rho+sigma)"
   by (simp only: Rweight top; algebra)
 note coefficient = ramified_commutator_first_face_polynomial_bracket[OF l rho sum R P Rnz Pnz first]
 have raw: "ramified_pbw_coeff l (laurent_comp R P-laurent_comp P R) ?v j=
   coeff ([:of_int(ramified_weight_deg l rho sigma P)/(of_nat l*of_int rho):]*
   (pderiv(ramified_top_face_polynomial l rho sigma R)*ramified_top_face_polynomial l rho sigma P)-
   [:of_int(ramified_weight_deg l rho sigma R)/(of_nat l*of_int rho):]*
   (ramified_top_face_polynomial l rho sigma R*pderiv(ramified_top_face_polynomial l rho sigma P))) j"
   using coefficient by (simp only: ramified_pbw_coeff_def)
 have target: "ramified_pbw_coeff l P ?v j=coeff(ramified_top_face_polynomial l rho sigma P) j"
   by (rule ramified_top_face_coeff_of_weight[OF l P rho top, symmetric])
 show ?thesis using raw bracket[OF top] target by simp
qed

lemma ramified_top_face_equation_of_bracket_coeffs:
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and R: "R\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Rnz: "R\<noteq>0"
 and bracket: "\<And>j v. ramified_weight l rho sigma (v,j)=ramified_weight_deg l rho sigma P \<Longrightarrow>
   ramified_pbw_coeff l (laurent_comp R P-laurent_comp P R) v j=ramified_pbw_coeff l P v j"
 and Rweight: "ramified_weight_deg l rho sigma R=int l*(rho+sigma)"
 shows "[:of_int(ramified_weight_deg l rho sigma P)/(of_nat l*of_int rho):]*
   (pderiv(ramified_top_face_polynomial l rho sigma R)*ramified_top_face_polynomial l rho sigma P)-
   [:of_int(ramified_weight_deg l rho sigma R)/(of_nat l*of_int rho):]*
   (ramified_top_face_polynomial l rho sigma R*pderiv(ramified_top_face_polynomial l rho sigma P))=
   ramified_top_face_polynomial l rho sigma P"
proof (rule poly_eqI)
 fix j
 let ?f="ramified_top_face_polynomial l rho sigma R"
 let ?g="ramified_top_face_polynomial l rho sigma P"
 let ?D="ramified_weight_deg l rho sigma P"
 let ?A="ramified_weight_deg l rho sigma R"
 let ?H="[:of_int ?D/(of_nat l*of_int rho):]*(pderiv ?f*?g)-
   [:of_int ?A/(of_nat l*of_int rho):]*(?f*pderiv ?g)"
 show "coeff ?H j=coeff ?g j"
 proof (cases "j\<in>polynomial_support ?g")
   case True
   show ?thesis by (rule ramified_first_face_coeff_of_bracket_coeffs[OF l rho sum P R Pnz Rnz bracket Rweight True])
 next
   case False
   have gzero: "coeff ?g j=0" using False by (simp add: polynomial_support_def)
   have Hzero: "coeff ?H j=0"
   proof (rule ccontr)
     assume nonzero: "coeff ?H j\<noteq>0"
     have pair_sum: "(\<Sum>n\<in>polynomial_support ?f. \<Sum>m\<in>polynomial_support ?g.
       if n+m=j+1 then (of_int ?D/(of_nat l*of_int rho)*of_nat n-
         of_int ?A/(of_nat l*of_int rho)*of_nat m)*coeff ?f n*coeff ?g m else 0)\<noteq>0"
       using nonzero by (simp only: polynomial_derivative_bracket_coeff_support_pairs not_False_eq_True)
     obtain n where n: "n\<in>polynomial_support ?f"
       and nsum: "(\<Sum>m\<in>polynomial_support ?g.
       if n+m=j+1 then (of_int ?D/(of_nat l*of_int rho)*of_nat n-
         of_int ?A/(of_nat l*of_int rho)*of_nat m)*coeff ?f n*coeff ?g m else 0)\<noteq>0"
       using pair_sum by (rule sum.not_neutral_contains_not_neutral)
     obtain m where m: "m\<in>polynomial_support ?g"
       and bracket_term: "(if n+m=j+1 then (of_int ?D/(of_nat l*of_int rho)*of_nat n-
         of_int ?A/(of_nat l*of_int rho)*of_nat m)*coeff ?f n*coeff ?g m else 0)\<noteq>0"
       using nsum by (rule sum.not_neutral_contains_not_neutral)
     have indices: "n+m=j+1" using bracket_term by (auto split: if_splits)
     have cast_indices: "int n+int m=int j+1"
       using arg_cong[where f=int, OF indices] by (simp only: of_nat_add of_nat_1)
     have cast_j: "int j=int n+int m-1" using cast_indices by arith
     have ntop: "rho*ramified_pbw_top_laurent l R n+int l*sigma*int n=?A"
       using n by (simp add: ramified_top_face_polynomial_mem_support_iff)
     have mtop: "rho*ramified_pbw_top_laurent l P m+int l*sigma*int m=?D"
       using m by (simp add: ramified_top_face_polynomial_mem_support_iff)
     let ?v="ramified_pbw_top_laurent l R n+ramified_pbw_top_laurent l P m-int l"
     have expanded_weight: "ramified_weight l rho sigma (?v,j)=
       (rho*ramified_pbw_top_laurent l R n+int l*sigma*int n)+
       (rho*ramified_pbw_top_laurent l P m+int l*sigma*int m)-int l*(rho+sigma)"
       by (simp only: ramified_weight_def fst_conv snd_conv cast_j; algebra)
     have top: "ramified_weight l rho sigma (?v,j)=?D"
       using expanded_weight ntop mtop Rweight by simp
     have first: "ramified_weight l rho sigma (?v,j)=?A+?D-int l*(rho+sigma)"
       using top by (simp only: Rweight; algebra)
     have raw: "ramified_pbw_coeff l (laurent_comp R P-laurent_comp P R) ?v j=coeff ?H j"
       using ramified_commutator_first_face_polynomial_bracket[OF l rho sum R P Rnz Pnz first]
       by (simp only: ramified_pbw_coeff_def)
     have zero: "ramified_pbw_coeff l P ?v j=0"
       using ramified_top_face_coeff_of_weight[OF l P rho top] gzero by simp
     have "coeff ?H j=0" using raw bracket[OF top] zero by simp
     then show False using nonzero by contradiction
   qed
   show ?thesis by (simp only: Hzero gzero)
 qed
qed

lemma native_ramified_source_bracket_scalar:
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Fnz: "F\<noteq>0"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=
   ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=
   ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 shows "[:of_int(ramified_weight_deg l rho sigma P)/(of_nat l*of_int rho):]*
   (pderiv(ramified_top_face_polynomial l rho sigma (-F))*ramified_top_face_polynomial l rho sigma P)-
   [:of_int(ramified_weight_deg l rho sigma (-F))/(of_nat l*of_int rho):]*
   (ramified_top_face_polynomial l rho sigma (-F)*pderiv(ramified_top_face_polynomial l rho sigma P))=
   ramified_top_face_polynomial l rho sigma P"
proof -
 have additive: "P(x+y)=P x+P y" for x y
   using ramified_operator_algebra_linear[OF P] unfolding laurent_linear_def by blast
 have Pzero: "P 0=0" using additive[of 0 0] by simp
 have neg: "P(-x)=-P x" for x
 proof -
   have eq: "P(-x)+P x=0" using additive[of "-x" x] Pzero by simp
   show ?thesis using eq by (simp only: eq_neg_iff_add_eq_0)
 qed
 have swapped: "laurent_comp (-F) P-laurent_comp P (-F)=laurent_comp P F-laurent_comp F P"
   by (rule ext) (simp add: laurent_comp_def neg)
 have negative_F: "-F\<in>ramified_operator_algebra l" by (rule native_ramified_neg_carrier[OF F])
 have negative_Fnz: "-F\<noteq>0" using Fnz by simp
 have bracket: "ramified_pbw_coeff l (laurent_comp (-F) P-laurent_comp P (-F)) v j=
   ramified_pbw_coeff l P v j"
   if "ramified_weight l rho sigma (v,j)=ramified_weight_deg l rho sigma P" for j v
   by (simp only: swapped; rule ramified_source_leading_bracket_coeffs[OF l rho P F degree face that])
 have negative_weight: "ramified_weight_deg l rho sigma (-F)=int l*(rho+sigma)"
   by (simp only: ramifiedWeightDeg_neg[OF l F] Fweight)
 show ?thesis by (rule ramified_top_face_equation_of_bracket_coeffs[OF l rho sum P negative_F
   Pnz negative_Fnz bracket negative_weight])
qed

end
