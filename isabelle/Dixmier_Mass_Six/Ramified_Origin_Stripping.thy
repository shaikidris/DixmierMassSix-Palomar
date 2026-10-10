theory Ramified_Origin_Stripping
 imports "Polynomial_Ramified_Lift_Homomorphism"
   "Ramified_Grade_Exact_Pair"
begin

definition ramified_without_origin :: "nat\<Rightarrow>laurent_operator\<Rightarrow>laurent_operator" where
 "ramified_without_origin l T=T-normal_smult (ramified_pbw_coeff l T 0 0) id"

lemma ramified_without_origin_carrier:
 assumes "T\<in>ramified_operator_algebra l"
 shows "ramified_without_origin l T\<in>ramified_operator_algebra l"
 unfolding ramified_without_origin_def
 by (rule ramified_algebra_diff[OF assms ramified_algebra_smult])
   (simp add: ramified_operator_algebra_def)

lemma ramifiedWithoutOrigin_coeff:
 assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
 shows "ramified_pbw_coeff l (ramified_without_origin l T) (fst p) (snd p)=
   ramified_pbw_coeff l T (fst p) (snd p)-ramified_pbw_coeff l T 0 0*ramified_pbw_coeff l id (fst p) (snd p)"
proof -
 have one: "id\<in>ramified_operator_algebra l" by (simp add: ramified_operator_algebra_def)
 show ?thesis unfolding ramified_without_origin_def ramified_pbw_coeff_def
   by (simp add: ramified_pbw_coeffs_diff[OF l T ramified_algebra_smult[OF one]]
     ramified_pbw_coeffs_smult[OF l one] Poly_Mapping.lookup_minus ramified_pbw_smult_lookup laurent_smult_lookup)
qed

lemma ramifiedWithoutOrigin_coeff_origin:
 assumes "0<l" "T\<in>ramified_operator_algebra l"
 shows "ramified_pbw_coeff l (ramified_without_origin l T) 0 0=0"
 using ramifiedWithoutOrigin_coeff[where p="(0,0)", OF assms]
 by (simp add: ramified_pbw_coeff_def ramified_pbw_coeffs_one_coeff_at_origin[OF assms(1)])

lemma ramifiedWithoutOrigin_coeff_ne_origin:
 assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l" and other: "p\<noteq>(0,0)"
 shows "ramified_pbw_coeff l (ramified_without_origin l T) (fst p) (snd p)=ramified_pbw_coeff l T (fst p) (snd p)"
proof -
 have zero: "ramified_pbw_coeff l id (fst p) (snd p)=0"
 proof (rule ccontr)
   assume nonzero: "ramified_pbw_coeff l id (fst p) (snd p)\<noteq>0"
   have member: "fst p\<in>Poly_Mapping.keys(Poly_Mapping.lookup(ramified_pbw_coeffs l id)(snd p))"
     using nonzero by (simp add: ramified_pbw_coeff_def Poly_Mapping.in_keys_iff)
   have "snd p=0 \<and> fst p=0" by (rule ramified_pbw_coeffs_one_coeff_support[OF l member])
   then show False using other by (simp add: prod_eq_iff)
 qed
 show ?thesis by (simp only: ramifiedWithoutOrigin_coeff[OF l T] zero mult_zero_right diff_zero)
qed

lemma ramifiedWithoutOrigin_exact_pair:
 assumes l: "0<l" and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and exact: "laurent_comp Q P-laurent_comp P Q=id"
 shows "laurent_comp(ramified_without_origin l Q)(ramified_without_origin l P)-
   laurent_comp(ramified_without_origin l P)(ramified_without_origin l Q)=id"
proof -
 have Pl: "laurent_linear P" and Ql: "laurent_linear Q" using ramified_operator_algebra_linear[OF P] ramified_operator_algebra_linear[OF Q] by blast+
 have negation: "laurent_smult (-1) g=-g" for g
   by (rule Poly_Mapping.poly_mapping_eqI) simp
 have linear: "T(f-g)=T f-T g" if "laurent_linear T" for T f g
 proof -
   have add: "T(f+laurent_smult (-1) g)=T f+T(laurent_smult (-1) g)"
   and scale: "T(laurent_smult (-1)g)=laurent_smult (-1)(T g)"
     using that unfolding laurent_linear_def by blast+
   show ?thesis using add scale by (simp only: negation diff_conv_add_uminus)
 qed
 have scale: "T(laurent_smult c f)=laurent_smult c(T f)" if "laurent_linear T" for T c f
   using that unfolding laurent_linear_def by blast
 have shift: "laurent_comp(Q-normal_smult b id)(P-normal_smult a id)-
   laurent_comp(P-normal_smult a id)(Q-normal_smult b id)=laurent_comp Q P-laurent_comp P Q" for a b
 proof (rule ext)
   fix f
   show "(laurent_comp(Q-normal_smult b id)(P-normal_smult a id)-
     laurent_comp(P-normal_smult a id)(Q-normal_smult b id)) f=
     (laurent_comp Q P-laurent_comp P Q) f"
   proof (rule Poly_Mapping.poly_mapping_eqI)
     fix k
     show "Poly_Mapping.lookup ((laurent_comp(Q-normal_smult b id)(P-normal_smult a id)-
       laurent_comp(P-normal_smult a id)(Q-normal_smult b id)) f) k=
       Poly_Mapping.lookup ((laurent_comp Q P-laurent_comp P Q) f) k"
       unfolding laurent_comp_def normal_smult_def
       by (simp only: minus_apply id_apply linear[OF Pl] linear[OF Ql]
         scale[OF Pl] scale[OF Ql] laurent_smult_diff Poly_Mapping.lookup_minus
         laurent_smult_lookup; algebra)
   qed
 qed
 show ?thesis by (simp only: ramified_without_origin_def shift exact)
qed

lemma ramifiedWithoutOrigin_negative:
 assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
 and only: "\<And>p. p\<in>ramified_pbw_support l T \<Longrightarrow> 0\<le>fst p-int l*int(snd p) \<Longrightarrow> p=(0,0)"
 shows "\<And>p. p\<in>ramified_pbw_support l (ramified_without_origin l T) \<Longrightarrow> fst p-int l*int(snd p)<0"
proof -
 fix p assume member: "p\<in>ramified_pbw_support l (ramified_without_origin l T)"
 have carrier: "ramified_without_origin l T\<in>ramified_operator_algebra l" by (rule ramified_without_origin_carrier[OF T])
 have paired: "(fst p,snd p)\<in>ramified_pbw_support l (ramified_without_origin l T)"
   using member by (simp only: prod.collapse)
 have nonzero: "ramified_pbw_coeff l (ramified_without_origin l T) (fst p) (snd p)\<noteq>0"
   by (rule iffD1[OF ramified_pbw_support_mem_iff[OF l carrier] paired])
 have other: "p\<noteq>(0,0)" using nonzero ramifiedWithoutOrigin_coeff_origin[OF l T] by auto
 have original_coefficient: "ramified_pbw_coeff l T (fst p) (snd p)\<noteq>0"
   using nonzero by (simp only: ramifiedWithoutOrigin_coeff_ne_origin[OF l T other]; blast)
 have original_pair: "(fst p,snd p)\<in>ramified_pbw_support l T"
   by (rule iffD2[OF ramified_pbw_support_mem_iff[OF l T] original_coefficient])
 have original: "p\<in>ramified_pbw_support l T"
   using original_pair by (simp only: prod.collapse)
 have not_nonnegative: "\<not>0\<le>fst p-int l*int(snd p)"
 proof
   assume nonnegative: "0\<le>fst p-int l*int(snd p)"
   have equal: "p=(0,0)" by (rule only[OF original nonnegative])
   show False using equal other by contradiction
 qed
 show "fst p-int l*int(snd p)<0" using not_nonnegative by arith
qed

lemma ramified_exact_pair_has_nonorigin_nonnegative_grade_point:
 assumes l: "0<l" and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and exact: "laurent_comp Q P-laurent_comp P Q=id"
 shows "(\<exists>p\<in>ramified_pbw_support l P. p\<noteq>(0,0) \<and> 0\<le>fst p-int l*int(snd p)) \<or>
   (\<exists>q\<in>ramified_pbw_support l Q. q\<noteq>(0,0) \<and> 0\<le>fst q-int l*int(snd q))"
proof (rule ccontr)
 assume none: "\<not>?thesis"
 have Ponly: "\<And>p. p\<in>ramified_pbw_support l P \<Longrightarrow> 0\<le>fst p-int l*int(snd p) \<Longrightarrow> p=(0,0)"
 and Qonly: "\<And>q. q\<in>ramified_pbw_support l Q \<Longrightarrow> 0\<le>fst q-int l*int(snd q) \<Longrightarrow> q=(0,0)"
   using none by blast+
 have strippedP: "ramified_without_origin l P\<in>ramified_operator_algebra l" by (rule ramified_without_origin_carrier[OF P])
 have strippedQ: "ramified_without_origin l Q\<in>ramified_operator_algebra l" by (rule ramified_without_origin_carrier[OF Q])
 have stripped_exact: "laurent_comp(ramified_without_origin l Q)(ramified_without_origin l P)-
   laurent_comp(ramified_without_origin l P)(ramified_without_origin l Q)=id"
   by (rule ramifiedWithoutOrigin_exact_pair[OF l P Q exact])
 show False using ramified_exact_pair_has_nonnegative_grade_point[OF l strippedP strippedQ stripped_exact]
   ramifiedWithoutOrigin_negative[OF l P Ponly] ramifiedWithoutOrigin_negative[OF l Q Qonly] by fastforce
qed

end
