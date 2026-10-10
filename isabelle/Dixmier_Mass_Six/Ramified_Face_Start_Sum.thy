theory Ramified_Face_Start_Sum
 imports "Ramified_First_Face_Top_Pairs"
   "Ramified_Constant_Endpoint"
begin

lemma ramifiedPBWCoeffs_face_start_extremal:
 fixes P Q::laurent_operator and B C::"nat\<Rightarrow>int"
 assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and N: "Suc n\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P)"
 and M: "m\<in>Poly_Mapping.keys(ramified_pbw_coeffs l Q)"
 and BP: "\<And>a. a\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P) \<Longrightarrow>
   laurent_upper (Poly_Mapping.lookup(ramified_pbw_coeffs l P) a) (B a)"
 and CQ: "\<And>b. b\<in>Poly_Mapping.keys(ramified_pbw_coeffs l Q) \<Longrightarrow>
   laurent_upper (Poly_Mapping.lookup(ramified_pbw_coeffs l Q) b) (C b)"
 and upperP: "\<And>a. a\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P) \<Longrightarrow>
   rho*B a+int l*sigma*int a\<le>A"
 and upperQ: "\<And>b. b\<in>Poly_Mapping.keys(ramified_pbw_coeffs l Q) \<Longrightarrow>
   rho*C b+int l*sigma*int b\<le>D"
 and minP: "\<And>a. a\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P) \<Longrightarrow>
   rho*B a+int l*sigma*int a=A \<Longrightarrow> Suc n\<le>a"
 and minQ: "\<And>b. b\<in>Poly_Mapping.keys(ramified_pbw_coeffs l Q) \<Longrightarrow>
   rho*C b+int l*sigma*int b=D \<Longrightarrow> m\<le>b"
 and topP: "rho*B(Suc n)+int l*sigma*int(Suc n)=A"
 and topQ: "rho*C m+int l*sigma*int m=D"
 and fi: "B(Suc n)\<in>Poly_Mapping.keys(Poly_Mapping.lookup(ramified_pbw_coeffs l P)(Suc n))"
 and gu: "C m\<in>Poly_Mapping.keys(Poly_Mapping.lookup(ramified_pbw_coeffs l Q)m)"
 shows "Poly_Mapping.lookup (Poly_Mapping.lookup(ramified_pbw_coeffs l
   (laurent_comp P Q-laurent_comp Q P))(n+m))(B(Suc n)+C m-int l)=
   ((of_nat(Suc n)*of_int(C m)-of_nat m*of_int(B(Suc n)))/of_nat l::complex)*
   Poly_Mapping.lookup(Poly_Mapping.lookup(ramified_pbw_coeffs l P)(Suc n))(B(Suc n))*
   Poly_Mapping.lookup(Poly_Mapping.lookup(ramified_pbw_coeffs l Q)m)(C m)"
proof -
 let ?j="n+m" let ?v="B(Suc n)+C m-int l"
 let ?SP="Poly_Mapping.keys(ramified_pbw_coeffs l P)"
 let ?SQ="Poly_Mapping.keys(ramified_pbw_coeffs l Q)"
 let ?f="\<lambda>a. Poly_Mapping.lookup(ramified_pbw_coeffs l P)a"
 let ?g="\<lambda>b. Poly_Mapping.lookup(ramified_pbw_coeffs l Q)b"
 let ?F="\<lambda>a b. if a+b=?j+1 \<and> rho*B a+int l*sigma*int a=A \<and>
   rho*C b+int l*sigma*int b=D then
   Poly_Mapping.lookup (?f a*laurent_smult(of_nat a)(ramified_derivative l (?g b))-
     ?g b*laurent_smult(of_nat b)(ramified_derivative l (?f a))) ?v else 0"
 have weight: "A+D-int l*(rho+sigma)\<le>ramified_weight l rho sigma(?v,?j)"
   using topP topQ by (simp add: ramified_weight_def algebra_simps)
 have full: "Poly_Mapping.lookup(Poly_Mapping.lookup(ramified_pbw_coeffs l
   (laurent_comp P Q-laurent_comp Q P))?j)?v=(\<Sum>a\<in>?SP.\<Sum>b\<in>?SQ.?F a b)"
   by (rule ramified_pbw_coeffs_commutator_first_face_top_pairs[OF
     l rho positive P Q BP CQ upperP upperQ weight])
 have unique: "a=Suc n \<and> b=m"
   if a: "a\<in>?SP" and b: "b\<in>?SQ"
   and first: "a+b=?j+1" and atop: "rho*B a+int l*sigma*int a=A"
   and btop: "rho*C b+int l*sigma*int b=D" for a b
   using minP[OF a atop] minQ[OF b btop] first by presburger
 have zero: "?F a b=0" if a: "a\<in>?SP" and b: "b\<in>?SQ"
   and neq: "a\<noteq>Suc n \<or> b\<noteq>m" for a b
 proof -
   have excluded: "\<not>(a+b=?j+1 \<and> rho*B a+int l*sigma*int a=A \<and>
      rho*C b+int l*sigma*int b=D)"
   proof
     assume condition: "a+b=?j+1 \<and> rho*B a+int l*sigma*int a=A \<and>
      rho*C b+int l*sigma*int b=D"
     have first: "a+b=?j+1" and atop: "rho*B a+int l*sigma*int a=A"
       and btop: "rho*C b+int l*sigma*int b=D" using condition by blast+
     have equal: "a=Suc n \<and>b=m" by (rule unique[OF a b first atop btop])
     show False using equal neq by blast
   qed
   show ?thesis by (simp only: excluded if_False)
 qed
 have innerZero: "(\<Sum>b\<in>?SQ-{m}.?F(Suc n)b)=0"
 proof (rule sum.neutral, intro ballI)
   fix b assume member: "b\<in>?SQ-{m}"
   have b: "b\<in>?SQ" and neq: "b\<noteq>m" using member by auto
   show "?F(Suc n)b=0" by (rule zero[OF N b]) (use neq in blast)
 qed
 have inner: "(\<Sum>b\<in>?SQ.?F(Suc n)b)=?F(Suc n)m"
   using sum.remove[OF Poly_Mapping.finite_keys M, of "?F(Suc n)"]
   by (simp only: innerZero add_0_right)
 have outerZero: "(\<Sum>a\<in>?SP-{Suc n}.\<Sum>b\<in>?SQ.?F a b)=0"
 proof (rule sum.neutral, intro ballI)
   fix a assume member: "a\<in>?SP-{Suc n}"
   have a: "a\<in>?SP" and neq: "a\<noteq>Suc n" using member by auto
   show "(\<Sum>b\<in>?SQ.?F a b)=0"
   proof (rule sum.neutral, intro ballI)
     fix b assume b: "b\<in>?SQ"
     show "?F a b=0" by (rule zero[OF a b]) (use neq in blast)
   qed
 qed
 have outer: "(\<Sum>a\<in>?SP.\<Sum>b\<in>?SQ.?F a b)=(\<Sum>b\<in>?SQ.?F(Suc n)b)"
   using sum.remove[OF Poly_Mapping.finite_keys N, of "\<lambda>a.\<Sum>b\<in>?SQ.?F a b"]
   by (simp only: outerZero add_0_right)
 have condition: "Suc n+m=?j+1 \<and> rho*B(Suc n)+int l*sigma*int(Suc n)=A \<and>
   rho*C m+int l*sigma*int m=D" using topP topQ by simp
 have selected: "?F(Suc n)m=Poly_Mapping.lookup
   (?f(Suc n)*laurent_smult(of_nat(Suc n))(ramified_derivative l (?g m))-
    ?g m*laurent_smult(of_nat m)(ramified_derivative l (?f(Suc n))))?v"
   by (simp only: condition simp_thms if_True)
 have atom: "Poly_Mapping.lookup(Poly_Mapping.lookup(ramified_pbw_coeffs l
   (laurent_comp(ramified_pbw_atom l (?f(Suc n))(Suc n))(ramified_pbw_atom l (?g m)m)-
    laurent_comp(ramified_pbw_atom l (?g m)m)(ramified_pbw_atom l (?f(Suc n))(Suc n))))?j)?v=
   ((of_nat(Suc n)*of_int(C m)-of_nat m*of_int(B(Suc n)))/of_nat l::complex)*
   Poly_Mapping.lookup(?f(Suc n))(B(Suc n))*Poly_Mapping.lookup(?g m)(C m)"
   by (rule ramified_pbw_coeffs_atom_commutator_first_extremal[OF l BP[OF N] CQ[OF M] fi gu])
 show ?thesis using full outer inner selected atom
   by (simp only: ramified_pbw_coeffs_atom_commutator_first_any_second[OF l])
qed

lemma ramified_exact_pair_face_start_nonparallel_iff_constant:
 fixes P Q::laurent_operator and B C::"nat\<Rightarrow>int"
 assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and comm: "laurent_comp P Q-laurent_comp Q P=id"
 and N: "Suc n\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P)"
 and M: "m\<in>Poly_Mapping.keys(ramified_pbw_coeffs l Q)"
 and BP: "\<And>a. a\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P) \<Longrightarrow>
   laurent_upper (Poly_Mapping.lookup(ramified_pbw_coeffs l P) a) (B a)"
 and CQ: "\<And>b. b\<in>Poly_Mapping.keys(ramified_pbw_coeffs l Q) \<Longrightarrow>
   laurent_upper (Poly_Mapping.lookup(ramified_pbw_coeffs l Q) b) (C b)"
 and upperP: "\<And>a. a\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P) \<Longrightarrow>
   rho*B a+int l*sigma*int a\<le>A"
 and upperQ: "\<And>b. b\<in>Poly_Mapping.keys(ramified_pbw_coeffs l Q) \<Longrightarrow>
   rho*C b+int l*sigma*int b\<le>D"
 and minP: "\<And>a. a\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P) \<Longrightarrow>
   rho*B a+int l*sigma*int a=A \<Longrightarrow> Suc n\<le>a"
 and minQ: "\<And>b. b\<in>Poly_Mapping.keys(ramified_pbw_coeffs l Q) \<Longrightarrow>
   rho*C b+int l*sigma*int b=D \<Longrightarrow> m\<le>b"
 and topP: "rho*B(Suc n)+int l*sigma*int(Suc n)=A"
 and topQ: "rho*C m+int l*sigma*int m=D"
 and fi: "B(Suc n)\<in>Poly_Mapping.keys(Poly_Mapping.lookup(ramified_pbw_coeffs l P)(Suc n))"
 and gu: "C m\<in>Poly_Mapping.keys(Poly_Mapping.lookup(ramified_pbw_coeffs l Q)m)"
 shows "(of_nat(Suc n)*of_int(C m)-of_nat m*of_int(B(Suc n))::complex)\<noteq>0
   \<longleftrightarrow> n+m=0 \<and> B(Suc n)+C m=int l"
proof -
 let ?det="of_nat(Suc n)*of_int(C m)-of_nat m*of_int(B(Suc n))::complex"
 let ?a="Poly_Mapping.lookup(Poly_Mapping.lookup(ramified_pbw_coeffs l P)(Suc n))(B(Suc n))"
 let ?b="Poly_Mapping.lookup(Poly_Mapping.lookup(ramified_pbw_coeffs l Q)m)(C m)"
 have coefficient: "Poly_Mapping.lookup(Poly_Mapping.lookup(ramified_pbw_coeffs l
   (laurent_comp P Q-laurent_comp Q P))(n+m))(B(Suc n)+C m-int l)=
   (?det/of_nat l)*?a*?b"
   by (rule ramifiedPBWCoeffs_face_start_extremal[OF l rho positive P Q N M BP CQ
     upperP upperQ minP minQ topP topQ fi gu])
 have anz: "?a\<noteq>0" and bnz: "?b\<noteq>0" using fi gu by (simp_all add: Poly_Mapping.in_keys_iff)
 have origin: "?det/of_nat l\<noteq>0 \<longleftrightarrow> n+m=0 \<and> B(Suc n)+C m-int l=0"
   by (rule ramified_exact_pair_determinant_nonzero_iff_origin[OF l P Q comm anz bnz coefficient])
 have lnz: "(of_nat l::complex)\<noteq>0" using l by simp
 show ?thesis using origin lnz by simp
qed

end
