theory Ramified_Canonical_Face_Start_Pair
 imports Ramified_Canonical_Face_Min Ramified_Face_Start_Sum
begin

lemma exists_ramified_exact_pair_canonical_face_starts:
 assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and exact: "laurent_comp P Q-laurent_comp Q P=id"
 shows "\<exists>N M. N\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P) \<and>
 M\<in>Poly_Mapping.keys(ramified_pbw_coeffs l Q) \<and>
 ramified_weight l rho sigma(ramified_pbw_top_laurent l P N,N)=ramified_weight_deg l rho sigma P \<and>
 ramified_weight l rho sigma(ramified_pbw_top_laurent l Q M,M)=ramified_weight_deg l rho sigma Q \<and>
 (\<forall>a\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P).
 ramified_weight l rho sigma(ramified_pbw_top_laurent l P a,a)=ramified_weight_deg l rho sigma P \<longrightarrow>N\<le>a) \<and>
 (\<forall>b\<in>Poly_Mapping.keys(ramified_pbw_coeffs l Q).
 ramified_weight l rho sigma(ramified_pbw_top_laurent l Q b,b)=ramified_weight_deg l rho sigma Q \<longrightarrow>M\<le>b) \<and>
 (0<N \<longrightarrow> ((of_nat N*of_int(ramified_pbw_top_laurent l Q M)-
 of_nat M*of_int(ramified_pbw_top_laurent l P N)::complex)\<noteq>0 \<longleftrightarrow>
 N+M=1 \<and> ramified_pbw_top_laurent l P N+ramified_pbw_top_laurent l Q M=int l))"
proof -
 have PS: "ramified_pbw_support l P\<noteq>{}" and QS: "ramified_pbw_support l Q\<noteq>{}"
   using ramified_exact_pair_support_nonempty[OF l P Q exact] by blast+
 obtain A N where N: "N\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P)"
 and Pu: "\<forall>a\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P).
 rho*ramified_pbw_top_laurent l P a+int l*sigma*int a\<le>A"
 and Nt: "rho*ramified_pbw_top_laurent l P N+int l*sigma*int N=A"
 and Nm: "\<forall>a\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P).
 rho*ramified_pbw_top_laurent l P a+int l*sigma*int a=A \<longrightarrow>N\<le>a"
 and Ni: "ramified_pbw_top_laurent l P N\<in>Poly_Mapping.keys(Poly_Mapping.lookup(ramified_pbw_coeffs l P)N)"
 and Pd: "ramified_weight_deg l rho sigma P=A"
   using exists_ramified_canonical_face_start[OF l P rho PS, where sigma=sigma] by blast
 obtain D M where M: "M\<in>Poly_Mapping.keys(ramified_pbw_coeffs l Q)"
 and Qu: "\<forall>b\<in>Poly_Mapping.keys(ramified_pbw_coeffs l Q).
 rho*ramified_pbw_top_laurent l Q b+int l*sigma*int b\<le>D"
 and Mt: "rho*ramified_pbw_top_laurent l Q M+int l*sigma*int M=D"
 and Mm: "\<forall>b\<in>Poly_Mapping.keys(ramified_pbw_coeffs l Q).
 rho*ramified_pbw_top_laurent l Q b+int l*sigma*int b=D \<longrightarrow>M\<le>b"
 and Mi: "ramified_pbw_top_laurent l Q M\<in>Poly_Mapping.keys(Poly_Mapping.lookup(ramified_pbw_coeffs l Q)M)"
 and Qd: "ramified_weight_deg l rho sigma Q=D"
   using exists_ramified_canonical_face_start[OF l Q rho QS, where sigma=sigma] by blast
 have criterion: "(of_nat N*of_int(ramified_pbw_top_laurent l Q M)-
 of_nat M*of_int(ramified_pbw_top_laurent l P N)::complex)\<noteq>0 \<longleftrightarrow>
 N+M=1 \<and> ramified_pbw_top_laurent l P N+ramified_pbw_top_laurent l Q M=int l"
 if pos: "0<N"
 proof -
   obtain n where Ns: "N=Suc n" using pos by (cases N) auto
   have upperP: "\<And>a. a\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P) \<Longrightarrow>
      rho*ramified_pbw_top_laurent l P a+int l*sigma*int a\<le>A" using Pu by blast
   have upperQ: "\<And>b. b\<in>Poly_Mapping.keys(ramified_pbw_coeffs l Q) \<Longrightarrow>
      rho*ramified_pbw_top_laurent l Q b+int l*sigma*int b\<le>D" using Qu by blast
   have minP: "\<And>a. a\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P) \<Longrightarrow>
      rho*ramified_pbw_top_laurent l P a+int l*sigma*int a=A \<Longrightarrow>Suc n\<le>a"
      using Nm Ns by blast
   have minQ: "\<And>b. b\<in>Poly_Mapping.keys(ramified_pbw_coeffs l Q) \<Longrightarrow>
      rho*ramified_pbw_top_laurent l Q b+int l*sigma*int b=D \<Longrightarrow>M\<le>b"
      using Mm by blast
   note result = ramified_exact_pair_face_start_nonparallel_iff_constant
     [OF l rho positive P Q exact N[unfolded Ns] M ramified_pbw_top_laurent_upper
       ramified_pbw_top_laurent_upper upperP upperQ minP minQ Nt[unfolded Ns] Mt Ni[unfolded Ns] Mi]
   have natEq: "n+M=0 \<longleftrightarrow>Suc n+M=1" by arith
   show ?thesis using result by (simp only: Ns natEq)
 qed
 show ?thesis
   by (rule exI[where x=N], rule exI[where x=M])
     (use N M Nt Mt Nm Mm Pd Qd criterion in \<open>auto simp: ramified_weight_def\<close>)
qed
end
