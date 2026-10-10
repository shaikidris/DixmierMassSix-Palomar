theory Ramified_Unequal_Face_Exclusion
 imports Ramified_Canonical_Face_Start_Pair Ramified_Unequal_Slope_Geometry
begin

lemma ramified_exact_pair_no_unequal_first_face:
 fixes E F::"int\<times>nat"
 assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and order: "2\<le>snd F" and old: "int(snd E)*fst F=int(snd F)*fst E"
 and Et: "ramified_weight l rho sigma E=ramified_weight_deg l rho sigma P"
 and Ft: "ramified_weight l rho sigma F=ramified_weight_deg l rho sigma Q"
 and n0: "n0\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P)"
 and n0t: "ramified_weight l rho sigma(ramified_pbw_top_laurent l P n0,n0)=ramified_weight_deg l rho sigma P"
 and below: "n0<snd E"
 and singleton: "\<And>u. u\<in>ramified_pbw_support l Q \<Longrightarrow>
 ramified_weight l rho sigma u=ramified_weight_deg l rho sigma Q \<Longrightarrow>u=F"
 shows False
proof -
 obtain M N where M: "M\<in>Poly_Mapping.keys(ramified_pbw_coeffs l Q)"
 and N: "N\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P)"
 and Mt: "ramified_weight l rho sigma(ramified_pbw_top_laurent l Q M,M)=ramified_weight_deg l rho sigma Q"
 and Nt: "ramified_weight l rho sigma(ramified_pbw_top_laurent l P N,N)=ramified_weight_deg l rho sigma P"
 and minN: "\<forall>a\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P).
 ramified_weight l rho sigma(ramified_pbw_top_laurent l P a,a)=ramified_weight_deg l rho sigma P \<longrightarrow>N\<le>a"
 and criterion: "0<M \<longrightarrow>((of_nat M*of_int(ramified_pbw_top_laurent l P N)-
 of_nat N*of_int(ramified_pbw_top_laurent l Q M)::complex)\<noteq>0 \<longleftrightarrow>
 M+N=1 \<and> ramified_pbw_top_laurent l Q M+ramified_pbw_top_laurent l P N=int l)"
   using exists_ramified_exact_pair_canonical_face_starts[OF l rho positive Q P exact] by blast
 have JF: "(ramified_pbw_top_laurent l Q M,M)=F"
   by (rule singleton[OF ramified_pbw_top_laurent_support[OF M] Mt])
 have Meq: "M=snd F" and Jeq: "ramified_pbw_top_laurent l Q M=fst F"
   using arg_cong[OF JF, where f=snd] arg_cong[OF JF, where f=fst] by simp_all
 have Nlt: "N<snd E" using minN n0 n0t below by auto
 have Epos: "0<snd E" using Nlt by arith
 have Mpos: "0<M" using Meq order by arith
 have W: "ramified_weight l rho sigma E\<noteq>0"
   by (rule ramified_exact_pair_parallel_new_weight_nonzero[OF l rho positive P Q exact Epos old Et Ft])
 have face: "rho*fst E+(int l*sigma)*int(snd E)=
 rho*ramified_pbw_top_laurent l P N+(int l*sigma)*int N"
   using Et Nt by (simp add: ramified_weight_def)
 have weight: "rho*fst E+(int l*sigma)*int(snd E)\<noteq>0"
   using W by (simp add: ramified_weight_def)
 have oldM: "int(snd E)*fst F=int M*fst E" using old Meq by simp
 have detZ: "int N*fst F\<noteq>int M*ramified_pbw_top_laurent l P N"
   by (rule ramified_new_face_point_not_parallel_to_old_mate[OF Mpos Nlt oldM face weight])
 have z: "int M*ramified_pbw_top_laurent l P N-int N*fst F\<noteq>0" using detZ by arith
 have cast: "(of_int(int M*ramified_pbw_top_laurent l P N-int N*fst F)::complex)\<noteq>0"
   using z by (simp only: of_int_eq_0_iff; simp)
 have detC: "(of_nat M*of_int(ramified_pbw_top_laurent l P N)-
 of_nat N*of_int(ramified_pbw_top_laurent l Q M)::complex)\<noteq>0"
   using cast by (simp only: Jeq of_int_diff of_int_mult of_int_of_nat_eq; simp)
 have "M+N=1" using criterion Mpos detC by blast
 then show False using order Meq by arith
qed
end
