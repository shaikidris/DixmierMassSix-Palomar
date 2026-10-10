theory Ramified_Parallel_Companion_Full_Root
 imports Ramified_Corner_Companion_Cases
begin

lemma ramified_parallel_corner_companion_full_root:
 fixes n d::nat
 assumes l: "0<l" and rho: "0<rho" and rhol: "rho=int l" and sumone: "rho+sigma=1"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0" and Fnz: "F\<noteq>0" and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and Ppos: "0<ramified_weight_deg l rho sigma P" and Qpos: "0<ramified_weight_deg l rho sigma Q"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and d: "0<d" and cop: "coprime d n"
 and ratio: "ramified_weight_deg l rho sigma Q*int d=ramified_weight_deg l rho sigma P*int n"
 and Pdegree: "degree(ramified_top_face_polynomial l rho sigma P)=2*d"
 and zero: "0\<in>polynomial_support(ramified_top_face_polynomial l rho sigma P)"
 and coord: "ramified_pbw_top_laurent l P 0=int d"
 shows "\<exists>c::complex. c\<noteq>0 \<and> poly(ramified_top_face_polynomial l rho sigma P)c=0 \<and>
   rootMultiplicity c (ramified_top_face_polynomial l rho sigma P)=degree(ramified_top_face_polynomial l rho sigma P) \<and>
   rootMultiplicity c (ramified_top_face_polynomial l rho sigma Q)=degree(ramified_top_face_polynomial l rho sigma Q)"
proof -
 let ?p="ramified_top_face_polynomial l rho sigma P"
 let ?q="ramified_top_face_polynomial l rho sigma Q"
 let ?A="ramified_weight_deg l rho sigma P" let ?D="ramified_weight_deg l rho sigma Q"
 let ?k="ramified_cut_exponent l rho sigma"
 have div: "rho dvd int l" by (simp only: rhol dvd_refl)
 have sum: "0<rho+sigma" by (simp only: sumone zero_less_one)
 have weight: "?A=rho*int d" using zero by (simp add: ramified_top_face_polynomial_mem_support_iff coord)
 have dZ: "1\<le>int d" using d by simp
 have step_value: "int l*(rho+sigma)=int l" by (simp only: sumone mult_1_right)
 have step: "int l*(rho+sigma)=rho" by (rule trans[OF step_value rhol[symmetric]])
 have Arho: "rho\<le>?A"
 proof -
   have "rho*1\<le>rho*int d" by (rule mult_left_mono[OF dZ]) (use rho in arith)
   then show ?thesis by (simp only: weight mult_1_right)
 qed
 have threshold: "0<?A+?D-int l*(rho+sigma)" using Arho Qpos by (simp only: step; arith)
 have positive: "0<degree ?p" by (simp only: Pdegree) (use d in simp)
 have nonzero: "?p\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l P rho Pnz])
 obtain c where root: "poly ?p c=0" and maximum: "rootMultiplicity c ?p=max_root_mult ?p"
   using native_complex_polynomial_max_root_exists[OF positive] by blast
 let ?M="rootMultiplicity c ?p" let ?N="rootMultiplicity c ?q"
 have Mpos: "0<?M" using root order_gt_0_iff[OF nonzero, where x=c]
   by (simp only: rootMultiplicity_eq_order[OF nonzero])
 have reverse_threshold: "0<?D+?A-int l*(rho+sigma)" using threshold by arith
 note natural = ramified_exact_pair_top_face_rootMultiplicity_ratio[where a=c, OF l rho sum Q P Qnz Pnz exact Qpos Ppos reverse_threshold]
 have castA: "int(nat ?A)=?A" using Ppos by simp
 have castD: "int(nat ?D)=?D" using Qpos by simp
 have roots: "?D*int ?M=?A*int ?N"
   using arg_cong[where f=int, OF natural] by (simp only: of_nat_mult castA castD)
 have cop': "coprime n d" using cop by (simp only: coprime_commute)
 have divides: "d dvd ?M" using reduced_ratio_root_orders_divide[OF Ppos ratio roots cop'] by blast
 obtain t where multiple: "?M=d*t" using divides by (auto simp: dvd_def)
 have bound: "?M\<le>2*d" using max_root_mult_degree_bound[of ?p] by (simp only: maximum Pdegree)
 have tpos: "0<t" using multiple Mpos by (cases t) auto
 have cast_bound: "int ?M\<le>int(2*d)" using bound by (simp only: of_nat_le_iff)
 have scaled_bound: "int d*int t\<le>int d*2" using cast_bound
   by (simp only: multiple of_nat_mult of_nat_numeral mult.commute)
 have dpositive: "0<int d" using d by simp
 have twobound: "int t\<le>2" by (rule iffD1[OF mult_le_cancel_left_pos[OF dpositive] scaled_bound])
 have cases: "t=1 \<or> t=2" using tpos twobound by arith
 have upper: "\<forall>p\<in>ramified_pbw_support l P. ramified_weight l rho sigma p\<le>?A"
   using ramified_weight_deg_upper by blast
 have poly: "?p=ramified_face_polynomial l P (int d) ?k"
   by (rule ramified_top_face_polynomial_eq_cut_face[OF l P rho div weight upper])
 have kfactor: "rho*?k=rho*sigma" using ramified_cut_exponent_weight[OF div] by (simp only: rhol)
 have rhonz: "rho\<noteq>0" using rho by arith
 have ksigma: "?k=sigma" by (rule iffD1[OF mult_left_cancel[OF rhonz] kfactor])
 have sigma_value: "sigma=1-int l" using sumone by (simp only: rhol; arith)
 have exponent: "?k=1-int l" by (rule trans[OF ksigma sigma_value])
 have zeroindex: "0\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P)"
   using zero by (simp add: ramified_top_face_polynomial_mem_support_iff)
 have point: "(int d,0)\<in>ramified_pbw_support l P"
   using ramified_pbw_top_laurent_support[OF zeroindex] by (simp only: coord)
 have top: "ramified_weight l rho sigma (int d,0)=rho*int d" by (simp add: ramified_weight_def)
 have upperpoint: "\<And>u j. (u,j)\<in>ramified_pbw_support l P \<Longrightarrow> ramified_weight l rho sigma (u,j)\<le>rho*int d"
   using upper by (simp only: weight; blast)
 have face_degree: "degree(ramified_face_polynomial l P (int d) ?k)=2*d"
   by (simp only: poly[symmetric] Pdegree)
 have oldend_value: "int d-(?k+int l)*int(degree(ramified_face_polynomial l P (int d) ?k))=-int d"
 proof -
   have "int d-(?k+int l)*int(degree(ramified_face_polynomial l P (int d) ?k))=
     int d-(?k+int l)*int(2*d)"
     by (rule arg_cong[where f="\<lambda>x. int d-(?k+int l)*int x", OF face_degree])
   also have "...=-int d" by (simp only: exponent of_nat_mult of_nat_numeral; algebra)
   finally show ?thesis .
 qed
 have oldend: "int d-(?k+int l)*int(degree(ramified_face_polynomial l P (int d) ?k))<0"
   using d by (simp only: oldend_value neg_less_0_iff_less of_nat_0_less_iff)
 have maximumpoly: "rootMultiplicity c (ramified_face_polynomial l P (int d) ?k)=max_root_mult(ramified_face_polynomial l P (int d) ?k)"
   by (simp only: poly[symmetric] maximum)
 have negative: "int d-(?k+int l)*int(rootMultiplicity c (ramified_face_polynomial l P (int d) ?k))<0"
   by (rule ramifiedCutAut_maxRoot_grade_negative_of_source_companion[OF l rho div sum _ P Q F exact Pnz Fnz point top upperpoint degree face Fweight positive oldend maximumpoly])
     (use Ppos in \<open>simp only: weight\<close>)
 have full: "?M=degree ?p"
 proof (cases "t=1")
   case True
   have face_multiplicity: "rootMultiplicity c (ramified_face_polynomial l P (int d) ?k)=d"
     by (simp only: poly[symmetric] multiple True mult_1_right)
   have step_factor: "?k+int l=1" by (simp only: exponent; algebra)
   have impossible: "(0::int)<0" using negative
     by (simp only: face_multiplicity step_factor mult_1_left diff_self)
   show ?thesis using impossible by simp
 next
   case False
   have "t=2" using cases False by blast
   then show ?thesis by (simp only: multiple Pdegree mult.commute)
 qed
 have cnz: "c\<noteq>0"
 proof
   assume "c=0"
   then have "coeff ?p 0=0" using root by (simp add: poly_0_coeff_0)
   then show False using zero by (simp add: polynomial_support_def)
 qed
 have mate: "?N=degree ?q" by (rule ramified_exact_pair_full_degree_root_mate_of_reverse_commutator[OF l rho sum P Q Pnz Qnz exact Ppos Qpos threshold full])
 show ?thesis by (intro exI[of _ c]) (use cnz root full mate in auto)
qed

end
