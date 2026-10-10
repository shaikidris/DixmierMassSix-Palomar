theory Ramified_First_Endpoint_Proportion
 imports Ramified_Normalized_Corner_Threshold
   "Ramified_Face_Root_Multiplicity"
begin

lemma ramified_first_endpoint_zero_rootMultiplicity:
 assumes l: "0<l" and rho: "0<rho" and P: "P\<in>ramified_operator_algebra l" and Pnz: "P\<noteq>0"
 and member: "p\<in>ramified_pbw_support l P"
 and top: "ramified_weight l rho sigma p=ramified_weight_deg l rho sigma P"
 and minimum: "\<And>q. q\<in>ramified_pbw_support l P \<Longrightarrow>
   ramified_weight l rho sigma q=ramified_weight_deg l rho sigma P \<Longrightarrow> snd p\<le>snd q"
 shows "rootMultiplicity 0 (ramified_top_face_polynomial l rho sigma P)=snd p"
proof -
 let ?f="ramified_top_face_polynomial l rho sigma P"
 have nonzero: "?f\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l P rho Pnz])
 have coefficient: "coeff ?f (snd p)\<noteq>0"
 proof -
   have point: "(fst p,snd p)\<in>ramified_pbw_support l P" using member by simp
   have weight: "ramified_weight l rho sigma (fst p,snd p)=ramified_weight_deg l rho sigma P" using top by simp
   show ?thesis using point ramified_top_face_coeff_of_weight[OF l P rho weight]
     by (simp only: ramified_pbw_support_mem_iff[OF l P] not_False_eq_True)
 qed
 have lower: "coeff ?f j=0" if less: "j<snd p" for j
 proof (rule ccontr)
   assume "coeff ?f j\<noteq>0"
   then have support: "j\<in>polynomial_support ?f" by (simp only: polynomial_support_def mem_Collect_eq not_False_eq_True)
   have index: "j\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P)"
   and weight: "rho*ramified_pbw_top_laurent l P j+int l*sigma*int j=ramified_weight_deg l rho sigma P"
     using support by (simp_all add: ramified_top_face_polynomial_mem_support_iff)
   have point: "(ramified_pbw_top_laurent l P j,j)\<in>ramified_pbw_support l P"
     by (rule ramified_pbw_top_laurent_support[OF index])
   have top: "ramified_weight l rho sigma (ramified_pbw_top_laurent l P j,j)=ramified_weight_deg l rho sigma P"
     using weight by (simp only: ramified_weight_def fst_conv snd_conv)
   have "snd p\<le>j" using minimum[OF point top] by simp
   then show False using less by arith
 qed
 have divides: "monom 1 (snd p) dvd ?f" using lower by (auto simp: monom_1_dvd_iff')
 have below: "snd p\<le>Polynomial.order 0 ?f" using divides by (simp only: monom_1_dvd_iff[OF nonzero])
 have above: "Polynomial.order 0 ?f\<le>snd p"
 proof (rule ccontr)
   assume "\<not>Polynomial.order 0 ?f\<le>snd p"
   then have less: "snd p<Polynomial.order 0 ?f" by arith
   have monomial: "monom 1 (Polynomial.order 0 ?f) dvd ?f"
     by (simp only: monom_1_dvd_iff[OF nonzero] le_refl)
   have "coeff ?f (snd p)=0" using monomial less by (simp add: monom_1_dvd_iff')
   then show False using coefficient by contradiction
 qed
 have equality: "Polynomial.order 0 ?f=snd p" using below above by arith
 show ?thesis by (simp only: rootMultiplicity_eq_order[OF nonzero] equality)
qed

lemma ramified_exact_pair_first_endpoints_proportional:
 fixes n d::nat
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0" and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and Ppos: "0<ramified_weight_deg l rho sigma P" and Qpos: "0<ramified_weight_deg l rho sigma Q"
 and threshold: "0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
 and pmem: "p\<in>ramified_pbw_support l P" and qmem: "q\<in>ramified_pbw_support l Q"
 and ptop: "ramified_weight l rho sigma p=ramified_weight_deg l rho sigma P"
 and qtop: "ramified_weight l rho sigma q=ramified_weight_deg l rho sigma Q"
 and pmin: "\<And>a. a\<in>ramified_pbw_support l P \<Longrightarrow> ramified_weight l rho sigma a=ramified_weight_deg l rho sigma P \<Longrightarrow> snd p\<le>snd a"
 and qmin: "\<And>a. a\<in>ramified_pbw_support l Q \<Longrightarrow> ramified_weight l rho sigma a=ramified_weight_deg l rho sigma Q \<Longrightarrow> snd q\<le>snd a"
 and ratio: "ramified_weight_deg l rho sigma Q*int d=ramified_weight_deg l rho sigma P*int n"
 shows "int n*fst p=int d*fst q \<and> n*snd p=d*snd q"
proof -
 let ?A="ramified_weight_deg l rho sigma P" let ?D="ramified_weight_deg l rho sigma Q"
 have pzero: "rootMultiplicity 0 (ramified_top_face_polynomial l rho sigma P)=snd p"
   by (rule ramified_first_endpoint_zero_rootMultiplicity[OF l rho P Pnz pmem ptop pmin])
 have qzero: "rootMultiplicity 0 (ramified_top_face_polynomial l rho sigma Q)=snd q"
   by (rule ramified_first_endpoint_zero_rootMultiplicity[OF l rho Q Qnz qmem qtop qmin])
 have swapped_threshold: "0<?D+?A-int l*(rho+sigma)" using threshold by arith
 note roots = ramified_exact_pair_top_face_rootMultiplicity_ratio[where a=0, OF l rho sum Q P Qnz Pnz exact Qpos Ppos swapped_threshold]
 have natural: "nat ?A*snd q=nat ?D*snd p" using roots by (simp only: pzero qzero)
 have castA: "int(nat ?A)=?A" using Ppos by simp
 have castD: "int(nat ?D)=?D" using Qpos by simp
 have integer: "?A*int(snd q)=?D*int(snd p)"
   using arg_cong[where f=int, OF natural] by (simp only: of_nat_mult castA castD)
 have multiplied_ratio: "(?D*int d)*int(snd p)=(?A*int n)*int(snd p)"
   by (rule arg_cong[OF ratio])
 have multiplied_roots: "(?A*int(snd q))*int d=(?D*int(snd p))*int d"
   by (rule arg_cong[OF integer])
 have yfactor: "?A*(int n*int(snd p))=?A*(int d*int(snd q))"
   using multiplied_ratio multiplied_roots by (simp only: algebra_simps; linarith)
 have Anz: "?A\<noteq>0" using Ppos by arith
 have yn: "int n*int(snd p)=int d*int(snd q)" by (rule iffD1[OF mult_left_cancel[OF Anz] yfactor])
 have weightp: "rho*fst p+int l*sigma*int(snd p)=?A" using ptop by (simp only: ramified_weight_def fst_conv snd_conv split_beta)
 have weightq: "rho*fst q+int l*sigma*int(snd q)=?D" using qtop by (simp only: ramified_weight_def fst_conv snd_conv split_beta)
 have wp: "int n*(rho*fst p+int l*sigma*int(snd p))=int n*?A" by (rule arg_cong[OF weightp])
 have wq: "int d*(rho*fst q+int l*sigma*int(snd q))=int d*?D" by (rule arg_cong[OF weightq])
 have wy: "int l*sigma*(int n*int(snd p))=int l*sigma*(int d*int(snd q))" by (rule arg_cong[OF yn])
 have xf: "rho*(int n*fst p)=rho*(int d*fst q)" using wp wq wy ratio by (simp only: algebra_simps; linarith)
 have rhonz: "rho\<noteq>0" using rho by arith
 have x: "int n*fst p=int d*fst q" by (rule iffD1[OF mult_left_cancel[OF rhonz] xf])
 have y: "n*snd p=d*snd q" using yn by (simp only: of_nat_mult[symmetric] of_nat_eq_iff)
 show ?thesis by (rule conjI[OF x y])
qed


lemma ramified_exact_pair_no_diagonal_start_of_source_leading_bracket:
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and positive: "0<ramified_weight_deg l rho sigma P" and Fnz: "F\<noteq>0"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and member: "p\<in>ramified_pbw_support l P"
 and top: "ramified_weight l rho sigma p=ramified_weight_deg l rho sigma P"
 and minimum: "\<And>q. q\<in>ramified_pbw_support l P \<Longrightarrow> ramified_weight l rho sigma q=ramified_weight_deg l rho sigma P \<Longrightarrow> snd p\<le>snd q"
 shows "fst p-int l*int(snd p)\<noteq>0"
proof
 assume diagonal: "fst p-int l*int(snd p)=0"
 have coordinate: "fst p=int l*int(snd p)" using diagonal by arith
 have order: "0<snd p"
 proof (rule ccontr)
   assume "\<not>0<snd p"
   then have zero: "snd p=0" by arith
   have "ramified_weight_deg l rho sigma P=0" using top by (simp add: ramified_weight_def coordinate zero split_beta)
   then show False using positive by arith
 qed
 have Pnz: "P\<noteq>0" using positive by (auto simp: ramified_pbw_zero_data(3)[OF l])
 have reconstruction: "p=(int l*int(snd p),snd p)"
   using prod.collapse[of p] by (simp only: coordinate)
 have point: "(int l*int(snd p),snd p)\<in>ramified_pbw_support l P"
   by (rule subst[where P="\<lambda>q. q\<in>ramified_pbw_support l P", OF reconstruction member])
 have weight: "ramified_weight l rho sigma (int l*int(snd p),snd p)=ramified_weight_deg l rho sigma P" by (rule trans[OF arg_cong[where f="ramified_weight l rho sigma", OF reconstruction[symmetric]] top])
 have low: "snd p\<le>j" if support: "j\<in>polynomial_support(ramified_top_face_polynomial l rho sigma P)" for j
 proof -
   have index: "j\<in>Poly_Mapping.keys(ramified_pbw_coeffs l P)"
   and endpoint_value: "rho*ramified_pbw_top_laurent l P j+int l*sigma*int j=ramified_weight_deg l rho sigma P"
     using support by (simp_all add: ramified_top_face_polynomial_mem_support_iff)
   have point: "(ramified_pbw_top_laurent l P j,j)\<in>ramified_pbw_support l P" by (rule ramified_pbw_top_laurent_support[OF index])
   have top: "ramified_weight l rho sigma (ramified_pbw_top_laurent l P j,j)=ramified_weight_deg l rho sigma P"
     using endpoint_value by (simp only: ramified_weight_def fst_conv snd_conv)
   show ?thesis using minimum[OF point top] by simp
 qed
 show False by (rule ramified_no_diagonal_start_of_source_leading_bracket[OF l rho sum P F Pnz Fnz degree face Fweight order point weight low])
qed

lemma ramified_corner_exists_positive_primitive_first_point:
 fixes n d h::nat
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0" and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and Ppos: "0<ramified_weight_deg l rho sigma P" and Qpos: "0<ramified_weight_deg l rho sigma Q"
 and threshold: "0<ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
 and Fnz: "F\<noteq>0" and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and pmem: "p\<in>ramified_pbw_support l P" and qmem: "q\<in>ramified_pbw_support l Q"
 and ptop: "ramified_weight l rho sigma p=ramified_weight_deg l rho sigma P"
 and qtop: "ramified_weight l rho sigma q=ramified_weight_deg l rho sigma Q"
 and pmin: "\<And>a. a\<in>ramified_pbw_support l P \<Longrightarrow> ramified_weight l rho sigma a=ramified_weight_deg l rho sigma P \<Longrightarrow> snd p\<le>snd a"
 and qmin: "\<And>a. a\<in>ramified_pbw_support l Q \<Longrightarrow> ramified_weight l rho sigma a=ramified_weight_deg l rho sigma Q \<Longrightarrow> snd q\<le>snd a"
 and d: "0<d" and cop: "coprime d n"
 and ratio: "ramified_weight_deg l rho sigma Q*int d=ramified_weight_deg l rho sigma P*int n"
 and corner: "ramified_weight l rho sigma (int d*(int h*int l-1),d*h)=ramified_weight_deg l rho sigma P"
 and Bmem: "B\<in>ramified_pbw_support l P" and Btop: "ramified_weight l rho sigma B=ramified_weight_deg l rho sigma P"
 and Blower: "snd B<d*h"
 shows "\<exists>i::int. \<exists>j::nat. fst p=int d*i \<and> snd p=d*j \<and> 0<i-int l*int j \<and>
   rho*i+int l*sigma*int j=rho*(int l*int h-1)+int l*sigma*int h"
proof -
 have proportion: "int n*fst p=int d*fst q \<and> n*snd p=d*snd q"
   by (rule ramified_exact_pair_first_endpoints_proportional[OF l rho sum P Q Pnz Qnz exact Ppos Qpos threshold pmem qmem ptop qtop pmin qmin ratio])
 have propfirst: "int n*fst p=int d*fst q" and propsecond: "n*snd p=d*snd q" using proportion by auto
 have order: "snd p<d*h" using pmin[OF Bmem Btop] Blower by simp
 have order_cast: "int(snd p)<int(d*h)" using order by (simp only: of_nat_less_iff)
 have order_product: "int(snd p)<int d*int h" using order_cast by (simp only: of_nat_mult)
 have orderZ: "0<int d*int h-int(snd p)" using order_product by arith
 have right: "0<(int l*(rho+sigma))*(int d*int h-int(snd p))" using l sum orderZ by simp
 have relation: "rho*(fst p-int l*int(snd p)+int d)=(int l*(rho+sigma))*(int d*int h-int(snd p))"
   using ptop corner by (simp only: ramified_weight_def fst_conv snd_conv split_beta of_nat_mult; simp only: algebra_simps; linarith)
 have positivegap: "0<fst p-int l*int(snd p)+int d" using right rho
   by (simp only: relation[symmetric] zero_less_mult_iff; arith)
 have gap: "-int d<fst p-int l*int(snd p)" using positivegap by arith
 have nondiag: "fst p-int l*int(snd p)\<noteq>0"
   by (rule ramified_exact_pair_no_diagonal_start_of_source_leading_bracket[OF l rho sum P Q F exact Ppos Fnz degree face Fweight pmem ptop pmin])
 obtain i j where first: "fst p=int d*i" and second: "snd p=d*j" and grade: "0<i-int l*int j"
   using ramified_primitive_start_point_of_coprime_proportion[OF d cop propfirst propsecond gap nondiag] by blast
 have equal: "int d*(rho*i+int l*sigma*int j)=int d*(rho*(int l*int h-1)+int l*sigma*int h)"
   using ptop corner by (simp only: ramified_weight_def fst_conv snd_conv split_beta first second of_nat_mult; simp only: algebra_simps; linarith)
 have dnz: "int d\<noteq>0" using d by simp
 have line: "rho*i+int l*sigma*int j=rho*(int l*int h-1)+int l*sigma*int h"
   by (rule iffD1[OF mult_left_cancel[OF dnz] equal])
 show ?thesis by (intro exI[of _ i] exI[of _ j]) (use first second grade line in auto)
qed

end
