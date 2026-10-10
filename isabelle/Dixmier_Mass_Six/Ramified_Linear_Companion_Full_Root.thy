theory Ramified_Linear_Companion_Full_Root
 imports Ramified_First_Endpoint_Proportion
begin

lemma native_polynomial_full_root_shape:
 fixes p::"complex poly"
 assumes p: "p\<noteq>0" and full: "rootMultiplicity c p=degree p"
 shows "p=[:lead_coeff p:]*[:-c,1:]^degree p"
proof -
 have order: "Polynomial.order c p=degree p" using full by (simp only: rootMultiplicity_eq_order[OF p])
 have divides: "[:-c,1:]^degree p dvd p" using order_1[where p=p and a=c] by (simp only: order)
 obtain q where shape: "p=[:-c,1:]^degree p*q" using divides by (auto simp: dvd_def)
 have qnz: "q\<noteq>0" using p shape by auto
 have base: "[:-c,1:]^degree p\<noteq>0" by simp
 have total: "degree p=degree p+degree q" using arg_cong[where f=degree, OF shape]
   by (simp only: degree_mult_eq[OF base qnz] degree_linear_power)
 have qdegree: "degree q=0" using total by arith
 obtain a where scalarshape: "q=[:a:]" using degree0_coeffs[OF qdegree] by blast
 have leading: "lead_coeff p=a" using arg_cong[where f=lead_coeff, OF shape]
   by (simp add: scalarshape lead_coeff_mult lead_coeff_power)
 have "p=[:-c,1:]^degree p*q" by (rule shape)
 also have "...=[:-c,1:]^degree p*[:a:]" by (simp only: scalarshape)
 also have "...=[:lead_coeff p:]*[:-c,1:]^degree p" by (simp only: leading mult.commute)
 finally show ?thesis .
qed

lemma ramified_linear_source_companion_maxRoot_eq_degree:
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Fnz: "F\<noteq>0"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and linear: "degree(ramified_top_face_polynomial l rho sigma (-F))=1"
 shows "max_root_mult(ramified_top_face_polynomial l rho sigma P)=degree(ramified_top_face_polynomial l rho sigma P)"
proof -
 let ?p="ramified_top_face_polynomial l rho sigma P"
 have count: "card(set_mset(proots ?p))\<le>1"
   using ramified_source_companion_top_face_root_count[OF l rho sum P F Pnz Fnz degree face Fweight] by (simp only: linear)
 have lower: "degree ?p\<le>max_root_mult ?p"
   using complex_polynomial_companion_root_budget[OF count] by simp
 have upper: "max_root_mult ?p\<le>degree ?p" by (rule max_root_mult_degree_bound)
 show ?thesis using lower upper by arith
qed

lemma ramified_linear_source_companion_face_eq_power:
 assumes l: "0<l" and rho: "0<rho" and sum: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Fnz: "F\<noteq>0"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and linear: "degree(ramified_top_face_polynomial l rho sigma (-F))=1"
 and positive: "0<degree(ramified_top_face_polynomial l rho sigma P)"
 shows "\<exists>c. poly(ramified_top_face_polynomial l rho sigma P)c=0 \<and>
   ramified_top_face_polynomial l rho sigma P=[:lead_coeff(ramified_top_face_polynomial l rho sigma P):]*
     [:-c,1:]^degree(ramified_top_face_polynomial l rho sigma P)"
proof -
 let ?p="ramified_top_face_polynomial l rho sigma P"
 have nonzero: "?p\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l P rho Pnz])
 have max: "max_root_mult ?p=degree ?p"
   by (rule ramified_linear_source_companion_maxRoot_eq_degree[OF l rho sum P F Pnz Fnz degree face Fweight linear])
 obtain c where root: "poly ?p c=0" and multiplicity: "rootMultiplicity c ?p=max_root_mult ?p"
   using native_complex_polynomial_max_root_exists[OF positive] by blast
 have shape: "?p=[:lead_coeff ?p:]*[:-c,1:]^degree ?p"
   by (rule native_polynomial_full_root_shape[OF nonzero]) (simp only: multiplicity max)
 show ?thesis by (intro exI[of _ c] conjI[OF root shape])
qed

lemma ramified_adjacent_face_first_coordinate_dvd_index:
 fixes l j::nat and rho sigma i i'::int
 assumes direction: "is_direction rho sigma"
 and weight: "rho*i+int l*sigma*int j=rho*i'+int l*sigma*int(j+1)"
 shows "rho dvd int l"
proof -
 have gcdN: "gcd(nat(abs rho))(nat(abs sigma))=1" using direction by (simp add: is_direction_def)
 have gcdZ: "gcd rho sigma=1" by (simp only: gcd_int_def gcdN of_nat_1)
 have cop: "coprime rho sigma" using gcdZ by (simp only: coprime_iff_gcd_eq_1)
 have identity: "sigma*int l=rho*(i-i')" using weight by (simp only: of_nat_add of_nat_1; simp only: algebra_simps; linarith)
 have divides: "rho dvd sigma*int l" unfolding dvd_def by (rule exI[of _ "i-i'"]) (rule identity)
 have commuted: "rho dvd int l*sigma" using divides by (simp only: mult.commute)
 show ?thesis by (rule iffD1[OF coprime_dvd_mult_left_iff[OF cop] commuted])
qed

lemma ramified_pure_power_face_root_ne_zero:
 assumes l: "0<l" and P: "P\<in>ramified_operator_algebra l"
 and member: "j\<in>polynomial_support(ramified_top_face_polynomial l rho sigma P)"
 and distinct: "j\<noteq>degree(ramified_top_face_polynomial l rho sigma P)"
 and shape: "ramified_top_face_polynomial l rho sigma P=
   [:lead_coeff(ramified_top_face_polynomial l rho sigma P):]*[:-c,1:]^degree(ramified_top_face_polynomial l rho sigma P)"
 shows "c\<noteq>0"
proof
 assume zero: "c=0"
 let ?p="ramified_top_face_polynomial l rho sigma P"
 have nonzero: "coeff ?p j\<noteq>0" using member by (simp only: polynomial_support_def mem_Collect_eq not_False_eq_True)
 have monomial: "[:0,1:]^degree ?p=monom 1 (degree ?p)" by (simp add: monom_altdef)
 note coefficient = arg_cong[where f="\<lambda>q. coeff q j", OF shape]
 have different: "degree ?p\<noteq>j" using distinct by (rule not_sym)
 have "coeff ?p j=0" using coefficient
   by (simp only: zero minus_zero monomial mult_pCons_left mult_zero_left pCons_0_0 add_0_right coeff_smult coeff_monom different if_False mult_zero_right)
 then show False using nonzero by contradiction
qed

lemma ramified_pure_power_face_rho_dvd_index:
 assumes l: "0<l" and direction: "is_direction rho sigma" and P: "P\<in>ramified_operator_algebra l"
 and cnz: "c\<noteq>0" and positive: "0<degree(ramified_top_face_polynomial l rho sigma P)"
 and shape: "ramified_top_face_polynomial l rho sigma P=
   [:lead_coeff(ramified_top_face_polynomial l rho sigma P):]*[:-c,1:]^degree(ramified_top_face_polynomial l rho sigma P)"
 shows "rho dvd int l"
proof -
 let ?p="ramified_top_face_polynomial l rho sigma P"
 obtain k where degree: "degree ?p=Suc k" using positive by (cases "degree ?p") auto
 have nonzero: "?p\<noteq>0" using positive by auto
 have lead: "lead_coeff ?p\<noteq>0" using nonzero by simp
 have power: "coeff([:-c,1:]^Suc k)k= of_nat(Suc k)*(-c)"
   using coeff_linear_poly_power[of k "Suc k" "-c::complex" 1] by simp
 have penultimate: "coeff ?p k\<noteq>0"
 proof -
   have coeff: "coeff ?p k=lead_coeff ?p*(of_nat(Suc k)*(-c))"
     using arg_cong[where f="\<lambda>q. coeff q k", OF shape]
     by (simp only: degree mult_pCons_left mult_zero_left pCons_0_0 add_0_right coeff_smult power)
   have cast_nonzero: "(of_nat(Suc k)::complex)\<noteq>0" by (rule of_nat_neq_0)
   show ?thesis using cnz lead cast_nonzero
     by (simp only: coeff mult_eq_0_iff neg_equal_0_iff_equal; blast)
 qed
 have high: "coeff ?p (Suc k)\<noteq>0" using nonzero by (simp only: degree[symmetric]) simp
 have lowmember: "k\<in>polynomial_support ?p" using penultimate
   by (simp only: polynomial_support_def mem_Collect_eq not_False_eq_True)
 have lowtop: "rho*ramified_pbw_top_laurent l P k+int l*sigma*int k=ramified_weight_deg l rho sigma P"
   using lowmember by (simp only: ramified_top_face_polynomial_mem_support_iff; blast)
 have hightop: "rho*ramified_pbw_top_laurent l P (Suc k)+int l*sigma*int(Suc k)=ramified_weight_deg l rho sigma P"
   using native_ramified_top_face_degree_weight[OF nonzero] by (simp only: degree)
 have adjacent: "rho*ramified_pbw_top_laurent l P k+int l*sigma*int k=
   rho*ramified_pbw_top_laurent l P(Suc k)+int l*sigma*int(k+1)" using lowtop hightop by simp
 show ?thesis by (rule ramified_adjacent_face_first_coordinate_dvd_index[OF direction adjacent])
qed


lemma ramified_linear_source_companion_admissible_full_root:
 assumes l: "0<l" and rho: "0<rho" and direction: "is_direction rho sigma"
 and P: "P\<in>ramified_operator_algebra l" and F: "F\<in>ramified_operator_algebra l"
 and Pnz: "P\<noteq>0" and Fnz: "F\<noteq>0"
 and degree: "ramified_weight_deg l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_weight_deg l rho sigma P"
 and face: "ramified_top_face_polynomial l rho sigma (laurent_comp P F-laurent_comp F P)=ramified_top_face_polynomial l rho sigma P"
 and Fweight: "ramified_weight_deg l rho sigma F=int l*(rho+sigma)"
 and linear: "degree(ramified_top_face_polynomial l rho sigma (-F))=1"
 and member: "j\<in>polynomial_support(ramified_top_face_polynomial l rho sigma P)"
 and distinct: "j\<noteq>degree(ramified_top_face_polynomial l rho sigma P)"
 shows "rho dvd int l \<and> (\<exists>c::complex. c\<noteq>0 \<and>
   poly(ramified_top_face_polynomial l rho sigma P)c=0 \<and>
   rootMultiplicity c (ramified_top_face_polynomial l rho sigma P)=degree(ramified_top_face_polynomial l rho sigma P) \<and>
   ramified_top_face_polynomial l rho sigma P=[:lead_coeff(ramified_top_face_polynomial l rho sigma P):]*
     [:-c,1:]^degree(ramified_top_face_polynomial l rho sigma P))"
proof -
 let ?p="ramified_top_face_polynomial l rho sigma P"
 have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have coeff: "coeff ?p j\<noteq>0" using member by (simp only: polynomial_support_def mem_Collect_eq not_False_eq_True)
 have le: "j\<le>degree ?p" by (rule le_degree[OF coeff])
 have positive: "0<degree ?p" using le distinct by arith
 have nonzero: "?p\<noteq>0" using positive by auto
 have max: "max_root_mult ?p=degree ?p"
   by (rule ramified_linear_source_companion_maxRoot_eq_degree[OF l rho sum P F Pnz Fnz degree face Fweight linear])
 obtain c where root: "poly ?p c=0" and multiplicity: "rootMultiplicity c ?p=max_root_mult ?p"
   using native_complex_polynomial_max_root_exists[OF positive] by blast
 have full: "rootMultiplicity c ?p=degree ?p" by (simp only: multiplicity max)
 have shape: "?p=[:lead_coeff ?p:]*[:-c,1:]^degree ?p" by (rule native_polynomial_full_root_shape[OF nonzero full])
 have cnz: "c\<noteq>0" by (rule ramified_pure_power_face_root_ne_zero[OF l P member distinct shape])
 have divides: "rho dvd int l" by (rule ramified_pure_power_face_rho_dvd_index[OF l direction P cnz positive shape])
 show ?thesis by (intro conjI[OF divides] exI[of _ c]) (use cnz root full shape in auto)
qed

end
