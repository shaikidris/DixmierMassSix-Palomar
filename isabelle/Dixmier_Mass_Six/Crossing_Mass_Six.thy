theory Crossing_Mass_Six
 imports "Crossing_Cut_Endpoint"
   "Sparse_Power_Divisibility"
begin

lemma crossing_parameter_weight_identity:
 fixes rho s a b::nat
 assumes direction: "s<rho" and base: "b<a"
 shows "rho*a-s*b=(rho-s)*a+s*(a-b)"
proof -
 have bound: "s*b\<le>rho*a" by (rule crossing_monomial_weight_bound[OF direction base])
 have signed: "int(rho*a-s*b)=int((rho-s)*a+s*(a-b))"
  using direction base bound by (simp add: of_nat_diff algebra_simps)
 show ?thesis by (rule of_nat_eq_iff[where 'a=int, THEN iffD1, OF signed])
qed

lemma crossing_maxMultiplicity_gt_a:
 fixes rho s a b e L q::nat
 assumes s: "0<s" and direction: "s<rho" and base: "b<a" and L: "0<L"
 and identity: "(rho-s)*e=(a-b)+(rho*a-s*b)*L" and bound: "e\<le>q*L"
 shows "a<q"
proof -
 have H: "0<a-b" using base by arith
 have multiplied: "(rho-s)*e\<le>(rho-s)*(q*L)" by (rule mult_le_mono2[OF bound])
 have product: "(rho-s)*e\<le>((rho-s)*q)*L" using multiplied by (simp add: mult.assoc)
 have strict: "(rho*a-s*b)*L<((rho-s)*q)*L" using product identity H by arith
 have weights: "rho*a-s*b<(rho-s)*q" using strict L by (simp add: mult_less_cancel2)
 have shape: "rho*a-s*b=(rho-s)*a+s*(a-b)" by (rule crossing_parameter_weight_identity[OF direction base])
 show ?thesis
 proof (rule ccontr)
  assume "\<not>a<q"
  then have "q\<le>a" by arith
  then have product: "(rho-s)*q\<le>(rho-s)*a" by (rule mult_le_mono2)
  show False using weights product shape by arith
 qed
qed

lemma crossing_exists_rootMultiplicity_gt_a:
 fixes rho s a b::nat and r f::"complex poly"
 assumes s: "0<s" and direction: "s<rho" and base: "b<a" and r0: "coeff r 0=1" and r: "0<degree r"
 and scalar: "[:of_nat rho- of_nat s:]*[:0,1:]*f*pderiv r-
 (([:of_nat a- of_nat b:]*f+[:of_nat rho* of_nat a- of_nat s* of_nat b:]*[:0,1:]*pderiv f+1)*r)=0"
 shows "\<exists>alpha. poly r alpha=0 \<and> a<rootMultiplicity alpha r \<and>
 (\<forall>beta. poly r beta=0 \<longrightarrow> rootMultiplicity beta r\<le>rootMultiplicity alpha r)"
proof -
 have facts: "0<degree f \<and> degree f<degree r \<and>
 (rho-s)*degree r=(a-b)+(rho*a-s*b)*degree f \<and>
 (\<forall>alpha. poly r alpha=0 \<longrightarrow> poly f alpha=0 \<and>
 alpha*poly(pderiv f)alpha*(of_nat(rho-s)* of_nat(rootMultiplicity alpha r)- of_nat(rho*a-s*b))=1)"
  by (rule crossing_general_scalar_facts[OF direction base r0 r scalar])
 obtain alpha where root: "poly r alpha=0" and maximal: "\<forall>beta. poly r beta=0 \<longrightarrow> rootMultiplicity beta r\<le>rootMultiplicity alpha r"
  using exists_max_rootMultiplicity[OF r] by blast
 have rnz: "r\<noteq>0" using r by auto
 have fnz: "f\<noteq>0" using facts by auto
 have roots: "\<And>beta. poly r beta=0 \<Longrightarrow> poly f beta=0" using facts by blast
 have multiplicity: "rootMultiplicity beta r\<le>rootMultiplicity alpha r" if "poly r beta=0" for beta
  by (rule mp[OF spec[where x=beta, OF maximal] that])
 have order: "degree r\<le>rootMultiplicity alpha r*degree f"
  by (rule degree_le_maxMultiplicity_mul_companionDegree[where q="rootMultiplicity alpha r", OF rnz fnz roots multiplicity])
 have L: "0<degree f" and identity: "(rho-s)*degree r=(a-b)+(rho*a-s*b)*degree f" using facts by blast+
 have large: "a<rootMultiplicity alpha r" by (rule crossing_maxMultiplicity_gt_a[OF s direction base L identity order])
 show ?thesis using root maximal large by blast
qed

lemma crossing_power_multiplicity_lt_termCount:
 fixes r::"complex poly"
 assumes r0: "coeff r 0=1" and root: "poly r alpha=0"
 shows "k*rootMultiplicity alpha r<termCount(r^k)"
proof -
 have r: "r\<noteq>0" using r0 by auto
 have alpha: "alpha\<noteq>0" using root r0 by (auto simp: poly_0_coeff_0)
 have divides: "([:0,1:]-[:alpha:])^(k*rootMultiplicity alpha r) dvd r^k"
 proof -
  have "([:-alpha,1:]^Polynomial.order alpha r)^k dvd r^k" by (rule dvd_power_same[OF Polynomial.order_1])
  then show ?thesis by (simp only: rootMultiplicity_eq_order[OF r] power_mult[symmetric] mult.commute; simp)
 qed
 show ?thesis by (rule pow_dvd_imp_lt_termCount[OF _ alpha divides]) (use r in simp)
qed

lemma crossing_six_parameter_arithmetic:
 fixes k a b q t::nat
 assumes k: "2\<le>k" and base: "b<a" and q: "a<q" and product: "k*q<t" and t: "t\<le>6"
 shows "k=2 \<and> a=1 \<and> b=0 \<and> q=2"
proof -
 have q2: "2\<le>q" using base q by arith
 have one: "2*q\<le>k*q" by (rule mult_le_mono1[OF k])
 have two: "k*2\<le>k*q" by (rule mult_le_mono2[OF q2])
 show ?thesis using one two product t k q2 base q by arith
qed

lemma crossing_mass_six_parameters_of_scalar:
 fixes rho s a b k::nat and r f::"complex poly"
 assumes s: "0<s" and direction: "s<rho" and base: "b<a" and k: "2\<le>k"
 and r0: "coeff r 0=1" and r: "0<degree r"
 and scalar: "[:of_nat rho- of_nat s:]*[:0,1:]*f*pderiv r-
 (([:of_nat a- of_nat b:]*f+[:of_nat rho* of_nat a- of_nat s* of_nat b:]*[:0,1:]*pderiv f+1)*r)=0"
 and terms: "termCount(r^k)\<le>6"
 shows "k=2 \<and> a=1 \<and> b=0 \<and> (\<exists>alpha. poly r alpha=0 \<and> rootMultiplicity alpha r=2)"
proof -
 obtain alpha where root: "poly r alpha=0" and large: "a<rootMultiplicity alpha r"
  using crossing_exists_rootMultiplicity_gt_a[OF s direction base r0 r scalar] by blast
 have product: "k*rootMultiplicity alpha r<termCount(r^k)" by (rule crossing_power_multiplicity_lt_termCount[OF r0 root])
 have parameters: "k=2 \<and> a=1 \<and> b=0 \<and> rootMultiplicity alpha r=2"
  by (rule crossing_six_parameter_arithmetic[OF k base large product terms])
 show ?thesis using parameters root by blast
qed

end
