theory Common_Power_Root
 imports "Bivariate_Prime_Multiplicity"
begin

lemma reduced_multiplicity_ratio:
 fixes B R p::"complex bivariate"
 assumes B: "B\<noteq>0" and R: "R\<noteq>0" and c: "c\<noteq>0"
 and power: "B^m=[:[:c:]:]*R^omega"
 and prime: "prime_elem p" and m: "0<m"
 and ratio: "omega*d=m*n"
 shows "n*multiplicity p R=d*multiplicity p B"
proof -
 have original: "m*multiplicity p B=omega*multiplicity p R"
   by (rule multiplicity_power_ratio[OF B R c power prime])
 have "m*(n*multiplicity p R)=m*(d*multiplicity p B)"
 proof -
   have "m*(n*multiplicity p R)=(m*n)*multiplicity p R" by (simp add: mult.assoc)
   also have "...=(omega*d)*multiplicity p R" by (simp only: ratio)
   also have "...=d*(omega*multiplicity p R)" by (simp add: mult_ac)
   also have "...=d*(m*multiplicity p B)" by (simp only: original[symmetric])
   also have "...=m*(d*multiplicity p B)" by (simp add: mult_ac)
   finally show ?thesis .
 qed
 then show ?thesis using m by simp
qed

lemma reduced_multiplicity_divides:
 fixes B R p::"complex bivariate"
 assumes B: "B\<noteq>0" and R: "R\<noteq>0" and c: "c\<noteq>0"
 and power: "B^m=[:[:c:]:]*R^omega"
 and prime: "prime_elem p" and m: "0<m"
 and ratio: "omega*d=m*n" and cop: "coprime d n"
 shows "d dvd multiplicity p R"
proof -
 have eq: "n*multiplicity p R=d*multiplicity p B"
   by (rule reduced_multiplicity_ratio[OF B R c power prime m ratio])
 have "d dvd multiplicity p R*n" using eq by (simp add: mult.commute)
 then show ?thesis using cop by (simp add: coprime_dvd_mult_left_iff)
qed

lemma bivariate_unit_is_scalar:
 fixes U::"complex bivariate"
 assumes "is_unit U"
 obtains c where "c\<noteq>0" "U=[:[:c:]:]"
 using assms that by (auto simp: is_unit_poly_iff dvd_field_iff)

lemma native_scalar_of_equal_normalizations:
 fixes B T::"complex bivariate"
 assumes B: "B\<noteq>0" and T: "T\<noteq>0" and equal: "normalize B=normalize T"
 shows "\<exists>nu::complex. nu\<noteq>0 \<and> B=[:[:nu:]:]*T"
proof -
 obtain b where b: "b\<noteq>0" "unit_factor B=[:[:b:]:]"
   by (rule bivariate_unit_is_scalar[where U="unit_factor B"]) (use B in auto)
 obtain t where t: "t\<noteq>0" "unit_factor T=[:[:t:]:]"
   by (rule bivariate_unit_is_scalar[where U="unit_factor T"]) (use T in auto)
 have Bs: "B=[:[:b:]:]*normalize T"
 proof -
   have "B=unit_factor B*normalize B" by simp
   then show ?thesis by (simp only: b(2) equal)
 qed
 have Ts: "T=[:[:t:]:]*normalize T"
 proof -
   have "T=unit_factor T*normalize T" by simp
   then show ?thesis by (simp only: t(2))
 qed
 have scalar: "([:[:b/t:]:]::complex bivariate)*[:[:t:]:]=[:[:b:]:]"
   using t by simp
 have shape: "B=[:[:b/t:]:]*T"
 proof -
   have "B=[:[:b:]:]*normalize T" by (rule Bs)
   also have "...=[:[:b/t:]:]*([:[:t:]:]*normalize T)"
     by (simp only: mult.assoc[symmetric] scalar)
   also have "...=[:[:b/t:]:]*T"
     by (rule arg_cong[OF Ts[symmetric]])
   finally show ?thesis .
 qed
 show ?thesis by (intro exI[of _ "b/t"]) (use b t shape in auto)
qed


lemma native_normalized_prime_product:
 fixes R::"complex bivariate"
 assumes R: "R\<noteq>0"
 shows "normalize(\<Prod>p\<in>prime_factors R. p^multiplicity p R)=normalize R"
proof -
 have factors: "(\<Prod>p\<in>prime_factors R. p^multiplicity p R)=prod_mset(prime_factorization R)"
 proof -
   have "prod_mset(prime_factorization R)=
     (\<Prod>p\<in>prime_factors R. p^count(prime_factorization R) p)"
     by (subst prod_mset_multiplicity) simp_all
   also have "...=(\<Prod>p\<in>prime_factors R. p^multiplicity p R)"
   proof (rule prod.cong)
     show "prime_factors R=prime_factors R" by simp
     fix p assume p: "p\<in>prime_factors R"
     have prime: "prime p" by (rule in_prime_factors_imp_prime[OF p])
     show "p^count(prime_factorization R) p=p^multiplicity p R"
       by (simp only: count_prime_factorization_prime[OF prime])
   qed
   finally show ?thesis by simp
 qed
 show ?thesis by (simp only: factors prod_mset_prime_factorization_weak[OF R])
qed

lemma bivariate_common_root_of_coprime_ratio:
 fixes B R::"complex bivariate"
 assumes B: "B\<noteq>0" and R: "R\<noteq>0" and c: "c\<noteq>0"
 and ratio: "omega*d=m*n" and m: "0<m" and omega: "0<omega"
 and n: "0<n" and d: "0<d" and cop: "coprime d n"
 and power: "B^m=[:[:c:]:]*R^omega"
 shows "\<exists>S nu mu. S\<noteq>0 \<and> nu\<noteq>0 \<and> mu\<noteq>0 \<and>
   R=[:[:nu:]:]*S^d \<and> B=[:[:mu:]:]*S^n"
proof -
 let ?A="prime_factors R"
 let ?S="\<Prod>p\<in>?A. p^(multiplicity p R div d)"
 have multiplicities: "n*multiplicity p R=d*multiplicity p B" if "prime p" for p
   by (rule reduced_multiplicity_ratio[OF B R c power prime_imp_prime_elem[OF that] m ratio])
 have divisible: "d dvd multiplicity p R" if "prime p" for p
   by (rule reduced_multiplicity_divides[OF B R c power prime_imp_prime_elem[OF that] m ratio cop])
 have factors: "prime_factors B=?A"
   unfolding prime_factors_multiplicity
 proof (rule Collect_cong)
   fix p
   show "(prime p \<and> 0<multiplicity p B)=(prime p \<and> 0<multiplicity p R)"
   proof (cases "prime p")
     case True
     have eq: "n*multiplicity p R=d*multiplicity p B" by (rule multiplicities[OF True])
     have zero_eq: "(multiplicity p R=0)=(multiplicity p B=0)"
     proof -
       have "(n*multiplicity p R=0)=(d*multiplicity p B=0)" by (simp only: eq)
       then show ?thesis using n d by simp
     qed
     show ?thesis using True zero_eq
       by (cases "multiplicity p R=0"; cases "multiplicity p B=0") auto
   next
     case False then show ?thesis by simp
   qed
 qed
 have exponents_d: "(multiplicity p R div d)*d=multiplicity p R" if "p\<in>?A" for p
   using divisible[OF in_prime_factors_imp_prime[OF that]] by simp
 have exponents_n: "(multiplicity p R div d)*n=multiplicity p B" if "p\<in>?A" for p
 proof -
   have eq: "n*multiplicity p R=d*multiplicity p B"
     by (rule multiplicities[OF in_prime_factors_imp_prime[OF that]])
   have "d*((multiplicity p R div d)*n)=n*((multiplicity p R div d)*d)" by (simp only: mult_ac)
   also have "...=n*multiplicity p R" by (simp only: exponents_d[OF that])
   also have "...=d*multiplicity p B" by (rule eq)
   finally have products: "d*((multiplicity p R div d)*n)=d*multiplicity p B" .
   have dne: "d\<noteq>0" using d by arith
   show ?thesis using products by (simp only: mult_left_cancel[OF dne])
 qed
 have root_d: "normalize(?S^d)=normalize R"
 proof -
   have "?S^d=(\<Prod>p\<in>?A. p^multiplicity p R)"
     by (simp only: prod_power_distrib power_mult[symmetric])
       (rule prod.cong, simp, simp add: exponents_d)
   then show ?thesis by (simp only: native_normalized_prime_product[OF R])
 qed
 have root_n: "normalize(?S^n)=normalize B"
 proof -
   have "?S^n=(\<Prod>p\<in>?A. p^multiplicity p B)"
     by (simp only: prod_power_distrib power_mult[symmetric])
       (rule prod.cong, simp, simp add: exponents_n)
   then show ?thesis using native_normalized_prime_product[OF B] factors by simp
 qed
 have Sne: "?S\<noteq>0" using root_d R d by auto
 have Sd: "?S^d\<noteq>0" and Sn: "?S^n\<noteq>0" using Sne by simp_all
 obtain nu where nu: "nu\<noteq>0" and Rshape: "R=[:[:nu:]:]*?S^d"
   using native_scalar_of_equal_normalizations[OF R Sd root_d[symmetric]] by auto
 obtain mu where mu: "mu\<noteq>0" and Bshape: "B=[:[:mu:]:]*?S^n"
   using native_scalar_of_equal_normalizations[OF B Sn root_n[symmetric]] by auto
 show ?thesis by (intro exI[of _ ?S] exI[of _ nu] exI[of _ mu])
   (use Sne nu mu Rshape Bshape in blast)
qed

definition PrimitiveFactorProfile::"complex bivariate\<Rightarrow>bool" where
 "PrimitiveFactorProfile R \<longleftrightarrow> (\<forall>d::nat. 1<d \<longrightarrow> (\<exists>p. prime_elem p \<and> \<not>d dvd multiplicity p R))"

lemma native_scalar_power_of_multiplicity_divisibility:
 fixes R::"complex bivariate"
 assumes R: "R\<noteq>0"
 and divides: "\<And>p. prime_elem p \<Longrightarrow> d dvd multiplicity p R"
 shows "\<exists>nu S. nu\<noteq>0 \<and> R=[:[:nu:]:]*S^d"
proof -
 let ?S="\<Prod>p\<in>prime_factors R. p^(multiplicity p R div d)"
 have exponent: "(multiplicity p R div d)*d=multiplicity p R" if "p\<in>prime_factors R" for p
   using divides[OF prime_imp_prime_elem[OF in_prime_factors_imp_prime[OF that]]] by simp
 have root: "normalize(?S^d)=normalize R"
 proof -
   have "?S^d=(\<Prod>p\<in>prime_factors R. p^multiplicity p R)"
     by (simp only: prod_power_distrib power_mult[symmetric])
       (rule prod.cong, simp, simp add: exponent)
   then show ?thesis by (simp only: native_normalized_prime_product[OF R])
 qed
 have power_ne: "?S^d\<noteq>0" using root R by auto
 obtain nu where nu: "nu\<noteq>0" and shape: "R=[:[:nu:]:]*?S^d"
   using native_scalar_of_equal_normalizations[OF R power_ne root[symmetric]] by auto
 show ?thesis by (intro exI[of _ nu] exI[of _ ?S]) (use nu shape in blast)
qed

lemma primitive_factor_profile_of_no_proper_power:
 fixes R::"complex bivariate"
 assumes R: "R\<noteq>0"
 and no_power: "\<And>d S mu. 1<d \<Longrightarrow> mu\<noteq>0 \<Longrightarrow> R\<noteq>[:[:mu:]:]*S^d"
 shows "PrimitiveFactorProfile R"
 unfolding PrimitiveFactorProfile_def
proof (intro allI impI)
 fix d::nat assume d: "1<d"
 show "\<exists>p. prime_elem p \<and> \<not>d dvd multiplicity p R"
 proof (rule ccontr)
   assume absent: "\<not>(\<exists>p. prime_elem p \<and> \<not>d dvd multiplicity p R)"
   have divides: "d dvd multiplicity p R" if "prime_elem p" for p using absent that by blast
   obtain mu S where mu: "mu\<noteq>0" and shape: "R=[:[:mu:]:]*S^d"
     using native_scalar_power_of_multiplicity_divisibility[OF R divides] by auto
   show False using no_power[OF d mu] shape by contradiction
 qed
qed

lemma primitive_factor_profile_iff_no_proper_power:
 fixes R::"complex bivariate"
 assumes R: "R\<noteq>0"
 shows "PrimitiveFactorProfile R \<longleftrightarrow>
 (\<forall>d::nat. 1<d \<longrightarrow> (\<forall>S mu. mu\<noteq>0 \<longrightarrow> R\<noteq>[:[:mu:]:]*S^d))"
proof
 assume profile: "PrimitiveFactorProfile R"
 show "\<forall>d::nat. 1<d \<longrightarrow> (\<forall>S mu. mu\<noteq>0 \<longrightarrow> R\<noteq>[:[:mu:]:]*S^d)"
 proof (intro allI impI notI)
   fix d S mu assume d: "1<d" and mu: "mu\<noteq>0" and shape: "R=[:[:mu:]:]*S^d"
   obtain p where prime: "prime_elem p" and not_divides: "\<not>d dvd multiplicity p R"
     using profile d unfolding PrimitiveFactorProfile_def by blast
   show False using multiplicity_dvd_of_scalar_proper_power[OF R d mu shape prime] not_divides by contradiction
 qed
next
 assume no_power: "\<forall>d::nat. 1<d \<longrightarrow> (\<forall>S mu. mu\<noteq>0 \<longrightarrow> R\<noteq>[:[:mu:]:]*S^d)"
 show "PrimitiveFactorProfile R" by (rule primitive_factor_profile_of_no_proper_power[OF R]) (use no_power in blast)
qed

lemma exponent_divides_of_primitive_factor_profile:
 fixes B R::"complex bivariate"
 assumes m: "0<m" and B: "B\<noteq>0" and R: "R\<noteq>0" and c: "c\<noteq>0"
 and power: "B^m=[:[:c:]:]*R^omega" and profile: "PrimitiveFactorProfile R"
 shows "m dvd omega"
proof -
 let ?g="gcd m omega" let ?a="m div ?g" let ?b="omega div ?g"
 have g: "0<?g" using m by simp
 have ma: "?g*?a=m" by (simp add: dvd_mult_div_cancel gcd_dvd1)
 have ob: "?g*?b=omega" by (simp add: dvd_mult_div_cancel gcd_dvd2)
 have a: "0<?a" using ma m by (cases "?a=0") auto
 have cop: "coprime ?a ?b" by (rule div_gcd_coprime) (use m in auto)
 have ratio: "omega*?a=m*?b"
 proof -
   have "?g*(omega*?a)=omega*(?g*?a)" by (simp add: mult_ac)
   also have "...=omega*m" by (simp only: ma)
   also have "...=m*(?g*?b)" by (simp only: ob; simp add: mult.commute)
   also have "...=?g*(m*?b)" by (simp add: mult_ac)
   finally have products: "?g*(omega*?a)=?g*(m*?b)" .
   have gne: "?g\<noteq>0" using g by arith
   show ?thesis using products by (simp only: mult_left_cancel[OF gne])
 qed
 have small: "\<not>1<?a"
 proof
   assume proper: "1<?a"
   obtain p where prime: "prime_elem p" and not_divides: "\<not>?a dvd multiplicity p R"
     using profile proper unfolding PrimitiveFactorProfile_def by blast
   have "?a dvd multiplicity p R"
     by (rule reduced_multiplicity_divides[OF B R c power prime m ratio cop])
   then show False using not_divides by contradiction
 qed
 have one: "?a=1" using a small by arith
 have "m=?g" using ma by (simp add: one)
 then show ?thesis using gcd_dvd2[of m omega] by simp
qed


lemma scalar_power_of_divisible_exponents:
 fixes B R::"complex bivariate"
 assumes m: "0<m" and c: "c\<noteq>0" and power: "B^m=[:[:c:]:]*R^omega"
 and divides: "m dvd omega"
 shows "\<exists>nu::complex. \<exists>k::nat. nu\<noteq>0 \<and> omega=m*k \<and> B=[:[:nu:]:]*R^k"
proof -
 obtain k where k: "omega=m*k" using divides by (auto simp: dvd_def)
 have reordered: "R^omega=(R^k)^m" by (simp only: k mult.commute[of m k] power_mult)
 have powers: "B^m=[:[:c:]:]*(R^k)^m" using power by (simp only: reordered)
 show ?thesis
 proof (cases "B=0")
   case True
   have Bpower: "B^m=0" using True m by (cases m) auto
   have scalar_ne: "([:[:c:]:]::complex bivariate)\<noteq>0" using c by simp
   have zero_product: "[:[:c:]:]*(R^k)^m=0" using powers Bpower by simp
   have zero_power: "(R^k)^m=0" using zero_product scalar_ne by (simp only: mult_eq_0_iff; blast)
   have Tzero: "R^k=0" using zero_power by (simp only: power_eq_0_iff; blast)
   show ?thesis by (intro exI[of _ "1::complex"] exI[of _ k]) (simp add: True Tzero k)
 next
   case False
   have T: "R^k\<noteq>0"
   proof
     assume zero: "R^k=0"
     have term_power_zero: "(R^k)^m=0" using zero m by (cases m) auto
     have Bpower: "B^m=0" using powers term_power_zero by simp
     have Bzero: "B=0" using Bpower by (simp only: power_eq_0_iff; blast)
     show False using False Bzero by contradiction
   qed
   have normalized: "normalize B=normalize(R^k)"
   proof (rule multiplicity_eq_imp_eq[where x=B and y="R^k", OF False T])
     fix p::"complex bivariate" assume prime: "prime p"
     have equality: "m*multiplicity p B=m*multiplicity p (R^k)"
       by (rule multiplicity_power_ratio[OF False T c powers prime_imp_prime_elem[OF prime]])
     show "multiplicity p B=multiplicity p (R^k)" using equality m by simp
   qed
   obtain nu where nu: "nu\<noteq>0" and shape: "B=[:[:nu:]:]*R^k"
     using native_scalar_of_equal_normalizations[OF False T normalized] by auto
   show ?thesis by (intro exI[of _ nu] exI[of _ k]) (use nu shape k in blast)
 qed
qed

lemma scalar_power_of_primitive_factor_profile:
 fixes B R::"complex bivariate"
 assumes m: "0<m" and B: "B\<noteq>0" and R: "R\<noteq>0" and c: "c\<noteq>0"
 and power: "B^m=[:[:c:]:]*R^omega" and profile: "PrimitiveFactorProfile R"
 shows "\<exists>nu::complex. \<exists>k::nat. nu\<noteq>0 \<and> omega=m*k \<and> B=[:[:nu:]:]*R^k"
 by (rule scalar_power_of_divisible_exponents[OF m c power exponent_divides_of_primitive_factor_profile[OF m B R c power profile]])

lemma scalar_power_of_no_proper_power:
 fixes B R::"complex bivariate"
 assumes m: "0<m" and B: "B\<noteq>0" and R: "R\<noteq>0" and c: "c\<noteq>0"
 and power: "B^m=[:[:c:]:]*R^omega"
 and no_power: "\<And>d S mu. 1<d \<Longrightarrow> mu\<noteq>0 \<Longrightarrow> R\<noteq>[:[:mu:]:]*S^d"
 shows "\<exists>nu::complex. \<exists>k::nat. nu\<noteq>0 \<and> omega=m*k \<and> B=[:[:nu:]:]*R^k"
 by (rule scalar_power_of_primitive_factor_profile[OF m B R c power primitive_factor_profile_of_no_proper_power[OF R no_power]])

end
