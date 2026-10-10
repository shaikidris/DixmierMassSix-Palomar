theory General_Root_Degree
 imports "General_Companion"
   "Complex_Root_Budget"
begin

lemma degree_le_maxMultiplicity_mul_companionDegree:
 fixes r f::"complex poly" and q::nat
 assumes r: "r\<noteq>0" and f: "f\<noteq>0"
 and roots: "\<And>a. poly r a=0 \<Longrightarrow> poly f a=0"
 and multiplicity: "\<And>a. poly r a=0 \<Longrightarrow> rootMultiplicity a r\<le>q"
 shows "degree r\<le>q*degree f"
proof -
 let ?S="set_mset(proots r)"
 let ?T="set_mset(proots f)"
 have total: "degree r=(\<Sum>a\<in>?S. rootMultiplicity a r)"
   using size_proots_complex[of r]
   by (simp only: size_multiset_overloaded_def Multiset.size_multiset_def wcount_def rootMultiplicity_eq_count_proots; simp)
 have sum: "(\<Sum>a\<in>?S. rootMultiplicity a r)\<le>(\<Sum>a\<in>?S. q)"
   by (rule sum_mono) (use multiplicity r in auto)
 have subset: "?S\<subseteq>?T" using roots r f by auto
 have card: "card ?S\<le>card ?T" by (rule card_mono) (simp, rule subset)
 have fcard: "card ?T\<le>degree f" by (simp only: set_count_proots[OF f]; rule card_poly_roots_bound[OF f])
 have size: "card ?S\<le>degree f" by (rule order_trans[OF card fcard])
 have "degree r\<le>card ?S*q" using total sum by simp
 also have "...\<le>degree f*q" by (rule mult_le_mono1[OF size])
 also have "...=q*degree f" by (rule mult.commute)
 finally show ?thesis .
qed

lemma substituted_companion_root_count:
 fixes S r f::"complex poly" and rho::nat
 assumes rho: "0<rho" and S: "S\<noteq>0" and f: "f\<noteq>0"
 and roots: "\<And>a. poly r a=0 \<Longrightarrow> poly f a=0"
 and face: "\<And>z. poly S z=0 \<Longrightarrow> z=0 \<or> poly r (z^rho)=0"
 shows "card(set_mset(proots S))\<le>1+rho*degree f"
proof -
 let ?T="[:0,1:]*pcompose f ([:0,1:]^rho)"
 have powerdegree: "0<degree ([:0,1:]^rho::complex poly)" using rho by (simp add: degree_power_eq)
 have compnz: "pcompose f ([:0,1:]^rho)\<noteq>0" using f by (simp only: pcompose_eq_0_iff[OF powerdegree] not_False_eq_True)
 have Tnz: "?T\<noteq>0" using compnz by simp
 have subset: "set_mset(proots S)\<subseteq>set_mset(proots ?T)"
 proof (intro subsetI)
   fix z assume z: "z\<in>set_mset(proots S)"
   have Sz: "poly S z=0" using z S by simp
   have Tz: "poly ?T z=0" using face[OF Sz] roots by (auto simp: poly_pcompose)
   show "z\<in>set_mset(proots ?T)" using Tz Tnz by simp
 qed
 have card: "card(set_mset(proots S))\<le>card(set_mset(proots ?T))" by (rule card_mono) (simp, rule subset)
 have rootsbound: "card(set_mset(proots ?T))\<le>degree ?T"
   by (simp only: set_count_proots[OF Tnz]; rule card_poly_roots_bound[OF Tnz])
 have degree: "degree ?T\<le>1+rho*degree f"
   using degree_mult_le[of "[:0,1:]::complex poly" "pcompose f ([:0,1:]^rho)"]
     degree_pcompose_le[of f "[:0,1:]^rho"]
   by (simp add: degree_power_eq mult.commute; arith)
 show ?thesis by (rule order_trans[OF card order_trans[OF rootsbound degree]])
qed

lemma GenComp_substituted_companion_root_count:
 fixes r f S::"complex poly" and delta H W rho::nat
 assumes h: "GenComp delta H W r f" and delta: "0<delta" and r0: "poly r 0=1" and f: "f\<noteq>0"
 and rho: "0<rho" and S: "S\<noteq>0"
 and face: "\<And>z. poly S z=0 \<Longrightarrow> z=0 \<or> poly r (z^rho)=0"
 shows "card(set_mset(proots S))\<le>1+rho*degree f"
 by (rule substituted_companion_root_count[OF rho S f _ face])
   (rule GenComp_isRoot_f[OF h delta r0], assumption)

lemma GenComp_powered_face_root_count:
 fixes r f S::"complex poly" and delta H W rho b k::nat and nu::complex
 assumes h: "GenComp delta H W r f" and delta: "0<delta" and r0: "poly r 0=1" and f: "f\<noteq>0"
 and rho: "0<rho" and S: "S\<noteq>0"
 and shape: "S=[:nu:]*[:0,1:]^b*(pcompose r ([:0,1:]^rho))^k"
 shows "card(set_mset(proots S))\<le>1+rho*degree f"
proof (rule GenComp_substituted_companion_root_count[OF h delta r0 f rho S])
 fix z assume Sz: "poly S z=0"
 have nuz: "nu\<noteq>0" using S shape by auto
 have eq: "nu*z^b*(poly r (z^rho))^k=0" using Sz by (simp add: shape poly_pcompose)
 show "z=0 \<or> poly r (z^rho)=0" using eq nuz by auto
qed

lemma exists_max_rootMultiplicity:
 fixes r::"complex poly"
 assumes positive: "0<degree r"
 shows "\<exists>a. poly r a=0 \<and> (\<forall>b. poly r b=0 \<longrightarrow> rootMultiplicity b r\<le>rootMultiplicity a r)"
proof -
 have rnz: "r\<noteq>0" using positive by auto
 obtain a where root: "poly r a=0" and max: "rootMultiplicity a r=max_root_mult r"
   using native_complex_polynomial_max_root_exists[OF positive] by blast
 have bound: "rootMultiplicity b r\<le>max_root_mult r" if "poly r b=0" for b
 proof -
   let ?W="insert 0 ((\<lambda>x. count(proots r)x)`set_mset(proots r))"
   have finite_weights: "finite ?W" by simp
   have membership: "b\<in>set_mset(proots r)" using that rnz by simp
   have member_weight: "count(proots r)b\<in>?W" using membership by blast
   have inequality: "count(proots r)b\<le>Max ?W" by (rule Max_ge[OF finite_weights member_weight])
   show ?thesis by (simp only: rootMultiplicity_eq_count_proots max_root_mult_def; rule inequality)
 qed
 show ?thesis
 proof (rule exI[where x=a], intro conjI)
   show "poly r a=0" by (rule root)
   show "\<forall>b. poly r b=0 \<longrightarrow> rootMultiplicity b r\<le>rootMultiplicity a r"
   proof (intro allI impI)
     fix b assume root_b: "poly r b=0"
     show "rootMultiplicity b r\<le>rootMultiplicity a r"
       by (simp only: max; rule bound[OF root_b])
   qed
 qed
qed

lemma GenComp_exists_full_multiplicity_root:
 fixes r f::"complex poly" and delta H W::nat
 assumes h: "GenComp delta H W r f" and delta: "0<delta" and r0: "poly r 0=1"
 and r: "0<degree r" and f: "degree f=1"
 shows "\<exists>a. a\<noteq>0 \<and> poly r a=0 \<and> rootMultiplicity a r=degree r"
proof -
 have rnz: "r\<noteq>0" using r by auto
 have fnz: "f\<noteq>0" using f by auto
 obtain a where a: "poly r a=0" and maximal: "\<forall>b. poly r b=0 \<longrightarrow> rootMultiplicity b r\<le>rootMultiplicity a r"
   using exists_max_rootMultiplicity[OF r] by blast
 have containment: "poly f b=0" if "poly r b=0" for b by (rule GenComp_isRoot_f[OF h delta r0 that])
 have maximum_bound: "rootMultiplicity b r\<le>rootMultiplicity a r" if root_b: "poly r b=0" for b
   using maximal root_b by blast
 have bound: "degree r\<le>rootMultiplicity a r*degree f"
   by (rule degree_le_maxMultiplicity_mul_companionDegree[OF rnz fnz containment maximum_bound])
 have lower: "degree r\<le>rootMultiplicity a r" using bound f by simp
 have upper: "rootMultiplicity a r\<le>degree r" by (simp only: rootMultiplicity_eq_order[OF rnz]; rule order_degree[OF rnz])
 have anz: "a\<noteq>0" using a r0 by auto
 have equality: "rootMultiplicity a r=degree r" by (rule order_antisym[OF upper lower])
 show ?thesis by (rule exI[where x=a], intro conjI) (rule anz, rule a, rule equality)
qed

end
