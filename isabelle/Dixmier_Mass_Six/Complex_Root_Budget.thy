theory Complex_Root_Budget
 imports "Weyl_Statement_Interfaces"
   "Root_Multiplicity_Adapter"
   "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
begin

lemma complex_polynomial_companion_root_budget:
 fixes p::"complex poly"
 assumes bound: "card(set_mset(proots p))\<le>L"
 shows "degree p\<le>L*max_root_mult p"
proof -
 have counts: "count(proots p) a\<le>max_root_mult p" if "a\<in>set_mset(proots p)" for a
   unfolding max_root_mult_def
   by (rule Max_ge) (use that in auto)
 have total: "degree p=(\<Sum>a\<in>set_mset(proots p). count(proots p) a)"
   using size_proots_complex[of p]
   by (simp only: size_multiset_overloaded_def Multiset.size_multiset_def wcount_def; simp)
 have "degree p\<le>(\<Sum>a\<in>set_mset(proots p). max_root_mult p)"
   unfolding total by (rule sum_mono) (use counts in blast)
 also have "...=card(set_mset(proots p))*max_root_mult p" by simp
 also have "...\<le>L*max_root_mult p" by (rule mult_le_mono1[OF bound])
 finally show ?thesis .
qed

lemma native_complex_polynomial_max_root_exists:
 fixes p::"complex poly"
 assumes positive: "0<degree p"
 shows "\<exists>c. poly p c=0 \<and> rootMultiplicity c p=max_root_mult p"
proof -
 let ?R="set_mset(proots p)"
 let ?W="(\<lambda>c. count(proots p)c)`?R"
 have nonzero: "p\<noteq>0" using positive by auto
 have roots: "?R\<noteq>{}"
 proof
   assume empty: "?R={}"
   have proots_empty: "proots p={#}" using empty by simp
   have size: "size(proots p)=degree p" by (rule size_proots_complex)
   have "degree p=0" using size by (simp only: proots_empty size_empty)
   then show False using positive by arith
 qed
 have fin: "finite ?W" by simp
 have weights: "?W\<noteq>{}" using roots by simp
 have member: "Max ?W\<in>?W" by (rule Max_in[OF fin weights])
 obtain c where c: "c\<in>?R" and maximum: "Max ?W=count(proots p)c" using member by auto
 have max: "max_root_mult p=count(proots p)c"
   by (simp add: max_root_mult_def Max_insert[OF fin weights] maximum)
 have root: "poly p c=0" using c nonzero by simp
 show ?thesis using root max by (auto simp: rootMultiplicity_eq_count_proots)
qed

end
