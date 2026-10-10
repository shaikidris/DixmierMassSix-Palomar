theory Fourier_Generation
 imports "Fourier_Grade_Mass"
   "Weyl_Statement_Interfaces"
begin

declare id_def [simp del]

definition weyl_alg_equiv_contract :: "('k::field poly_operator \<Rightarrow> 'k poly_operator) \<Rightarrow> bool" where
 "weyl_alg_equiv_contract E \<longleftrightarrow>
  E\<in>ring_iso weyl_operator_ring weyl_operator_ring \<and> (\<forall>c. E(op_scalar c)=op_scalar c)"

locale fourier_equivalence_transport =
 fixes E :: "'k::field poly_operator \<Rightarrow> 'k poly_operator"
 assumes equivalence: "weyl_alg_equiv_contract E"
begin
lemma hom: "E\<in>ring_hom (weyl_operator_ring :: 'k poly_operator ring) weyl_operator_ring"
 using equivalence by (simp only: weyl_alg_equiv_contract_def ring_iso_def mem_Collect_eq; blast)
lemma bij: "bij_betw E (weyl_algebra :: 'k poly_operator set) weyl_algebra"
 using equivalence by (simp only: weyl_alg_equiv_contract_def ring_iso_def mem_Collect_eq weyl_operator_ring_simps; blast)
lemma map_scalar: "E(op_scalar c)=op_scalar c"
 using equivalence by (auto simp only: weyl_alg_equiv_contract_def)
lemma map_closed: "T\<in>weyl_algebra \<Longrightarrow> E T\<in>weyl_algebra"
 using ring_hom_closed[OF hom] by (simp only: weyl_operator_ring_simps)
lemma map_add:
 "T\<in>weyl_algebra \<Longrightarrow> U\<in>weyl_algebra \<Longrightarrow> E(T+U)=E T+E U"
 using ring_hom_add[OF hom] by (simp only: weyl_operator_ring_simps)
lemma map_comp:
 "T\<in>weyl_algebra \<Longrightarrow> U\<in>weyl_algebra \<Longrightarrow> E(op_comp T U)=op_comp (E T) (E U)"
 using ring_hom_mult[OF hom] by (simp only: weyl_operator_ring_simps)
lemma map_zero: "E 0=0" using map_scalar[of 0] by (simp only: free_op_scalar_zero)
lemma map_neg:
 assumes "T\<in>weyl_algebra"
 shows "E(-T)=-E T"
proof -
 have "E T+E(-T)=0" using map_add[OF assms fourier_weyl_neg[OF assms]]
   by (simp only: add.right_inverse map_zero)
 then show ?thesis by (metis add_eq_0_iff)
qed
lemma map_diff:
 assumes "T\<in>weyl_algebra" "U\<in>weyl_algebra"
 shows "E(T-U)=E T-E U"
 using map_add[OF assms(1) fourier_weyl_neg[OF assms(2)]]
 by (simp only: diff_conv_add_uminus map_neg[OF assms(2)])
lemma generated_image:
 fixes P Q :: "'k poly_operator"
 assumes p: "P\<in>weyl_algebra" and q: "Q\<in>weyl_algebra" and t: "T\<in>op_adjoin {P,Q}"
 shows "E T\<in>op_adjoin {E P,E Q}"
proof -
 have sub: "op_adjoin {P,Q}\<subseteq>weyl_algebra"
   by (rule weyl_nested_adjoin) (use p q in auto)
 show ?thesis using t
 proof (induction rule: op_adjoin.induct)
  case (generator U)
  then show ?case by (auto intro: op_adjoin.generator)
 next
  case (scalar c)
  show ?case by (simp only: map_scalar) (rule op_adjoin.scalar)
 next
  case (add U V)
  have u: "U\<in>weyl_algebra" and v: "V\<in>weyl_algebra" using sub add.hyps by blast+
  show ?case by (simp only: map_add[OF u v]) (rule op_adjoin.add[OF add.IH])
 next
  case (diff U V)
  have u: "U\<in>weyl_algebra" and v: "V\<in>weyl_algebra" using sub diff.hyps by blast+
  show ?case by (simp only: map_diff[OF u v]) (rule op_adjoin.diff[OF diff.IH])
 next
  case (comp U V)
  have u: "U\<in>weyl_algebra" and v: "V\<in>weyl_algebra" using sub comp.hyps by blast+
  show ?case by (simp only: map_comp[OF u v]) (rule op_adjoin.comp[OF comp.IH])
 qed
qed
end

lemma adjoin_pair_eq_top_of_algEquiv:
 fixes E :: "'k::field poly_operator \<Rightarrow> 'k poly_operator" and P Q :: "'k poly_operator"
 assumes eqv: "weyl_alg_equiv_contract E" and p: "P\<in>weyl_algebra" and q: "Q\<in>weyl_algebra"
   and gen: "op_adjoin {P,Q}=weyl_algebra"
 shows "op_adjoin {E P,E Q}=weyl_algebra"
proof -
 interpret H: fourier_equivalence_transport E by (rule fourier_equivalence_transport.intro[OF eqv])
 have sub: "op_adjoin {E P,E Q}\<subseteq>weyl_algebra"
   by (rule weyl_nested_adjoin) (use H.map_closed[OF p] H.map_closed[OF q] in auto)
 have reverse: "weyl_algebra\<subseteq>op_adjoin {E P,E Q}"
 proof
  fix U :: "'k poly_operator"
  assume u: "U\<in>weyl_algebra"
  have image: "E ` weyl_algebra=weyl_algebra" using H.bij by (simp only: bij_betw_def; blast)
  have uim: "U\<in>E ` (weyl_algebra :: 'k poly_operator set)"
    using u by (simp only: image)
  obtain T where t: "T\<in>weyl_algebra" and et: "E T=U"
    using uim by (elim imageE; blast)
  have tg: "T\<in>op_adjoin {P,Q}" using t by (simp only: gen)
  show "U\<in>op_adjoin {E P,E Q}" using H.generated_image[OF p q tg] et by simp
 qed
 show ?thesis by (rule antisym[OF sub reverse])
qed
lemma canonical_fourier_equiv_contract:
 "weyl_alg_equiv_contract (fourier_alg_hom :: 'k::field_char_0 poly_operator \<Rightarrow> 'k poly_operator)"
 using fourier_alg_equiv_ring_iso[where 'k='k, unfolded fourier_alg_equiv_def] fourier_alg_hom_scalar
 by (auto simp only: weyl_alg_equiv_contract_def)
lemma adjoin_fourier_eq_top_iff:
 fixes P Q :: "'k::field_char_0 poly_operator"
 assumes p: "P\<in>weyl_algebra" and q: "Q\<in>weyl_algebra"
 shows "op_adjoin {fourier_alg_hom P,fourier_alg_hom Q}=weyl_algebra \<longleftrightarrow>
   op_adjoin {P,Q}=weyl_algebra"
proof
 assume h: "op_adjoin {fourier_alg_hom P,fourier_alg_hom Q}=weyl_algebra"
 note h2 = adjoin_pair_eq_top_of_algEquiv[OF canonical_fourier_equiv_contract
   fourier_alg_hom_closed[OF p] fourier_alg_hom_closed[OF q] h]
 note h3 = adjoin_pair_eq_top_of_algEquiv[OF canonical_fourier_equiv_contract
   fourier_alg_hom_closed[OF fourier_alg_hom_closed[OF p]]
   fourier_alg_hom_closed[OF fourier_alg_hom_closed[OF q]] h2]
 note h4 = adjoin_pair_eq_top_of_algEquiv[OF canonical_fourier_equiv_contract
   fourier_alg_hom_closed[OF fourier_alg_hom_closed[OF fourier_alg_hom_closed[OF p]]]
   fourier_alg_hom_closed[OF fourier_alg_hom_closed[OF fourier_alg_hom_closed[OF q]]] h3]
 show "op_adjoin {P,Q}=weyl_algebra" using h4
   by (simp only: fourierAlgHom_fourth[OF p] fourierAlgHom_fourth[OF q])
next
 assume h: "op_adjoin {P,Q}=weyl_algebra"
 show "op_adjoin {fourier_alg_hom P,fourier_alg_hom Q}=weyl_algebra"
   by (rule adjoin_pair_eq_top_of_algEquiv[OF canonical_fourier_equiv_contract p q h])
qed
lemma isCounterexamplePair_fourier:
 fixes P Q :: "complex poly_operator"
 assumes "is_counterexample_pair P Q"
 shows "is_counterexample_pair (fourier_alg_hom P) (fourier_alg_hom Q)"
proof -
 have p: "P\<in>weyl_algebra" and q: "Q\<in>weyl_algebra" and comm: "op_comp Q P-op_comp P Q=id"
   and non: "op_adjoin {P,Q}\<noteq>weyl_algebra" using assms by (auto simp only: is_counterexample_pair_def)
 have mapped: "op_comp (fourier_alg_hom Q) (fourier_alg_hom P) -
    op_comp (fourier_alg_hom P) (fourier_alg_hom Q)=id"
 proof -
  have "fourier_alg_hom (op_comp Q P-op_comp P Q)=fourier_alg_hom id" using comm by simp
  then show ?thesis by (simp only: fourier_alg_hom_diff[OF fourier_weyl_comp[OF q p] fourier_weyl_comp[OF p q]]
    fourier_alg_hom_comp[OF q p] fourier_alg_hom_comp[OF p q] fourier_alg_hom_id)
 qed
 have nongeneration: "op_adjoin {fourier_alg_hom P,fourier_alg_hom Q}\<noteq>weyl_algebra"
   using non adjoin_fourier_eq_top_iff[OF p q] by blast
 show ?thesis using fourier_alg_hom_closed[OF p] fourier_alg_hom_closed[OF q] mapped nongeneration
   by (simp only: is_counterexample_pair_def simp_thms)
qed
lemma positive_weight_sum_of_crossing_range:
 fixes rho sigma :: int
 assumes "-rho<sigma"
 shows "0<rho+sigma"
 using assms by linarith

end
