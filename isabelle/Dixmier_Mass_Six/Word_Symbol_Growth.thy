theory Word_Symbol_Growth
  imports "Exact_Pair_Word_Independence"
    "Signed_Coordinate_Bounds"
begin

lemma exact_word_carrier:
  assumes "P\<in>weyl_algebra" "Q\<in>weyl_algebra"
  shows "op_comp (P^^i) (Q^^j)\<in>weyl_algebra"
  using assms unfolding weyl_algebra_def by (intro op_adjoin.comp op_adjoin_power)

lemma exact_pair_word_symbols_coefficients_zero:
  fixes P Q :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and exact: "op_comp Q P-op_comp P Q=id"
    and finite: "finite S"
    and relation: "(\<Sum>d\<in>S. smult [:c d:] (pbw_symbol (op_comp (P^^fst d) (Q^^snd d))))=0"
    and member: "d\<in>S"
  shows "c d=0"
proof -
  let ?T = "\<lambda>d. \<lambda>r. smult (c d) (op_comp (P^^fst d) (Q^^snd d) r)"
  have words: "op_comp (P^^fst d) (Q^^snd d)\<in>weyl_algebra" for d
    by (rule exact_word_carrier[OF P Q])
  have carriers: "?T d\<in>weyl_algebra" for d by (rule weyl_scalar_closed[OF words])
  have sumcarrier: "(\<Sum>d\<in>S. ?T d)\<in>weyl_algebra" by (rule weyl_sum_closed) (rule carriers)
  have symbolzero: "pbw_symbol (\<Sum>d\<in>S. ?T d)=0"
    by (simp only: weyl_symbol_sum[OF finite carriers] weyl_symbol_smult[OF words] relation)
  have zero: "(\<Sum>d\<in>S. ?T d)=0"
    by (rule weyl_symbol_injective[OF sumcarrier]) (simp_all add: weyl_algebra_def symbolzero)
  show ?thesis by (rule exact_pair_words_linearIndependent[OF weyl_linear[OF P] weyl_linear[OF Q] exact finite zero member])
qed

lemma exact_pair_word_symbol_index_injective:
  fixes P Q :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "inj (\<lambda>d::nat\<times>nat. pbw_symbol (op_comp (P^^fst d) (Q^^snd d)))"
proof (rule injI)
  fix d e :: "nat\<times>nat"
  assume equal: "pbw_symbol (op_comp (P^^fst d) (Q^^snd d))=pbw_symbol (op_comp (P^^fst e) (Q^^snd e))"
  have opeq: "op_comp (P^^fst d) (Q^^snd d)=op_comp (P^^fst e) (Q^^snd e)"
    by (rule weyl_symbol_injective[OF exact_word_carrier[OF P Q] exact_word_carrier[OF P Q] equal])
  have evaluated: "wordEvaluation P Q (biv_monom 1 (fst d) (snd d))=
    wordEvaluation P Q (biv_monom 1 (fst e) (snd e))"
    by (simp only: wordEvaluation_monomial smult_1_left opeq)
  have polyeq: "biv_monom (1::complex) (fst d) (snd d)=biv_monom 1 (fst e) (snd e)"
    by (rule injD[OF wordEvaluation_injective[OF weyl_linear[OF P] weyl_linear[OF Q] exact] evaluated])
  note coefficient = arg_cong[OF polyeq, where f="\<lambda>p. biv_coeff p (fst d) (snd d)"]
  show "d=e" using coefficient by (auto simp: prod_eq_iff split: if_splits)
qed

lemma exact_pair_rectangular_word_symbols_linearIndependent:
  fixes P Q :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "joseph_bivariate.independent (rectangular_word_symbols P Q N M)"
proof -
  let ?I = "{..<N}\<times>{..<M}"
  let ?v = "\<lambda>d. pbw_symbol (op_comp (P^^fst d) (Q^^snd d))"
  have injective: "inj_on ?v ?I" by (rule inj_on_subset[OF exact_pair_word_symbol_index_injective[OF P Q exact]]) simp
  show ?thesis
  proof (rule joseph_bivariate.independent_if_scalars_zero)
    show "finite (rectangular_word_symbols P Q N M)" by (simp add: rectangular_word_symbols_def)
    fix c x
    assume relation: "(\<Sum>x\<in>rectangular_word_symbols P Q N M. joseph_biv_scale (c x) x)=0"
      and member: "x\<in>rectangular_word_symbols P Q N M"
    obtain d where d: "d\<in>?I" and x: "x=?v d" using member unfolding rectangular_word_symbols_def by blast
    have reindexed: "(\<Sum>d\<in>?I. smult [:c (?v d):] (?v d))=0"
      using relation by (simp only: rectangular_word_symbols_def sum.reindex[OF injective] comp_def joseph_biv_scale_def)
    have "c (?v d)=0"
      by (rule exact_pair_word_symbols_coefficients_zero[OF P Q exact _ reindexed d]) simp
    then show "c x=0" by (simp only: x)
  qed
qed

lemma exact_pair_rectangular_word_symbols_finrank:
  fixes P Q :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "joseph_bivariate.dim (joseph_bivariate.span (rectangular_word_symbols P Q N M))=N*M"
proof -
  have independent: "joseph_bivariate.independent (rectangular_word_symbols P Q N M)"
    by (rule exact_pair_rectangular_word_symbols_linearIndependent[OF P Q exact])
  have injective: "inj_on (\<lambda>d::nat\<times>nat. pbw_symbol (op_comp (P^^fst d) (Q^^snd d))) ({..<N}\<times>{..<M})"
    by (rule inj_on_subset[OF exact_pair_word_symbol_index_injective[OF P Q exact]]) simp
  show ?thesis by (simp only: joseph_bivariate.dim_span_eq_card_independent[OF independent])
    (simp add: rectangular_word_symbols_def card_image[OF injective])
qed

end
