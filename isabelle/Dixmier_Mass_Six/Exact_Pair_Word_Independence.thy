theory Exact_Pair_Word_Independence
  imports Exact_Pair_Word_Evaluation
begin

lemma exact_pair_words_linearIndependent:
  fixes P Q :: "complex poly_operator"
  assumes P: "poly_linear P" and Q: "poly_linear Q"
    and exact: "op_comp Q P-op_comp P Q=id"
    and finite: "finite S"
    and relation: "(\<Sum>d\<in>S. (\<lambda>r. smult (c d) (op_comp (P^^fst d) (Q^^snd d) r)))=0"
    and member: "d\<in>S"
  shows "c d=0"
proof -
  let ?f = "\<Sum>d\<in>S. biv_monom (c d) (fst d) (snd d)"
  have evaluated: "wordEvaluation P Q ?f=0"
    by (simp only: wordEvaluation_sum wordEvaluation_monomial relation)
  have fzero: "?f=0"
    by (rule injD[OF wordEvaluation_injective[OF P Q exact]]) (simp only: evaluated wordEvaluation_zero)
  have coefficient: "biv_coeff ?f (fst d) (snd d)=0"
    by (simp only: fzero biv_coeff_zero)
  show ?thesis using coefficient member
    by (simp add: biv_sum_monom_coeff[OF finite])
qed

lemma exact_pair_rectangular_words_linearIndependent:
  fixes P Q :: "complex poly_operator"
  assumes P: "poly_linear P" and Q: "poly_linear Q"
    and exact: "op_comp Q P-op_comp P Q=id"
    and relation: "(\<Sum>d\<in>{..<N}\<times>{..<M}.
      (\<lambda>r. smult (c d) (op_comp (P^^fst d) (Q^^snd d) r)))=0"
    and member: "d\<in>{..<N}\<times>{..<M}"
  shows "c d=0"
  by (rule exact_pair_words_linearIndependent[OF P Q exact _ relation member]) simp

end
