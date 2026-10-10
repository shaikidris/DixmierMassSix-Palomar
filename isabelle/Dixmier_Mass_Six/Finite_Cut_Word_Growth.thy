theory Finite_Cut_Word_Growth
  imports Finite_Cut_Linear_Transport "Word_Symbol_Growth"
begin

definition rectangular_finite_cut_words where
  "rectangular_finite_cut_words l cuts P Q N M=
    (\<lambda>d. finite_cut_image l cuts (op_comp (P^^fst d) (Q^^snd d))) ` ({..<N}\<times>{..<M})"

lemma exact_pair_finite_cut_word_coefficients_zero:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and exact: "op_comp Q P-op_comp P Q=id" and finite: "finite S"
    and relation: "(\<Sum>d\<in>S. normal_smult (c d) (finite_cut_image l cuts (op_comp (P^^fst d) (Q^^snd d))))=0"
    and member: "d\<in>S"
  shows "c d=0"
proof -
  let ?T = "\<lambda>d. \<lambda>r. smult (c d) (op_comp (P^^fst d) (Q^^snd d) r)"
  have words: "op_comp (P^^fst d) (Q^^snd d)\<in>weyl_algebra" for d
    by (rule exact_word_carrier[OF P Q])
  have carriers: "?T d\<in>weyl_algebra" for d by (rule weyl_scalar_closed[OF words])
  have sumcarrier: "(\<Sum>d\<in>S. ?T d)\<in>weyl_algebra"
    by (rule weyl_sum_closed) (rule carriers)
  have imagezero: "finite_cut_image l cuts (\<Sum>d\<in>S. ?T d)=0"
    by (simp only: finite_cut_image_sum[OF l finite carriers] finite_cut_image_smult[OF l words] relation)
  have zero: "(\<Sum>d\<in>S. ?T d)=0"
    using finite_cut_image_nonzero_iff[OF l sumcarrier, where cuts=cuts] imagezero by blast
  show ?thesis by (rule exact_pair_words_linearIndependent[OF weyl_linear[OF P] weyl_linear[OF Q] exact finite zero member])
qed

lemma exact_pair_finite_cut_word_index_injective:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "inj (\<lambda>d::nat\<times>nat. finite_cut_image l cuts (op_comp (P^^fst d) (Q^^snd d)))"
proof (rule injI)
  fix d e :: "nat\<times>nat"
  assume equal: "finite_cut_image l cuts (op_comp (P^^fst d) (Q^^snd d))=
    finite_cut_image l cuts (op_comp (P^^fst e) (Q^^snd e))"
  have words: "op_comp (P^^fst k) (Q^^snd k)\<in>weyl_algebra" for k
    by (rule exact_word_carrier[OF P Q])
  have opeq: "op_comp (P^^fst d) (Q^^snd d)=op_comp (P^^fst e) (Q^^snd e)"
    by (rule finite_cut_image_injective[OF l words words equal])
  have symbols: "pbw_symbol (op_comp (P^^fst d) (Q^^snd d))=pbw_symbol (op_comp (P^^fst e) (Q^^snd e))"
    by (rule arg_cong[OF opeq])
  show "d=e" by (rule injD[OF exact_pair_word_symbol_index_injective[OF P Q exact] symbols])
qed

lemma exact_pair_rectangular_finite_cut_words_linearIndependent:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "ramified_operator_vector.independent (rectangular_finite_cut_words l cuts P Q N M)"
proof -
  let ?I = "{..<N}\<times>{..<M}"
  let ?v = "\<lambda>d. finite_cut_image l cuts (op_comp (P^^fst d) (Q^^snd d))"
  have injective: "inj_on ?v ?I"
    by (rule inj_on_subset[OF exact_pair_finite_cut_word_index_injective[OF l P Q exact]]) simp
  show ?thesis
  proof (rule ramified_operator_vector.independent_if_scalars_zero)
    show "finite (rectangular_finite_cut_words l cuts P Q N M)"
      by (simp add: rectangular_finite_cut_words_def)
    fix c x
    assume relation: "(\<Sum>x\<in>rectangular_finite_cut_words l cuts P Q N M. normal_smult (c x) x)=0"
      and member: "x\<in>rectangular_finite_cut_words l cuts P Q N M"
    have member_image: "x\<in>?v ` ?I" using member by (simp only: rectangular_finite_cut_words_def)
    obtain d where x: "x=?v d" and d: "d\<in>?I"
      by (rule imageE[OF member_image])
    have reindexed: "(\<Sum>d\<in>?I. normal_smult (c (?v d)) (?v d))=0"
      using relation by (simp only: rectangular_finite_cut_words_def sum.reindex[OF injective] comp_def)
    have "c (?v d)=0"
      by (rule exact_pair_finite_cut_word_coefficients_zero[OF l P Q exact _ reindexed d]) simp
    then show "c x=0" by (simp only: x)
  qed
qed

lemma exact_pair_rectangular_finite_cut_words_finrank:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "ramified_operator_vector.dim (ramified_operator_vector.span (rectangular_finite_cut_words l cuts P Q N M))=N*M"
proof -
  have independent: "ramified_operator_vector.independent (rectangular_finite_cut_words l cuts P Q N M)"
    by (rule exact_pair_rectangular_finite_cut_words_linearIndependent[OF l P Q exact])
  have injective: "inj_on (\<lambda>d::nat\<times>nat. finite_cut_image l cuts (op_comp (P^^fst d) (Q^^snd d))) ({..<N}\<times>{..<M})"
    by (rule inj_on_subset[OF exact_pair_finite_cut_word_index_injective[OF l P Q exact]]) simp
  show ?thesis by (simp only: ramified_operator_vector.dim_span_eq_card_independent[OF independent])
    (simp add: rectangular_finite_cut_words_def card_image[OF injective])
qed

end
