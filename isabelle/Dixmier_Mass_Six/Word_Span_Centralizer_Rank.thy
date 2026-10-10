theory Word_Span_Centralizer_Rank
  imports Filtered_Centralizer_Component
    "Word_Symbol_Span_Recovery"
    "Generated_Face_Filtration"
begin

lemma rectangular_word_span_centralizer_rank:
  fixes P Q :: "complex poly_operator" and f :: "complex bivariate"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and hf: "weighted_homogeneous rho sigma m f" and hfne: "f\<noteq>0" and hm: "m\<noteq>0"
    and hc: "\<And>R. R\<in>weyl_algebra \<Longrightarrow> R\<in>op_adjoin {P,Q} \<Longrightarrow>
      biv_poisson f (leading_form rho sigma R)=0"
    and hb: "\<And>p u. p\<in>joseph_bivariate.span (rectangular_word_symbols P Q N M) \<Longrightarrow>
      u\<in>biv_support p \<Longrightarrow> abs (pair_weight rho sigma u)\<le>int B"
  shows "joseph_bivariate.dim (joseph_bivariate.span (rectangular_word_symbols P Q N M))\<le>2*B+1"
proof -
  let ?S = "joseph_bivariate.span (rectangular_word_symbols P Q N M)"
  have filtered: "biv_poisson f (weighted_component rho sigma b p)=0"
    if p: "p\<in>restrictedWeightBelow ?S rho sigma (b+1)" for b p
  proof -
    have ps: "p\<in>?S" and below: "p\<in>signedWeightBelow rho sigma (b+1)"
      using p by (auto simp: restrictedWeightBelow_def)
    obtain T where T: "T\<in>weyl_algebra" "T\<in>op_adjoin {P,Q}" "pbw_symbol T=p"
      using rectangular_word_symbol_span_recovery[OF P Q ps] by blast
    have "pbw_symbol T\<in>signedWeightBelow rho sigma (b+1)" using below T(3) by simp
    then show ?thesis using generated_face_centralization_implies_filtered_component[OF P Q T(1) hc T(2)]
      by (simp only: T(3))
  qed
  show ?thesis by (rule filtered_centralizer_finrank_le_abs_interval[OF
    joseph_bivariate.subspace_span hf hfne hm hb filtered])
qed

lemma joseph_quadratic_word_rank_exceeds_interval:
  "2*(2*(4*C+2)*C)+1<(4*C+2)*(4*C+2)" for C :: nat
proof -
  have equal: "(4*C+2)*(4*C+2)=2*(2*(4*C+2)*C)+1+(8*C+3)"
    by (simp add: algebra_simps)
  show ?thesis using equal by arith
qed

end
