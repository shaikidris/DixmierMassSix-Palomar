theory Joseph_Initial_Witness
  imports "Word_Span_Centralizer_Rank"
    "Word_Symbol_Growth"
    "Joseph_Local_Nilpotence"
begin

lemma generated_nonzero_leading_bracket_exists:
  fixes P Q :: "complex poly_operator" and f :: "complex bivariate"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and exact: "op_comp Q P-op_comp P Q=id"
    and hf: "weighted_homogeneous rho sigma m f" and hfne: "f\<noteq>0" and hm: "m\<noteq>0"
  shows "\<exists>R. R\<in>weyl_algebra \<and> R\<in>op_adjoin {P,Q} \<and>
    biv_poisson f (leading_form rho sigma R)\<noteq>0"
proof (rule ccontr)
  assume no: "\<not>(\<exists>R. R\<in>weyl_algebra \<and> R\<in>op_adjoin {P,Q} \<and>
    biv_poisson f (leading_form rho sigma R)\<noteq>0)"
  have central: "biv_poisson f (leading_form rho sigma R)=0"
    if "R\<in>weyl_algebra" "R\<in>op_adjoin {P,Q}" for R using no that by blast
  obtain D where pbound: "\<forall>e\<in>biv_support (pbw_symbol P). fst e\<le>D \<and> snd e\<le>D"
    and qbound: "\<forall>e\<in>biv_support (pbw_symbol Q). fst e\<le>D \<and> snd e\<le>D"
    using pair_symbol_coordinate_bound_exists[of P Q] by blast
  let ?C = "(nat (abs rho)+nat (abs sigma))*D"
  let ?N = "4*?C+2"
  let ?B = "2*?N*?C"
  have scalar_bound: "(abs rho+abs sigma)*int ((?N+?N)*D)=int ?B"
    by (simp add: algebra_simps)
  have hP: "\<And>e. e\<in>biv_support (pbw_symbol P) \<Longrightarrow> fst e\<le>D \<and> snd e\<le>D"
    using pbound by blast
  have hQ: "\<And>e. e\<in>biv_support (pbw_symbol Q) \<Longrightarrow> fst e\<le>D \<and> snd e\<le>D"
    using qbound by blast
  have bound: "abs (pair_weight rho sigma u)\<le>int ?B"
    if p: "p\<in>joseph_bivariate.span (rectangular_word_symbols P Q ?N ?N)"
      and u: "u\<in>biv_support p" for p u
    using rectangular_word_span_signed_bound[OF P Q hP hQ p u, where rho=rho and sigma=sigma]
      scalar_bound by simp
  have upper: "joseph_bivariate.dim (joseph_bivariate.span (rectangular_word_symbols P Q ?N ?N))\<le>2*?B+1"
    by (rule rectangular_word_span_centralizer_rank[OF P Q hf hfne hm central bound])
  have lower: "joseph_bivariate.dim (joseph_bivariate.span (rectangular_word_symbols P Q ?N ?N))=?N*?N"
    by (rule exact_pair_rectangular_word_symbols_finrank[OF P Q exact])
  show False using upper lower joseph_quadratic_word_rank_exceeds_interval[of ?C] by arith
qed

lemma joseph_two_bracket_exists_of_positive_degree:
  fixes P Q :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and exact: "op_comp Q P-op_comp P Q=id"
    and weight: "0<rho+sigma" and degree: "0<v_degree rho sigma P"
  shows "\<exists>T. T\<in>weyl_algebra \<and> T\<in>op_adjoin {P,Q} \<and>
    biv_poisson (leading_form rho sigma P) (leading_form rho sigma T)\<noteq>0 \<and>
    biv_poisson (leading_form rho sigma P)
      (biv_poisson (leading_form rho sigma P) (leading_form rho sigma T))=0"
proof -
  have pd: "weighted_degree rho sigma (pbw_symbol P)=bot.Value (v_degree rho sigma P)"
    using degree by (cases "weighted_degree rho sigma (pbw_symbol P)") (auto simp: v_degree_def)
  have nz: "leading_form rho sigma P\<noteq>0"
    unfolding leading_form_def by (rule weighted_top_component_nonzero[OF pd])
  have homogeneous: "weighted_homogeneous rho sigma (v_degree rho sigma P) (leading_form rho sigma P)"
    unfolding leading_form_def by (rule weighted_component_homogeneous)
  have nonzero: "v_degree rho sigma P\<noteq>0" using degree by arith
  obtain R where R: "R\<in>weyl_algebra" "R\<in>op_adjoin {P,Q}"
    "biv_poisson (leading_form rho sigma P) (leading_form rho sigma R)\<noteq>0"
    using generated_nonzero_leading_bracket_exists[OF P Q exact homogeneous nz nonzero] by blast
  show ?thesis by (rule joseph_two_bracket_of_generated_nonzero_bracket[OF P Q R(1) exact weight R(2,3)])
qed

end
