theory Polynomial_Finite_Cut_Dimension_Witness
  imports Finite_Cut_Word_Span_Recovery
begin

lemma finite_cut_quadratic_word_rank_exceeds_interval:
  "2*(2*(4*C+2)*C)+1<(4*C+2)*(4*C+2)" for C :: nat
proof -
  have equal: "(4*C+2)*(4*C+2)=2*(2*(4*C+2)*C)+1+(8*C+3)"
    by (simp add: algebra_simps)
  show ?thesis using equal by arith
qed

lemma finite_cut_generated_noncentralizing_face_exists:
  fixes P Q :: "complex poly_operator"
  assumes l: "0<l" and P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and exact: "op_comp Q P-op_comp P Q=id"
    and history: "admissible_ramified_history l cuts" and rho: "0<rho"
    and U: "U\<in>ramified_operator_algebra l" and Unz: "U\<noteq>0"
    and degree: "ramified_weight_deg l rho sigma U\<noteq>0"
  shows "\<exists>R. R\<in>weyl_algebra \<and> R\<in>op_adjoin {P,Q} \<and>
    ramified_face_centralization l rho sigma U (finite_cut_image l cuts R)\<noteq>0"
proof (rule ccontr)
  assume no: "\<not>(\<exists>R. R\<in>weyl_algebra \<and> R\<in>op_adjoin {P,Q} \<and>
    ramified_face_centralization l rho sigma U (finite_cut_image l cuts R)\<noteq>0)"
  have central_source: "ramified_face_centralization l rho sigma U (finite_cut_image l cuts R)=0"
    if "R\<in>weyl_algebra" "R\<in>op_adjoin {P,Q}" for R using no that by blast
  obtain D where pbound: "\<forall>e\<in>biv_support (pbw_symbol P). fst e\<le>D \<and> snd e\<le>D"
    and qbound: "\<forall>e\<in>biv_support (pbw_symbol Q). fst e\<le>D \<and> snd e\<le>D"
    using pair_symbol_coordinate_bound_exists[of P Q] by blast
  have hP: "\<And>e. e\<in>biv_support (pbw_symbol P) \<Longrightarrow> fst e\<le>D \<and> snd e\<le>D" using pbound by blast
  have hQ: "\<And>e. e\<in>biv_support (pbw_symbol Q) \<Longrightarrow> fst e\<le>D \<and> snd e\<le>D" using qbound by blast
  let ?C = "l*((length cuts+1)*nat(abs rho)+nat(abs sigma))*D"
  let ?N = "4*?C+2"
  let ?B = "2*?N*?C"
  let ?S = "ramified_operator_vector.span (rectangular_finite_cut_words l cuts P Q ?N ?N)"
  have scalar_bound: "int l*((int(length cuts)+1)*abs rho+abs sigma)*int ((?N+?N)*D)=int ?B"
    by (simp add: algebra_simps)
  have span_bound: "T\<in>ramified_operator_algebra l \<and>
    (\<forall>p\<in>ramified_pbw_support l T. abs(ramified_weight l rho sigma p)\<le>int ?B)"
    if member: "T\<in>?S" for T
  proof -
    have raw: "T\<in>ramified_operator_algebra l \<and>
      (\<forall>p\<in>ramified_pbw_support l T. abs(ramified_weight l rho sigma p)\<le>
        int l*((int(length cuts)+1)*abs rho+abs sigma)*int ((?N+?N)*D))"
    proof (rule rectangular_finite_cut_word_span_signed_bound[where l=l and P=P and Q=Q and D=D
      and N="?N" and M="?N" and rho=rho and sigma=sigma and cuts=cuts and T=T, OF l P Q])
      fix e assume e: "e\<in>biv_support(pbw_symbol P)"
      show "fst e\<le>D \<and> snd e\<le>D" by (rule hP[OF e])
    next
      fix e assume e: "e\<in>biv_support(pbw_symbol Q)"
      show "fst e\<le>D \<and> snd e\<le>D" by (rule hQ[OF e])
    next
      show "admissible_ramified_history l cuts" by (rule history)
    next
      show "T\<in>ramified_operator_vector.span(rectangular_finite_cut_words l cuts P Q ?N ?N)" by (rule member)
    qed
    show ?thesis
    proof (rule conjI)
      show "T\<in>ramified_operator_algebra l" by (rule conjunct1[OF raw])
      show "\<forall>p\<in>ramified_pbw_support l T. abs(ramified_weight l rho sigma p)\<le>int ?B"
      proof (intro ballI)
        fix p assume p: "p\<in>ramified_pbw_support l T"
        have bound: "abs(ramified_weight l rho sigma p)\<le>
          int l*((int(length cuts)+1)*abs rho+abs sigma)*int ((?N+?N)*D)"
          by (rule bspec[OF conjunct2[OF raw] p])
        show "abs(ramified_weight l rho sigma p)\<le>int ?B"
          by (subst scalar_bound[symmetric]; rule bound)
      qed
    qed
  qed
  have carrier: "?S\<subseteq>ramified_operator_algebra l" using span_bound by blast
  have central: "ramified_face_centralization l rho sigma U T=0" if member: "T\<in>?S" for T
  proof -
    obtain R where R: "R\<in>weyl_algebra" "R\<in>op_adjoin {P,Q}" "finite_cut_image l cuts R=T"
      using rectangular_finite_cut_word_span_recovery[OF l P Q member] by blast
    show ?thesis using central_source[OF R(1,2)] by (simp only: R(3))
  qed
  have lower: "ramified_pbw_coeff l T i j=0"
    if member: "T\<in>?S" and below: "ramified_weight l rho sigma (i,j)< -int ?B" for T i j
  proof (rule ccontr)
    assume nonzero: "ramified_pbw_coeff l T i j\<noteq>0"
    have Tc: "T\<in>ramified_operator_algebra l" using carrier member by blast
    have support: "(i,j)\<in>ramified_pbw_support l T" using nonzero ramified_pbw_support_mem_iff[OF l Tc] by blast
    have bound: "abs(ramified_weight l rho sigma (i,j))\<le>int ?B" using span_bound[OF member] support by blast
    show False using bound below by arith
  qed
  have upper: "ramified_pbw_coeff l T i j=0"
    if member: "T\<in>?S" and above: "-int ?B+int(2*?B+1)\<le>ramified_weight l rho sigma (i,j)" for T i j
  proof (rule ccontr)
    assume nonzero: "ramified_pbw_coeff l T i j\<noteq>0"
    have Tc: "T\<in>ramified_operator_algebra l" using carrier member by blast
    have support: "(i,j)\<in>ramified_pbw_support l T" using nonzero ramified_pbw_support_mem_iff[OF l Tc] by blast
    have bound: "abs(ramified_weight l rho sigma (i,j))\<le>int ?B" using span_bound[OF member] support by blast
    show False using bound above by (simp add: algebra_simps; arith)
  qed
  have rank_upper: "ramified_operator_vector.dim ?S\<le>2*?B+1"
    by (rule ramified_top_centralizer_finrank_le_interval[OF l rho ramified_operator_vector.subspace_span carrier U Unz degree lower upper central])
  have rank_lower: "ramified_operator_vector.dim ?S=?N*?N"
    by (rule exact_pair_rectangular_finite_cut_words_finrank[OF l P Q exact])
  show False using rank_upper rank_lower finite_cut_quadratic_word_rank_exceeds_interval[of ?C] by arith
qed

end
