theory Signed_Coordinate_Bounds
  imports Product_Coordinate_Support Word_Span_Signed_Bounds
begin

lemma signed_weight_abs_le_coordinates:
  assumes hx: "fst e\<le>a" and hy: "snd e\<le>b"
  shows "abs (pair_weight rho sigma e)\<le>abs rho*int a+abs sigma*int b"
proof -
  have triangle: "abs (int (fst e)*rho+int (snd e)*sigma)\<le>
      abs (int (fst e)*rho)+abs (int (snd e)*sigma)" by (rule abs_triangle_ineq)
  have xb: "abs rho*int (fst e)\<le>abs rho*int a"
    by (rule mult_left_mono) (use hx in auto)
  have yb: "abs sigma*int (snd e)\<le>abs sigma*int b"
    by (rule mult_left_mono) (use hy in auto)
  show ?thesis using triangle xb yb by (simp add: pair_weight_def abs_mult mult.commute; arith)
qed

lemma symbol_word_signed_weight_abs_le:
  fixes P Q :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and hP: "\<And>e. e\<in>biv_support (pbw_symbol P) \<Longrightarrow> fst e\<le>a \<and> snd e\<le>b"
    and hQ: "\<And>e. e\<in>biv_support (pbw_symbol Q) \<Longrightarrow> fst e\<le>c \<and> snd e\<le>d"
    and e: "e\<in>biv_support (pbw_symbol (op_comp (P^^i) (Q^^j)))"
  shows "abs (pair_weight rho sigma e)\<le>abs rho*int (i*a+j*c)+abs sigma*int (i*b+j*d)"
  using symbol_word_coordinate_le[OF P Q hP hQ e]
  by (intro signed_weight_abs_le_coordinates) auto

lemma pair_symbol_coordinate_bound_exists:
  fixes P Q :: "complex poly_operator"
  shows "\<exists>D. (\<forall>e\<in>biv_support (pbw_symbol P). fst e\<le>D \<and> snd e\<le>D) \<and>
    (\<forall>e\<in>biv_support (pbw_symbol Q). fst e\<le>D \<and> snd e\<le>D)"
proof -
  let ?I = "biv_support (pbw_symbol P)\<union>biv_support (pbw_symbol Q)"
  let ?A = "insert 0 ((\<lambda>e. max (fst e) (snd e)) ` ?I)"
  have finite: "finite ?A" by simp
  have bound: "fst e\<le>Max ?A \<and> snd e\<le>Max ?A" if "e\<in>?I" for e
  proof -
    have "max (fst e) (snd e)\<le>Max ?A" by (rule Max_ge[OF finite]) (use that in auto)
    then show ?thesis by auto
  qed
  show ?thesis by (rule exI[of _ "Max ?A"]) (use bound in auto)
qed

definition rectangular_word_symbols :: "complex poly_operator \<Rightarrow> complex poly_operator \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex bivariate set" where
  "rectangular_word_symbols P Q N M =
    (\<lambda>k. pbw_symbol (op_comp (P^^fst k) (Q^^snd k))) ` ({..<N}\<times>{..<M})"

lemma rectangular_word_span_signed_bound:
  fixes P Q :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and hP: "\<And>e. e\<in>biv_support (pbw_symbol P) \<Longrightarrow> fst e\<le>D \<and> snd e\<le>D"
    and hQ: "\<And>e. e\<in>biv_support (pbw_symbol Q) \<Longrightarrow> fst e\<le>D \<and> snd e\<le>D"
    and hp: "p\<in>joseph_bivariate.span (rectangular_word_symbols P Q N M)"
    and e: "e\<in>biv_support p"
  shows "abs (pair_weight rho sigma e)\<le>(abs rho+abs sigma)*int ((N+M)*D)"
proof -
  have bound: "abs (pair_weight rho sigma u)\<le>(abs rho+abs sigma)*int ((N+M)*D)"
    if "x\<in>rectangular_word_symbols P Q N M" "u\<in>biv_support x" for x u
  proof -
    have member_image: "x\<in>(\<lambda>k. pbw_symbol (op_comp (P^^fst k) (Q^^snd k))) ` ({..<N}\<times>{..<M})"
      using that(1) by (simp only: rectangular_word_symbols_def)
    obtain k where xk: "x=pbw_symbol (op_comp (P^^fst k) (Q^^snd k))"
      and k: "k\<in>{..<N}\<times>{..<M}"
      by (rule imageE[OF member_image])
    obtain i j where keq: "k=(i,j)" by (cases k) auto
    have i: "i<N" and j: "j<M" using k by (simp_all add: keq)
    have x: "x=pbw_symbol (op_comp (P^^i) (Q^^j))" using xk by (simp only: keq fst_conv snd_conv)
    have support_word: "u\<in>biv_support (pbw_symbol (op_comp (P^^i) (Q^^j)))"
      using that(2) by (simp only: x)
    have coord: "fst u\<le>i*D+j*D \<and> snd u\<le>i*D+j*D"
      by (rule symbol_word_coordinate_le[OF P Q hP hQ support_word])
    have ij: "i*D+j*D\<le>(N+M)*D"
    proof -
      have ile: "i\<le>N" and jle: "j\<le>M" using i j by arith+
      have im: "i*D\<le>N*D" by (rule mult_right_mono[OF ile]) simp
      have jm: "j*D\<le>M*D" by (rule mult_right_mono[OF jle]) simp
      show ?thesis using add_mono[OF im jm] by (simp add: distrib_right)
    qed
    have xb: "fst u\<le>(N+M)*D" by (rule order_trans[OF coord[THEN conjunct1] ij])
    have yb: "snd u\<le>(N+M)*D" by (rule order_trans[OF coord[THEN conjunct2] ij])
    have "abs (pair_weight rho sigma u)\<le>abs rho*int ((N+M)*D)+abs sigma*int ((N+M)*D)"
      by (rule signed_weight_abs_le_coordinates[OF xb yb])
    then show ?thesis by (simp add: algebra_simps)
  qed
  have hz: "\<forall>u. (abs rho+abs sigma)*int ((N+M)*D)<abs (pair_weight rho sigma u)
      \<longrightarrow> biv_coeff p (fst u) (snd u)=0"
    using hp
  proof (induction rule: joseph_bivariate.span_induct_alt)
    case base show ?case by simp
  next
    case (step c x y)
    have coeff: "biv_coeff x (fst u) (snd u)=0"
      if "(abs rho+abs sigma)*int ((N+M)*D)<abs (pair_weight rho sigma u)" for u
    proof (rule ccontr)
      assume "biv_coeff x (fst u) (snd u)\<noteq>0"
      then have "u\<in>biv_support x" by (simp add: biv_support_def)
      then have "abs (pair_weight rho sigma u)\<le>(abs rho+abs sigma)*int ((N+M)*D)"
        by (rule bound[OF step.hyps(1)])
      then show False using that by arith
    qed
    show ?case using step.IH coeff by (auto simp: joseph_biv_scale_def)
  qed
  show ?thesis
  proof (rule ccontr)
    assume "\<not>abs (pair_weight rho sigma e)\<le>(abs rho+abs sigma)*int ((N+M)*D)"
    then have "(abs rho+abs sigma)*int ((N+M)*D)<abs (pair_weight rho sigma e)" by arith
    then have "biv_coeff p (fst e) (snd e)=0" using hz by blast
    then show False using e by (simp add: biv_support_def)
  qed
qed

end
