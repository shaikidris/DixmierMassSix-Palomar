theory Polynomial_Finite_Cut_Word_Bounds
  imports "Ramified_Finite_Cut_Support"
    "Finite_Cut_Word_Growth"
    "Polynomial_Lift_Face_Transport"
begin

lemma polynomial_finite_cut_signed_weight_bound:
  assumes l: "0<l" and R: "R\<in>(weyl_algebra::complex poly_operator set)"
    and coordinates: "\<And>e. e\<in>biv_support (pbw_symbol R) \<Longrightarrow> fst e\<le>J \<and> snd e\<le>J"
    and history: "admissible_ramified_history l cuts"
    and support: "(i,j)\<in>ramified_pbw_support l (finite_cut_image l cuts R)"
  shows "abs (ramified_weight l rho sigma (i,j))\<le>
    int l*((int(length cuts)+1)*abs rho+abs sigma)*int J"
proof -
  let ?T = "polynomial_ramified_lift l R"
  have order: "n\<le>J" if key: "n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l ?T)" for n
  proof -
    have point: "(ramified_pbw_top_laurent l ?T n,n)\<in>ramified_pbw_support l ?T"
      by (rule ramified_pbw_top_laurent_support[OF key])
    obtain u where source: "(u,n)\<in>biv_support (pbw_symbol R)"
      using point by (simp only: polynomialRamifiedLift_support_iff_symbol[OF l R]) blast
    show ?thesis using coordinates[OF source] by simp
  qed
  have box: "0\<le>k \<and> k\<le>int l*int J"
    if key: "k\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l ?T) n)" for n k
  proof -
    have coeffnz: "ramified_pbw_coeff l ?T k n\<noteq>0"
      using key by (simp only: ramified_pbw_coeff_def Poly_Mapping.in_keys_iff; simp)
    have point: "(k,n)\<in>ramified_pbw_support l ?T"
      using coeffnz ramified_pbw_support_mem_iff[OF l polynomial_ramified_lift_carrier] by blast
    obtain u where index: "k=int l*int u" and source: "(u,n)\<in>biv_support (pbw_symbol R)"
      using point by (simp only: polynomialRamifiedLift_support_iff_symbol[OF l R]) blast
    have uJ: "u\<le>J" using coordinates[OF source] by simp
    have bound: "int l*int u\<le>int l*int J" by (rule mult_left_mono) (use uJ in auto)
    show ?thesis by (simp only: index) (use bound in auto)
  qed
  have cut_support: "(i,j)\<in>ramified_pbw_support l (ramified_finite_cut_aut l cuts ?T)"
    using support by (simp only: finite_cut_image_def)
  show ?thesis by (rule ramified_finite_cut_aut_signed_weight_bound[OF l polynomial_ramified_lift_carrier order box history cut_support])
qed

lemma ramified_span_signed_weight_abs_le:
  assumes l: "0<l" and generators: "\<And>x. x\<in>A \<Longrightarrow> x\<in>ramified_operator_algebra l"
    and bounds: "\<And>x i j. x\<in>A \<Longrightarrow> (i,j)\<in>ramified_pbw_support l x \<Longrightarrow>
      abs(ramified_weight l rho sigma (i,j))\<le>B"
    and span: "T\<in>ramified_operator_vector.span A"
  shows "T\<in>ramified_operator_algebra l \<and>
    (\<forall>p\<in>ramified_pbw_support l T. abs(ramified_weight l rho sigma p)\<le>B)"
proof -
  have property: "T\<in>ramified_operator_algebra l \<and>
    (\<forall>i j. B<abs(ramified_weight l rho sigma (i,j)) \<longrightarrow> ramified_pbw_coeff l T i j=0)"
    using span
  proof (induction rule: ramified_operator_vector.span_induct_alt)
    case base
    have zero_carrier: "(0::laurent_operator)\<in>ramified_operator_algebra l"
      unfolding ramified_operator_algebra_def by (rule laurent_adjoin_zero)
    have zero_coeff: "ramified_pbw_coeff l (0::laurent_operator) i j=0" for i j
      by (simp only: ramified_pbw_coeff_def ramified_pbw_coeffs_zero[OF l] Poly_Mapping.lookup_zero)
    show ?case by (intro conjI zero_carrier allI impI zero_coeff)
  next
    case (step c x y)
    have xc: "x\<in>ramified_operator_algebra l" by (rule generators[OF step.hyps(1)])
    have yc: "y\<in>ramified_operator_algebra l" using step.IH by blast
    have sc: "normal_smult c x\<in>ramified_operator_algebra l" by (rule ramified_algebra_smult[OF xc])
    have sumc: "normal_smult c x+y\<in>ramified_operator_algebra l" by (rule ramified_algebra_add[OF sc yc])
    have xzero: "ramified_pbw_coeff l x i j=0"
      if excessive: "B<abs(ramified_weight l rho sigma (i,j))" for i j
    proof (rule ccontr)
      assume nonzero: "ramified_pbw_coeff l x i j\<noteq>0"
      have support: "(i,j)\<in>ramified_pbw_support l x"
        using nonzero ramified_pbw_support_mem_iff[OF l xc] by blast
      have "abs(ramified_weight l rho sigma (i,j))\<le>B" by (rule bounds[OF step.hyps(1) support])
      then show False using excessive by arith
    qed
    have yzero: "ramified_pbw_coeff l y i j=0"
      if excessive: "B<abs(ramified_weight l rho sigma(i,j))" for i j
      using step.IH excessive by blast
    have sumzero: "ramified_pbw_coeff l (normal_smult c x+y) i j=0"
      if excessive: "B<abs(ramified_weight l rho sigma(i,j))" for i j
    proof -
      have coefficient: "ramified_pbw_coeff l (normal_smult c x+y) i j=
        c*ramified_pbw_coeff l x i j+ramified_pbw_coeff l y i j"
        by (simp only: ramified_pbw_coeff_def ramified_pbw_coeffs_add[OF l sc yc]
          Poly_Mapping.lookup_add ramified_pbw_coeffs_smult[OF l xc] ramified_pbw_smult_lookup laurent_smult_lookup)
      show ?thesis by (simp only: coefficient xzero[OF excessive] yzero[OF excessive] mult_zero_right add_0)
    qed
    have normalized: "(\<lambda>a. normal_smult c x a+y a)=normal_smult c x+y"
      by (rule ext) simp
    have result: "normal_smult c x+y\<in>ramified_operator_algebra l \<and>
      (\<forall>i j. B<abs(ramified_weight l rho sigma(i,j)) \<longrightarrow> ramified_pbw_coeff l (normal_smult c x+y) i j=0)"
      by (intro conjI sumc allI impI) (rule sumzero)
    show ?case by (rule result)
  qed
  have carrier: "T\<in>ramified_operator_algebra l" using property by blast
  have bound: "abs(ramified_weight l rho sigma p)\<le>B"
    if support: "p\<in>ramified_pbw_support l T" for p
  proof (rule ccontr)
    assume excessive: "\<not>abs(ramified_weight l rho sigma p)\<le>B"
    obtain i j where pair: "p=(i,j)" by (cases p) auto
    have coefficient: "ramified_pbw_coeff l T i j\<noteq>0"
      using support by (simp only: pair ramified_pbw_support_mem_iff[OF l carrier]; simp)
    have over: "B<abs(ramified_weight l rho sigma (i,j))" using excessive by (simp only: pair; arith)
    have zero: "ramified_pbw_coeff l T i j=0" using property over by blast
    show False using coefficient zero by contradiction
  qed
  show ?thesis using carrier bound by blast
qed

lemma rectangular_finite_cut_word_span_signed_bound:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and hP: "\<And>e. e\<in>biv_support (pbw_symbol P) \<Longrightarrow> fst e\<le>D \<and> snd e\<le>D"
    and hQ: "\<And>e. e\<in>biv_support (pbw_symbol Q) \<Longrightarrow> fst e\<le>D \<and> snd e\<le>D"
    and history: "admissible_ramified_history l cuts"
    and T: "T\<in>ramified_operator_vector.span (rectangular_finite_cut_words l cuts P Q N M)"
  shows "T\<in>ramified_operator_algebra l \<and>
    (\<forall>p\<in>ramified_pbw_support l T. abs(ramified_weight l rho sigma p)\<le>
      int l*((int(length cuts)+1)*abs rho+abs sigma)*int ((N+M)*D))"
proof -
  have generator: "x\<in>ramified_operator_algebra l \<and>
    (\<forall>p\<in>ramified_pbw_support l x. abs(ramified_weight l rho sigma p)\<le>
      int l*((int(length cuts)+1)*abs rho+abs sigma)*int ((N+M)*D))"
    if member: "x\<in>rectangular_finite_cut_words l cuts P Q N M" for x
  proof -
    have image: "x\<in>(\<lambda>d. finite_cut_image l cuts (op_comp (P^^fst d) (Q^^snd d))) ` ({..<N}\<times>{..<M})"
      using member by (simp only: rectangular_finite_cut_words_def)
    obtain d where xd: "x=finite_cut_image l cuts (op_comp (P^^fst d) (Q^^snd d))"
      and d: "d\<in>{..<N}\<times>{..<M}" by (rule imageE[OF image])
    let ?R = "op_comp (P^^fst d) (Q^^snd d)"
    have R: "?R\<in>weyl_algebra" by (rule exact_word_carrier[OF P Q])
    have ij: "fst d*D+snd d*D\<le>(N+M)*D"
    proof -
      have i: "fst d\<le>N" and j: "snd d\<le>M" using d by auto
      have im: "fst d*D\<le>N*D" by (rule mult_right_mono[OF i]) simp
      have jm: "snd d*D\<le>M*D" by (rule mult_right_mono[OF j]) simp
      show ?thesis using add_mono[OF im jm] by (simp add: distrib_right)
    qed
    have coordinates: "fst e\<le>(N+M)*D \<and> snd e\<le>(N+M)*D"
      if e: "e\<in>biv_support (pbw_symbol ?R)" for e
    proof -
      have coord: "fst e\<le>fst d*D+snd d*D \<and> snd e\<le>fst d*D+snd d*D"
        by (rule symbol_word_coordinate_le[OF P Q hP hQ e])
      have first: "fst e\<le>(N+M)*D" by (rule order_trans[OF conjunct1[OF coord] ij])
      have second: "snd e\<le>(N+M)*D" by (rule order_trans[OF conjunct2[OF coord] ij])
      show ?thesis by (rule conjI[OF first second])
    qed
    have bounds: "abs(ramified_weight l rho sigma p)\<le>int l*((int(length cuts)+1)*abs rho+abs sigma)*int ((N+M)*D)"
      if support: "p\<in>ramified_pbw_support l x" for p
    proof -
      obtain i j where pair: "p=(i,j)" by (cases p) auto
      have supported: "(i,j)\<in>ramified_pbw_support l (finite_cut_image l cuts ?R)"
        using support by (simp only: pair xd)
      show ?thesis by (simp only: pair; rule polynomial_finite_cut_signed_weight_bound[OF l R coordinates history supported])
    qed
    have carrier: "x\<in>ramified_operator_algebra l" by (simp only: xd; rule finite_cut_image_carrier[OF l])
    show ?thesis using carrier bounds by blast
  qed
  show ?thesis by (rule ramified_span_signed_weight_abs_le[OF l _ _ T]) (use generator in blast)+
qed

end
