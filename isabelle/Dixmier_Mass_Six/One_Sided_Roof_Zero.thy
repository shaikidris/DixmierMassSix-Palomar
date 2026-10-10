theory One_Sided_Roof_Zero
  imports One_Sided_Roof_Exposure Newton_Endpoint_Cones
    "Leading_Mate"
begin

lemma positive_scalar_cone_contains:
  "S\<subseteq>positive_scalar_cone S"
  unfolding positive_scalar_cone_def
  by (intro subsetI CollectI exI[of _ 1]) auto

lemma no_exact_pair_all_positive_integer_leading_brackets_zero:
  fixes P Q::"complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and pnonconstant: "\<exists>d\<in>biv_support (pbw_symbol P). d\<noteq>(0,0)"
    and qnonconstant: "\<exists>d\<in>biv_support (pbw_symbol Q). d\<noteq>(0,0)"
    and pscalar: "(0,0)\<notin>biv_support (pbw_symbol P)" and qscalar: "(0,0)\<notin>biv_support (pbw_symbol Q)"
    and pside: "\<forall>d\<in>biv_support (pbw_symbol P). pair_grade d\<le>0"
    and exact: "op_comp Q P-op_comp P Q=id"
    and bracket: "\<And>rho sigma::int. 0<rho+sigma \<Longrightarrow> biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=0"
  shows False
proof -
  have reverse: "\<And>rho sigma::int. 0<rho+sigma \<Longrightarrow> biv_poisson (leading_form rho sigma P) (leading_form rho sigma Q)=0"
  proof -
    fix rho sigma::int assume sum: "0<rho+sigma"
    have anti: "biv_poisson (leading_form rho sigma P) (leading_form rho sigma Q)= -biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)"
      by (simp add: biv_poisson_def algebra_simps)
    show "biv_poisson (leading_form rho sigma P) (leading_form rho sigma Q)=0" by (simp add: anti bracket[OF sum])
  qed
  have cones: "positive_scalar_cone (integer_positive_newton_roof P)=positive_scalar_cone (integer_positive_newton_roof Q)"
    by (rule integerPositiveNewtonRoof_cones_equal_of_zeroBracket_and_scalarFree[OF P Q pnonconstant qnonconstant pscalar qscalar reverse])
  have bound: "positive_scalar_cone (integer_positive_newton_roof P)\<subseteq>{z::real\<times>real. fst z\<le>snd z}"
    by (rule integerPositiveNewtonRoof_cone_grade_nonpositive[OF P pside])
  have qside: "\<forall>d\<in>biv_support (pbw_symbol Q). pair_grade d\<le>0"
  proof (rule ccontr)
    assume "\<not>(\<forall>d\<in>biv_support (pbw_symbol Q). pair_grade d\<le>0)"
    then have pos: "\<exists>d\<in>biv_support (pbw_symbol Q). 0<pair_grade d"
      by (simp only: Ball_def Bex_def not_all not_imp not_le)
    obtain d where ds: "d\<in>biv_support (pbw_symbol Q)" and dp: "0<pair_grade d"
      and dr: "exponent_point d\<in>integer_positive_newton_roof Q"
      using exists_positive_grade_exponent_in_integerPositiveNewtonRoof[OF pos] by blast
    have dc: "exponent_point d\<in>positive_scalar_cone (integer_positive_newton_roof Q)"
      using positive_scalar_cone_contains dr by blast
    have le: "fst (exponent_point d)\<le>snd (exponent_point d)" using dc cones bound by blast
    have "snd d<fst d" using dp by (simp add: pair_grade_def)
    then have "snd (exponent_point d)<fst (exponent_point d)" by (simp add: exponent_point_def)
    then show False using le by arith
  qed
  show False using no_exact_pair_both_nonpositive[OF P Q pside qside] exact by blast
qed

lemma exists_integer_positive_direction_leading_bracket_one:
  fixes P Q::"complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and pnonconstant: "\<exists>d\<in>biv_support (pbw_symbol P). d\<noteq>(0,0)"
    and qnonconstant: "\<exists>d\<in>biv_support (pbw_symbol Q). d\<noteq>(0,0)"
    and pscalar: "(0,0)\<notin>biv_support (pbw_symbol P)" and qscalar: "(0,0)\<notin>biv_support (pbw_symbol Q)"
    and pside: "\<forall>d\<in>biv_support (pbw_symbol P). pair_grade d\<le>0"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "\<exists>rho sigma::int. 0<rho+sigma \<and> biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=1"
proof (rule ccontr)
  assume no: "\<not>(\<exists>rho sigma::int. 0<rho+sigma \<and> biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=1)"
  have zero: "\<And>rho sigma::int. 0<rho+sigma \<Longrightarrow> biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=0"
    using exactPair_leadingPoisson_zero_or_one[OF P Q _ exact] no by blast
  show False by (rule no_exact_pair_all_positive_integer_leading_brackets_zero[OF P Q pnonconstant qnonconstant pscalar qscalar pside exact zero])
qed

lemma support_cone_grade_nonpositive:
  assumes side: "\<forall>d\<in>biv_support p. pair_grade d\<le>0"
  shows "positive_scalar_cone (convex hull (exponent_point ` biv_support p))\<subseteq>{z::real\<times>real. fst z\<le>snd z}"
proof (rule positiveScalarCone_subset_nonpositive_halfspace, rule hull_minimal)
  show "exponent_point ` biv_support p\<subseteq>{z::real\<times>real. fst z\<le>snd z}"
    using side exponent_point_grade_nonpositive by auto
  show "convex {z::real\<times>real. fst z\<le>snd z}" by (rule convex_nonpositive_grade_halfspace)
qed

lemma poisson_ne_zero_of_homogeneous_faces_grade_separated:
  fixes rho sigma degreeP degreeQ::int and p q::"complex bivariate"
  assumes nonzero: "rho\<noteq>0 \<or> sigma\<noteq>0"
    and phom: "\<And>d. d\<in>biv_support p \<Longrightarrow> pair_weight rho sigma d=degreeP"
    and qhom: "\<And>e. e\<in>biv_support q \<Longrightarrow> pair_weight rho sigma e=degreeQ"
    and pnonconstant: "\<exists>d\<in>biv_support p. d\<noteq>(0,0)"
    and qnonconstant: "\<exists>e\<in>biv_support q. e\<noteq>(0,0)"
    and p: "p\<noteq>0" and q: "q\<noteq>0"
    and pside: "\<forall>d\<in>biv_support p. pair_grade d\<le>0"
    and qpositive: "\<exists>e\<in>biv_support q. 0<pair_grade e"
  shows "biv_poisson p q\<noteq>0"
proof
  assume bracket: "biv_poisson p q=0"
  have cones: "positive_scalar_cone (convex hull (exponent_point ` biv_support p))=
    positive_scalar_cone (convex hull (exponent_point ` biv_support q))"
    by (rule poisson_homogeneous_support_cones_equal[OF nonzero phom qhom pnonconstant qnonconstant p q bracket])
  obtain e where e: "e\<in>biv_support q" and ep: "0<pair_grade e" using qpositive by blast
  have eh: "exponent_point e\<in>convex hull (exponent_point ` biv_support q)"
    by (rule hull_inc) (use e in auto)
  have ec: "exponent_point e\<in>positive_scalar_cone (convex hull (exponent_point ` biv_support q))"
    using positive_scalar_cone_contains eh by blast
  have bound: "positive_scalar_cone (convex hull (exponent_point ` biv_support p))\<subseteq>{z::real\<times>real. fst z\<le>snd z}"
    by (rule support_cone_grade_nonpositive[OF pside])
  have le: "fst (exponent_point e)\<le>snd (exponent_point e)" using bound cones ec by blast
  have "snd e<fst e" using ep by (simp add: pair_grade_def)
  then have "snd (exponent_point e)<fst (exponent_point e)" by (simp add: exponent_point_def)
  then show False using le by arith
qed

end
