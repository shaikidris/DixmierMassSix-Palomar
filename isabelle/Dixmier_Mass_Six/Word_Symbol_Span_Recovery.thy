theory Word_Symbol_Span_Recovery
  imports Signed_Coordinate_Bounds
begin

lemma normal_ordered_word_mem_adjoin:
  "op_comp (P^^i) (Q^^j)\<in>op_adjoin {P,Q}"
  by (intro op_adjoin.comp op_adjoin_power op_adjoin.generator) auto

lemma rectangular_word_symbol_span_recovery:
  fixes P Q :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and hp: "p\<in>joseph_bivariate.span (rectangular_word_symbols P Q N M)"
  shows "\<exists>T. T\<in>weyl_algebra \<and> T\<in>op_adjoin {P,Q} \<and> pbw_symbol T=p"
proof -
  have nested: "op_adjoin {P,Q}\<subseteq>weyl_algebra"
    by (rule weyl_nested_adjoin) (use P Q in auto)
  have generator: "\<exists>T. T\<in>weyl_algebra \<and> T\<in>op_adjoin {P,Q} \<and> pbw_symbol T=x"
    if "x\<in>rectangular_word_symbols P Q N M" for x
  proof -
    have member_image: "x\<in>(\<lambda>k. pbw_symbol (op_comp (P^^fst k) (Q^^snd k))) ` ({..<N}\<times>{..<M})"
      using that by (simp only: rectangular_word_symbols_def)
    obtain k where xk: "x=pbw_symbol (op_comp (P^^fst k) (Q^^snd k))"
      and k: "k\<in>{..<N}\<times>{..<M}"
      by (rule imageE[OF member_image])
    obtain i j where keq: "k=(i,j)" by (cases k) auto
    have x: "x=pbw_symbol (op_comp (P^^i) (Q^^j))" using xk by (simp only: keq fst_conv snd_conv)
    have mem: "op_comp (P^^i) (Q^^j)\<in>op_adjoin {P,Q}"
      by (rule normal_ordered_word_mem_adjoin)
    show ?thesis by (intro exI[of _ "op_comp (P^^i) (Q^^j)"] conjI)
      (use mem nested x in auto)
  qed
  show ?thesis using hp
  proof (induction rule: joseph_bivariate.span_induct_alt)
    case base
    have zero_weyl: "(0::complex poly_operator)\<in>weyl_algebra"
      unfolding weyl_algebra_def by (rule op_adjoin_zero)
    have zero_adjoin: "(0::complex poly_operator)\<in>op_adjoin {P,Q}"
      by (rule op_adjoin_zero)
    have zero_symbol: "pbw_symbol (0::complex poly_operator)=(0::complex bivariate)"
      by (rule pbw_symbol_zero)
    show ?case by (intro exI[of _ "0::complex poly_operator"] conjI
      zero_weyl zero_adjoin zero_symbol)
  next
    case (step c x y)
    obtain T where T: "T\<in>weyl_algebra" "T\<in>op_adjoin {P,Q}" "pbw_symbol T=x"
      using generator[OF step.hyps(1)] by blast
    obtain U where U: "U\<in>weyl_algebra" "U\<in>op_adjoin {P,Q}" "pbw_symbol U=y"
      using step.IH by blast
    let ?S = "\<lambda>r. smult c (T r)"
    have S: "?S\<in>weyl_algebra" by (rule weyl_scalar_closed[OF T(1)])
    have adjoin: "?S+U\<in>op_adjoin {P,Q}"
      by (intro op_adjoin.add op_adjoin_smult T(2) U(2))
    have carrier: "?S+U\<in>weyl_algebra"
      using S U(1) unfolding weyl_algebra_def by (rule op_adjoin.add)
    have symbol: "pbw_symbol (?S+U)=joseph_biv_scale c x+y"
      by (simp only: weyl_symbol_add[OF S U(1)] weyl_symbol_smult[OF T(1)]
          T(3) U(3) joseph_biv_scale_def)
    show ?case by (intro exI[of _ "?S+U"] conjI carrier adjoin symbol)
  qed
qed

end
