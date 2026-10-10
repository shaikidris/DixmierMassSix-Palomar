theory Finite_Cut_Word_Span_Recovery
  imports "Polynomial_Finite_Cut_Word_Bounds"
    "Ramified_Filtered_Centralizer_Rank"
begin

lemma finite_cut_image_add:
  assumes l: "0<l" and R: "R\<in>(weyl_algebra::complex poly_operator set)" and S: "S\<in>weyl_algebra"
  shows "finite_cut_image l cuts (R+S)=finite_cut_image l cuts R+finite_cut_image l cuts S"
  by (simp only: finite_cut_image_def polynomial_ramified_lift_add[OF l R S]
    finite_cut_aut_add[OF l polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier])

lemma finite_cut_normal_ordered_word_mem_adjoin:
  "op_comp (P^^i) (Q^^j)\<in>op_adjoin {P,Q}"
  by (intro op_adjoin.comp op_adjoin_power op_adjoin.generator) auto

lemma rectangular_finite_cut_word_span_recovery:
  fixes P Q :: "complex poly_operator"
  assumes l: "0<l" and P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and hp: "p\<in>ramified_operator_vector.span (rectangular_finite_cut_words l cuts P Q N M)"
  shows "\<exists>T. T\<in>weyl_algebra \<and> T\<in>op_adjoin {P,Q} \<and> finite_cut_image l cuts T=p"
proof -
  have nested: "op_adjoin {P,Q}\<subseteq>weyl_algebra"
    by (rule weyl_nested_adjoin) (use P Q in auto)
  have generator: "\<exists>T. T\<in>weyl_algebra \<and> T\<in>op_adjoin {P,Q} \<and> finite_cut_image l cuts T=x"
    if "x\<in>rectangular_finite_cut_words l cuts P Q N M" for x
  proof -
    have member_image: "x\<in>(\<lambda>k. finite_cut_image l cuts (op_comp (P^^fst k) (Q^^snd k))) ` ({..<N}\<times>{..<M})"
      using that by (simp only: rectangular_finite_cut_words_def)
    obtain k where xk: "x=finite_cut_image l cuts (op_comp (P^^fst k) (Q^^snd k))"
      and k: "k\<in>{..<N}\<times>{..<M}"
      by (rule imageE[OF member_image])
    obtain i j where keq: "k=(i,j)" by (cases k) auto
    have x: "x=finite_cut_image l cuts (op_comp (P^^i) (Q^^j))" using xk by (simp only: keq fst_conv snd_conv)
    have mem: "op_comp (P^^i) (Q^^j)\<in>op_adjoin {P,Q}"
      by (rule finite_cut_normal_ordered_word_mem_adjoin)
    show ?thesis by (intro exI[of _ "op_comp (P^^i) (Q^^j)"] conjI)
      (use mem nested x in auto)
  qed
  show ?thesis using hp
  proof (induction rule: ramified_operator_vector.span_induct_alt)
    case base
    have zero_weyl: "(0::complex poly_operator)\<in>weyl_algebra"
      unfolding weyl_algebra_def by (rule op_adjoin_zero)
    have zero_adjoin: "(0::complex poly_operator)\<in>op_adjoin {P,Q}"
      by (rule op_adjoin_zero)
    have zero_symbol: "finite_cut_image l cuts (0::complex poly_operator)=(0::laurent_operator)"
      by (rule finite_cut_image_zero[OF l])
    show ?case by (intro exI[of _ "0::complex poly_operator"] conjI
      zero_weyl zero_adjoin zero_symbol)
  next
    case (step c x y)
    obtain T where T: "T\<in>weyl_algebra" "T\<in>op_adjoin {P,Q}" "finite_cut_image l cuts T=x"
      using generator[OF step.hyps(1)] by blast
    obtain U where U: "U\<in>weyl_algebra" "U\<in>op_adjoin {P,Q}" "finite_cut_image l cuts U=y"
      using step.IH by blast
    let ?S = "\<lambda>r. smult c (T r)"
    have S: "?S\<in>weyl_algebra" by (rule weyl_scalar_closed[OF T(1)])
    have adjoin: "?S+U\<in>op_adjoin {P,Q}"
      by (intro op_adjoin.add op_adjoin_smult T(2) U(2))
    have carrier: "?S+U\<in>weyl_algebra"
      using S U(1) unfolding weyl_algebra_def by (rule op_adjoin.add)
    have symbol: "finite_cut_image l cuts (?S+U)=normal_smult c x+y"
      by (simp only: finite_cut_image_add[OF l S U(1)] finite_cut_image_smult[OF l T(1)]
          T(3) U(3))
    show ?case by (intro exI[of _ "?S+U"] conjI carrier adjoin symbol)
  qed
qed

end
