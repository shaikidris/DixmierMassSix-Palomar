theory Carrier_Ordered_Word_Descent
  imports Carrier_Operator_Products "Operator_Word_Span"
begin

context dixmier_carrier_char_zero_embedding
begin

lemma carrier_operator_words:
  assumes G: "G \<subseteq> carrier_weyl E" and w: "w \<in> operator_words G"
  shows "w \<in> carrier_weyl E"
  using w
proof (induction rule: operator_words.induct)
  case (generator w) show ?case by (rule subsetD[OF G generator])
next
  case one show ?case by (rule carrier_weyl_id)
next
  case (comp u v) show ?case by (rule carrier_weyl_comp[OF comp.IH])
qed

theorem carrier_operator_words_lift:
  assumes G: "G \<subseteq> carrier_weyl E"
    and z: "z \<in> operator_words (concrete_base_change f ` G)"
  shows "\<exists>w. w \<in> operator_words G \<and> concrete_base_change f w = z"
  using z
proof (induction rule: operator_words.induct)
  case (generator z)
  then obtain w where w: "w \<in> G" "concrete_base_change f w = z" by blast
  show ?case using operator_words.generator[OF w(1)] w(2) by blast
next
  case one
  show ?case by (intro exI[of _ id] conjI operator_words.one) (simp only: carrier_base_change_id)
next
  case (comp x y)
  obtain u where u: "u \<in> operator_words G" "concrete_base_change f u = x"
    using comp.IH(1) by blast
  obtain v where v: "v \<in> operator_words G" "concrete_base_change f v = y"
    using comp.IH(2) by blast
  have "concrete_base_change f (op_comp u v) = op_comp x y"
    using carrier_base_change_comp[OF carrier_operator_words[OF G u(1)]
        carrier_operator_words[OF G v(1)]] u(2) v(2) by simp
  then show ?case using operator_words.comp[OF u(1) v(1)] by blast
qed

theorem carrier_adjoin_mem_descends:
  assumes G: "G \<subseteq> carrier_weyl E" and T: "T \<in> carrier_weyl E"
    and generated: "concrete_base_change f T \<in> op_adjoin (concrete_base_change f ` G)"
  shows "T \<in> op_adjoin G"
proof -
  have image_in_weyl: "concrete_base_change f ` G \<subseteq> weyl_algebra"
    using G by (auto intro: carrier_base_change_in_weyl dest: carrier_weyl_in_weyl)
  have span: "concrete_base_change f T \<in> operator_span (operator_words (concrete_base_change f ` G))"
    using generated op_adjoin_eq_word_span[OF image_in_weyl] by simp
  obtain A a where finite_A: "finite A" and words_A: "A \<subseteq> operator_words (concrete_base_change f ` G)"
    and expansion: "(\<Sum>z\<in>A. operator_scale (a z) z) = concrete_base_change f T"
    using span unfolding operator_span_explicit by blast
  let ?w = "\<lambda>z. SOME w. w \<in> operator_words G \<and> concrete_base_change f w = z"
  have choice: "?w z \<in> operator_words G \<and> concrete_base_change f (?w z) = z"
    if "z \<in> A" for z
  proof -
    have zin: "z \<in> operator_words (concrete_base_change f ` G)" using words_A that by blast
    have ex: "\<exists>w. w \<in> operator_words G \<and> concrete_base_change f w = z"
      by (rule carrier_operator_words_lift[OF G zin])
    show ?thesis by (rule someI_ex[OF ex])
  qed
  have source_members: "?w z \<in> carrier_weyl E" if "z \<in> A" for z
    by (rule carrier_operator_words[OF G]) (use choice[OF that] in blast)
  have maps: "concrete_base_change f (?w z) = z" if "z \<in> A" for z
    using choice[OF that] by blast
  have equality: "(\<Sum>z\<in>A. (\<lambda>p. smult (a z) (concrete_base_change f (?w z) p))) = concrete_base_change f T"
  proof -
    have "(\<Sum>z\<in>A. (\<lambda>p. smult (a z) (concrete_base_change f (?w z) p))) =
        (\<Sum>z\<in>A. operator_scale (a z) z)"
      by (intro sum.cong refl) (simp add: maps operator_scale_def)
    also have "\<dots> = concrete_base_change f T" by (rule expansion)
    finally show ?thesis .
  qed
  have solution: "\<exists>a :: 'l poly_operator \<Rightarrow> 'l.
    (\<Sum>z\<in>A. (\<lambda>p. smult (a z) (concrete_base_change f (?w z) p))) = concrete_base_change f T"
    using equality by blast
  obtain b where recovered: "(\<Sum>z\<in>A. (\<lambda>p. smult (b z) (?w z p))) = T"
    using carrier_finite_weyl_span_descends[OF finite_A source_members T solution] by blast
  have "(\<Sum>z\<in>A. (\<lambda>p. smult (b z) (?w z p))) \<in> op_adjoin G"
  proof (rule op_adjoin_sum)
    fix z assume "z \<in> A"
    then have "?w z \<in> operator_words G" using choice by blast
    then show "(\<lambda>p. smult (b z) (?w z p)) \<in> op_adjoin G"
      by (intro op_adjoin_smult operator_words_in_adjoin)
  qed
  then show ?thesis by (simp only: recovered)
qed

text \<open>Only X and Y are descended here. An arbitrary source Weyl operator
need not have coefficients in E; the final K-algebra closure supplies its scalars.\<close>
theorem carrier_adjoin_eq_weyl_descends:
  assumes G: "G \<subseteq> carrier_weyl E"
    and generated: "op_adjoin (concrete_base_change f ` G) = weyl_algebra"
  shows "op_adjoin G = weyl_algebra"
proof -
  have gw: "G \<subseteq> weyl_algebra" using G by (auto dest: carrier_weyl_in_weyl)
  have algebra: "op_subalgebra (op_adjoin G)"
    by (rule op_adjoin_subalgebra) (use gw in \<open>auto intro: weyl_linear\<close>)
  have x: "x_op \<in> op_adjoin G"
  proof (rule carrier_adjoin_mem_descends[OF G carrier_weyl_x])
    show "concrete_base_change f x_op \<in> op_adjoin (concrete_base_change f ` G)"
      by (simp only: generated carrier_base_change_x weyl_x)
  qed
  have y: "y_op \<in> op_adjoin G"
  proof (rule carrier_adjoin_mem_descends[OF G carrier_weyl_y])
    show "concrete_base_change f y_op \<in> op_adjoin (concrete_base_change f ` G)"
      by (simp only: generated carrier_base_change_y weyl_y)
  qed
  show ?thesis by (rule subset_antisym[OF weyl_nested_adjoin[OF gw] weyl_least[OF algebra x y]])
qed

theorem carrier_pair_generation_descends:
  assumes P: "P \<in> carrier_weyl E" and Q: "Q \<in> carrier_weyl E"
    and generated: "op_adjoin {concrete_base_change f P, concrete_base_change f Q} = weyl_algebra"
  shows "op_adjoin {P,Q} = weyl_algebra"
proof (rule carrier_adjoin_eq_weyl_descends)
  show "{P,Q} \<subseteq> carrier_weyl E" using P Q by auto
  show "op_adjoin (concrete_base_change f ` {P,Q}) = weyl_algebra" using generated by simp
qed

end
end
