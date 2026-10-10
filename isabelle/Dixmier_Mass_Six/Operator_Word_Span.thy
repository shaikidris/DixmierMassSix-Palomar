theory Operator_Word_Span
  imports "Finite_Weyl_Span_Descent"
begin

definition operator_scale :: "'a::field \<Rightarrow> 'a poly_operator \<Rightarrow> 'a poly_operator" where
  "operator_scale c T = (\<lambda>p. smult c (T p))"

interpretation operator_module: module "operator_scale :: 'a::field \<Rightarrow> 'a poly_operator \<Rightarrow> 'a poly_operator"
  by standard (simp_all add: operator_scale_def fun_eq_iff smult_add_right smult_add_left)

definition operator_span :: "'a::field poly_operator set \<Rightarrow> 'a poly_operator set" where
  "operator_span S = module.span operator_scale S"

lemma operator_span_zero: "0 \<in> operator_span S"
  unfolding operator_span_def by (rule operator_module.span_zero)
lemma operator_span_base: "T \<in> S \<Longrightarrow> T \<in> operator_span S"
  unfolding operator_span_def by (rule operator_module.span_base)
lemma operator_span_add:
  "T \<in> operator_span S \<Longrightarrow> U \<in> operator_span S \<Longrightarrow> T+U \<in> operator_span S"
  unfolding operator_span_def by (rule operator_module.span_add)
lemma operator_span_diff:
  "T \<in> operator_span S \<Longrightarrow> U \<in> operator_span S \<Longrightarrow> T-U \<in> operator_span S"
  unfolding operator_span_def by (rule operator_module.span_diff)
lemma operator_span_scale:
  "T \<in> operator_span S \<Longrightarrow> operator_scale c T \<in> operator_span S"
  unfolding operator_span_def by (rule operator_module.span_scale)
lemma operator_span_induct_alt [consumes 1, case_names base step]:
  assumes "T \<in> operator_span S" "P 0"
    "\<And>c x y. x \<in> S \<Longrightarrow> P y \<Longrightarrow> P (operator_scale c x + y)"
  shows "P T"
  using assms unfolding operator_span_def by (rule operator_module.span_induct_alt)
lemma operator_span_explicit:
  "T \<in> operator_span S \<longleftrightarrow>
    (\<exists>A c. finite A \<and> A \<subseteq> S \<and> (\<Sum>u\<in>A. operator_scale (c u) u) = T)"
  by (auto simp: operator_span_def operator_module.span_explicit eq_commute)

inductive_set operator_words :: "'a::field poly_operator set \<Rightarrow> 'a poly_operator set" for G where
  generator: "T \<in> G \<Longrightarrow> T \<in> operator_words G"
| one: "id \<in> operator_words G"
| comp: "T \<in> operator_words G \<Longrightarrow> U \<in> operator_words G \<Longrightarrow> op_comp T U \<in> operator_words G"

lemma operator_words_in_adjoin:
  "T \<in> operator_words G \<Longrightarrow> T \<in> op_adjoin G"
proof (induction rule: operator_words.induct)
  case (generator T) then show ?case by (rule op_adjoin.generator)
next
  case one show ?case by (rule op_adjoin_id)
next
  case (comp T U) show ?case by (rule op_adjoin.comp[OF comp.IH])
qed
lemma operator_words_in_weyl:
  assumes "G \<subseteq> weyl_algebra" "T \<in> operator_words G"
  shows "T \<in> weyl_algebra"
  using operator_words_in_adjoin[OF assms(2)] weyl_nested_adjoin[OF assms(1)] by blast
lemma operator_words_linear:
  "G \<subseteq> weyl_algebra \<Longrightarrow> T \<in> operator_words G \<Longrightarrow> poly_linear T"
  by (intro weyl_linear operator_words_in_weyl)

lemma operator_scale_linear:
  "poly_linear T \<Longrightarrow> poly_linear (operator_scale c T)"
  unfolding operator_scale_def by (rule poly_linear_smult)
lemma operator_span_linear:
  assumes "T \<in> operator_span S" "\<And>U. U \<in> S \<Longrightarrow> poly_linear U"
  shows "poly_linear T"
  using assms(1)
proof (induction rule: operator_span_induct_alt)
  case base show ?case by (rule poly_linear_zero)
next
  case (step c x y)
  have xlin: "poly_linear x" by (rule assms(2)[OF step.hyps])
  show ?case by (rule poly_linear_add[OF operator_scale_linear[OF xlin] step.IH])
qed

lemma word_comp_zero_left: "op_comp 0 T = 0"
  by (rule ext) (simp add: op_comp_def)
lemma word_comp_zero_right:
  "poly_linear T \<Longrightarrow> op_comp T 0 = 0"
  by (rule ext) (simp add: op_comp_def poly_linear_zero_image)
lemma word_comp_scale_left:
  "op_comp (operator_scale c T) U = operator_scale c (op_comp T U)"
  by (simp add: operator_scale_def op_comp_def)
lemma word_comp_scale_right:
  "poly_linear T \<Longrightarrow> op_comp T (operator_scale c U) = operator_scale c (op_comp T U)"
  by (auto simp: operator_scale_def op_comp_def poly_linear_def)

lemma operator_span_left_word:
  assumes G: "G \<subseteq> weyl_algebra" and W: "W \<in> operator_words G"
    and U: "U \<in> operator_span (operator_words G)"
  shows "op_comp W U \<in> operator_span (operator_words G)"
proof -
  have lin: "poly_linear W" by (rule operator_words_linear[OF G W])
  from U show ?thesis
  proof (induction rule: operator_span_induct_alt)
    case base show ?case by (simp only: word_comp_zero_right[OF lin]) (rule operator_span_zero)
  next
    case (step c x y)
    have left: "op_comp W x \<in> operator_span (operator_words G)"
      by (rule operator_span_base, rule operator_words.comp[OF W step.hyps(1)])
    show ?case
      by (simp only: op_comp_add_right[OF lin] word_comp_scale_right[OF lin])
         (rule operator_span_add[OF operator_span_scale[OF left] step.IH])
  qed
qed

lemma operator_span_words_comp:
  assumes G: "G \<subseteq> weyl_algebra"
    and T: "T \<in> operator_span (operator_words G)"
    and U: "U \<in> operator_span (operator_words G)"
  shows "op_comp T U \<in> operator_span (operator_words G)"
  using T
proof (induction rule: operator_span_induct_alt)
  case base show ?case by (simp only: word_comp_zero_left) (rule operator_span_zero)
next
  case (step c x y)
  have left: "op_comp x U \<in> operator_span (operator_words G)"
    by (rule operator_span_left_word[OF G step.hyps(1) U])
  show ?case
    by (simp only: op_comp_add_left word_comp_scale_left)
       (rule operator_span_add[OF operator_span_scale[OF left] step.IH])
qed

lemma operator_word_span_subalgebra:
  assumes G: "G \<subseteq> weyl_algebra"
  shows "op_subalgebra (operator_span (operator_words G))"
proof -
  have lin: "poly_linear T" if "T \<in> operator_span (operator_words G)" for T
    by (rule operator_span_linear[OF that]) (rule operator_words_linear[OF G])
  have scalar: "op_scalar c \<in> operator_span (operator_words G)" for c
  proof -
    have "operator_scale c id \<in> operator_span (operator_words G)"
      by (intro operator_span_scale operator_span_base operator_words.one)
    then show ?thesis by (simp add: operator_scale_def op_scalar_def)
  qed
  show ?thesis unfolding op_subalgebra_def
  proof (intro conjI ballI allI)
    fix T assume "T \<in> operator_span (operator_words G)"
    then show "poly_linear T" by (rule lin)
  next
    fix c show "op_scalar c \<in> operator_span (operator_words G)" by (rule scalar)
  next
    fix T U
    assume t: "T \<in> operator_span (operator_words G)"
      and u: "U \<in> operator_span (operator_words G)"
    show "T+U \<in> operator_span (operator_words G)" by (rule operator_span_add[OF t u])
  next
    fix T U
    assume t: "T \<in> operator_span (operator_words G)"
      and u: "U \<in> operator_span (operator_words G)"
    show "T-U \<in> operator_span (operator_words G)" by (rule operator_span_diff[OF t u])
  next
    fix T U
    assume t: "T \<in> operator_span (operator_words G)"
      and u: "U \<in> operator_span (operator_words G)"
    show "op_comp T U \<in> operator_span (operator_words G)"
      by (rule operator_span_words_comp[OF G t u])
  qed
qed

lemma operator_span_words_le_adjoin:
  "T \<in> operator_span (operator_words G) \<Longrightarrow> T \<in> op_adjoin G"
proof (induction rule: operator_span_induct_alt)
  case base show ?case by (rule op_adjoin_zero)
next
  case (step c x y)
  have "operator_scale c x \<in> op_adjoin G"
    unfolding operator_scale_def
    by (rule op_adjoin_smult[OF operator_words_in_adjoin[OF step.hyps(1)]])
  then show ?case by (rule op_adjoin.add[OF _ step.IH])
qed

lemma op_adjoin_eq_word_span:
  assumes "G \<subseteq> weyl_algebra"
  shows "op_adjoin G = operator_span (operator_words G)"
proof (rule subset_antisym)
  show "op_adjoin G \<subseteq> operator_span (operator_words G)"
  proof (rule op_adjoin_least)
    show "G \<subseteq> operator_span (operator_words G)"
      by (auto intro: operator_span_base operator_words.generator)
    show "op_subalgebra (operator_span (operator_words G))"
      by (rule operator_word_span_subalgebra[OF assms])
  qed
  show "operator_span (operator_words G) \<subseteq> op_adjoin G"
    by (auto intro: operator_span_words_le_adjoin)
qed

end
