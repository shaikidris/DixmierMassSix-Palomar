theory Normal_Order_Span
  imports Weyl_Adjunction
begin

definition normal_monomial :: "nat \<Rightarrow> nat \<Rightarrow> 'a::field poly_operator" where
  "normal_monomial a b = op_comp (x_op ^^ a) (y_op ^^ b)"
lemma normal_monomial_apply:
  "normal_monomial a b p = [:0, 1:] ^ a * (pderiv ^^ b) p"
  by (simp add: normal_monomial_def op_comp_def x_op_power_apply y_op_def)
lemma normal_monomial_linear: "poly_linear (normal_monomial a b)"
  unfolding normal_monomial_def by (intro poly_linear_comp poly_linear_power) simp_all
lemma normal_monomial_zero [simp]: "normal_monomial 0 0 = id"
  by (simp add: normal_monomial_def)
lemma x_normal_monomial:
  "op_comp x_op (normal_monomial a b) = normal_monomial (Suc a) b"
  by (rule ext) (simp add: op_comp_def normal_monomial_apply x_op_def algebra_simps)
lemma y_normal_monomial:
  "op_comp y_op (normal_monomial a b) =
    (\<lambda>p. smult (of_nat a) (normal_monomial (a - 1) b p)) + normal_monomial a (Suc b)"
  by (rule ext)
    (simp add: op_comp_def normal_monomial_apply y_op_def pderiv_mult
      pderiv_power pderiv_pCons algebra_simps)

inductive_set normal_span :: "'a::field poly_operator set" where
  monomial: "normal_monomial a b \<in> normal_span"
| zero: "0 \<in> normal_span"
| add: "T \<in> normal_span \<Longrightarrow> U \<in> normal_span \<Longrightarrow> T + U \<in> normal_span"
| smult: "T \<in> normal_span \<Longrightarrow> (\<lambda>p. smult c (T p)) \<in> normal_span"

lemma normal_span_linear:
  "T \<in> normal_span \<Longrightarrow> poly_linear T"
  by (induction rule: normal_span.induct)
    (blast intro: normal_monomial_linear poly_linear_zero poly_linear_add poly_linear_smult)+
lemma normal_span_id: "id \<in> normal_span"
  using normal_span.monomial[of 0 0] by simp
lemma normal_span_scalar: "op_scalar c \<in> normal_span"
  using normal_span.smult[OF normal_span_id, of c]
  by (simp add: op_scalar_def)
lemma normal_span_diff:
  assumes "T \<in> normal_span" "U \<in> normal_span"
  shows "T - U \<in> normal_span"
proof -
  have "(\<lambda>p. smult (-1) (U p)) = - U" by (rule ext) simp
  then have "- U \<in> normal_span" using normal_span.smult[OF assms(2), of "-1"] by simp
  then show ?thesis using normal_span.add[OF assms(1)] by (simp only: diff_conv_add_uminus)
qed
lemma normal_span_left_x:
  "T \<in> normal_span \<Longrightarrow> op_comp x_op T \<in> normal_span"
proof (induction rule: normal_span.induct)
  case (monomial a b) then show ?case by (simp add: x_normal_monomial normal_span.monomial)
next
  case zero then show ?case by (simp add: op_comp_def x_op_def zero_fun_def[symmetric] normal_span.zero)
next
  case (add T U)
  then show ?case using op_comp_add_right[OF poly_linear_x, of T U]
    by (metis normal_span.add)
next
  case (smult T c)
  have "op_comp x_op (\<lambda>p. smult c (T p)) = (\<lambda>p. smult c (op_comp x_op T p))"
    by (rule ext) (simp add: op_comp_def x_op_def)
  then show ?case using smult by (metis normal_span.smult)
qed
lemma normal_span_left_y:
  "T \<in> normal_span \<Longrightarrow> op_comp y_op T \<in> normal_span"
proof (induction rule: normal_span.induct)
  case (monomial a b)
  show ?case unfolding y_normal_monomial
    by (intro normal_span.add normal_span.smult normal_span.monomial)
next
  case zero then show ?case by (simp add: op_comp_def y_op_def zero_fun_def[symmetric] normal_span.zero)
next
  case (add T U)
  then show ?case using op_comp_add_right[OF poly_linear_y, of T U]
    by (metis normal_span.add)
next
  case (smult T c)
  have "op_comp y_op (\<lambda>p. smult c (T p)) = (\<lambda>p. smult c (op_comp y_op T p))"
    by (rule ext) (simp add: op_comp_def y_op_def pderiv_smult)
  then show ?case using smult by (metis normal_span.smult)
qed

lemma normal_span_left_iterate:
  assumes step: "\<And>U. U \<in> normal_span \<Longrightarrow> op_comp T U \<in> normal_span"
    and "U \<in> normal_span"
  shows "op_comp (T ^^ n) U \<in> normal_span"
proof (induction n)
  case 0 then show ?case using assms(2) by (simp add: id_def[symmetric])
next
  case (Suc n)
  have "op_comp (T ^^ Suc n) U = op_comp T (op_comp (T ^^ n) U)"
    by (simp add: op_comp_def fun_eq_iff)
  then show ?case using step[OF Suc.IH] by (simp only: comp_def)
qed
lemma normal_span_left_monomial:
  assumes "U \<in> normal_span"
  shows "op_comp (normal_monomial a b) U \<in> normal_span"
  unfolding normal_monomial_def op_comp_assoc
  by (intro normal_span_left_iterate normal_span_left_x normal_span_left_y assms)
lemma normal_span_comp:
  assumes "T \<in> normal_span" "U \<in> normal_span"
  shows "op_comp T U \<in> normal_span"
  using assms(1)
proof (induction rule: normal_span.induct)
  case (monomial a b) show ?case by (rule normal_span_left_monomial[OF assms(2)])
next
  case zero
  have "op_comp 0 U = 0" by (rule ext) (simp add: op_comp_def)
  then show ?case by (simp add: zero_fun_def[symmetric] normal_span.zero)
next
  case (add T V)
  then show ?case unfolding op_comp_add_left by (blast intro: normal_span.add)
next
  case (smult T c)
  have "op_comp (\<lambda>p. smult c (T p)) U = (\<lambda>p. smult c (op_comp T U p))"
    by (simp add: op_comp_def)
  then show ?case using smult by (metis normal_span.smult)
qed
lemma normal_span_subalgebra: "op_subalgebra normal_span"
  unfolding op_subalgebra_def
  by (blast intro: normal_span_linear normal_span_scalar normal_span.add normal_span_diff normal_span_comp)
lemma normal_monomial_in_weyl: "normal_monomial a b \<in> weyl_algebra"
  unfolding normal_monomial_def weyl_algebra_def
  by (intro op_adjoin.comp op_adjoin_power op_adjoin.generator) auto
lemma normal_span_le_weyl: "normal_span \<subseteq> weyl_algebra"
proof
  fix T assume "T \<in> normal_span"
  then show "T \<in> weyl_algebra"
  proof (induction rule: normal_span.induct)
    case (monomial a b) show ?case by (rule normal_monomial_in_weyl)
  next
    case zero show ?case unfolding weyl_algebra_def by (rule op_adjoin_zero)
  next
    case (add T U) then show ?case unfolding weyl_algebra_def by (blast intro: op_adjoin.add)
  next
    case (smult T c) then show ?case unfolding weyl_algebra_def by (blast intro: op_adjoin_smult)
  qed
qed
lemma weyl_eq_normal_span: "weyl_algebra = normal_span"
proof (rule subset_antisym)
  show "weyl_algebra \<subseteq> normal_span"
  proof (rule weyl_least[OF normal_span_subalgebra])
    show "x_op \<in> normal_span"
      using normal_span_left_x[OF normal_span_id] by simp
    show "y_op \<in> normal_span"
      using normal_span_left_y[OF normal_span_id] by simp
  qed
  show "normal_span \<subseteq> weyl_algebra" by (rule normal_span_le_weyl)
qed

definition normal_list :: "((nat \<times> nat) \<times> 'a::field) list \<Rightarrow> 'a poly_operator" where
  "normal_list ts = (\<lambda>p. sum_list (map (\<lambda>t. smult (snd t)
    (normal_monomial (fst (fst t)) (snd (fst t)) p)) ts))"
lemma normal_list_empty [simp]: "normal_list [] = 0"
  by (rule ext) (simp add: normal_list_def)
lemma normal_list_append:
  "normal_list (ts @ us) = normal_list ts + normal_list us"
  by (rule ext) (simp add: normal_list_def)
lemma normal_list_smult:
  "normal_list (map (\<lambda>t. (fst t, c * snd t)) ts) = (\<lambda>p. smult c (normal_list ts p))"
  by (rule ext) (induction ts; simp add: normal_list_def smult_add_right smult_smult)
lemma normal_span_finite_list:
  "T \<in> normal_span \<Longrightarrow> \<exists>ts. T = normal_list ts"
proof (induction rule: normal_span.induct)
  case (monomial a b)
  have "normal_monomial a b = normal_list [((a,b),1)]"
    by (rule ext) (simp add: normal_list_def)
  then show ?case by blast
next
  case zero
  show ?case by (rule exI[of _ "[]"]) simp
next
  case (add T U)
  then obtain ts us where "T = normal_list ts" "U = normal_list us" by blast
  then show ?case by (rule_tac x="ts @ us" in exI) (simp only: normal_list_append)
next
  case (smult T c)
  then obtain ts where "T = normal_list ts" by blast
  then show ?case by (rule_tac x="map (\<lambda>t. (fst t, c * snd t)) ts" in exI)
    (simp only: normal_list_smult)
qed
lemma weyl_finite_normal_expansion:
  "T \<in> weyl_algebra \<Longrightarrow> \<exists>ts. T = normal_list ts"
  unfolding weyl_eq_normal_span by (rule normal_span_finite_list)

end
