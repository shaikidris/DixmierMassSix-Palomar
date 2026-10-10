theory Weyl_Adjunction
  imports Polynomial_Endomorphisms
begin

text \<open>The generated algebra is a set inside the linear-operator carrier.
The scalar cases include zero and identity. Composition order remains explicit.\<close>

inductive_set op_adjoin :: "'a::field poly_operator set \<Rightarrow> 'a poly_operator set"
  for G where
  generator: "T \<in> G \<Longrightarrow> T \<in> op_adjoin G"
| scalar: "op_scalar c \<in> op_adjoin G"
| add: "T \<in> op_adjoin G \<Longrightarrow> U \<in> op_adjoin G \<Longrightarrow> T + U \<in> op_adjoin G"
| diff: "T \<in> op_adjoin G \<Longrightarrow> U \<in> op_adjoin G \<Longrightarrow> T - U \<in> op_adjoin G"
| comp: "T \<in> op_adjoin G \<Longrightarrow> U \<in> op_adjoin G \<Longrightarrow> op_comp T U \<in> op_adjoin G"

definition op_subalgebra :: "'a::field poly_operator set \<Rightarrow> bool" where
  "op_subalgebra A \<longleftrightarrow>
    (\<forall>T\<in>A. poly_linear T) \<and>
    (\<forall>c. op_scalar c \<in> A) \<and>
    (\<forall>T\<in>A. \<forall>U\<in>A. T + U \<in> A \<and> T - U \<in> A \<and> op_comp T U \<in> A)"

lemma op_adjoin_linear:
  assumes "\<And>T. T \<in> G \<Longrightarrow> poly_linear T" "T \<in> op_adjoin G"
  shows "poly_linear T"
  using assms(2) by (induction rule: op_adjoin.induct)
    (blast intro: assms(1) poly_linear_scalar poly_linear_add poly_linear_diff poly_linear_comp)+
lemma op_adjoin_subalgebra:
  "(\<And>T. T \<in> G \<Longrightarrow> poly_linear T) \<Longrightarrow> op_subalgebra (op_adjoin G)"
  by (auto simp: op_subalgebra_def intro: op_adjoin_linear op_adjoin.intros)
lemma op_adjoin_least:
  assumes "G \<subseteq> A" "op_subalgebra A"
  shows "op_adjoin G \<subseteq> A"
proof
  fix T assume "T \<in> op_adjoin G"
  then show "T \<in> A"
    by (induction rule: op_adjoin.induct) (use assms in \<open>unfold op_subalgebra_def; blast\<close>)+
qed
lemma op_adjoin_mono:
  "G \<subseteq> H \<Longrightarrow> op_adjoin G \<subseteq> op_adjoin H"
proof
  fix T assume GH: "G \<subseteq> H" and "T \<in> op_adjoin G"
  from \<open>T \<in> op_adjoin G\<close> show "T \<in> op_adjoin H"
    by (induction rule: op_adjoin.induct) (use GH in \<open>blast intro: op_adjoin.intros\<close>)+
qed
lemma op_adjoin_zero [simp]: "0 \<in> op_adjoin G"
proof -
  have "op_scalar 0 = (0 :: 'a poly_operator)" by (rule ext) (simp add: op_scalar_def)
  then show ?thesis using op_adjoin.scalar[of 0 G] by metis
qed
lemma op_adjoin_id [simp]: "id \<in> op_adjoin G"
proof -
  have "op_scalar 1 = (id :: 'a poly_operator)" by (rule ext) (simp add: op_scalar_def)
  then show ?thesis using op_adjoin.scalar[of 1 G] by metis
qed
lemma op_adjoin_smult:
  "T \<in> op_adjoin G \<Longrightarrow> (\<lambda>p. smult c (T p)) \<in> op_adjoin G"
  using op_adjoin.comp[OF op_adjoin.scalar, of T G c]
  by (simp add: op_comp_def op_scalar_def)
lemma op_adjoin_sum:
  "(\<And>i. i \<in> I \<Longrightarrow> f i \<in> op_adjoin G) \<Longrightarrow> (\<Sum>i\<in>I. f i) \<in> op_adjoin G"
  by (induction I rule: infinite_finite_induct) (auto intro: op_adjoin.add)
lemma op_adjoin_power:
  "T \<in> op_adjoin G \<Longrightarrow> (T ^^ n) \<in> op_adjoin G"
proof (induction n)
  case 0 then show ?case using op_adjoin_id[of G] by (simp only: funpow_0 id_def[symmetric])
next
  case (Suc n)
  have "(T ^^ Suc n) = op_comp T (T ^^ n)"
    by (simp add: op_comp_def fun_eq_iff)
  then show ?case using Suc by (metis op_adjoin.comp)
qed

definition weyl_algebra :: "'a::field poly_operator set" where
  "weyl_algebra = op_adjoin {x_op, y_op}"
lemma weyl_x [simp]: "x_op \<in> weyl_algebra"
  by (auto simp: weyl_algebra_def intro: op_adjoin.generator)
lemma weyl_y [simp]: "y_op \<in> weyl_algebra"
  by (auto simp: weyl_algebra_def intro: op_adjoin.generator)
lemma weyl_linear:
  "T \<in> weyl_algebra \<Longrightarrow> poly_linear T"
  unfolding weyl_algebra_def by (rule op_adjoin_linear) auto
lemma weyl_subalgebra: "op_subalgebra weyl_algebra"
  by (auto simp: weyl_algebra_def intro: op_adjoin_subalgebra)
lemma weyl_least:
  "op_subalgebra A \<Longrightarrow> x_op \<in> A \<Longrightarrow> y_op \<in> A \<Longrightarrow> weyl_algebra \<subseteq> A"
  unfolding weyl_algebra_def by (rule op_adjoin_least) auto
lemma weyl_nested_adjoin:
  "G \<subseteq> weyl_algebra \<Longrightarrow> op_adjoin G \<subseteq> weyl_algebra"
  by (rule op_adjoin_least) (auto intro: weyl_subalgebra)

end
