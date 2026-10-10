theory GGV_Grade_Normalization
  imports "Weyl_Statement_Interfaces"
    "Generator_Centralizer"
begin

text \<open>Local scalar-normalization continuation; no terminal GGV grade-field claim is made. Source pin:
61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff.
Only scalar-normalization and generated-algebra facts whose prerequisites
already have native interfaces are included. No grade-field claim is made.\<close>

lemma adjoin_eq_top_of_xy_mem:
  fixes S :: "'k::field poly_operator set"
  assumes "S \<subseteq> weyl_algebra" "op_subalgebra S"
    "x_op \<in> S" "y_op \<in> S"
  shows "S = weyl_algebra"
  using assms weyl_least by blast

definition pbw_constant :: "complex poly_operator \<Rightarrow> complex" where
  "pbw_constant T = biv_coeff (pbw_symbol T) 0 0"

definition remove_pbw_constant :: "complex poly_operator \<Rightarrow> complex poly_operator" where
  "remove_pbw_constant T = T - op_scalar (pbw_constant T)"

lemma grade_scalar_carrier:
  "op_scalar c \<in> (weyl_algebra :: 'k::field poly_operator set)"
  unfolding weyl_algebra_def by (rule op_adjoin.scalar)

lemma remove_pbw_constant_carrier:
  "T \<in> weyl_algebra \<Longrightarrow> remove_pbw_constant T \<in> weyl_algebra"
  unfolding remove_pbw_constant_def weyl_algebra_def
  by (rule op_adjoin.diff) (auto intro: op_adjoin.scalar)

lemma grade_symbol_scalar:
  "pbw_symbol (op_scalar c :: 'k::field_char_0 poly_operator) = biv_monom c 0 0"
proof -
  have ident: "pbw_symbol (id :: 'k poly_operator) = biv_monom 1 0 0"
    using pbw_symbol_normal_monomial[of 0 0, where 'a='k]
    by (simp add: normal_monomial_def)
  have "pbw_symbol (op_scalar c :: 'k poly_operator) = smult [:c:] (pbw_symbol id)"
    using weyl_symbol_smult[where T="id :: 'k poly_operator" and c=c]
    by (simp add: weyl_algebra_def op_scalar_def)
  also have "... = biv_monom c 0 0"
    by (simp add: ident biv_monom_def monom_0)
  finally show ?thesis .
qed

lemma symbol_remove_pbw_constant:
  assumes "T \<in> weyl_algebra"
  shows "pbw_symbol (remove_pbw_constant T) =
    pbw_symbol T - biv_monom (pbw_constant T) 0 0"
  unfolding remove_pbw_constant_def
  by (simp only: weyl_symbol_sub[OF assms grade_scalar_carrier] grade_symbol_scalar)

lemma remove_pbw_constant_scalar_free:
  assumes "T \<in> weyl_algebra"
  shows "(0,0) \<notin> biv_support (pbw_symbol (remove_pbw_constant T))"
  by (simp add: symbol_remove_pbw_constant[OF assms] biv_support_def pbw_constant_def)

lemma remove_pbw_constant_coeff_of_ne_zero:
  assumes "T \<in> weyl_algebra" "(i,j) \<noteq> (0,0)"
  shows "biv_coeff (pbw_symbol (remove_pbw_constant T)) i j =
    biv_coeff (pbw_symbol T) i j"
  using assms(2) by (auto simp: symbol_remove_pbw_constant[OF assms(1)])

lemma remove_pbw_constant_support_iff:
  assumes "T \<in> weyl_algebra" "u \<noteq> (0,0)"
  shows "u \<in> biv_support (pbw_symbol (remove_pbw_constant T)) \<longleftrightarrow>
    u \<in> biv_support (pbw_symbol T)"
  using remove_pbw_constant_coeff_of_ne_zero[OF assms(1), of "fst u" "snd u"] assms(2)
  by (simp add: biv_support_def)

lemma remove_pbw_constant_preserves_nonpositive_grades:
  assumes T: "T \<in> weyl_algebra"
    and side: "\<And>u. u \<in> biv_support (pbw_symbol T) \<Longrightarrow> pair_grade u \<le> 0"
    and mem: "u \<in> biv_support (pbw_symbol (remove_pbw_constant T))"
  shows "pair_grade u \<le> 0"
proof -
  have nz: "u \<noteq> (0,0)" using mem remove_pbw_constant_scalar_free[OF T] by blast
  have "u \<in> biv_support (pbw_symbol T)"
    using mem remove_pbw_constant_support_iff[OF T nz] by simp
  then show ?thesis by (rule side)
qed

lemma grade_linear_subtract:
  assumes "poly_linear T"
  shows "T (p - q) = T p - T q"
proof -
  have neg: "T (-q) = - T q"
    proof -
    have "T (smult (-1) q) = smult (-1) (T q)"
      using assms unfolding poly_linear_def by blast
    then show ?thesis by (simp only: smult_minus_left smult_1_left)
  qed
  show ?thesis using assms neg unfolding poly_linear_def
    by (metis diff_conv_add_uminus)
qed

lemma grade_linear_smult:
  "poly_linear T \<Longrightarrow> T (smult c p) = smult c (T p)"
  by (simp add: poly_linear_def)

lemma remove_pbw_constant_exact_pair:
  assumes P: "P \<in> weyl_algebra" and Q: "Q \<in> weyl_algebra"
    and exact: "op_comp Q P - op_comp P Q = id"
  shows "op_comp (remove_pbw_constant Q) (remove_pbw_constant P) -
    op_comp (remove_pbw_constant P) (remove_pbw_constant Q) = id"
proof -
  have pl: "poly_linear P" and ql: "poly_linear Q"
    using P Q by (auto intro: weyl_linear)
  have eq: "op_comp (remove_pbw_constant Q) (remove_pbw_constant P) -
      op_comp (remove_pbw_constant P) (remove_pbw_constant Q) = op_comp Q P - op_comp P Q"
    by (rule ext) (use pl ql in \<open>auto simp: remove_pbw_constant_def op_comp_def
      op_scalar_def grade_linear_subtract[OF pl] grade_linear_subtract[OF ql]
      grade_linear_smult[OF pl] grade_linear_smult[OF ql] smult_diff_right smult_smult algebra_simps\<close>)
  show ?thesis using eq exact by simp
qed

lemma generation_of_remove_pbw_constant_generation:
  assumes P: "P \<in> weyl_algebra" and Q: "Q \<in> weyl_algebra"
    and gen: "op_adjoin {remove_pbw_constant P,remove_pbw_constant Q} = weyl_algebra"
  shows "op_adjoin {P,Q} = weyl_algebra"
proof -
  have norm: "remove_pbw_constant T \<in> op_adjoin {P,Q}" if "T \<in> {P,Q}" for T
    unfolding remove_pbw_constant_def
    by (rule op_adjoin.diff) (use that in \<open>auto intro: op_adjoin.generator op_adjoin.scalar\<close>)
  have lower: "op_adjoin {remove_pbw_constant P,remove_pbw_constant Q} \<subseteq> op_adjoin {P,Q}"
    by (rule op_adjoin_least) (use norm P Q in \<open>auto intro: op_adjoin_subalgebra weyl_linear\<close>)
  have upper: "op_adjoin {P,Q} \<subseteq> weyl_algebra"
    by (rule weyl_nested_adjoin) (use P Q in auto)
  show ?thesis using lower upper gen by blast
qed

lemma scalar_free_operator_without_nonconstant_is_zero:
  fixes T :: "complex poly_operator"
  assumes T: "T \<in> weyl_algebra"
    and scalar: "(0,0) \<notin> biv_support (pbw_symbol T)"
    and empty: "\<not>(\<exists>u\<in>biv_support (pbw_symbol T). u \<noteq> (0,0))"
  shows "T = 0"
proof -
  have coeff: "biv_coeff (pbw_symbol T) i j = 0" for i j
    using scalar empty by (auto simp: biv_support_def)
  have sym: "pbw_symbol T = 0" by (rule biv_eqI) (simp add: coeff)
  have zero: "(0 :: complex poly_operator) \<in> weyl_algebra"
    by (simp add: weyl_algebra_def)
  show ?thesis by (rule weyl_symbol_injective[OF T zero]) (simp add: sym)
qed

lemma scalar_free_exact_pair_left_nonconstant:
  fixes P Q :: "complex poly_operator"
  assumes P: "P \<in> weyl_algebra" and Q: "Q \<in> weyl_algebra"
    and exact: "op_comp Q P - op_comp P Q = id"
    and scalar: "(0,0) \<notin> biv_support (pbw_symbol P)"
  shows "\<exists>u\<in>biv_support (pbw_symbol P). u \<noteq> (0,0)"
proof (rule ccontr)
  assume empty: "\<not>(\<exists>u\<in>biv_support (pbw_symbol P). u \<noteq> (0,0))"
  have Pzero: "P = 0" by (rule scalar_free_operator_without_nonconstant_is_zero[OF P scalar empty])
  have "(0 :: complex poly) = 1"
    using fun_cong[OF exact, of 1] poly_linear_zero_image[OF weyl_linear[OF Q]]
    by (simp add: Pzero op_comp_def)
  then show False by simp
qed

lemma scalar_free_exact_pair_right_nonconstant:
  fixes P Q :: "complex poly_operator"
  assumes P: "P \<in> weyl_algebra" and Q: "Q \<in> weyl_algebra"
    and exact: "op_comp Q P - op_comp P Q = id"
    and scalar: "(0,0) \<notin> biv_support (pbw_symbol Q)"
  shows "\<exists>u\<in>biv_support (pbw_symbol Q). u \<noteq> (0,0)"
proof (rule ccontr)
  assume empty: "\<not>(\<exists>u\<in>biv_support (pbw_symbol Q). u \<noteq> (0,0))"
  have Qzero: "Q = 0" by (rule scalar_free_operator_without_nonconstant_is_zero[OF Q scalar empty])
  have "(0 :: complex poly) = 1"
    using fun_cong[OF exact, of 1] poly_linear_zero_image[OF weyl_linear[OF P]]
    by (simp add: Qzero op_comp_def)
  then show False by simp
qed

end
