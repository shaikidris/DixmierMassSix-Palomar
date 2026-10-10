theory Countable_Complex_Root_Avoidance
  imports "HOL-Computational_Algebra.Polynomial" "HOL-Analysis.Continuum_Not_Denumerable"
begin

definition coefficient_polynomials :: "complex set \<Rightarrow> complex poly set" where
  "coefficient_polynomials A = {p. set (coeffs p)\<subseteq>A}"
definition algebraic_root_locus :: "complex set \<Rightarrow> complex set" where
  "algebraic_root_locus A = (\<Union>p\<in>coefficient_polynomials A-{0}. {z. poly p z=0})"
lemma countable_coefficient_polynomials:
  assumes "countable A"
  shows "countable (coefficient_polynomials A)"
proof -
  have sub: "coefficient_polynomials A \<subseteq> Poly ` lists A"
  proof
    fix p assume "p\<in>coefficient_polynomials A"
    then have cp: "coeffs p\<in>lists A" by (auto simp: coefficient_polynomials_def in_lists_conv_set)
    show "p\<in>Poly ` lists A" by (rule image_eqI[where x="coeffs p"]) (use cp in auto)
  qed
  have cnt: "countable (Poly ` lists A)" using assms by simp
  show ?thesis by (rule countable_subset[OF sub cnt])
qed
lemma countable_algebraic_root_locus:
  assumes "countable A"
  shows "countable (algebraic_root_locus A)"
proof -
  have index: "countable (coefficient_polynomials A-{0})"
    using countable_coefficient_polynomials[OF assms] by simp
  have roots: "countable {z. poly p z=0}" if "p\<in>coefficient_polynomials A-{0}" for p
    by (rule countable_finite, rule poly_roots_finite) (use that in auto)
  show ?thesis unfolding algebraic_root_locus_def by (rule countable_UN[OF index roots])
qed
lemma exists_complex_avoiding_countable_coefficients:
  assumes cnt: "countable A"
  shows "\<exists>z::complex. \<forall>p::complex poly. p\<noteq>0 \<longrightarrow> set (coeffs p)\<subseteq>A \<longrightarrow> poly p z\<noteq>0"
proof -
  have count: "countable (algebraic_root_locus A)" by (rule countable_algebraic_root_locus[OF cnt])
  have ne: "algebraic_root_locus A\<noteq>UNIV"
    using count uncountable_UNIV_complex by auto
  obtain z where out: "z\<notin>algebraic_root_locus A" using ne by blast
  show ?thesis by (rule exI[of _ z]) (use out in \<open>auto simp: algebraic_root_locus_def coefficient_polynomials_def\<close>)
qed
lemma coefficient_list_subset_of_all_coefficients:
  assumes "\<And>n. coeff p n\<in>A"
  shows "set (coeffs p)\<subseteq>A"
proof -
  have "range (coeff p)\<subseteq>A" using assms by auto
  then show ?thesis by (simp add: range_coeff)
qed
lemma exists_complex_avoiding_countable_field_coefficients:
  assumes "countable A"
  shows "\<exists>z::complex. \<forall>p::complex poly. p\<noteq>0 \<longrightarrow> (\<forall>n. coeff p n\<in>A) \<longrightarrow> poly p z\<noteq>0"
proof -
  obtain z where avoid: "\<forall>p::complex poly. p\<noteq>0 \<longrightarrow> set (coeffs p)\<subseteq>A \<longrightarrow> poly p z\<noteq>0"
    using exists_complex_avoiding_countable_coefficients[OF assms] by blast
  show ?thesis
  proof (rule exI[of _ z], intro allI impI)
    fix p::"complex poly" assume nz: "p\<noteq>0" and cs: "\<forall>n. coeff p n\<in>A"
    have sub: "set (coeffs p)\<subseteq>A"
      by (rule coefficient_list_subset_of_all_coefficients) (use cs in auto)
    show "poly p z\<noteq>0" using avoid[rule_format, OF nz sub] .
  qed
qed

end
