theory Weyl_Statement_Interfaces
  imports "Weyl_Leading_Forms"
    "Weighted_Newton_Definitions"
begin

definition max_root_mult :: "'a::field poly \<Rightarrow> nat" where
  "max_root_mult p = Max (insert 0 ((\<lambda>a. count (proots p) a) ` set_mset (proots p)))"
lemma root_count_zero_normalized_order:
  "count (proots p) a = (if p=0 then 0 else order a (p::'a::field poly))"
  by (cases "p=0") simp_all
lemma max_root_mult_zero [simp]: "max_root_mult (0::'a::field poly)=0"
  by (simp add: max_root_mult_def)
lemma max_root_mult_constant [simp]: "max_root_mult [:c::'a::field:]=0"
  by (simp add: max_root_mult_def)
lemma max_root_mult_nonzero_order:
  "p\<noteq>0 \<Longrightarrow> max_root_mult (p::'a::field poly)=Max (insert 0 ((\<lambda>a. order a p) ` {a. poly p a=0}))"
  by (simp add: max_root_mult_def)
lemma max_root_mult_root_bound:
  assumes "p\<noteq>0" "poly p a=0"
  shows "order a (p::'a::field poly)\<le>max_root_mult p"
proof -
  have fin: "finite (insert 0 ((\<lambda>x. count (proots p) x) ` set_mset (proots p)))" by simp
  have root: "a\<in>set_mset (proots p)" using assms by simp
  have b: "count (proots p) a\<le>Max (insert 0 ((\<lambda>x. count (proots p) x) ` set_mset (proots p)))"
    by (rule Max_ge[OF fin]) (use root in auto)
  have eq: "order a p=count (proots p) a" by (rule sym, rule count_proots[OF assms(1)])
  show ?thesis unfolding max_root_mult_def eq by (rule b)
qed
lemma max_root_mult_degree_bound:
  "max_root_mult (p::'a::field poly)\<le>degree p"
proof -
  have cb: "count (proots p) a\<le>degree p" for a
    by (rule order_trans[OF count_le_size size_proots_le])
  show ?thesis unfolding max_root_mult_def by (rule Max.boundedI) (use cb in auto)
qed
lemma max_root_mult_linear [simp]: "max_root_mult [:a::'a::field,1:]=1"
  by (simp add: max_root_mult_def)

definition is_counterexample_pair :: "complex poly_operator \<Rightarrow> complex poly_operator \<Rightarrow> bool" where
  "is_counterexample_pair P Q \<longleftrightarrow> P\<in>weyl_algebra \<and> Q\<in>weyl_algebra \<and>
    op_comp Q P-op_comp P Q=id \<and> op_adjoin {P,Q}\<noteq>weyl_algebra"
definition two_root_total_symbol :: "complex poly_operator \<Rightarrow> bool" where
  "two_root_total_symbol T \<longleftrightarrow> poly_linear T \<and>
    (\<exists>lam alpha beta u v. lam\<noteq>0 \<and> alpha\<noteq>0 \<and> beta\<noteq>0 \<and> alpha\<noteq>beta \<and> 1\<le>u \<and> 1\<le>v \<and>
      leading_form 1 1 T=biv_monom lam 0 0*(biv_monom 1 0 1-biv_monom alpha 1 0)^u*
        (biv_monom 1 0 1-biv_monom beta 1 0)^v)"
definition case_alternative :: "complex poly_operator \<Rightarrow> bool" where
  "case_alternative T \<longleftrightarrow> poly_linear T \<and>
    ((\<exists>rho sigma::int. 0<rho \<and> -rho<sigma \<and> sigma\<le>0 \<and>
      gcd (nat (abs rho)) (nat (abs sigma))=1 \<and> strict_crossing rho sigma T) \<or>
      10\<le>weyl_mass T \<or> two_root_total_symbol T)"
lemma counterexample_pair_carrier:
  "is_counterexample_pair P Q \<Longrightarrow> P\<in>weyl_algebra \<and> Q\<in>weyl_algebra"
  by (simp add: is_counterexample_pair_def)
lemma counterexample_pair_source_formula:
  assumes "P\<in>weyl_algebra" "Q\<in>weyl_algebra"
  shows "is_counterexample_pair P Q \<longleftrightarrow> op_comp Q P-op_comp P Q=id \<and> op_adjoin {P,Q}\<noteq>weyl_algebra"
  using assms by (simp add: is_counterexample_pair_def)
lemma pair_generated_inside_weyl:
  assumes "P\<in>weyl_algebra" "Q\<in>weyl_algebra"
  shows "op_adjoin {P,Q}\<subseteq>weyl_algebra"
  by (rule op_adjoin_least[OF _ weyl_subalgebra]) (use assms in auto)
lemma generators_not_counterexample:
  "\<not>is_counterexample_pair x_op y_op"
  by (simp add: is_counterexample_pair_def weyl_algebra_def)
lemma two_root_total_symbol_source_formula:
  assumes "poly_linear T"
  shows "two_root_total_symbol T \<longleftrightarrow>
    (\<exists>lam alpha beta u v. lam\<noteq>0 \<and> alpha\<noteq>0 \<and> beta\<noteq>0 \<and> alpha\<noteq>beta \<and> 1\<le>u \<and> 1\<le>v \<and>
      leading_form 1 1 T=biv_monom lam 0 0*(biv_monom 1 0 1-biv_monom alpha 1 0)^u*
        (biv_monom 1 0 1-biv_monom beta 1 0)^v)"
  using assms by (simp only: two_root_total_symbol_def simp_thms)
lemma case_alternative_source_formula:
  assumes "poly_linear T"
  shows "case_alternative T \<longleftrightarrow>
    ((\<exists>rho sigma::int. 0<rho \<and> -rho<sigma \<and> sigma\<le>0 \<and>
      gcd (nat (abs rho)) (nat (abs sigma))=1 \<and> strict_crossing rho sigma T) \<or>
      10\<le>weyl_mass T \<or> two_root_total_symbol T)"
  using assms by (simp only: case_alternative_def simp_thms)
lemma statement_operator_domains:
  "two_root_total_symbol T \<Longrightarrow> poly_linear T"
  "case_alternative T \<Longrightarrow> poly_linear T"
  by (simp_all add: two_root_total_symbol_def case_alternative_def)
end
