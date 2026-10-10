theory One_Sided_Grade_Basic
 imports "Weighted_Components"
begin
lemma leading_support_subset:
 "biv_support(leading_form rho sigma T)\<subseteq>biv_support(pbw_symbol T)"
 by (auto simp: leading_form_def weighted_component_support)
lemma leading_support_grade_bound:
 assumes "\<forall>u\<in>biv_support(pbw_symbol T). pair_grade u\<le>b"
 shows "\<forall>u\<in>biv_support(leading_form rho sigma T). pair_grade u\<le>b"
 using leading_support_subset assms by blast
lemma pbw_coeff_order_zero_apply_one:
 fixes T :: "complex poly_operator"
 shows "pbw_coeff T i 0=coeff(T 1)i"
 by (simp add: pbw_coeff_def)
lemma nonpositive_grades_apply_one_constant:
 fixes T :: "complex poly_operator"
 assumes T: "T\<in>weyl_algebra" and grades: "\<forall>u\<in>biv_support(pbw_symbol T). pair_grade u\<le>0"
 shows "\<exists>c. T 1=[:c:]"
proof -
 have vanish: "coeff(T 1)i=0" if "0<i" for i
 proof (rule ccontr)
  assume nz: "coeff(T 1)i\<noteq>0"
  have "biv_coeff(pbw_symbol T)i 0\<noteq>0" using nz weyl_symbol_coeff[OF T,of i 0] by (simp add: pbw_coeff_order_zero_apply_one)
  then have mem: "(i,0)\<in>biv_support(pbw_symbol T)" by (simp add: biv_support_def)
  have g: "pair_grade(i,0)\<le>0" by (rule bspec[OF grades mem])
  have "int i\<le>0" using g by (simp add: pair_grade_def)
  with that show False by simp
 qed
 have "T 1=[:coeff(T 1)0:]"
  proof (rule poly_eqI)
  fix i show "coeff(T 1)i=coeff[:coeff(T 1)0:]i" using vanish[of i] by (cases i) simp_all
 qed
 then show ?thesis by blast
qed
lemma no_exact_pair_both_nonpositive:
 fixes P Q :: "complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and gp: "\<forall>u\<in>biv_support(pbw_symbol P). pair_grade u\<le>0"
 and gq: "\<forall>u\<in>biv_support(pbw_symbol Q). pair_grade u\<le>0"
 shows "op_comp Q P-op_comp P Q\<noteq>id"
proof
 assume eq: "op_comp Q P-op_comp P Q=id"
 obtain a where a: "P 1=[:a:]" using nonpositive_grades_apply_one_constant[OF P gp] by blast
 obtain b where b: "Q 1=[:b:]" using nonpositive_grades_apply_one_constant[OF Q gq] by blast
 have lp: "poly_linear P" and lq: "poly_linear Q" using P Q by (auto intro: weyl_linear)
 have pc: "P [:c:]=[:c*a:]" for c
 proof -
  have "P(smult c 1)=smult c(P 1)" using lp by (auto simp only: poly_linear_def)
  then show ?thesis using a by simp
 qed
 have qc: "Q [:c:]=[:c*b:]" for c
 proof -
  have "Q(smult c 1)=smult c(Q 1)" using lq by (auto simp only: poly_linear_def)
  then show ?thesis using b by simp
 qed
 have zero: "(op_comp Q P-op_comp P Q)1=0" by (simp add: op_comp_def a b pc qc mult.commute)
 have one: "(op_comp Q P-op_comp P Q)1=1" using eq by simp
 show False using zero one by simp
qed

lemma derivative_one_control: "(y_op::complex poly_operator)1=0"
 by (simp add: y_op_def)
lemma multiply_one_nonconstant_control: "(x_op::complex poly_operator)1\<noteq>[:c:]"
proof
 assume eq: "(x_op::complex poly_operator)1=[:c:]"
 have "coeff((x_op::complex poly_operator)1)1=coeff[:c:]1" by (rule arg_cong[OF eq])
 then show False by (simp add: x_op_def)
qed
end
