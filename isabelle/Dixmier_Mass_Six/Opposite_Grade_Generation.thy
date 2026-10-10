theory Opposite_Grade_Generation
  imports "Opposite_Grade_Commutator"
    "Opposite_Grade_Projection"
    "GGV_Grade_Normalization"
begin

text \<open>Native formalization of the OppositeGradeSlice
and PureGradeGeneration declarations at source commit
61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff. The source field is complex;
the full mate has no support, order, degree, or mass restriction.\<close>

lemma opposite_grade_homogeneous_pair_reduction:
  fixes P Q :: "complex poly_operator"
  assumes P: "P \<in> weyl_algebra" and Q: "Q \<in> weyl_algebra"
    and positive: "0<k"
    and grade: "\<And>u. u \<in> biv_support (pbw_symbol P) \<Longrightarrow> pair_grade u = -int k"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "\<exists>S\<in>weyl_algebra. \<exists>f g::complex poly.
    P=op_comp (op_poly_eval euler_yx f) (y_op ^^ k) \<and>
    S=op_comp (op_poly_eval euler_yx g) (x_op ^^ k) \<and>
    k=1 \<and> degree f=0 \<and> degree g=0 \<and>
    op_comp (Q-S) P-op_comp P (Q-S)=0"
proof -
  obtain S where S: "S \<in> weyl_algebra"
    and sg: "\<And>u. u \<in> biv_support (pbw_symbol S) \<Longrightarrow> pair_grade u=int k"
    and top_exact: "op_comp S P-op_comp P S=id"
    and tail: "op_comp (Q-S) P-op_comp P (Q-S)=0"
    using opposite_grade_projection_is_exact_mate[OF P Q grade exact] by blast
  obtain f g where Pf: "P=op_comp (op_poly_eval euler_yx f) (y_op ^^ k)"
    and Sg: "S=op_comp (op_poly_eval euler_yx g) (x_op ^^ k)"
    and k_one: "k=1" and f_degree: "degree f=0" and g_degree: "degree g=0"
    using opposite_grade_exact_pair_forces_generator_forms[OF P S positive grade sg top_exact] by blast
  show ?thesis by (rule bexI[of _ S], rule exI[of _ f], rule exI[of _ g])
    (use S Pf Sg k_one f_degree g_degree tail in auto)
qed

lemma grade_generation_identity_nonzero:
  "(id :: complex poly_operator) \<noteq> 0"
proof
  assume equal: "(id :: complex poly_operator)=0"
  have "(1::complex poly)=0" using fun_cong[OF equal, of 1] by simp
  then show False by simp
qed

lemma grade_generation_constant_polynomial:
  "degree f=0 \<Longrightarrow> f=[:coeff f 0:]"
  for f :: "'k::field poly"
  by (metis degree_eq_zeroE coeff_pCons_0)

lemma opposite_grade_generator_slice:
  fixes P Q :: "complex poly_operator"
  assumes P: "P \<in> weyl_algebra" and Q: "Q \<in> weyl_algebra"
    and positive: "0<k"
    and grade: "\<And>u. u \<in> biv_support (pbw_symbol P) \<Longrightarrow> pair_grade u = -int k"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "\<exists>S\<in>weyl_algebra. \<exists>a b::complex.
    P=(\<lambda>p. smult a (y_op p)) \<and>
    S=(\<lambda>p. smult b (x_op p)) \<and>
    op_comp S P-op_comp P S=id \<and> k=1 \<and> a\<noteq>0 \<and>
    op_comp (Q-S) y_op-op_comp y_op (Q-S)=0"
proof -
  obtain S where S: "S \<in> weyl_algebra"
    and sg: "\<And>u. u \<in> biv_support (pbw_symbol S) \<Longrightarrow> pair_grade u=int k"
    and top_exact: "op_comp S P-op_comp P S=id"
    and tail: "op_comp (Q-S) P-op_comp P (Q-S)=0"
    using opposite_grade_projection_is_exact_mate[OF P Q grade exact] by blast
  obtain f g where Pf: "P=op_comp (op_poly_eval euler_yx f) (y_op ^^ k)"
    and Sg: "S=op_comp (op_poly_eval euler_yx g) (x_op ^^ k)"
    and k_one: "k=1" and f_degree: "degree f=0" and g_degree: "degree g=0"
    using opposite_grade_exact_pair_forces_generator_forms[OF P S positive grade sg top_exact] by blast
  let ?a = "coeff f 0"
  let ?b = "coeff g 0"
  have eval_f: "op_poly_eval euler_yx f=op_scalar ?a"
    using arg_cong[OF grade_generation_constant_polynomial[OF f_degree], of "op_poly_eval euler_yx"]
    by (simp only: op_poly_eval_const[OF euler_yx_linear])
  have eval_g: "op_poly_eval euler_yx g=op_scalar ?b"
    using arg_cong[OF grade_generation_constant_polynomial[OF g_degree], of "op_poly_eval euler_yx"]
    by (simp only: op_poly_eval_const[OF euler_yx_linear])
  have P_scalar: "P=(\<lambda>p. smult ?a (y_op p))"
    using Pf by (simp add: eval_f k_one op_comp_def op_scalar_def)
  have S_scalar: "S=(\<lambda>p. smult ?b (x_op p))"
    using Sg by (simp add: eval_g k_one op_comp_def op_scalar_def)
  have a_nonzero: "?a\<noteq>0"
  proof
    assume zero: "?a=0"
    have P_zero: "P=0" using P_scalar zero by (simp add: fun_eq_iff)
    have "(id::complex poly_operator)=0"
      using exact poly_linear_zero_image[OF weyl_linear[OF Q]]
      by (simp add: P_zero op_comp_def fun_eq_iff)
    then show False using grade_generation_identity_nonzero by contradiction
  qed
  have tail_carrier: "Q-S \<in> weyl_algebra" by (rule opposite_weyl_diff[OF Q S])
  have tail_linear: "poly_linear (Q-S)" by (rule weyl_linear[OF tail_carrier])
  have tail_y: "op_comp (Q-S) y_op-op_comp y_op (Q-S)=0"
  proof (rule ext)
    fix p
    have scaled: "smult ?a ((Q-S) (y_op p)-y_op ((Q-S) p))=0"
      using fun_cong[OF tail, of p] tail_linear
      by (simp add: P_scalar op_comp_def poly_linear_def smult_diff_right)
    have "(Q-S) (y_op p)-y_op ((Q-S) p)=0"
      using scaled a_nonzero by simp
    then show "(op_comp (Q-S) y_op-op_comp y_op (Q-S)) p=0 p"
      by (simp add: op_comp_def)
  qed
  show ?thesis by (rule bexI[of _ S], rule exI[of _ ?a], rule exI[of _ ?b])
    (use S P_scalar S_scalar top_exact k_one a_nonzero tail_y in auto)
qed

lemma pure_negative_grade_exact_pair_generates:
  fixes P Q :: "complex poly_operator"
  assumes P: "P \<in> weyl_algebra" and Q: "Q \<in> weyl_algebra"
    and positive: "0<k"
    and grade: "\<And>u. u \<in> biv_support (pbw_symbol P) \<Longrightarrow> pair_grade u = -int k"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "op_adjoin {P,Q}=weyl_algebra"
proof -
  obtain S a b where S: "S \<in> weyl_algebra"
    and P_scalar: "P=(\<lambda>p. smult a (y_op p))"
    and S_scalar: "S=(\<lambda>p. smult b (x_op p))"
    and top_exact: "op_comp S P-op_comp P S=id"
    and a_nonzero: "a\<noteq>0"
    and tail_y: "op_comp (Q-S) y_op-op_comp y_op (Q-S)=0"
    using opposite_grade_generator_slice[OF P Q positive grade exact] by blast
  let ?A = "op_adjoin {P,Q}"
  have P_mem: "P \<in> ?A" and Q_mem: "Q \<in> ?A"
    by (auto intro: op_adjoin.generator)
  have b_nonzero: "b\<noteq>0"
  proof
    assume zero: "b=0"
    have S_zero: "S=0" using S_scalar zero by (simp add: fun_eq_iff)
    have "(id::complex poly_operator)=0"
      using top_exact poly_linear_zero_image[OF weyl_linear[OF P]]
      by (simp add: S_zero op_comp_def fun_eq_iff)
    then show False using grade_generation_identity_nonzero by contradiction
  qed
  have y_mem: "y_op \<in> ?A"
  proof -
    have scaled: "(\<lambda>p. smult (inverse a) (P p)) \<in> ?A"
      by (rule op_adjoin_smult[OF P_mem])
    have unscale: "(\<lambda>p. smult (inverse a) (P p))=y_op"
      by (rule ext) (simp add: P_scalar smult_smult a_nonzero)
    show ?thesis using scaled unscale by simp
  qed
  have tail_carrier: "Q-S \<in> weyl_algebra" by (rule opposite_weyl_diff[OF Q S])
  have centralizer_orientation: "op_comp y_op (Q-S)-op_comp (Q-S) y_op=0"
    using tail_y by simp
  have tail_small: "Q-S \<in> op_adjoin {y_op}"
    by (rule mem_adjoin_y_of_commutes_y[OF tail_carrier centralizer_orientation])
  have closed: "op_subalgebra ?A"
    by (rule op_adjoin_subalgebra) (use P Q in \<open>auto intro: weyl_linear\<close>)
  have small_inside: "op_adjoin {y_op} \<subseteq> ?A"
    by (rule op_adjoin_least[OF _ closed]) (use y_mem in auto)
  have tail_mem: "Q-S \<in> ?A" using small_inside tail_small by blast
  have S_mem: "S \<in> ?A"
  proof -
    have "Q-(Q-S) \<in> ?A" by (rule op_adjoin.diff[OF Q_mem tail_mem])
    then show ?thesis by simp
  qed
  have x_mem: "x_op \<in> ?A"
  proof -
    have scaled: "(\<lambda>p. smult (inverse b) (S p)) \<in> ?A"
      by (rule op_adjoin_smult[OF S_mem])
    have unscale: "(\<lambda>p. smult (inverse b) (S p))=x_op"
      by (rule ext) (simp add: S_scalar smult_smult b_nonzero)
    show ?thesis using scaled unscale by simp
  qed
  have inside: "?A \<subseteq> weyl_algebra"
    by (rule weyl_nested_adjoin) (use P Q in auto)
  show ?thesis by (rule adjoin_eq_top_of_xy_mem[OF inside closed x_mem y_mem])
qed

end
