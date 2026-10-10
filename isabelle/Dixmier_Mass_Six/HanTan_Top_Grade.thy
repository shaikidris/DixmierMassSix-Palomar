theory HanTan_Top_Grade
  imports "Top_Grade_Commutator_Coefficients"
    "Pure_Grade_Commutator"
    "Grade_Projection_Adapters"
    "Opposite_Grade_Commutator"
begin

lemma hantan_weyl_neg:
  "T\<in>(weyl_algebra::complex poly_operator set) \<Longrightarrow> -T\<in>weyl_algebra"
  using opposite_weyl_diff[of 0 T] by (simp add: weyl_algebra_def)
lemma hantan_symbol_neg:
  "T\<in>(weyl_algebra::complex poly_operator set) \<Longrightarrow> pbw_symbol (-T)=-pbw_symbol T"
  using weyl_symbol_sub[of 0 T] by (simp add: weyl_algebra_def)
lemma hantan_support_neg:
  "T\<in>(weyl_algebra::complex poly_operator set) \<Longrightarrow> biv_support (pbw_symbol (-T))=biv_support (pbw_symbol T)"
  by (simp add: hantan_symbol_neg biv_support_def biv_coeff_def)
lemma hantan_pbw_coeff_neg:
  "pbw_coeff (-T) i j=-pbw_coeff T i j" for T :: "complex poly_operator"
  using pbw_coeff_diff[of 0 T i j] by (simp add: pbw_coeff_def coeff_poly_def)
lemma hantan_linear_neg_image:
  "poly_linear T \<Longrightarrow> T (-p)=-T p" for T :: "complex poly_operator"
proof -
  assume linear: "poly_linear T"
  have "T (smult (-1) p)=smult (-1) (T p)" using linear unfolding poly_linear_def by blast
  then show ?thesis by simp
qed
lemma hantan_reverse_sign_exact:
  "op_comp P Q-op_comp Q P=id \<Longrightarrow> poly_linear Q \<Longrightarrow>
    op_comp Q (-P)-op_comp (-P) Q=id"
  for P Q :: "complex poly_operator"
  by (intro impI ext) (simp add: op_comp_def hantan_linear_neg_image fun_eq_iff)

lemma exact_pair_excludes_top_grade_minusOne_positive:
  fixes P Q Ptop Qtop :: "complex poly_operator" and j :: nat
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and Ptop: "Ptop\<in>weyl_algebra" and Qtop: "Qtop\<in>weyl_algebra"
    and j: "1<j" and exact: "op_comp Q P-op_comp P Q=id"
    and Pupper: "\<And>u. u\<in>biv_support (pbw_symbol P) \<Longrightarrow> pair_grade u\<le>-1"
    and Qupper: "\<And>u. u\<in>biv_support (pbw_symbol Q) \<Longrightarrow> pair_grade u\<le>int j"
    and Pgrade: "\<And>u. u\<in>biv_support (pbw_symbol Ptop) \<Longrightarrow> pair_grade u=-1"
    and Qgrade: "\<And>u. u\<in>biv_support (pbw_symbol Qtop) \<Longrightarrow> pair_grade u=int j"
    and Pnz: "Ptop\<noteq>0" and Qnz: "Qtop\<noteq>0"
    and Pcoeff: "\<And>a b. pbw_coeff Ptop a b=(if int a-int b=-1 then pbw_coeff P a b else 0)"
    and Qcoeff: "\<And>a b. pbw_coeff Qtop a b=(if int a-int b=int j then pbw_coeff Q a b else 0)"
  shows False
proof -
  let ?C = "op_comp Qtop Ptop-op_comp Ptop Qtop"
  have positive: "0<j" using j by arith
  have nonzero: "?C\<noteq>0"
    by (rule pureGrade_minusOne_positive_commutator_ne_zero[OF Ptop Qtop positive Pnz Qnz Pgrade Qgrade])
  have QP: "op_comp Qtop Ptop\<in>weyl_algebra" by (rule opposite_weyl_comp[OF Qtop Ptop])
  have PQ: "op_comp Ptop Qtop\<in>weyl_algebra" by (rule opposite_weyl_comp[OF Ptop Qtop])
  have C: "?C\<in>weyl_algebra" by (rule opposite_weyl_diff[OF QP PQ])
  have qpg: "pair_grade u=-1+int j" if "u\<in>biv_support (pbw_symbol (op_comp Qtop Ptop))" for u
    using symbol_mul_grade_eq[OF Qtop Ptop Qgrade Pgrade that] by arith
  have pqg: "pair_grade u=-1+int j" if "u\<in>biv_support (pbw_symbol (op_comp Ptop Qtop))" for u
    using symbol_mul_grade_eq[OF Ptop Qtop Pgrade Qgrade that] by simp
  have grade: "pair_grade u=-1+int j" if "u\<in>biv_support (pbw_symbol ?C)" for u
    by (rule symbol_sub_grade_eq[OF QP PQ qpg pqg that])
  have symbol_nonzero: "pbw_symbol ?C\<noteq>0"
  proof
    assume zero: "pbw_symbol ?C=0"
    have "?C=0" by (rule weyl_symbol_injective[OF C _])
      (use zero in \<open>simp_all add: weyl_algebra_def\<close>)
    then show False using nonzero by contradiction
  qed
  obtain u where u: "u\<in>biv_support (pbw_symbol ?C)"
    using symbol_nonzero by (meson biv_support_empty_iff equals0I)
  have cnz: "pbw_coeff ?C (fst u) (snd u)\<noteq>0"
    using u by (simp add: weyl_symbol_support[OF C] pbw_pair_support_def)
  have ij: "int(fst u)-int(snd u)=-1+int j"
    using grade[OF u] by (simp add: pair_grade_def)
  have comparison: "pbw_coeff (op_comp Q P-op_comp P Q) (fst u) (snd u)=
    pbw_coeff ?C (fst u) (snd u)"
    by (rule top_grade_commutator_coeff_eq[OF P Q Ptop Qtop
      Pupper Qupper Pgrade Qgrade Pcoeff Qcoeff ij])
  have not_origin: "\<not>(fst u=0 \<and> snd u=0)" using ij j by (auto; arith)
  have zero_id: "pbw_coeff (id::complex poly_operator) (fst u) (snd u)=0"
    by (simp add: identity_pbw_coeff not_origin)
  show False using comparison exact zero_id cnz by simp
qed

lemma hantan_adjacent_grade_nonmonomial_impossible:
  fixes P Q :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and Pgrade: "\<And>u. u\<in>biv_support (pbw_symbol P) \<Longrightarrow> pair_grade u=-1"
    and Qgrade: "\<And>u. u\<in>biv_support (pbw_symbol Q) \<Longrightarrow> pair_grade u=1"
    and exact: "op_comp P Q-op_comp Q P=id"
    and nonmonomial: "1<card(biv_support (pbw_symbol P))"
  shows False
proof -
  have NQ: "-Q\<in>weyl_algebra" by (rule hantan_weyl_neg[OF Q])
  have NQgrade: "pair_grade u=int 1" if "u\<in>biv_support (pbw_symbol (-Q))" for u
    using Qgrade that hantan_support_neg[OF Q] by simp
  have reverse: "op_comp (-Q) P-op_comp P (-Q)=id"
  proof -
    have "op_comp (-Q) P-op_comp P (-Q)=op_comp P Q-op_comp Q P"
      by (rule ext) (simp add: op_comp_def hantan_linear_neg_image[OF weyl_linear[OF P]])
    then show ?thesis using exact by simp
  qed
  have one_positive: "0<(1::nat)" by simp
  have Pgrade1: "pair_grade u=-int 1" if "u\<in>biv_support (pbw_symbol P)" for u
    using Pgrade[OF that] by simp
  obtain f g where Pf: "P=op_comp (op_poly_eval euler_yx f) (y_op ^^ 1)"
    and fdeg: "degree f=0"
    using opposite_grade_exact_pair_forces_generator_forms[where k=1,
      OF P NQ one_positive Pgrade1 NQgrade reverse] by auto
  have constant_poly: "f=[:coeff f 0:]" using fdeg by (metis degree_eq_zeroE coeff_pCons_0)
  have eval_f: "op_poly_eval euler_yx f=op_scalar (coeff f 0)"
    using arg_cong[OF constant_poly, of "op_poly_eval euler_yx"]
    by (simp only: op_poly_eval_const[OF euler_yx_linear])
  have scalar: "P=(\<lambda>p. smult (coeff f 0) (y_op p))"
    using Pf by (simp add: eval_f op_comp_def op_scalar_def)
  have y_symbol: "pbw_symbol (y_op::complex poly_operator)=biv_monom 1 0 1"
    using pbw_symbol_normal_monomial[of 0 1, where 'a=complex]
    by (simp add: normal_monomial_def op_comp_def)
  have symbol: "pbw_symbol P=biv_monom (coeff f 0) 0 1"
    using weyl_symbol_smult[OF weyl_y, of "coeff f 0"]
    by (simp add: scalar y_symbol endpoint_biv_smult_monom)
  have card: "card(biv_support (pbw_symbol P))\<le>1"
    by (cases "coeff f 0=0") (simp_all add: symbol weighted_support_monom)
  show False using nonmonomial card by arith
qed

lemma top_grade_source_case_nonmonomial_impossible:
  fixes P Q Ptop Qtop :: "complex poly_operator" and j :: nat
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and Ptop: "Ptop\<in>weyl_algebra" and Qtop: "Qtop\<in>weyl_algebra"
    and j: "0<j" and exact: "op_comp P Q-op_comp Q P=id"
    and Pupper: "\<And>u. u\<in>biv_support (pbw_symbol P) \<Longrightarrow> pair_grade u\<le>-1"
    and Qupper: "\<And>u. u\<in>biv_support (pbw_symbol Q) \<Longrightarrow> pair_grade u\<le>int j"
    and Pgrade: "\<And>u. u\<in>biv_support (pbw_symbol Ptop) \<Longrightarrow> pair_grade u=-1"
    and Qgrade: "\<And>u. u\<in>biv_support (pbw_symbol Qtop) \<Longrightarrow> pair_grade u=int j"
    and Pnz: "Ptop\<noteq>0" and Qnz: "Qtop\<noteq>0"
    and Pcoeff: "\<And>a b. pbw_coeff Ptop a b=(if int a-int b=-1 then pbw_coeff P a b else 0)"
    and Qcoeff: "\<And>a b. pbw_coeff Qtop a b=(if int a-int b=int j then pbw_coeff Q a b else 0)"
    and nonmonomial: "1<card(biv_support (pbw_symbol Ptop))"
  shows False
proof (cases "j=1")
  case True
  have Qupper1: "pair_grade u\<le>1" if "u\<in>biv_support (pbw_symbol Q)" for u
    using Qupper[OF that] True by simp
  have Qgrade1: "pair_grade u=1" if "u\<in>biv_support (pbw_symbol Qtop)" for u
    using Qgrade[OF that] True by simp
  have Qcoeff1: "pbw_coeff Qtop a b=(if int a-int b=1 then pbw_coeff Q a b else 0)" for a b
    using Qcoeff[of a b] True by simp
  have adjacent: "op_comp Ptop Qtop-op_comp Qtop Ptop=id"
    by (rule adjacent_top_grade_commutator_eq_one[OF P Q Ptop Qtop exact
      Pupper Qupper1 Pgrade Qgrade1 Pcoeff Qcoeff1])
  show False by (rule hantan_adjacent_grade_nonmonomial_impossible[OF Ptop Qtop Pgrade Qgrade1 adjacent nonmonomial])
next
  case False
  have greater: "1<j" using j False by arith
  have NP: "-P\<in>weyl_algebra" by (rule hantan_weyl_neg[OF P])
  have NPtop: "-Ptop\<in>weyl_algebra" by (rule hantan_weyl_neg[OF Ptop])
  have NPupper: "pair_grade u\<le>-1" if "u\<in>biv_support (pbw_symbol (-P))" for u
    using Pupper that hantan_support_neg[OF P] by simp
  have NPgrade: "pair_grade u=-1" if "u\<in>biv_support (pbw_symbol (-Ptop))" for u
    using Pgrade that hantan_support_neg[OF Ptop] by simp
  have NPnz: "-Ptop\<noteq>0" using Pnz by simp
  have NPcoeff: "pbw_coeff (-Ptop) a b=(if int a-int b=-1 then pbw_coeff (-P) a b else 0)" for a b
    using Pcoeff[of a b] by (simp add: hantan_pbw_coeff_neg)
  have reverse: "op_comp Q (-P)-op_comp (-P) Q=id"
    by (rule hantan_reverse_sign_exact[OF exact weyl_linear[OF Q]])
  show False by (rule exact_pair_excludes_top_grade_minusOne_positive[OF NP Q NPtop Qtop
    greater reverse NPupper Qupper NPgrade Qgrade NPnz Qnz NPcoeff Qcoeff])
qed

end
