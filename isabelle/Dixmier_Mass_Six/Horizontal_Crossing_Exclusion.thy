theory Horizontal_Crossing_Exclusion
  imports "Weighted_Newton_Definitions"
begin

text \<open>Exact horizontal crossing argument from source commit
61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff. The horizontal first face is
Y*A(Y), and its mate is X*B(Y). Degree-zero rigidity is proved in this
horizontal specialization by the same univariate product-degree obstruction.
The source scalar-free condition is retained.\<close>

definition horizontal_embedding :: "complex poly\<Rightarrow>complex bivariate" where
  "horizontal_embedding A=map_poly (\<lambda>c. [:c:]) A"

lemma horizontal_embedding_coeff:
  "biv_coeff (horizontal_embedding A) i j=(if i=0 then coeff A j else 0)"
  by (cases i) (simp_all add: horizontal_embedding_def biv_coeff_def coeff_map_poly coeff_pCons)
lemma horizontal_embedding_zero [simp]: "horizontal_embedding 0=0"
  by (simp add: horizontal_embedding_def)
lemma horizontal_embedding_one [simp]: "horizontal_embedding 1=1"
  by (simp add: horizontal_embedding_def)
lemma horizontal_embedding_injective:
  "horizontal_embedding A=horizontal_embedding B \<Longrightarrow> A=B"
proof -
  assume equal: "horizontal_embedding A=horizontal_embedding B"
  show "A=B"
  proof (rule poly_eqI)
    fix j
    have "biv_coeff (horizontal_embedding A) 0 j=biv_coeff (horizontal_embedding B) 0 j"
      using equal by simp
    then show "coeff A j=coeff B j" by (simp add: horizontal_embedding_coeff)
  qed
qed
lemma horizontal_embedding_mult:
  "horizontal_embedding (A*B)=horizontal_embedding A*horizontal_embedding B"
  unfolding horizontal_embedding_def by (rule map_poly_hom_mult[OF constant_polynomial_hom])
lemma horizontal_embedding_X:
  "horizontal_embedding [:0,1:]=biv_monom 1 0 1"
  proof (rule biv_eqI)
  fix i j
  show "biv_coeff (horizontal_embedding [:0,1:]) i j=biv_coeff (biv_monom 1 0 1) i j"
    by (cases j; cases i) (simp_all add: horizontal_embedding_coeff coeff_pCons split: nat.splits)
qed
lemma horizontal_embedding_const:
  "horizontal_embedding [:c:]=biv_monom c 0 0"
  proof (rule biv_eqI)
  fix i j
  show "biv_coeff (horizontal_embedding [:c:]) i j=biv_coeff (biv_monom c 0 0) i j"
    by (cases j) (simp_all add: horizontal_embedding_coeff coeff_pCons)
qed
lemma horizontal_embedding_derivative:
  "biv_dy (horizontal_embedding A)=horizontal_embedding (pderiv A)"
  by (rule biv_eqI) (simp add: biv_dy_coeff horizontal_embedding_coeff coeff_pderiv)
lemma horizontal_embedding_dx_zero:
  "biv_dx (horizontal_embedding A)=0"
  by (rule biv_eqI) (simp add: biv_dx_coeff horizontal_embedding_coeff)
lemma horizontal_x_embedding_coeff:
  "biv_coeff (biv_monom 1 1 0*horizontal_embedding B) i j=(if i=1 then coeff B j else 0)"
  by (cases i) (simp_all add: biv_coeff_def horizontal_embedding_def biv_monom_def monom_0 monom_altdef coeff_map_poly coeff_pCons split: nat.splits)
lemma horizontal_x_embedding_dx:
  "biv_dx (biv_monom 1 1 0*horizontal_embedding B)=horizontal_embedding B"
proof (rule biv_eqI)
  fix i j
  show "biv_coeff (biv_dx (biv_monom 1 1 0*horizontal_embedding B)) i j=
    biv_coeff (horizontal_embedding B) i j"
    by (simp only: biv_dx_coeff horizontal_x_embedding_coeff horizontal_embedding_coeff;
      cases i; simp)
qed

lemma horizontal_coefficient_zero_of_other_x_grade:
  fixes R :: "complex bivariate"
  assumes homogeneous: "\<And>u. u\<in>biv_support R \<Longrightarrow> pair_weight 1 0 u=int a"
    and other: "i\<noteq>a"
  shows "biv_coeff R i j=0"
proof (rule ccontr)
  assume nonzero: "biv_coeff R i j\<noteq>0"
  have support: "(i,j)\<in>biv_support R" using nonzero by (simp add: biv_support_def)
  show False using homogeneous[OF support] other by (simp add: pair_weight_def)
qed

lemma horizontal_scalarfree_face_shape:
  fixes R :: "complex bivariate"
  assumes nonzero: "R\<noteq>0"
    and homogeneous: "\<And>u. u\<in>biv_support R \<Longrightarrow> pair_weight 1 0 u=0"
    and scalar_free: "biv_coeff R 0 0=0"
  shows "\<exists>A::complex poly. A\<noteq>0 \<and> R=biv_monom 1 0 1*horizontal_embedding A"
proof -
  let ?U = "map_poly (\<lambda>p::complex poly. coeff p 0) R"
  have U_coeff: "coeff ?U j=biv_coeff R 0 j" for j
    by (simp add: biv_coeff_def coeff_map_poly)
  have R_embedding: "R=horizontal_embedding ?U"
  proof (rule biv_eqI)
    fix i j
    show "biv_coeff R i j=biv_coeff (horizontal_embedding ?U) i j"
    proof (cases "i=0")
      case True then show ?thesis by (simp add: horizontal_embedding_coeff U_coeff)
    next
      case False
      have zero: "biv_coeff R i j=0"
        by (rule horizontal_coefficient_zero_of_other_x_grade[where a=0, OF _ False])
          (use homogeneous in simp)
      show ?thesis using zero False by (simp add: horizontal_embedding_coeff)
    qed
  qed
  have constant_zero: "coeff ?U 0=0" using scalar_free by (simp add: U_coeff)
  have low_coefficients: "\<forall>k<1. coeff ?U k=0"
    using constant_zero by auto
  have monom_divides: "monom 1 1 dvd ?U"
    by (rule iffD2[OF monom_1_dvd_iff']) (rule low_coefficients)
  have X_divides: "[:0,1:] dvd ?U"
    using monom_divides by (simp only: monom_altdef power_one_right smult_1_left)
  obtain A where factor: "?U=[:0,1:]*A" using X_divides by (auto simp: dvd_def)
  have embedded_factor: "horizontal_embedding ?U=horizontal_embedding ([:0,1:]*A)"
    by (rule arg_cong[OF factor])
  have shape: "R=biv_monom 1 0 1*horizontal_embedding A"
  proof -
    have "R=horizontal_embedding ?U" by (rule R_embedding)
    also have "...=horizontal_embedding ([:0,1:]*A)" by (rule embedded_factor)
    also have "...=biv_monom 1 0 1*horizontal_embedding A"
      by (simp only: horizontal_embedding_mult horizontal_embedding_X)
    finally show ?thesis .
  qed
  have A_nonzero: "A\<noteq>0" using nonzero shape by auto
  show ?thesis using A_nonzero shape by blast
qed

lemma horizontal_mate_face_shape:
  fixes F :: "complex bivariate"
  assumes nonzero: "F\<noteq>0"
    and homogeneous: "\<And>u. u\<in>biv_support F \<Longrightarrow> pair_weight 1 0 u=1"
  shows "\<exists>B::complex poly. B\<noteq>0 \<and> F=biv_monom 1 1 0*horizontal_embedding B"
proof -
  let ?B = "map_poly (\<lambda>p::complex poly. coeff p 1) F"
  have B_coeff: "coeff ?B j=biv_coeff F 1 j" for j by (simp add: biv_coeff_def coeff_map_poly)
  have shape: "F=biv_monom 1 1 0*horizontal_embedding ?B"
  proof (rule biv_eqI)
    fix i j
    show "biv_coeff F i j=biv_coeff (biv_monom 1 1 0*horizontal_embedding ?B) i j"
    proof (cases "i=1")
      case True then show ?thesis by (simp only: horizontal_x_embedding_coeff B_coeff; simp)
    next
      case False
      have zero: "biv_coeff F i j=0"
        by (rule horizontal_coefficient_zero_of_other_x_grade[where a=1, OF _ False])
          (use homogeneous in simp)
      show ?thesis using zero False by (simp only: horizontal_x_embedding_coeff; simp)
    qed
  qed
  have nonzero_B: "?B\<noteq>0" using nonzero shape by auto
  show ?thesis using nonzero_B shape by blast
qed

lemma horizontal_opposite_bases_bracket:
  "biv_poisson (biv_monom 1 0 1*horizontal_embedding A)
      (biv_monom 1 1 0*horizontal_embedding B)=
    horizontal_embedding (pderiv ([:0,1:]*A)*B)"
proof -
  have first: "biv_monom 1 0 1*horizontal_embedding A=horizontal_embedding ([:0,1:]*A)"
    by (simp only: horizontal_embedding_mult horizontal_embedding_X)
  have bracket: "biv_poisson (biv_monom 1 0 1*horizontal_embedding A)
      (biv_monom 1 1 0*horizontal_embedding B)=
    horizontal_embedding (pderiv ([:0,1:]*A))*horizontal_embedding B"
    by (simp only: first biv_poisson_def horizontal_embedding_derivative
      horizontal_embedding_dx_zero horizontal_x_embedding_dx mult_zero_left diff_zero)
  show ?thesis using bracket by (simp only: horizontal_embedding_mult)
qed

lemma horizontal_pair_degrees:
  fixes A B :: "complex poly"
  assumes A: "A\<noteq>0" and B: "B\<noteq>0"
    and bracket: "biv_poisson (biv_monom 1 0 1*horizontal_embedding A)
      (biv_monom 1 1 0*horizontal_embedding B)=1"
  shows "degree A=0 \<and> degree B=0"
proof -
  have embedded: "horizontal_embedding (pderiv ([:0,1:]*A)*B)=horizontal_embedding 1"
    using bracket by (simp only: horizontal_opposite_bases_bracket horizontal_embedding_one)
  have product: "pderiv ([:0,1:]*A)*B=1" by (rule horizontal_embedding_injective[OF embedded])
  have derivative_nonzero: "pderiv ([:0,1:]*A)\<noteq>0" using product by auto
  have product_degree: "degree (pderiv ([:0,1:]*A)*B)=degree (pderiv ([:0,1:]*A))+degree B"
    by (rule degree_mult_eq[OF derivative_nonzero B])
  have degree_sum: "degree (pderiv ([:0,1:]*A))+degree B=0"
    using arg_cong[OF product, of degree] by (simp only: product_degree degree_1)
  have X_nonzero: "([:0,1:]::complex poly)\<noteq>0" by simp
  have X_degree: "degree ([:0,1:]::complex poly)=1" by simp
  have first_degree: "degree ([:0,1:]*A)=1+degree A"
    by (simp only: degree_mult_eq[OF X_nonzero A] X_degree)
  have derivative_degree: "degree (pderiv ([:0,1:]*A))=degree A"
    by (simp only: degree_pderiv first_degree; arith)
  show ?thesis using degree_sum by (simp only: derivative_degree add_is_0)
qed

lemma horizontal_constant_factor_support:
  fixes R :: "complex bivariate" and A :: "complex poly"
  assumes A: "A\<noteq>0" and shape: "R=biv_monom 1 0 1*horizontal_embedding A"
    and degree: "degree A=0"
  shows "biv_support R={(0,1)}"
proof -
  have constant_form: "A=[:coeff A 0:]" using degree by (metis degree_eq_zeroE coeff_pCons_0)
  have coefficient: "coeff A 0\<noteq>0"
  proof
    assume zero_coefficient: "coeff A 0=0"
    have zero_A: "A=0" by (rule trans[OF constant_form]) (simp add: zero_coefficient)
    show False using A zero_A by contradiction
  qed
  have embedding_form: "horizontal_embedding A=horizontal_embedding [:coeff A 0:]"
    by (rule arg_cong[OF constant_form])
  have evaluation: "horizontal_embedding A=biv_monom (coeff A 0) 0 0"
    using embedding_form by (simp only: horizontal_embedding_const)
  have monomial: "R=biv_monom (coeff A 0) 0 1"
    by (simp only: shape evaluation biv_mult_monom; simp)
  show ?thesis using coefficient by (simp add: monomial weighted_support_monom)
qed

lemma horizontal_nonmonomial_face_excludes_bracket_one:
  fixes R F :: "complex bivariate" and ell :: nat
  assumes positive: "0<ell" and primitive: "coprime ell 0"
    and R_homogeneous: "\<And>u. u\<in>biv_support R \<Longrightarrow> pair_weight (int ell) 0 u=0"
    and F_homogeneous: "\<And>u. u\<in>biv_support F \<Longrightarrow> pair_weight (int ell) 0 u=int ell"
    and scalar_free: "biv_coeff R 0 0=0"
    and nonmonomial: "1<card(biv_support R)"
  shows "biv_poisson R F\<noteq>1"
proof
  assume bracket: "biv_poisson R F=1"
  have ell_one: "ell=1" using primitive by simp
  have R_homogeneous_one: "pair_weight 1 0 u=0" if "u\<in>biv_support R" for u
    using R_homogeneous[OF that] ell_one by simp
  have F_homogeneous_one: "pair_weight 1 0 u=1" if "u\<in>biv_support F" for u
    using F_homogeneous[OF that] ell_one by simp
  have R_nonzero: "R\<noteq>0" and F_nonzero: "F\<noteq>0"
    using bracket by (auto simp: biv_poisson_def)
  obtain A where A: "A\<noteq>0" and R_shape: "R=biv_monom 1 0 1*horizontal_embedding A"
    using horizontal_scalarfree_face_shape[OF R_nonzero R_homogeneous_one scalar_free] by blast
  obtain B where B: "B\<noteq>0" and F_shape: "F=biv_monom 1 1 0*horizontal_embedding B"
    using horizontal_mate_face_shape[OF F_nonzero F_homogeneous_one] by blast
  have normalized_bracket: "biv_poisson (biv_monom 1 0 1*horizontal_embedding A)
      (biv_monom 1 1 0*horizontal_embedding B)=1" using bracket by (simp only: R_shape F_shape)
  have A_degree: "degree A=0" using horizontal_pair_degrees[OF A B normalized_bracket] by blast
  have support: "biv_support R={(0,1)}"
    by (rule horizontal_constant_factor_support[OF A R_shape A_degree])
  show False using nonmonomial by (simp add: support)
qed

end
