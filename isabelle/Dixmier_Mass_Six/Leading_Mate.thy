theory Leading_Mate
  imports "Weyl_Leading_Forms"
begin

lemma symbol_one_A1:
  "pbw_symbol (id :: 'k::field_char_0 poly_operator) = (1 :: 'k bivariate)"
  using pbw_symbol_normal_monomial[of 0 0, where 'a='k]
  by (simp add: normal_monomial_def biv_monom_def monom_0 one_pCons)

lemma vDeg_one_A1:
  "v_degree rho sigma (id :: 'k::field_char_0 poly_operator)=0"
  using v_degree_normal_monomial[of rho sigma 0 0, where 'a='k]
  by (simp add: normal_monomial_def pair_weight_def)

lemma leading_mate_one:
  "leading_form rho sigma (id :: 'k::field_char_0 poly_operator) = (1 :: 'k bivariate)"
  using leading_normal_monomial[of rho sigma 0 0, where 'a='k]
  by (simp add: normal_monomial_def biv_monom_def monom_0 one_pCons)

lemma leadingPoisson_eq_zero_of_exact_commutator:
  fixes P Q :: "'k::field_char_0 poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and weight: "0<rho+sigma" and exact: "op_comp Q P-op_comp P Q=id"
    and target: "0<v_degree rho sigma Q+v_degree rho sigma P-(rho+sigma)"
  shows "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=0"
proof (rule ccontr)
  assume nonzero: "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)\<noteq>0"
  note commutator = leading_form_commutator[OF P Q weight nonzero]
  have "0=v_degree rho sigma Q+v_degree rho sigma P-(rho+sigma)"
    using conjunct1[OF commutator] by (simp only: exact vDeg_one_A1)
  then show False using target by arith
qed

lemma exactPair_leadingPoisson_zero_or_one:
  fixes P Q :: "'k::field_char_0 poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and weight: "0<rho+sigma" and exact: "op_comp Q P-op_comp P Q=id"
  shows "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=0 \<or>
    biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=1"
proof (cases "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=0")
  case True
  then show ?thesis by simp
next
  case False
  note commutator = leading_form_commutator[OF P Q weight False]
  have "1=biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)"
    using conjunct2[OF commutator] by (simp only: exact leading_mate_one)
  then show ?thesis by simp
qed

lemma exactPair_target_eq_zero_of_leadingPoisson_eq_one:
  fixes P Q :: "'k::field_char_0 poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and weight: "0<rho+sigma" and exact: "op_comp Q P-op_comp P Q=id"
    and bracket: "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=1"
  shows "v_degree rho sigma Q+v_degree rho sigma P-(rho+sigma)=0"
proof -
  have nonzero: "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)\<noteq>0"
    using bracket by simp
  note commutator = leading_form_commutator[OF P Q weight nonzero]
  show ?thesis using conjunct1[OF commutator] by (simp only: exact vDeg_one_A1; arith)
qed

end
