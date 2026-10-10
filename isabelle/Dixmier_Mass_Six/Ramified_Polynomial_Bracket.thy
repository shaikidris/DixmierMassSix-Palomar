theory Ramified_Polynomial_Bracket
 imports "Ramified_First_Face_Exact"
begin
lemma polynomial_pderiv_finite_sum:
  "pderiv (\<Sum>n\<in>S. F n::complex poly)=(\<Sum>n\<in>S. pderiv (F n))"
  by (rule poly_eqI) (simp add: coeff_pderiv coeff_sum sum_distrib_left)
lemma polynomial_derivative_atom_coeff:
  "coeff ([:alpha:]*(pderiv (monom a n)*monom b m)::complex poly) j=
    (if n+m=j+1 then alpha*of_nat n*a*b else 0)"
proof (cases n)
  case 0 then show ?thesis by (simp add: pderiv_monom)
next
  case (Suc k)
  show ?thesis
  proof (cases "Suc k+m=j+1")
    case True
    have index: "k+m=j" using True by presburger
    show ?thesis using True by (simp add: Suc pderiv_monom mult_monom coeff_monom index algebra_simps)
  next
    case False
    have index: "k+m\<noteq>j" using False by presburger
    show ?thesis using False by (simp add: Suc pderiv_monom mult_monom coeff_monom index algebra_simps)
  qed
qed
lemma polynomial_derivative_bracket_coeff_support_pairs:
  "coeff ([:alpha:]*(pderiv f*g)-[:beta:]*(f*pderiv g)::complex poly) j=
    (\<Sum>n\<in>polynomial_support f. \<Sum>m\<in>polynomial_support g.
      if n+m=j+1 then (alpha*of_nat n-beta*of_nat m)*coeff f n*coeff g m else 0)"
proof -
  let ?S = "polynomial_support f"
  let ?U = "polynomial_support g"
  have left: "[:alpha:]*(pderiv f*g)=
    (\<Sum>n\<in>?S. \<Sum>m\<in>?U. [:alpha:]*(pderiv (monom (coeff f n) n)*monom (coeff g m) m))"
  proof -
    have derivative: "pderiv f=(\<Sum>n\<in>?S. pderiv (monom (coeff f n) n))"
      using arg_cong[OF polynomial_support_expansion[of f], where f=pderiv]
      by (simp only: polynomial_pderiv_finite_sum)
    show ?thesis by (subst derivative; subst (1) polynomial_support_expansion[of g])
      (simp only: sum_distrib_left sum_distrib_right; rule sum.swap)
  qed
  have right: "[:beta:]*(f*pderiv g)=
    (\<Sum>n\<in>?S. \<Sum>m\<in>?U. [:beta:]*(monom (coeff f n) n*pderiv (monom (coeff g m) m)))"
  proof -
    have derivative: "pderiv g=(\<Sum>m\<in>?U. pderiv (monom (coeff g m) m))"
      using arg_cong[OF polynomial_support_expansion[of g], where f=pderiv]
      by (simp only: polynomial_pderiv_finite_sum)
    show ?thesis by (subst derivative; subst (1) polynomial_support_expansion[of f])
      (simp only: sum_distrib_left sum_distrib_right; rule sum.swap)
  qed
  have normalized:
    "(\<Sum>n\<in>?S. \<Sum>m\<in>?U.
      coeff ([:alpha:]*(pderiv (monom (coeff f n) n)*monom (coeff g m) m)) j-
      coeff ([:beta:]*(monom (coeff f n) n*pderiv (monom (coeff g m) m))) j)=
    (\<Sum>n\<in>?S. \<Sum>m\<in>?U.
      if n+m=j+1 then (alpha*of_nat n-beta*of_nat m)*coeff f n*coeff g m else 0)"
  proof (rule sum.cong[OF refl], rule sum.cong[OF refl])
    fix n m
    show "coeff ([:alpha:]*(pderiv (monom (coeff f n) n)*monom (coeff g m) m)) j-
      coeff ([:beta:]*(monom (coeff f n) n*pderiv (monom (coeff g m) m))) j=
      (if n+m=j+1 then (alpha*of_nat n-beta*of_nat m)*coeff f n*coeff g m else 0)"
      by (simp only: mult.commute[of "monom (coeff f n) n" "pderiv (monom (coeff g m) m)"]
        polynomial_derivative_atom_coeff; simp add: add.commute algebra_simps)
  qed
  show ?thesis
    by (simp only: left right coeff_diff coeff_sum sum_subtractf[symmetric]; rule normalized)
qed
lemma ramified_top_pair_determinant_weight_formula:
  assumes "0<l" "0<rho" "rho*B+int l*sigma*int n=A" "rho*C+int l*sigma*int m=D"
  shows "((of_nat n*of_int C-of_nat m*of_int B)/of_nat l::complex)=
    (of_nat n*of_int D-of_nat m*of_int A)/(of_nat l*of_int rho)"
proof -
  have p: "int m*(rho*B+int l*sigma*int n)=int m*A" using assms(3) by simp
  have q: "int n*(rho*C+int l*sigma*int m)=int n*D" using assms(4) by simp
  have integer: "(int n*C-int m*B)*rho=int n*D-int m*A"
    using p q by (simp add: algebra_simps; arith)
  have complex: "(of_nat n*of_int C-of_nat m*of_int B)*of_int rho=
    (of_nat n*of_int D-of_nat m*of_int A::complex)"
    using arg_cong[OF integer, where f="of_int::int\<Rightarrow>complex"] by simp
  have nonzero: "(of_int rho::complex)\<noteq>0" using assms(2) by simp
  show ?thesis by (subst complex[symmetric])
    (rule nonzero_mult_divide_mult_cancel_right[symmetric, OF nonzero])
qed

lemma polynomial_derivative_bracket_coeff_finite_sets:
  assumes "finite S" "finite U" "polynomial_support f\<subseteq>S" "polynomial_support g\<subseteq>U"
  shows "coeff ([:alpha:]*(pderiv f*g)-[:beta:]*(f*pderiv g)::complex poly) j=
    (\<Sum>n\<in>S. \<Sum>m\<in>U.
      if n+m=j+1 then (alpha*of_nat n-beta*of_nat m)*coeff f n*coeff g m else 0)"
proof -
  have extended:
    "(\<Sum>n\<in>polynomial_support f. \<Sum>m\<in>polynomial_support g.
      if n+m=j+1 then (alpha*of_nat n-beta*of_nat m)*coeff f n*coeff g m else 0)=
    (\<Sum>n\<in>S. \<Sum>m\<in>U.
      if n+m=j+1 then (alpha*of_nat n-beta*of_nat m)*coeff f n*coeff g m else 0)"
  proof (rule sum.mono_neutral_cong_left[OF assms(1,3)])
    show "\<forall>n\<in>S-polynomial_support f.
      (\<Sum>m\<in>U. if n+m=j+1 then (alpha*of_nat n-beta*of_nat m)*coeff f n*coeff g m else 0)=0"
    proof (intro ballI)
      fix n assume "n\<in>S-polynomial_support f"
      then have zero: "coeff f n=0" by (auto simp: polynomial_support_def)
      show "(\<Sum>m\<in>U. if n+m=j+1 then (alpha*of_nat n-beta*of_nat m)*coeff f n*coeff g m else 0)=0"
        by (intro sum.neutral ballI) (simp add: zero)
    qed
  next
    fix n assume "n\<in>polynomial_support f"
    show "(\<Sum>m\<in>polynomial_support g.
      if n+m=j+1 then (alpha*of_nat n-beta*of_nat m)*coeff f n*coeff g m else 0)=
      (\<Sum>m\<in>U. if n+m=j+1 then (alpha*of_nat n-beta*of_nat m)*coeff f n*coeff g m else 0)"
      by (rule sum.mono_neutral_cong_left[OF assms(2,4)]) (auto simp: polynomial_support_def)
  qed
  show ?thesis
    by (simp only: polynomial_derivative_bracket_coeff_support_pairs; rule extended)
qed

end
