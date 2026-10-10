theory Ramified_Noncentralizing_First_Face
  imports Ramified_Commutator_First_Weight
begin

definition ramified_face_bracket where
  "ramified_face_bracket l rho sigma P Q=
    [:of_int (ramified_weight_deg l rho sigma Q)/(of_nat l*of_int rho):]*
      (pderiv (ramified_top_face_polynomial l rho sigma P)*ramified_top_face_polynomial l rho sigma Q)-
    [:of_int (ramified_weight_deg l rho sigma P)/(of_nat l*of_int rho):]*
      (ramified_top_face_polynomial l rho sigma P*pderiv (ramified_top_face_polynomial l rho sigma Q))"

lemma ramified_nonzero_first_bracket_attained:
  assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
    and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
    and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0"
    and bracket: "ramified_face_bracket l rho sigma P Q\<noteq>0"
  shows "\<exists>p\<in>ramified_pbw_support l (laurent_comp P Q-laurent_comp Q P).
    ramified_weight l rho sigma p=ramified_weight_deg l rho sigma P+
      ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
proof -
  let ?f = "ramified_top_face_polynomial l rho sigma P"
  let ?g = "ramified_top_face_polynomial l rho sigma Q"
  let ?A = "ramified_weight_deg l rho sigma P"
  let ?D = "ramified_weight_deg l rho sigma Q"
  let ?den = "of_nat l*of_int rho::complex"
  let ?H = "[:of_int ?D/?den:]*(pderiv ?f*?g)-[:of_int ?A/?den:]*(?f*pderiv ?g)"
  have Hnz: "?H\<noteq>0" using bracket by (simp only: ramified_face_bracket_def; simp)
  have exists: "\<exists>j. coeff ?H j\<noteq>0"
  proof (rule ccontr)
    assume "\<not>(\<exists>j. coeff ?H j\<noteq>0)"
    then have zero: "coeff ?H j=0" for j by blast
    have "?H=0" by (rule poly_eqI) (simp only: zero coeff_0)
    then show False using Hnz by contradiction
  qed
  obtain j where nonzero: "coeff ?H j\<noteq>0" using exists by blast
    let ?F = "\<lambda>n m. if n+m=j+1 then (of_int ?D/?den*of_nat n-of_int ?A/?den*of_nat m)*coeff ?f n*coeff ?g m else 0"
    have sum_nonzero: "(\<Sum>n\<in>polynomial_support ?f. \<Sum>m\<in>polynomial_support ?g. ?F n m)\<noteq>0"
      using nonzero by (simp only: polynomial_derivative_bracket_coeff_support_pairs; simp)
    obtain n where n: "n\<in>polynomial_support ?f"
      and inner: "(\<Sum>m\<in>polynomial_support ?g. ?F n m)\<noteq>0"
      using sum_nonzero by (rule sum.not_neutral_contains_not_neutral)
    obtain m where m: "m\<in>polynomial_support ?g" and term_nonzero: "?F n m\<noteq>0"
      using inner by (rule sum.not_neutral_contains_not_neutral)
    have first: "n+m=j+1" using term_nonzero by (cases "n+m=j+1") auto
    let ?B = "ramified_pbw_top_laurent l P n"
    let ?C = "ramified_pbw_top_laurent l Q m"
    let ?v = "?B+?C-int l"
    have topP: "rho*?B+int l*sigma*int n=?A"
      using n by (simp add: ramified_top_face_polynomial_mem_support_iff)
    have topQ: "rho*?C+int l*sigma*int m=?D"
      using m by (simp add: ramified_top_face_polynomial_mem_support_iff)
    have cast: "int n+int m=int j+1" using first by presburger
    have castmul: "int l*sigma*(int n+int m)=int l*sigma*(int j+1)" by (simp only: cast)
    have weight: "ramified_weight l rho sigma (?v,j)=?A+?D-int l*(rho+sigma)"
      using topP topQ castmul unfolding ramified_weight_def by (simp add: algebra_simps; arith)

  have commcarrier: "laurent_comp P Q-laurent_comp Q P\<in>ramified_operator_algebra l"
    by (intro ramified_algebra_diff ramified_algebra_comp P Q)
  have equality: "ramified_pbw_coeff l (laurent_comp P Q-laurent_comp Q P) ?v j=coeff ?H j"
    using ramified_commutator_first_face_polynomial_bracket[OF l rho positive P Q Pnz Qnz weight]
    by (simp only: ramified_pbw_coeff_def)
  have coeffnz: "ramified_pbw_coeff l (laurent_comp P Q-laurent_comp Q P) ?v j\<noteq>0"
    by (subst equality; rule nonzero)
  have support: "(?v,j)\<in>ramified_pbw_support l (laurent_comp P Q-laurent_comp Q P)"
    using coeffnz ramified_pbw_support_mem_iff[OF l commcarrier] by blast
  show ?thesis by (intro bexI[of _ "(?v,j)"] weight support)
qed

lemma ramified_noncentralizing_commutator_weight:
  assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
    and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
    and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0"
    and bracket: "ramified_face_bracket l rho sigma P Q\<noteq>0"
  shows "ramified_weight_deg l rho sigma (laurent_comp P Q-laurent_comp Q P)=
    ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
proof (rule ramified_weight_deg_eq_of_attained_upper)
  show "\<exists>p\<in>ramified_pbw_support l (laurent_comp P Q-laurent_comp Q P).
    ramified_weight l rho sigma p=ramified_weight_deg l rho sigma P+
      ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
    by (rule ramified_nonzero_first_bracket_attained[OF l rho positive P Q Pnz Qnz bracket])
  show "\<forall>p\<in>ramified_pbw_support l (laurent_comp P Q-laurent_comp Q P).
    ramified_weight l rho sigma p\<le>ramified_weight_deg l rho sigma P+
      ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
  proof (intro ballI)
    fix p assume p: "p\<in>ramified_pbw_support l (laurent_comp P Q-laurent_comp Q P)"
    obtain i j where ij: "p=(i,j)" by (cases p) auto
    show "ramified_weight l rho sigma p\<le>ramified_weight_deg l rho sigma P+
      ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
      by (simp only: ij; rule ramified_commutator_support_first_weight_upper[OF l rho positive P Q Pnz Qnz])
        (use p in \<open>simp only: ij\<close>)
  qed
qed

end
