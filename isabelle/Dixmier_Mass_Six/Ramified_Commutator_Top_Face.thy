theory Ramified_Commutator_Top_Face
  imports Ramified_Noncentralizing_First_Face
    "Ramified_Filtered_Centralizer_Rank"
begin

lemma ramified_face_bracket_coeff_weight_lattice:
  assumes nonzero: "coeff (ramified_face_bracket l rho sigma P Q) j\<noteq>0"
  shows "rho dvd ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-
    int l*(rho+sigma)-int l*sigma*int j"
proof -
  let ?f = "ramified_top_face_polynomial l rho sigma P"
  let ?g = "ramified_top_face_polynomial l rho sigma Q"
  let ?A = "ramified_weight_deg l rho sigma P"
  let ?D = "ramified_weight_deg l rho sigma Q"
  let ?den = "of_nat l*of_int rho::complex"
  let ?H = "[:of_int ?D/?den:]*(pderiv ?f*?g)-[:of_int ?A/?den:]*(?f*pderiv ?g)"
  have nonzero: "coeff ?H j\<noteq>0" using nonzero by (simp only: ramified_face_bracket_def; simp)
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

  have numerator: "?A+?D-int l*(rho+sigma)-int l*sigma*int j=rho*?v"
    using weight by (simp add: ramified_weight_def)
  show ?thesis by (simp only: numerator) simp
qed

lemma ramified_first_weight_component_eq_bracket:
  assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
    and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
    and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0"
  shows "ramified_weight_component_polynomial l rho sigma
    (ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma))
    (laurent_comp P Q-laurent_comp Q P)=ramified_face_bracket l rho sigma P Q"
proof (rule poly_eqI)
  fix j
  let ?b = "ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
  let ?num = "?b-int l*sigma*int j"
  show "coeff (ramified_weight_component_polynomial l rho sigma ?b (laurent_comp P Q-laurent_comp Q P)) j=
    coeff (ramified_face_bracket l rho sigma P Q) j"
  proof (cases "rho dvd ?num")
    case True
    have cancel: "rho*(?num div rho)=?num" by (rule dvd_mult_div_cancel[OF True])
    have weight: "ramified_weight l rho sigma (?num div rho,j)=?b"
      using cancel by (simp only: ramified_weight_def fst_conv snd_conv; arith)
    have coeff: "ramified_pbw_coeff l (laurent_comp P Q-laurent_comp Q P) (?num div rho) j=
      coeff (ramified_face_bracket l rho sigma P Q) j"
      using ramified_commutator_first_face_polynomial_bracket[OF l rho positive P Q Pnz Qnz weight]
      by (simp only: ramified_pbw_coeff_def ramified_face_bracket_def)
    show ?thesis by (simp only: ramified_weight_component_coeff True if_True coeff)
  next
    case False
    have zero: "coeff (ramified_face_bracket l rho sigma P Q) j=0"
      using False ramified_face_bracket_coeff_weight_lattice[where l=l and rho=rho and sigma=sigma and P=P and Q=Q and j=j] by blast
    show ?thesis by (simp only: ramified_weight_component_coeff False if_False zero)
  qed
qed

lemma ramified_noncentralizing_commutator_top_face:
  assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
    and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
    and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0"
    and bracket: "ramified_face_bracket l rho sigma P Q\<noteq>0"
  shows "ramified_top_face_polynomial l rho sigma (laurent_comp P Q-laurent_comp Q P)=
    ramified_face_bracket l rho sigma P Q"
proof -
  have carrier: "laurent_comp P Q-laurent_comp Q P\<in>ramified_operator_algebra l"
    by (intro ramified_algebra_diff ramified_algebra_comp P Q)
  have degree: "ramified_weight_deg l rho sigma (laurent_comp P Q-laurent_comp Q P)=
    ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
    by (rule ramified_noncentralizing_commutator_weight[OF l rho positive P Q Pnz Qnz bracket])
  have component: "ramified_weight_component_polynomial l rho sigma
    (ramified_weight_deg l rho sigma (laurent_comp P Q-laurent_comp Q P))
    (laurent_comp P Q-laurent_comp Q P)=ramified_top_face_polynomial l rho sigma (laurent_comp P Q-laurent_comp Q P)"
    by (rule ramified_weight_component_at_degree[OF l rho carrier])
  show ?thesis using component ramified_first_weight_component_eq_bracket[OF l rho positive P Q Pnz Qnz]
    by (simp only: degree)
qed

lemma ramified_face_bracket_eq_neg_centralization:
  "ramified_face_bracket l rho sigma P Q= -ramified_face_centralization l rho sigma P Q"
  by (simp add: ramified_face_bracket_def ramified_face_centralization_def algebra_simps)

lemma ramified_face_centralization_zero_right:
  assumes l: "0<l"
  shows "ramified_face_centralization l rho sigma P 0=0"
  by (simp add: ramified_face_centralization_def ramified_top_face_polynomial_zero[OF l])

end
