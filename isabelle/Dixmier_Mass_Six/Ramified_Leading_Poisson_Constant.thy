theory Ramified_Leading_Poisson_Constant
 imports Ramified_Corner_Companion_Endpoints
   "Ramified_Exact_Weight_Lower"
begin
lemma ramified_exact_pair_top_face_bracket_eq_one_of_threshold_zero:
  assumes "0<l" "0<rho" "0<rho+sigma"
    "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "P\<noteq>0" "Q\<noteq>0"
    "laurent_comp P Q-laurent_comp Q P=id"
    "ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)=0"
  shows "([:of_int (ramified_weight_deg l rho sigma Q)/(of_nat l* of_int rho):]*
      (pderiv (ramified_top_face_polynomial l rho sigma P)*ramified_top_face_polynomial l rho sigma Q)-
      [:of_int (ramified_weight_deg l rho sigma P)/(of_nat l* of_int rho):]*
      (ramified_top_face_polynomial l rho sigma P*pderiv (ramified_top_face_polynomial l rho sigma Q)))=1"
proof (rule poly_eqI)
  fix j
  let ?f = "ramified_top_face_polynomial l rho sigma P"
  let ?g = "ramified_top_face_polynomial l rho sigma Q"
  let ?A = "ramified_weight_deg l rho sigma P"
  let ?D = "ramified_weight_deg l rho sigma Q"
  let ?den = "of_nat l* of_int rho::complex"
  let ?H = "[:of_int ?D/?den:]*(pderiv ?f*?g)-[:of_int ?A/?den:]*(?f*pderiv ?g)"
  show "coeff ?H j=coeff (1::complex poly) j"
  proof (cases "j=0")
    case True
    have weight: "ramified_weight l rho sigma (0,0)=?A+?D-int l*(rho+sigma)"
      using assms(9) by (simp add: ramified_weight_def)
    note coefficient = ramified_commutator_first_face_polynomial_bracket[OF assms(1,2,3,4,5,6,7) weight]
    show ?thesis using coefficient by (simp add: True assms(8) ramified_pbw_coeffs_one_coeff_at_origin[OF assms(1)])
  next
    case False
    have zero: "coeff ?H j=0"
    proof (rule ccontr)
    assume nonzero: "coeff ?H j\<noteq>0"
    let ?F = "\<lambda>n m. if n+m=j+1 then (of_int ?D/?den* of_nat n- of_int ?A/?den* of_nat m)*coeff ?f n*coeff ?g m else 0"
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
    note coefficient = ramified_commutator_first_face_polynomial_bracket[OF assms(1,2,3,4,5,6,7) weight]
    have raw: "Poly_Mapping.lookup(Poly_Mapping.lookup(ramified_pbw_coeffs l (laurent_comp P Q-laurent_comp Q P))j)?v\<noteq>0"
      using coefficient nonzero by simp
    have origin: "j=0 \<and> ?v=0"
      using ramified_exact_pair_coeff_nonzero_iff_origin[OF assms(1,4,5,8)] raw by simp
    show False using origin False by blast
    qed
    show ?thesis using False zero by simp
  qed
qed

lemma ramified_exact_pair_threshold_zero_has_top_order_zero:
 assumes "0<l" "0<rho" "0<rho+sigma"
   "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
   "P\<noteq>0" "Q\<noteq>0" "laurent_comp P Q-laurent_comp Q P=id"
   "ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)=0"
 shows "0\<in>polynomial_support(ramified_top_face_polynomial l rho sigma P) \<or>
   0\<in>polynomial_support(ramified_top_face_polynomial l rho sigma Q)"
proof (rule ccontr)
 assume none: "\<not>(0\<in>polynomial_support(ramified_top_face_polynomial l rho sigma P) \<or>
   0\<in>polynomial_support(ramified_top_face_polynomial l rho sigma Q))"
 have pzero: "poly(ramified_top_face_polynomial l rho sigma P)0=0"
 and qzero: "poly(ramified_top_face_polynomial l rho sigma Q)0=0"
   using none by (simp_all add: polynomial_support_def poly_0_coeff_0)
 note equation = ramified_exact_pair_top_face_bracket_eq_one_of_threshold_zero[OF assms]
 have "(0::complex)=1"
   using arg_cong[where f="\<lambda>p. poly p 0", OF equation]
   by (simp add: pzero qzero)
 then show False by simp
qed

end
