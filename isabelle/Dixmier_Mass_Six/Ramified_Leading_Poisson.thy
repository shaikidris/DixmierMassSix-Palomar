theory Ramified_Leading_Poisson
 imports Ramified_Polynomial_Bracket
begin
lemma ramified_commutator_first_face_polynomial_bracket:
  assumes "0<l" "0<rho" "0<rho+sigma"
    "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "P\<noteq>0" "Q\<noteq>0"
    "ramified_weight l rho sigma (v,j)=ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
  shows "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp P Q-laurent_comp Q P)) j) v=
    coeff ([:of_int (ramified_weight_deg l rho sigma Q)/(of_nat l*of_int rho):]*
      (pderiv (ramified_top_face_polynomial l rho sigma P)*ramified_top_face_polynomial l rho sigma Q)-
      [:of_int (ramified_weight_deg l rho sigma P)/(of_nat l*of_int rho):]*
      (ramified_top_face_polynomial l rho sigma P*pderiv (ramified_top_face_polynomial l rho sigma Q))) j"
proof -
  have supportP: "polynomial_support (ramified_top_face_polynomial l rho sigma P)\<subseteq>
    Poly_Mapping.keys (ramified_pbw_coeffs l P)"
    by (auto simp: ramified_top_face_polynomial_support)
  have supportQ: "polynomial_support (ramified_top_face_polynomial l rho sigma Q)\<subseteq>
    Poly_Mapping.keys (ramified_pbw_coeffs l Q)"
    by (auto simp: ramified_top_face_polynomial_support)
  have normalized:
    "(\<Sum>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
      \<Sum>m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
      if n+m=j+1 \<and>
        rho*ramified_pbw_top_laurent l P n+int l*sigma*int n=ramified_weight_deg l rho sigma P \<and>
        rho*ramified_pbw_top_laurent l Q m+int l*sigma*int m=ramified_weight_deg l rho sigma Q
      then ((of_nat n*of_int (ramified_pbw_top_laurent l Q m)-
        of_nat m*of_int (ramified_pbw_top_laurent l P n))/of_nat l::complex)*
        Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) (ramified_pbw_top_laurent l P n)*
        Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) (ramified_pbw_top_laurent l Q m)
      else 0)=
    (\<Sum>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
      \<Sum>m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
      if n+m=j+1 then
        (of_int (ramified_weight_deg l rho sigma Q)/(of_nat l*of_int rho)*of_nat n-
         of_int (ramified_weight_deg l rho sigma P)/(of_nat l*of_int rho)*of_nat m)*
        coeff (ramified_top_face_polynomial l rho sigma P) n*
        coeff (ramified_top_face_polynomial l rho sigma Q) m else 0)"
  proof (rule sum.cong[OF refl], rule sum.cong[OF refl])
    fix n m assume n: "n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P)"
      and m: "m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q)"
    let ?B = "ramified_pbw_top_laurent l P n"
    let ?C = "ramified_pbw_top_laurent l Q m"
    let ?A = "ramified_weight_deg l rho sigma P"
    let ?D = "ramified_weight_deg l rho sigma Q"
    let ?den = "of_nat l*of_int rho::complex"
    let ?f = "ramified_top_face_polynomial l rho sigma P"
    let ?g = "ramified_top_face_polynomial l rho sigma Q"
    let ?a = "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) ?B"
    let ?b = "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) ?C"
    show "(if n+m=j+1 \<and> rho*?B+int l*sigma*int n=?A \<and> rho*?C+int l*sigma*int m=?D
      then ((of_nat n*of_int ?C-of_nat m*of_int ?B)/of_nat l::complex)*?a*?b else 0)=
      (if n+m=j+1 then (of_int ?D/?den*of_nat n-of_int ?A/?den*of_nat m)*coeff ?f n*coeff ?g m else 0)"
    proof (cases "rho*?B+int l*sigma*int n=?A \<and> rho*?C+int l*sigma*int m=?D")
      case False
      show ?thesis using False n m
        by (auto simp: ramified_top_face_polynomial_coeff ramified_pbw_coeff_def)
    next
      case True
      have topP: "rho*?B+int l*sigma*int n=?A" and topQ: "rho*?C+int l*sigma*int m=?D"
        using True by simp_all
      have determinant: "((of_nat n*of_int ?C-of_nat m*of_int ?B)/of_nat l::complex)=
        (of_nat n*of_int ?D-of_nat m*of_int ?A)/?den"
        by (rule ramified_top_pair_determinant_weight_formula[OF assms(1,2) topP topQ])
      show ?thesis by (simp only: determinant; simp add: topP topQ n m ramified_top_face_polynomial_coeff
        ramified_pbw_coeff_def divide_inverse algebra_simps)
    qed
  qed
  show ?thesis
    by (simp only: ramified_pbw_coeffs_commutator_first_face_determinant[OF assms]
      polynomial_derivative_bracket_coeff_finite_sets[OF Poly_Mapping.finite_keys Poly_Mapping.finite_keys supportP supportQ];
      rule normalized)
qed
lemma ramified_exact_pair_first_face_polynomial_bracket_zero:
  assumes "0<l" "0<rho" "0<rho+sigma"
    "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "P\<noteq>0" "Q\<noteq>0"
    "laurent_comp P Q-laurent_comp Q P=id"
    "ramified_weight l rho sigma (v,j)=ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
    "0<ramified_weight l rho sigma (v,j)"
  shows "coeff ([:of_int (ramified_weight_deg l rho sigma Q)/(of_nat l*of_int rho):]*
      (pderiv (ramified_top_face_polynomial l rho sigma P)*ramified_top_face_polynomial l rho sigma Q)-
      [:of_int (ramified_weight_deg l rho sigma P)/(of_nat l*of_int rho):]*
      (ramified_top_face_polynomial l rho sigma P*pderiv (ramified_top_face_polynomial l rho sigma Q))) j=0"
proof -
  have zero: "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp P Q-laurent_comp Q P)) j) v=0"
  proof (rule ccontr)
    assume nonzero: "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l
      (laurent_comp P Q-laurent_comp Q P)) j) v\<noteq>0"
    have origin: "j=0 \<and> v=0"
      using ramified_exact_pair_coeff_nonzero_iff_origin[OF assms(1,4,5,8)] nonzero by simp
    then show False using assms(10) by (simp add: ramified_weight_def)
  qed
  show ?thesis using zero ramified_commutator_first_face_polynomial_bracket[OF assms(1,2,3,4,5,6,7,9)] by simp
qed
end
