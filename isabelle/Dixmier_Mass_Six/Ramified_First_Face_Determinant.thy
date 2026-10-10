theory Ramified_First_Face_Determinant
 imports Ramified_First_Face_Canonical
begin
lemma ramified_first_face_top_atom_determinant:
  assumes "0<l" "0<rho" "laurent_upper f B" "laurent_upper g C"
    "B\<in>Poly_Mapping.keys f" "C\<in>Poly_Mapping.keys g"
    "n+m=j+1" "rho*B+int l*sigma*int n=A" "rho*C+int l*sigma*int m=D"
    "ramified_weight l rho sigma (v,j)=A+D-int l*(rho+sigma)"
  shows "Poly_Mapping.lookup (f*laurent_smult (of_nat n) (ramified_derivative l g)-
    g*laurent_smult (of_nat m) (ramified_derivative l f)) v=
    ((of_nat n*of_int C-of_nat m*of_int B)/of_nat l::complex)*
      Poly_Mapping.lookup f B*Poly_Mapping.lookup g C"
proof -
  have cast: "int n+int m=int j+1" using assms(7) by presburger
  have castmul: "int l*sigma*(int n+int m)=int l*sigma*(int j+1)"
    by (simp only: cast)
  have scaled: "rho*v=rho*(B+C-int l)"
    using assms(8,9,10) castmul unfolding ramified_weight_def by (simp add: algebra_simps; arith)
  have coord: "v=B+C-int l" using scaled assms(2) by simp
  show ?thesis by (simp only: coord ramified_first_contraction_extremal_coeff[OF assms(3,4,5,6)])
qed

lemma ramified_pbw_coeffs_commutator_first_face_determinant:
  assumes "0<l" "0<rho" "0<rho+sigma"
    "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "P\<noteq>0" "Q\<noteq>0"
    "ramified_weight l rho sigma (v,j)=ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
  shows "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp P Q-laurent_comp Q P)) j) v=
    (\<Sum>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
     \<Sum>m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
      if n+m=j+1 \<and> rho*ramified_pbw_top_laurent l P n+int l*sigma*int n=ramified_weight_deg l rho sigma P \<and> rho*ramified_pbw_top_laurent l Q m+int l*sigma*int m=ramified_weight_deg l rho sigma Q then
        ((of_nat n*of_int (ramified_pbw_top_laurent l Q m)-of_nat m*of_int (ramified_pbw_top_laurent l P n))/of_nat l::complex)*
        Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) (ramified_pbw_top_laurent l P n)*
        Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) (ramified_pbw_top_laurent l Q m)
      else 0)"
proof -
  have threshold: "ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)\<le>
    ramified_weight l rho sigma (v,j)" using assms(8) by simp
  show ?thesis
    unfolding ramified_pbw_coeffs_commutator_first_face_canonical[OF assms(1,2,3,4,5,6,7) threshold]
  proof (rule sum.cong[OF refl]; rule sum.cong[OF refl])
    fix n m assume n: "n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P)"
      and m: "m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q)"
    let ?f = "Poly_Mapping.lookup (ramified_pbw_coeffs l P) n"
    let ?g = "Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m"
    let ?B = "ramified_pbw_top_laurent l P n"
    let ?C = "ramified_pbw_top_laurent l Q m"
    let ?first = "n+m=j+1 \<and> rho*?B+int l*sigma*int n=ramified_weight_deg l rho sigma P \<and>
      rho*?C+int l*sigma*int m=ramified_weight_deg l rho sigma Q"
    show "(if ?first then Poly_Mapping.lookup (?f*laurent_smult (of_nat n) (ramified_derivative l ?g)-
      ?g*laurent_smult (of_nat m) (ramified_derivative l ?f)) v else 0)=
      (if ?first then ((of_nat n*of_int ?C-of_nat m*of_int ?B)/of_nat l::complex)*
      Poly_Mapping.lookup ?f ?B*Poly_Mapping.lookup ?g ?C else 0)"
    proof (cases ?first)
      case False then show ?thesis by (simp only: False if_False)
    next
      case True
      have first: "n+m=j+1" and ptop: "rho*?B+int l*sigma*int n=ramified_weight_deg l rho sigma P"
        and qtop: "rho*?C+int l*sigma*int m=ramified_weight_deg l rho sigma Q" using True by simp_all
      have eq: "Poly_Mapping.lookup (?f*laurent_smult (of_nat n) (ramified_derivative l ?g)-
        ?g*laurent_smult (of_nat m) (ramified_derivative l ?f)) v=
        ((of_nat n*of_int ?C-of_nat m*of_int ?B)/of_nat l::complex)*Poly_Mapping.lookup ?f ?B*Poly_Mapping.lookup ?g ?C"
        by (rule ramified_first_face_top_atom_determinant[OF assms(1,2)
          ramified_pbw_top_laurent_upper ramified_pbw_top_laurent_upper
          ramified_pbw_top_laurent_mem[OF n] ramified_pbw_top_laurent_mem[OF m] first ptop qtop assms(8)])
      show ?thesis by (simp only: True if_True eq)
    qed
  qed
qed
end
