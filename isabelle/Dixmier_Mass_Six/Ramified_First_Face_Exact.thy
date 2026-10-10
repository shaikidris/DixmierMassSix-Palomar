theory Ramified_First_Face_Exact
 imports Ramified_Constant_Endpoint
begin
lemma ramified_exact_pair_first_face_determinant_zero:
  assumes "0<l" "0<rho" "0<rho+sigma"
    "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "P\<noteq>0" "Q\<noteq>0"
    "laurent_comp P Q-laurent_comp Q P=id"
    "ramified_weight l rho sigma (v,j)=ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
    "0<ramified_weight l rho sigma (v,j)"
  shows "(\<Sum>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
     \<Sum>m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
      if n+m=j+1 \<and> rho*ramified_pbw_top_laurent l P n+int l*sigma*int n=ramified_weight_deg l rho sigma P \<and> rho*ramified_pbw_top_laurent l Q m+int l*sigma*int m=ramified_weight_deg l rho sigma Q then
        ((of_nat n*of_int (ramified_pbw_top_laurent l Q m)-of_nat m*of_int (ramified_pbw_top_laurent l P n))/of_nat l::complex)*
        Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) (ramified_pbw_top_laurent l P n)*
        Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) (ramified_pbw_top_laurent l Q m)
      else 0)=0"
proof -
  note determinant = ramified_pbw_coeffs_commutator_first_face_determinant[OF assms(1,2,3,4,5,6,7,9)]
  have zero: "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp P Q-laurent_comp Q P)) j) v=0"
  proof (rule ccontr)
    assume nonzero: "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l
      (laurent_comp P Q-laurent_comp Q P)) j) v\<noteq>0"
    have origin: "j=0 \<and> v=0"
      using ramified_exact_pair_coeff_nonzero_iff_origin[OF assms(1,4,5,8)] nonzero by simp
    then show False using assms(10) by (simp add: ramified_weight_def)
  qed
  show ?thesis using determinant zero by simp
qed
end
