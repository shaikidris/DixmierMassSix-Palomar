theory Ramified_Constant_Endpoint
 imports Ramified_First_Face_Determinant
begin
lemma ramified_pbw_coeffs_one_coeff_support:
  assumes "0<l" "v\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l id) j)"
  shows "j=0 \<and> v=0"
  using assms(2) by (simp add: ramified_coeff_mul_one[symmetric]
    ramified_pbw_coeffs_coeff_mul[OF assms(1)] Poly_Mapping.lookup_single when_def
    Poly_Mapping.in_keys_iff Poly_Mapping.lookup_one split: if_splits)
lemma ramified_pbw_coeffs_one_coeff_at_origin:
  assumes "0<l"
  shows "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l id) 0) 0=1"
  by (simp add: ramified_coeff_mul_one[symmetric] ramified_pbw_coeffs_coeff_mul[OF assms]
    Poly_Mapping.lookup_single)
lemma ramified_exact_pair_coeff_nonzero_iff_origin:
  assumes "0<l" "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "laurent_comp P Q-laurent_comp Q P=id"
  shows "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp P Q-laurent_comp Q P)) j) v\<noteq>0 \<longleftrightarrow> j=0 \<and> v=0"
proof
  assume nonzero: "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp P Q-laurent_comp Q P)) j) v\<noteq>0"
  have "v\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l id) j)"
    using nonzero assms(4) by (simp add: Poly_Mapping.in_keys_iff)
  then show "j=0 \<and> v=0" by (rule ramified_pbw_coeffs_one_coeff_support[OF assms(1)])
next
  assume "j=0 \<and> v=0"
  then show "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp P Q-laurent_comp Q P)) j) v\<noteq>0"
    by (simp add: assms(4) ramified_pbw_coeffs_one_coeff_at_origin[OF assms(1)])
qed
lemma ramified_exact_pair_determinant_nonzero_iff_origin:
  assumes "0<l" "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "laurent_comp P Q-laurent_comp Q P=id" "a\<noteq>(0::complex)" "b\<noteq>0"
    "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l
      (laurent_comp P Q-laurent_comp Q P)) j) v=d*a*b"
  shows "d\<noteq>0 \<longleftrightarrow> j=0 \<and> v=0"
  using ramified_exact_pair_coeff_nonzero_iff_origin[OF assms(1,2,3,4), where j=j and v=v]
    assms(5,6,7) by auto
end
