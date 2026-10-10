theory Ramified_Product_Weight_All
  imports Ramified_Contraction_Weight_All
begin
lemma ramified_pbw_coeffs_atom_product_support_order:
  assumes "0<l" "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m))) j\<noteq>0"
  shows "m\<le>j \<and> j\<le>n+m"
proof -
  have lower: "m\<le>j"
  proof (rule ccontr)
    assume "\<not>m\<le>j" then have below: "j<m" by arith
    have shape: "laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m)=
      laurent_comp (laurent_comp (ramified_pbw_atom l f n) (ramified_coeff_mul g)) (ramified_derivative l ^^ m)"
      by (simp only: ramified_pbw_atom_def laurent_comp_assoc)
    have zero: "Poly_Mapping.lookup (ramified_pbw_coeffs l
      (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m))) j=0"
      unfolding shape by (rule ramified_pbw_coeffs_right_shift_zero_below[OF assms(1)
        ramified_algebra_comp[OF ramified_pbw_atom_carrier coeff_mem_ramified_operator_algebra] below])
    show False using zero assms(2) by contradiction
  qed
  have upper: "j\<le>n+m"
    using ramified_pbw_coeffs_atom_product_zero_above[OF assms(1), where n=n and m=m and j=j and f=f and g=g]
      assms(2) by (cases "n+m<j") auto
  show ?thesis using lower upper by simp
qed

lemma ramified_pbw_coeffs_atom_product_weight_upper_all:
  assumes "0<l" "0<rho" "laurent_upper f B" "laurent_upper g C"
    "v\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l
      (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m))) j)"
  shows "ramified_weight l rho sigma (v,j)\<le>
    rho*(B+C)+int l*sigma*(int n+int m)-int l*(rho+sigma)*(int n+int m-int j)"
proof -
  have nonzero: "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m))) j\<noteq>0"
    using assms(5) by auto
  have lower: "m\<le>j" using ramified_pbw_coeffs_atom_product_support_order[OF assms(1) nonzero] by simp
  have index: "j=(j-m)+m" using lower by presburger
  have cast: "int (j-m)=int j-int m" using lower by presburger
  have support: "v\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l
      (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m))) ((j-m)+m))"
    using assms(5) index by simp
  note bound = ramified_pbw_coeffs_atom_product_weight_upper[OF assms(1,2,3,4) support, where sigma=sigma]
  show ?thesis using bound by (simp only: index[symmetric] cast; simp add: algebra_simps)
qed

lemma ramified_pbw_coeffs_atom_commutator_weight_upper_all:
  assumes "0<l" "0<rho" "laurent_upper f B" "laurent_upper g C"
    "v\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l
      (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m)-
       laurent_comp (ramified_pbw_atom l g m) (ramified_pbw_atom l f n))) j)"
  shows "ramified_weight l rho sigma (v,j)\<le>
    rho*(B+C)+int l*sigma*(int n+int m)-int l*(rho+sigma)*(int n+int m-int j)"
proof -
  let ?U = "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m))) j"
  let ?V = "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l g m) (ramified_pbw_atom l f n))) j"
  have either: "v\<in>Poly_Mapping.keys ?U \<or> v\<in>Poly_Mapping.keys ?V"
    using assms(5) by (auto simp: ramified_pbw_coeffs_sub[OF assms(1)
      ramified_algebra_comp[OF ramified_pbw_atom_carrier ramified_pbw_atom_carrier]
      ramified_algebra_comp[OF ramified_pbw_atom_carrier ramified_pbw_atom_carrier]]
      Poly_Mapping.lookup_minus Poly_Mapping.in_keys_iff)
  then show ?thesis
  proof
    assume "v\<in>Poly_Mapping.keys ?U"
    then show ?thesis by (rule ramified_pbw_coeffs_atom_product_weight_upper_all[OF assms(1,2,3,4)])
  next
    assume supported: "v\<in>Poly_Mapping.keys ?V"
    show ?thesis using ramified_pbw_coeffs_atom_product_weight_upper_all[OF assms(1,2,4,3) supported, where sigma=sigma]
      by (simp add: algebra_simps)
  qed
qed

lemma ramified_pbw_coeffs_atom_commutator_below_first_of_defect_all:
  assumes "0<l" "0<rho" "0<rho+sigma" "laurent_upper f B" "laurent_upper g C"
    "j+1\<le>n+m" "rho*B+int l*sigma*int n\<le>A" "rho*C+int l*sigma*int m\<le>D"
    "rho*B+int l*sigma*int n<A \<or> rho*C+int l*sigma*int m<D \<or> j+2\<le>n+m"
    "v\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l
      (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m)-
       laurent_comp (ramified_pbw_atom l g m) (ramified_pbw_atom l f n))) j)"
  shows "ramified_weight l rho sigma (v,j)<A+D-int l*(rho+sigma)"
proof -
  let ?s = "int l*(rho+sigma)"
  let ?p = "rho*B+int l*sigma*int n"
  let ?q = "rho*C+int l*sigma*int m"
  have positive: "0<?s" using assms(1,3) by (intro mult_pos_pos) simp_all
  have gap: "1\<le>int n+int m-int j" using assms(6) by presburger
  have step: "?s\<le>?s*(int n+int m-int j)"
    using mult_left_mono[OF gap, of ?s] positive by simp
  have weight: "ramified_weight l rho sigma (v,j)\<le>?p+?q-?s*(int n+int m-int j)"
    using ramified_pbw_coeffs_atom_commutator_weight_upper_all[OF assms(1,2,4,5,10), where sigma=sigma]
    by (simp add: algebra_simps)
  consider "?p<A" | "?q<D" | "j+2\<le>n+m" using assms(9) by blast
  then show ?thesis
  proof cases
    case 1 show ?thesis using weight step 1 assms(8) by arith
  next
    case 2 show ?thesis using weight step 2 assms(7) by arith
  next
    case 3
    have gap2: "2\<le>int n+int m-int j" using 3 by presburger
    have step2: "?s*2\<le>?s*(int n+int m-int j)"
      by (rule mult_left_mono[OF gap2]) (use positive in arith)
    show ?thesis using weight step2 positive assms(7,8) by arith
  qed
qed
end
