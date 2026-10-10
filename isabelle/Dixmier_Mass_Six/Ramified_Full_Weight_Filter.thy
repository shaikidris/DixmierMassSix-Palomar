theory Ramified_Full_Weight_Filter
  imports Ramified_Product_Weight_All
begin
lemma ramified_pbw_coeffs_commutator_weight_defect_zero:
  assumes "0<l" "0<rho" "0<rho+sigma"
    "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "\<And>n. n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P) \<Longrightarrow>
      laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) (B n)"
    "\<And>m. m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q) \<Longrightarrow>
      laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) (C m)"
    "\<And>n. n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P) \<Longrightarrow>
      rho*B n+int l*sigma*int n\<le>A"
    "\<And>m. m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q) \<Longrightarrow>
      rho*C m+int l*sigma*int m\<le>D"
    "\<And>n m. n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P) \<Longrightarrow>
      m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q) \<Longrightarrow> j+1\<le>n+m \<Longrightarrow>
      rho*B n+int l*sigma*int n<A \<or> rho*C m+int l*sigma*int m<D \<or> j+2\<le>n+m"
    "A+D-int l*(rho+sigma)\<le>ramified_weight l rho sigma (v,j)"
  shows "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp P Q-laurent_comp Q P)) j) v=0"
proof -
  have zero: "Poly_Mapping.lookup
    (\<Sum>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
     \<Sum>m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
      Poly_Mapping.lookup (ramified_pbw_coeffs l
       (laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) n)
         (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) m)-
        laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) m)
         (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) n))) j) v=0"
  proof (rule ramified_weight_double_sum_coeff_zero[OF Poly_Mapping.finite_keys Poly_Mapping.finite_keys assms(2) _ assms(11)])
    fix n m u assume n: "n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P)"
      and m: "m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q)"
      and u: "u\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l
       (laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) n)
         (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) m)-
        laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) m)
         (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) n))) j)"
    have contraction: "j+1\<le>n+m"
    proof (rule ccontr)
      assume "\<not>j+1\<le>n+m" then have top: "n+m\<le>j" by presburger
      note zero = ramified_pbw_coeffs_atom_commutator_zero_at_or_above[OF assms(1) top,
        where f="Poly_Mapping.lookup (ramified_pbw_coeffs l P) n" and g="Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m"]
      show False using u zero by simp
    qed
    show "ramified_weight l rho sigma (u,j)<A+D-int l*(rho+sigma)"
      by (rule ramified_pbw_coeffs_atom_commutator_below_first_of_defect_all[OF assms(1,2,3)
        assms(6)[OF n] assms(7)[OF m] contraction assms(8)[OF n] assms(9)[OF m]
        assms(10)[OF n m contraction] u])
  qed
  show ?thesis using zero by (simp only: ramified_pbw_coeffs_commutator_double_sum[OF assms(1,4,5)])
qed

lemma ramified_pbw_coeffs_commutator_first_weight_survivor:
  assumes "0<l" "0<rho" "0<rho+sigma"
    "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "\<And>n. n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P) \<Longrightarrow>
      laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) (B n)"
    "\<And>m. m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q) \<Longrightarrow>
      laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) (C m)"
    "\<And>n. n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P) \<Longrightarrow>
      rho*B n+int l*sigma*int n\<le>A"
    "\<And>m. m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q) \<Longrightarrow>
      rho*C m+int l*sigma*int m\<le>D"
    "A+D-int l*(rho+sigma)\<le>ramified_weight l rho sigma (v,j)"
    "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l
      (laurent_comp P Q-laurent_comp Q P)) j) v\<noteq>0"
  shows "\<exists>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
    \<exists>m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
      j+1=n+m \<and> rho*B n+int l*sigma*int n=A \<and> rho*C m+int l*sigma*int m=D"
proof (rule ccontr)
  assume none: "\<not>(\<exists>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
    \<exists>m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
      j+1=n+m \<and> rho*B n+int l*sigma*int n=A \<and> rho*C m+int l*sigma*int m=D)"
  have defect: "\<And>n m. n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P) \<Longrightarrow>
    m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q) \<Longrightarrow> j+1\<le>n+m \<Longrightarrow>
    rho*B n+int l*sigma*int n<A \<or> rho*C m+int l*sigma*int m<D \<or> j+2\<le>n+m"
  proof -
    fix n m assume n: "n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P)"
      and m: "m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q)" and count: "j+1\<le>n+m"
    have missing: "\<not>(j+1=n+m \<and> rho*B n+int l*sigma*int n=A \<and> rho*C m+int l*sigma*int m=D)"
      using none n m by blast
    show "rho*B n+int l*sigma*int n<A \<or> rho*C m+int l*sigma*int m<D \<or> j+2\<le>n+m"
      using missing assms(8)[OF n] assms(9)[OF m] count by presburger
  qed
  show False using assms(11) ramified_pbw_coeffs_commutator_weight_defect_zero[OF assms(1,2,3,4,5,6,7,8,9) defect assms(10)]
    by contradiction
qed
end
