theory Ramified_Endpoint_Coefficient
  imports Ramified_Contraction_Weight
begin
lemma laurent_upper_mul_coeff_at_sum:
  "laurent_upper f i \<Longrightarrow> laurent_upper g u \<Longrightarrow>
   i\<in>Poly_Mapping.keys f \<Longrightarrow>
   Poly_Mapping.lookup (f*g) (i+u)=Poly_Mapping.lookup f i*Poly_Mapping.lookup g u"
  by (rule laurent_upper_mul_edge)

lemma laurent_upper_smult:
  "laurent_upper f B \<Longrightarrow> laurent_upper (laurent_smult c f) B"
  by (auto simp: laurent_upper_def Poly_Mapping.in_keys_iff laurent_smult_lookup)

lemma ramified_first_contraction_extremal_coeff:
  assumes "laurent_upper f i" "laurent_upper g u"
    "i\<in>Poly_Mapping.keys f" "u\<in>Poly_Mapping.keys g"
  shows "Poly_Mapping.lookup (f*laurent_smult (of_nat j) (ramified_derivative l g)-
      g*laurent_smult (of_nat k) (ramified_derivative l f)) (i+u-int l)=
      ((of_nat j*of_int u-of_nat k*of_int i)/of_nat l::complex)*Poly_Mapping.lookup f i*Poly_Mapping.lookup g u"
proof -
  have dg: "laurent_upper (laurent_smult (of_nat j) (ramified_derivative l g)) (u-int l)"
    by (intro laurent_upper_smult laurent_upper_derivative assms(2))
  have df: "laurent_upper (laurent_smult (of_nat k) (ramified_derivative l f)) (i-int l)"
    by (intro laurent_upper_smult laurent_upper_derivative assms(1))
  have first: "Poly_Mapping.lookup (f*laurent_smult (of_nat j) (ramified_derivative l g)) (i+u-int l)=
    Poly_Mapping.lookup f i * (of_nat j*(of_int u/of_nat l)*Poly_Mapping.lookup g u)"
    using laurent_upper_mul_edge[OF assms(1) dg]
    by (simp add: ramified_derivative_lookup laurent_smult_lookup algebra_simps)
  have second: "Poly_Mapping.lookup (g*laurent_smult (of_nat k) (ramified_derivative l f)) (i+u-int l)=
    Poly_Mapping.lookup g u * (of_nat k*(of_int i/of_nat l)*Poly_Mapping.lookup f i)"
    using laurent_upper_mul_edge[OF assms(2) df]
    by (simp add: ramified_derivative_lookup laurent_smult_lookup algebra_simps)
  show ?thesis by (simp only: Poly_Mapping.lookup_minus first second)
    (simp add: algebra_simps diff_divide_distrib)
qed

lemma ramified_first_contraction_extremal_coeff_ne_zero:
  assumes "0<l" "laurent_upper f i" "laurent_upper g u"
    "i\<in>Poly_Mapping.keys f" "u\<in>Poly_Mapping.keys g"
    "(of_nat j*of_int u-of_nat k*of_int i::complex)\<noteq>0"
  shows "Poly_Mapping.lookup (f*laurent_smult (of_nat j) (ramified_derivative l g)-
    g*laurent_smult (of_nat k) (ramified_derivative l f)) (i+u-int l)\<noteq>0"
  by (subst ramified_first_contraction_extremal_coeff[OF assms(2,3,4,5)])
     (use assms(1,4,5,6) in \<open>simp add: Poly_Mapping.in_keys_iff\<close>)
end
