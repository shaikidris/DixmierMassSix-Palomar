theory Ramified_First_Face_Canonical
 imports Ramified_First_Face_Top_Pairs
begin
lemma ramified_pbw_coeffs_commutator_first_face_canonical:
  assumes "0<l" "0<rho" "0<rho+sigma"
    "P\<in>ramified_operator_algebra l" "Q\<in>ramified_operator_algebra l"
    "P\<noteq>0" "Q\<noteq>0"
    "ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)\<le>ramified_weight l rho sigma (v,j)"
  shows "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp P Q-laurent_comp Q P)) j) v=
    (\<Sum>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
     \<Sum>m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
      if n+m=j+1 \<and> rho*ramified_pbw_top_laurent l P n+int l*sigma*int n=ramified_weight_deg l rho sigma P \<and> rho*ramified_pbw_top_laurent l Q m+int l*sigma*int m=ramified_weight_deg l rho sigma Q then Poly_Mapping.lookup
        (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n *
          laurent_smult (of_nat n) (ramified_derivative l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m))-
         Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m *
          laurent_smult (of_nat m) (ramified_derivative l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n))) v
      else 0)"
proof -
  have nonemptyP: "ramified_pbw_support l P\<noteq>{}"
    by (rule ramified_pbw_support_nonempty_of_ne_zero[OF assms(1,4,6)])
  have nonemptyQ: "ramified_pbw_support l Q\<noteq>{}"
    by (rule ramified_pbw_support_nonempty_of_ne_zero[OF assms(1,5,7)])
  obtain A N where boundP: "\<forall>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
    rho*ramified_pbw_top_laurent l P n+int l*sigma*int n\<le>A"
    and degreeP: "ramified_weight_deg l rho sigma P=A"
    using exists_ramified_canonical_face_endpoint[OF assms(2) nonemptyP, where sigma=sigma] by blast
  obtain D M where boundQ: "\<forall>m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
    rho*ramified_pbw_top_laurent l Q m+int l*sigma*int m\<le>D"
    and degreeQ: "ramified_weight_deg l rho sigma Q=D"
    using exists_ramified_canonical_face_endpoint[OF assms(2) nonemptyQ, where sigma=sigma] by blast
  have threshold: "A+D-int l*(rho+sigma)\<le>ramified_weight l rho sigma (v,j)"
    using assms(8) degreeP degreeQ by simp
  have uppersP: "\<And>n. n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P) \<Longrightarrow>
    laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) (ramified_pbw_top_laurent l P n)"
    by (rule ramified_pbw_top_laurent_upper)
  have uppersQ: "\<And>m. m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q) \<Longrightarrow>
    laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) (ramified_pbw_top_laurent l Q m)"
    by (rule ramified_pbw_top_laurent_upper)
  have weightsP: "\<And>n. n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P) \<Longrightarrow>
    rho*ramified_pbw_top_laurent l P n+int l*sigma*int n\<le>A" using boundP by simp
  have weightsQ: "\<And>m. m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q) \<Longrightarrow>
    rho*ramified_pbw_top_laurent l Q m+int l*sigma*int m\<le>D" using boundQ by simp
  show ?thesis using ramified_pbw_coeffs_commutator_first_face_top_pairs[OF assms(1,2,3,4,5)
    uppersP uppersQ weightsP weightsQ threshold] by (simp only: degreeP degreeQ)
qed
end
