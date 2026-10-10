theory Ramified_First_Face_Top_Pairs
  imports Ramified_First_Face_Bracket
begin
lemma ramified_first_face_atom_coeff_zero_of_lower_weight:
  assumes "0<l" "0<rho" "0<rho+sigma" "laurent_upper f B" "laurent_upper g C"
    "n+m=j+1" "rho*B+int l*sigma*int n\<le>A" "rho*C+int l*sigma*int m\<le>D"
    "rho*B+int l*sigma*int n<A \<or> rho*C+int l*sigma*int m<D"
    "A+D-int l*(rho+sigma)\<le>ramified_weight l rho sigma (v,j)"
  shows "Poly_Mapping.lookup (f*laurent_smult (of_nat n) (ramified_derivative l g)-
    g*laurent_smult (of_nat m) (ramified_derivative l f)) v=0"
proof (rule ccontr)
  assume nonzero: "Poly_Mapping.lookup (f*laurent_smult (of_nat n) (ramified_derivative l g)-
    g*laurent_smult (of_nat m) (ramified_derivative l f)) v\<noteq>0"
  have index: "j=n+m-1" and positive: "0<n+m" and contraction: "j+1\<le>n+m"
    using assms(6) by presburger+
  have support: "v\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m)-
     laurent_comp (ramified_pbw_atom l g m) (ramified_pbw_atom l f n))) j)"
    using nonzero by (simp only: index ramified_pbw_coeffs_atom_commutator_first_all[OF assms(1) positive]
      Poly_Mapping.in_keys_iff; simp)
  have defect: "rho*B+int l*sigma*int n<A \<or> rho*C+int l*sigma*int m<D \<or> j+2\<le>n+m"
    using assms(9) by blast
  have "ramified_weight l rho sigma (v,j)<A+D-int l*(rho+sigma)"
    by (rule ramified_pbw_coeffs_atom_commutator_below_first_of_defect_all[OF assms(1,2,3,4,5)
      contraction assms(7,8) defect support])
  then show False using assms(10) by arith
qed

lemma ramified_pbw_coeffs_commutator_first_face_top_pairs:
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
  shows "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp P Q-laurent_comp Q P)) j) v=
    (\<Sum>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
     \<Sum>m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
      if n+m=j+1 \<and> rho*B n+int l*sigma*int n=A \<and> rho*C m+int l*sigma*int m=D then Poly_Mapping.lookup
        (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n *
          laurent_smult (of_nat n) (ramified_derivative l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m))-
         Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m *
          laurent_smult (of_nat m) (ramified_derivative l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n))) v
      else 0)"
proof -
  have first_coefficient: "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp P Q-laurent_comp Q P)) j) v=
    (\<Sum>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
     \<Sum>m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
      if n+m=j+1 then Poly_Mapping.lookup
        (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n *
          laurent_smult (of_nat n) (ramified_derivative l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m))-
         Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m *
          laurent_smult (of_nat m) (ramified_derivative l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n))) v
      else 0)"
    by (rule ramified_pbw_coeffs_commutator_first_face_coefficient[OF assms])
  have normalized: "    (\<Sum>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
     \<Sum>m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
      if n+m=j+1 then Poly_Mapping.lookup
        (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n *
          laurent_smult (of_nat n) (ramified_derivative l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m))-
         Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m *
          laurent_smult (of_nat m) (ramified_derivative l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n))) v
      else 0)=
    (\<Sum>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
     \<Sum>m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
      if n+m=j+1 \<and> rho*B n+int l*sigma*int n=A \<and> rho*C m+int l*sigma*int m=D then Poly_Mapping.lookup
        (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n *
          laurent_smult (of_nat n) (ramified_derivative l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m))-
         Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m *
          laurent_smult (of_nat m) (ramified_derivative l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n))) v
      else 0)"
  proof (rule sum.cong[OF refl]; rule sum.cong[OF refl])
    fix n m assume n: "n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P)"
      and m: "m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q)"
    let ?f = "Poly_Mapping.lookup (ramified_pbw_coeffs l P) n"
    let ?g = "Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m"
    let ?c = "Poly_Mapping.lookup (?f*laurent_smult (of_nat n) (ramified_derivative l ?g)-
      ?g*laurent_smult (of_nat m) (ramified_derivative l ?f)) v"
    show "(if n+m=j+1 then ?c else 0)=
      (if n+m=j+1 \<and> rho*B n+int l*sigma*int n=A \<and> rho*C m+int l*sigma*int m=D then ?c else 0)"
    proof (cases "n+m=j+1")
      case False then show ?thesis by simp
    next
      case first: True
      show ?thesis
      proof (cases "rho*B n+int l*sigma*int n=A \<and> rho*C m+int l*sigma*int m=D")
        case True then show ?thesis using first by simp
      next
        case False
        have defect: "rho*B n+int l*sigma*int n<A \<or> rho*C m+int l*sigma*int m<D"
          using False assms(8)[OF n] assms(9)[OF m] by arith
        have zero: "?c=0"
          by (rule ramified_first_face_atom_coeff_zero_of_lower_weight[OF assms(1,2,3)
            assms(6)[OF n] assms(7)[OF m] first assms(8)[OF n] assms(9)[OF m] defect assms(10)])
        show ?thesis using first False zero by simp
      qed
    qed
  qed
  show ?thesis by (rule trans[OF first_coefficient normalized])
qed
end
