theory Ramified_First_Face_Bracket
  imports Ramified_Full_Weight_Filter
begin
lemma ramified_pbw_coeffs_atom_commutator_first_all:
  assumes "0<l" "0<n+m"
  shows "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l f n) (ramified_pbw_atom l g m)-
     laurent_comp (ramified_pbw_atom l g m) (ramified_pbw_atom l f n))) (n+m-1)=
    f*laurent_smult (of_nat n) (ramified_derivative l g)-
    g*laurent_smult (of_nat m) (ramified_derivative l f)"
proof (cases n)
  case (Suc k)
  have index: "Suc k+m-1=k+m" by presburger
  show ?thesis by (simp only: Suc index
    ramified_pbw_coeffs_atom_commutator_first_any_second[OF assms(1)])
next
  case 0
  obtain k where m: "m=Suc k" using assms(2) 0 by (cases m) auto
  have index: "0+Suc k-1=k" by presburger
  show ?thesis by (simp only: 0 m index
    ramified_pbw_coeffs_sub[OF assms(1)
    ramified_algebra_comp[OF ramified_pbw_atom_carrier ramified_pbw_atom_carrier]
    ramified_algebra_comp[OF ramified_pbw_atom_carrier ramified_pbw_atom_carrier]]
    Poly_Mapping.lookup_minus ramified_pbw_coeffs_zero_positive_product_next[OF assms(1)]
    ramified_pbw_coeffs_positive_zero_product_next[OF assms(1)] of_nat_0
    laurent_smult_zero_scalar mult_zero_right)
qed

lemma ramified_pbw_coeffs_commutator_first_face_coefficient:
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
      if n+m=j+1 then Poly_Mapping.lookup
        (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n *
          laurent_smult (of_nat n) (ramified_derivative l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m))-
         Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m *
          laurent_smult (of_nat m) (ramified_derivative l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n))) v
      else 0)"
unfolding ramified_pbw_coeffs_commutator_double_sum[OF assms(1,4,5)] Poly_Mapping.lookup_sum
proof (rule sum.cong[OF refl]; rule sum.cong[OF refl])
  fix n m assume n: "n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P)"
    and m: "m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q)"
  let ?f = "Poly_Mapping.lookup (ramified_pbw_coeffs l P) n"
  let ?g = "Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m"
  let ?h = "Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l ?f n) (ramified_pbw_atom l ?g m)-
     laurent_comp (ramified_pbw_atom l ?g m) (ramified_pbw_atom l ?f n))) j"
  show "Poly_Mapping.lookup ?h v=(if n+m=j+1 then Poly_Mapping.lookup
    (?f*laurent_smult (of_nat n) (ramified_derivative l ?g)-
     ?g*laurent_smult (of_nat m) (ramified_derivative l ?f)) v else 0)"
  proof (cases "n+m=j+1")
    case True
    have positive: "0<n+m" using True by presburger
    have index: "j=n+m-1" using True by presburger
    show ?thesis by (simp only: True refl if_True; subst index;
      simp only: ramified_pbw_coeffs_atom_commutator_first_all[OF assms(1) positive])
  next
    case False
    have zero: "Poly_Mapping.lookup ?h v=0"
    proof (cases "n+m\<le>j")
      case True
      show ?thesis by (simp only: ramified_pbw_coeffs_atom_commutator_zero_at_or_above[OF assms(1) True]
        Poly_Mapping.lookup_zero)
    next
      case lower: False
      have more: "j+2\<le>n+m" using False lower by presburger
      have contraction: "j+1\<le>n+m" using more by presburger
      show ?thesis
      proof (rule ccontr)
        assume "Poly_Mapping.lookup ?h v\<noteq>0"
        then have support: "v\<in>Poly_Mapping.keys ?h" by (simp add: Poly_Mapping.in_keys_iff)
        have defect: "rho*B n+int l*sigma*int n<A \<or> rho*C m+int l*sigma*int m<D \<or> j+2\<le>n+m"
          using more by simp
        have "ramified_weight l rho sigma (v,j)<A+D-int l*(rho+sigma)"
          by (rule ramified_pbw_coeffs_atom_commutator_below_first_of_defect_all[OF assms(1,2,3)
            assms(6)[OF n] assms(7)[OF m] contraction assms(8)[OF n] assms(9)[OF m] defect support])
        then show False using assms(10) by arith
      qed
    qed
    show ?thesis by (simp only: False if_False zero)
  qed
qed
end
