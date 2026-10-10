theory Polynomial_Shear_Top_Row
 imports "Polynomial_Monomial_Shear_Recovery"
   "Polynomial_Lift_Face_Transport"
begin

lemma ramified_cut_aut_pbwCoeff_zero_above_bound:
 fixes T::laurent_operator
 assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
   and rows: "\<And>n. b<n \<Longrightarrow> Poly_Mapping.lookup (ramified_pbw_coeffs l T) n=0"
   and above: "b<j"
 shows "ramified_pbw_coeff l (ramified_cut_aut l rho sigma c T) i j=0"
proof -
 have summand_zero: "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n *
   Poly_Mapping.lookup (ramified_shift_pbw_power l (ramified_cut_shift l rho sigma c) n) j) i=0" for n
 proof (cases "b<n")
   case True show ?thesis by (simp only: rows[OF True] mult_zero_left Poly_Mapping.lookup_zero)
 next
   case False
   have high: "n<j" using above False by arith
   show ?thesis by (simp only: ramified_shift_pbw_power_zero_above[OF high] mult_zero_right Poly_Mapping.lookup_zero)
 qed
 show ?thesis by (simp only: ramified_cut_aut_pbw_coeff_finset[OF l T] summand_zero sum.neutral_const)
qed

lemma ramified_cut_aut_pbwCoeff_top_row:
 fixes T::laurent_operator
 assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
   and rows: "\<And>n. b<n \<Longrightarrow> Poly_Mapping.lookup (ramified_pbw_coeffs l T) n=0"
 shows "ramified_pbw_coeff l (ramified_cut_aut l rho sigma c T) i b=ramified_pbw_coeff l T i b"
proof -
 have delta: "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n *
   Poly_Mapping.lookup (ramified_shift_pbw_power l (ramified_cut_shift l rho sigma c) n) b) i=
   (if n=b then ramified_pbw_coeff l T i b else 0)" for n
 proof (cases "n=b")
   case True show ?thesis by (simp only: True if_True ramified_shift_pbw_power_top mult_1_right ramified_pbw_coeff_def; simp)
 next
   case False
   show ?thesis
   proof (cases "b<n")
     case True show ?thesis by (simp only: rows[OF True] mult_zero_left Poly_Mapping.lookup_zero False if_False)
   next
     case no: False
     have high: "n<b" using no False by arith
     show ?thesis by (simp only: ramified_shift_pbw_power_zero_above[OF high] mult_zero_right Poly_Mapping.lookup_zero False if_False)
   qed
 qed
 show ?thesis
 proof (cases "b\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T)")
   case True show ?thesis by (simp only: ramified_cut_aut_pbw_coeff_finset[OF l T] delta sum.delta[OF Poly_Mapping.finite_keys] True if_True)
 next
   case False
   have rowzero: "Poly_Mapping.lookup (ramified_pbw_coeffs l T) b=0"
     using False by (simp only: Poly_Mapping.in_keys_iff; simp)
   have rhs_zero: "ramified_pbw_coeff l T i b=0"
     by (simp only: ramified_pbw_coeff_def rowzero Poly_Mapping.lookup_zero)
   have lhs_zero: "ramified_pbw_coeff l (ramified_cut_aut l rho sigma c T) i b=0"
   proof -
     have "ramified_pbw_coeff l (ramified_cut_aut l rho sigma c T) i b=
       (\<Sum>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
        Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n *
         Poly_Mapping.lookup (ramified_shift_pbw_power l (ramified_cut_shift l rho sigma c) n) b) i)"
       by (rule ramified_cut_aut_pbw_coeff_finset[OF l T])
     also have "...=0"
       by (simp only: delta sum.delta[OF Poly_Mapping.finite_keys] False if_False)
     finally show ?thesis .
   qed
   show ?thesis using lhs_zero rhs_zero by simp
 qed
qed

lemma polynomial_lift_zero_above_y_bound:
 fixes P::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra"
   and bound: "\<And>e. e\<in>biv_support(pbw_symbol P) \<Longrightarrow> snd e\<le>b"
   and above: "b<n"
 shows "Poly_Mapping.lookup (ramified_pbw_coeffs 1 (polynomial_ramified_lift 1 P)) n=0"
proof (rule poly_mapping_eqI)
 fix i
 show "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs 1 (polynomial_ramified_lift 1 P)) n) i=Poly_Mapping.lookup 0 i"
 proof (rule ccontr)
   assume nonzero: "\<not>Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs 1 (polynomial_ramified_lift 1 P)) n) i=Poly_Mapping.lookup 0 i"
   have coefficient: "ramified_pbw_coeff 1 (polynomial_ramified_lift 1 P) i n\<noteq>0"
     using nonzero by (simp add: ramified_pbw_coeff_def)
   have support: "(i,n)\<in>ramified_pbw_support 1 (polynomial_ramified_lift 1 P)"
     using coefficient ramified_pbw_support_mem_iff[OF zero_less_one polynomial_ramified_lift_carrier] by blast
   obtain k where source: "(k,n)\<in>biv_support(pbw_symbol P)"
     using support by (simp only: polynomialRamifiedLift_support_iff_symbol[OF zero_less_one P]; blast)
   have "n\<le>b" using bound[OF source] by simp
   then show False using above by arith
 qed
qed

lemma polynomial_cut_preserves_y_bound_and_top_row:
 fixes P R::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and R: "R\<in>weyl_algebra"
   and bound: "\<And>e. e\<in>biv_support(pbw_symbol P) \<Longrightarrow> snd e\<le>b"
   and recover: "polynomial_ramified_lift 1 R=ramified_cut_aut 1 rho sigma c (polynomial_ramified_lift 1 P)"
 shows "(\<forall>e\<in>biv_support(pbw_symbol R). snd e\<le>b) \<and>
   (\<forall>i. pbw_coeff R i b=pbw_coeff P i b)"
proof -
 have rows: "Poly_Mapping.lookup (ramified_pbw_coeffs 1 (polynomial_ramified_lift 1 P)) n=0"
   if "b<n" for n by (rule polynomial_lift_zero_above_y_bound[OF P bound that])
 have scaledP: "ramified_pbw_coeff 1 (polynomial_ramified_lift 1 P) (int i) j=pbw_coeff P i j" for i j
   using polynomial_ramified_lift_pbwCoeff_scaled[OF zero_less_one P, where i=i and j=j] by simp
 have scaledR: "ramified_pbw_coeff 1 (polynomial_ramified_lift 1 R) (int i) j=pbw_coeff R i j" for i j
   using polynomial_ramified_lift_pbwCoeff_scaled[OF zero_less_one R, where i=i and j=j] by simp
 have top: "pbw_coeff R i b=pbw_coeff P i b" for i
   using ramified_cut_aut_pbwCoeff_top_row[OF zero_less_one polynomial_ramified_lift_carrier rows,
     where rho=rho and sigma=sigma and c=c and i="int i"]
   by (simp only: recover[symmetric] scaledR scaledP)
 have upper: "snd e\<le>b" if source: "e\<in>biv_support(pbw_symbol R)" for e
 proof (rule ccontr)
   assume "\<not>snd e\<le>b" then have above: "b<snd e" by arith
   have zero: "pbw_coeff R (fst e) (snd e)=0"
     using ramified_cut_aut_pbwCoeff_zero_above_bound[OF zero_less_one polynomial_ramified_lift_carrier rows above,
       where rho=rho and sigma=sigma and c=c and i="int(fst e)"]
     by (simp only: recover[symmetric] scaledR)
   show False using source by (simp add: biv_support_def weyl_symbol_coeff[OF R] zero)
 qed
 show ?thesis using top upper by blast
qed

lemma polynomial_cut_preserves_top_row_point:
 fixes P R::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra" and R: "R\<in>weyl_algebra"
   and bound: "\<And>e. e\<in>biv_support(pbw_symbol P) \<Longrightarrow> snd e\<le>b"
   and point: "(a,b)\<in>biv_support(pbw_symbol P)"
   and recover: "polynomial_ramified_lift 1 R=ramified_cut_aut 1 rho sigma c (polynomial_ramified_lift 1 P)"
 shows "(a,b)\<in>biv_support(pbw_symbol R)"
proof -
 have top: "pbw_coeff R a b=pbw_coeff P a b"
   using polynomial_cut_preserves_y_bound_and_top_row[OF P R bound recover] by blast
 show ?thesis using point by (simp add: biv_support_def weyl_symbol_coeff[OF P] weyl_symbol_coeff[OF R] top)
qed

end
