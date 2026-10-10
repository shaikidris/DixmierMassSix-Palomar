theory GGV_Pure_Linear_Minimal_Exclusion
 imports GGV_Positive_Face_Minimal_Exclusion
   "Fourier_Diagonal_Symbol"
begin

lemma degreeMinimal_diagonal_y_power_impossible:
 fixes P Q::"complex poly_operator" and lam::complex and b::nat
 assumes minimal: "is_degree_minimal_counterexample_pair P Q" and lam: "lam\<noteq>0"
   and shape: "leading_form 1 1 P=[:[:lam:]:]*(biv_monom 1 0 1)^b"
 shows False
proof -
 have pair: "is_counterexample_pair P Q" using minimal by (simp add: is_degree_minimal_counterexample_pair_def)
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have original: "biv_support(leading_form 1 1 P)={(0,b)}"
   using weighted_monomial_support[OF lam, where a=0 and b=b] shape by simp
 have total: "total_degree P=b"
   using diagonal_face_point_total_degree[where P=P and e="(0,b)"] original by simp
 have only: "e=(0,b)" if "e\<in>biv_support(leading_form 1 1 P)" for e using original that by simp
 have positive: "0<b"
   using counterexample_vDeg_pos_all_directions[OF pair, where rho=1 and sigma=1]
     counterexample_diagonal_weight_eq_total_degree[OF pair] total by (simp add: is_direction_def)
 have diagonal: "total_degree P=0+b" using total by simp
 have positive_sum: "0<0+b" using positive by simp
 have fourier_data: "(b,0)\<in>biv_support(leading_form 1 1 (fourier_alg_hom P)) \<and>
   (\<forall>e\<in>biv_support(leading_form 1 1 (fourier_alg_hom P)). e=(b,0))"
   by (rule fourier_diagonal_face_unique[where P=P and a=0 and b=b,
     OF P diagonal positive_sum only])
 have Fourier: "(b,0)\<in>biv_support(leading_form 1 1 (fourier_alg_hom P))"
   by (rule conjunct1[OF fourier_data])
 have Fourier_only: "e=(b,0)"
   if member: "e\<in>biv_support(leading_form 1 1 (fourier_alg_hom P))" for e
   by (rule bspec[OF conjunct2[OF fourier_data] member])
 show False by (rule degreeMinimal_diagonal_axis_singleton_impossible[OF
   degreeMinimal_fourier_preserved[OF minimal] Fourier Fourier_only])
qed

lemma degreeMinimal_pure_linear_diagonal_impossible:
 fixes P Q::"complex poly_operator" and lam alpha::complex and b::nat
 assumes minimal: "is_degree_minimal_counterexample_pair P Q" and lam: "lam\<noteq>0"
   and degree: "total_degree P=b" and cut: "cut_poly 1 1 P=[:lam:]*[:-alpha,1:]^b"
 shows False
proof -
 obtain R S where minRS: "is_degree_minimal_counterexample_pair R S"
   and degreeR: "total_degree R=total_degree P"
   and translate: "cut_poly 1 1 R=pcompose (cut_poly 1 1 P) [:alpha,1:]"
   using degreeMinimal_linear_cut_recovers_pair[OF minimal, where c=alpha] by blast
 have pairRS: "is_counterexample_pair R S" using minRS by (simp add: is_degree_minimal_counterexample_pair_def)
 have affine: "pcompose ([:-alpha,1:]::complex poly) [:alpha,1:]=[:0,1:]"
   by (simp add: pcompose_pCons pcompose_1)
 have Rcut: "cut_poly 1 1 R=[:lam:]*[:0,1:]^b"
   by (simp add: translate cut pcompose_smult native_pcompose_power affine)
 have Rweight: "v_degree 1 1 R=int(0+1*b)"
   using counterexample_diagonal_weight_eq_total_degree[OF pairRS] degreeR degree by simp
 have native_weight: "v_degree 1 (int(1::nat)) R=int(0+1*b)" using Rweight by simp
 have native_cut: "cut_poly 1 (int(1::nat)) R=[:lam:]*[:- (0::complex),1:]^b" using Rcut by simp
 have Rshape: "leading_form 1 1 R=[:[:lam:]:]*(biv_monom 1 0 1)^b"
   using positive_face_eq_of_linear_power_cut[where P=R and lam=lam and alpha=0 and sigma=1 and a=0 and k=b,
     OF native_weight native_cut] by simp
 show False by (rule degreeMinimal_diagonal_y_power_impossible[OF minRS lam Rshape])
qed

end
