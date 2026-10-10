theory GGV_Single_Factor_Standardization
 imports "GGV_Singleton_Diagonal_Mate"
   "Homogeneous_Cut_Reconstruction"
   "Positive_Shear_Finite_Descent"
begin

lemma degreeMinimal_single_factor_subrectangular_pair:
 fixes P Q::"complex poly_operator" and lam alpha::complex and a k::nat
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
   and lam: "lam\<noteq>0" and a: "0<a" and k: "0<k"
   and diagonal: "total_degree P=a+k"
   and cut: "cut_poly 1 1 P=[:lam:]*[:-alpha,1:]^k"
 shows "\<exists>R S u v. is_degree_minimal_counterexample_pair R S \<and>
   total_degree R=total_degree P \<and> total_degree S=total_degree Q \<and>
   0<u \<and> 0<v \<and> is_subrectangular_at R a k \<and> is_subrectangular_at S u v \<and> a*v=k*u"
proof -
 obtain R S where minRS: "is_degree_minimal_counterexample_pair R S"
   and degreeR: "total_degree R=total_degree P" and degreeS: "total_degree S=total_degree Q"
   and translate: "cut_poly 1 1 R=pcompose (cut_poly 1 1 P) [:alpha,1:]"
   using degreeMinimal_linear_cut_recovers_pair[OF minimal, where c=alpha] by blast
 have pairRS: "is_counterexample_pair R S"
   using minRS by (simp add: is_degree_minimal_counterexample_pair_def)
 have affine: "pcompose ([:-alpha,1:]::complex poly) [:alpha,1:]=[:0,1:]"
   by (simp add: pcompose_pCons pcompose_1)
 have shifted: "cut_poly 1 1 R=[:lam:]*[:0,1:]^k"
   using translate by (simp add: cut pcompose_smult native_pcompose_power affine)
 have weight: "v_degree 1 1 R=int(a+k+0)"
   using counterexample_diagonal_weight_eq_total_degree[OF pairRS] degreeR diagonal by simp
 have shape: "leading_form 1 1 R=[:[:lam:]:]*(biv_monom 1 1 0)^a*(biv_monom 1 0 1)^k"
   using diagonal_face_eq_of_factored_cut[where P=R and lam=lam and alpha=0 and beta=0 and a=a and u=k and v=0, OF weight]
     shifted by simp
 have support: "biv_support(leading_form 1 1 R)={(a,k)}"
   by (simp only: shape weighted_monomial_support[OF lam])
 have member: "(a,k)\<in>biv_support(leading_form 1 1 R)" by (simp only: support; simp)
 have unique: "e=(a,k)" if "e\<in>biv_support(leading_form 1 1 R)" for e
   using that by (simp only: support; simp)
 have total: "total_degree R=a+k" by (simp only: degreeR diagonal)
 obtain u v where u: "0<u" and v: "0<v"
   and rectangleR: "is_subrectangular_at R a k" and rectangleS: "is_subrectangular_at S u v"
   and proportional: "a*v=k*u"
   using preliminary_companion_singleton_diagonal_pair_subrectangular[OF
     preliminary_companion_from_actual_GGV_companion pairRS total member unique a k] by blast
 show ?thesis by (intro exI[of _ R] exI[of _ S] exI[of _ u] exI[of _ v])
   (use minRS degreeR degreeS u v rectangleR rectangleS proportional in blast)
qed

end
