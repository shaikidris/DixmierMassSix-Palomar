theory GGV_Two_Root_Standardization
 imports "GGV_Single_Factor_Standardization"
   "Fourier_Diagonal_Symbol"
begin

lemma degreeMinimal_two_root_subrectangular_pair:
 fixes P Q::"complex poly_operator" and lam alpha beta::complex and u v::nat
 assumes minimal: "is_degree_minimal_counterexample_pair P Q"
   and lam: "lam\<noteq>0" and distinct: "alpha\<noteq>beta" and u: "0<u" and v: "0<v"
   and diagonal: "total_degree P=u+v"
   and cut: "cut_poly 1 1 P=[:lam:]*[:-alpha,1:]^u*[:-beta,1:]^v"
 shows "\<exists>R S a b. is_degree_minimal_counterexample_pair R S \<and>
   total_degree R=total_degree P \<and> total_degree S=total_degree Q \<and>
   0<a \<and> 0<b \<and> is_subrectangular_at R u v \<and> is_subrectangular_at S a b \<and> u*b=v*a"
proof -
 obtain R S where minRS: "is_degree_minimal_counterexample_pair R S"
   and degreeR: "total_degree R=total_degree P" and degreeS: "total_degree S=total_degree Q"
   and translate: "cut_poly 1 1 R=pcompose (cut_poly 1 1 P) [:alpha,1:]"
   using degreeMinimal_linear_cut_recovers_pair[OF minimal, where c=alpha] by blast
 let ?gamma="beta-alpha"
 have gamma: "?gamma\<noteq>0" using distinct by auto
 have pairRS: "is_counterexample_pair R S"
   using minRS by (simp add: is_degree_minimal_counterexample_pair_def)
 have R: "R\<in>weyl_algebra" and S: "S\<in>weyl_algebra"
   using pairRS by (simp_all add: is_counterexample_pair_def)
 have alpha_shift: "pcompose ([:-alpha,1:]::complex poly) [:alpha,1:]=[:0,1:]"
   by (simp add: pcompose_pCons pcompose_1)
 have beta_shift: "pcompose ([:-beta,1:]::complex poly) [:alpha,1:]=[:-?gamma,1:]"
   by (simp add: pcompose_pCons pcompose_1 algebra_simps)
 have shifted: "cut_poly 1 1 R=[:lam:]*[:0,1:]^u*[:-?gamma,1:]^v"
   using translate by (simp add: cut pcompose_mult pcompose_smult native_pcompose_power alpha_shift beta_shift)
 have weight: "v_degree 1 1 R=int(0+u+v)"
   using counterexample_diagonal_weight_eq_total_degree[OF pairRS] degreeR diagonal by simp
 have face: "leading_form 1 1 R=[:[:lam:]:]*(biv_monom 1 0 1)^u*
   (biv_monom 1 0 1-[:[:?gamma:]:]*biv_monom 1 1 0)^v"
   using diagonal_face_eq_of_factored_cut[where P=R and lam=lam and alpha=0 and beta="?gamma" and a=0 and u=u and v=v, OF weight]
     shifted by simp
 let ?mu="lam*(-1)^u*(-?gamma)^v"
 have mu: "?mu\<noteq>0" using lam gamma by simp
 have reverse_difference: "alpha-beta= -(beta-alpha)" by simp
 have inverse_coefficient: "inverse (beta-alpha)*(alpha-beta)= -1"
   by (simp only: reverse_difference mult_minus_right left_inverse[OF gamma])
 have linear: "([:-1:]::complex poly)-[:?gamma:]*[:0,1:]=[:-?gamma:]*[:inverse ?gamma,1:]"
   by (rule poly_eqI) (simp add: gamma inverse_coefficient coeff_pCons' split: nat.splits)
 have Fcut: "cut_poly 1 1 (fourier_alg_hom R)=[:?mu:]*[:inverse ?gamma,1:]^v"
 proof -
   have coefficient_linear: "([:-1:]::complex poly)-smult ?gamma (monom 1 (Suc 0))=[:-1,alpha-beta:]"
     by (rule poly_eqI) (simp add: coeff_pCons' coeff_monom split: nat.splits)
   have evaluation: "cut_poly 1 1 (fourier_alg_hom R)=
     [:lam:]*([:-1:]::complex poly)^u*([:-1:]-[:?gamma:]*[:0,1:])^v"
     by (simp add: cut_fourier_diagonal_evaluation[OF R] face biv_monom_def poly_monom coefficient_linear)
   have constant_power: "([:z:]::complex poly)^m=[:z^m:]" for z::complex and m::nat
     by (induction m) (simp_all add: one_pCons)
   show ?thesis by (simp only: evaluation linear power_mult_distrib constant_power)
     (simp add: algebra_simps)
 qed
 have minF: "is_degree_minimal_counterexample_pair (fourier_alg_hom R) (fourier_alg_hom S)"
   by (rule degreeMinimal_fourier_preserved[OF minRS])
 have degreeF: "total_degree(fourier_alg_hom R)=u+v"
   by (simp only: totalDeg_fourier_eq[OF R] degreeR diagonal)
 obtain T U a b where minTU: "is_degree_minimal_counterexample_pair T U"
   and degreeT: "total_degree T=total_degree(fourier_alg_hom R)"
   and degreeU: "total_degree U=total_degree(fourier_alg_hom S)"
   and a: "0<a" and b: "0<b" and rectangleT: "is_subrectangular_at T u v"
   and rectangleU: "is_subrectangular_at U a b" and proportional: "u*b=v*a"
   using degreeMinimal_single_factor_subrectangular_pair[OF minF mu u v degreeF,
     where alpha="-inverse ?gamma"] Fcut by (simp; blast)
 show ?thesis by (intro exI[of _ T] exI[of _ U] exI[of _ a] exI[of _ b])
   (use minTU degreeT degreeU degreeR degreeS a b rectangleT rectangleU proportional
     in \<open>simp add: totalDeg_fourier_eq[OF R] totalDeg_fourier_eq[OF S]\<close>)
qed

end
