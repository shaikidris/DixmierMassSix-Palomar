theory Positive_Shear_Monomial_Face
 imports "Polynomial_Cut_Translation"
   "Positive_Binomial_Reconstruction"
begin

lemma polynomial_root_shear_monomial_face:
 fixes P Q::"complex poly_operator" and sigma a k::nat and lam alpha::complex
 assumes pair: "is_counterexample_pair P Q"
 and degree: "v_degree 1 (int sigma) P=int(a+sigma*k)"
 and cut: "cut_poly 1 (int sigma) P=[:lam:]*[:-alpha,1:]^k"
 shows "\<exists>R S::complex poly_operator. is_counterexample_pair R S \<and>
   polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 (int sigma) alpha (polynomial_ramified_lift 1 P) \<and>
   leading_form 1 (int sigma) R=[:[:lam:]:]*(biv_monom 1 1 0)^a*(biv_monom 1 0 1)^k"
proof -
 obtain R S where RS: "is_counterexample_pair R S"
 and recover: "polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 (int sigma) alpha (polynomial_ramified_lift 1 P)"
 and weight: "v_degree 1 (int sigma) R=v_degree 1 (int sigma) P"
 and newcut: "cut_poly 1 (int sigma) R=[:lam:]*[:0,1:]^k"
   using polynomial_monomial_cut_removes_root[OF pair cut] by blast
 have degreeR: "v_degree 1 (int sigma) R=int(a+sigma*k)" using weight degree by simp
 have shape: "leading_form 1 (int sigma) R=[:[:lam:]:]*(biv_monom 1 1 0)^a*(biv_monom 1 0 1)^k"
   using positive_face_eq_of_linear_power_cut[where P=R and lam=lam and alpha=0 and sigma=sigma and a=a and k=k,
     OF degreeR] newcut by simp
 show ?thesis by (intro exI[of _ R] exI[of _ S]) (use RS recover shape in blast)
qed

lemma preliminary_positive_face_shear_monomial:
 fixes P Q::"complex poly_operator" and sigma::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
 and sigma: "1<sigma" and face: "in_direction 1 (int sigma) P"
 shows "\<exists>lam alpha::complex. \<exists>a k::nat. \<exists>R S::complex poly_operator.
   lam\<noteq>0 \<and> alpha\<noteq>0 \<and> 1\<le>k \<and> is_counterexample_pair R S \<and>
   polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 (int sigma) alpha (polynomial_ramified_lift 1 P) \<and>
   leading_form 1 (int sigma) R=[:[:lam:]:]*(biv_monom 1 1 0)^a*(biv_monom 1 0 1)^k"
proof -
 obtain lam alpha a k where lam: "lam\<noteq>0" and alpha: "alpha\<noteq>0" and k: "1\<le>k"
 and degree: "v_degree 1 (int sigma) P=int(a+sigma*k)"
 and shape: "leading_form 1 (int sigma) P=[:[:lam:]:]*(biv_monom 1 1 0)^a*(biv_monom 1 0 1-[:[:alpha:]:]*(biv_monom 1 1 0)^sigma)^k"
   using preliminary_positive_face_binomial[OF source pair sigma face] by blast
 have cut: "cut_poly 1 (int sigma) P=[:lam:]*[:-alpha,1:]^k" by (rule positive_binomial_face_cut[OF shape])
 obtain R S where RS: "is_counterexample_pair R S"
 and recover: "polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 (int sigma) alpha (polynomial_ramified_lift 1 P)"
 and mono: "leading_form 1 (int sigma) R=[:[:lam:]:]*(biv_monom 1 1 0)^a*(biv_monom 1 0 1)^k"
   using polynomial_root_shear_monomial_face[OF pair degree cut] by blast
 show ?thesis using lam alpha k RS recover mono by blast
qed

end
