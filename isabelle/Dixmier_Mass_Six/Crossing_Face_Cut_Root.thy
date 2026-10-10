theory Crossing_Face_Cut_Root
 imports "Crossing_Face_Endpoints"
   "Crossing_Cut_Multiplicity"
begin

lemma crossing_scalar_binomial_eval:
 "biv_univariate_eval ([:1,alpha:]^q) (biv_monom 1 s rho)=(1+biv_monom alpha s rho)^q"
proof -
 have linear: "biv_univariate_eval [:1,alpha:] (biv_monom 1 s rho)=1+biv_monom alpha s rho"
   by (simp add: biv_univariate_eval_def biv_monom_def map_poly_pCons one_pCons monom_0 mult_monom smult_monom)
 show ?thesis by (simp only: coefficient_hom_power[OF biv_univariate_eval_hom] linear)
qed

lemma crossingFace_cutPoly_maxRootMult:
 fixes T::"complex poly_operator" and q rho s e::nat
 assumes alpha: "alpha\<noteq>0" and nu: "nu\<noteq>0" and q: "0<q" and rho: "0<rho" and e: "0<e"
 and face: "leading_form (int rho) (-int s) T=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^e"
 shows "max_root_mult(cut_poly (int rho) (-int s) T)=q*e"
proof -
 let ?r="[:1,alpha:]^q"
 let ?beta="-inverse alpha"
 have beta: "?beta\<noteq>0" using alpha by simp
 have linear: "[:1,alpha:]=smult alpha [:-?beta,1:]"
   using alpha by (simp add: smult_pCons)
 have lnz: "([:1,alpha:]::complex poly)\<noteq>0" by simp
 have rnz: "?r\<noteq>0" using lnz by simp
 have degree: "degree([:1,alpha:]::complex poly)=1" using alpha by simp
 have rdegree: "degree ?r=q" by (simp only: degree_power_eq[OF lnz] degree mult_1_right)
 have root: "rootMultiplicity ?beta ?r=q"
 proof -
   have power: "?r=smult(alpha^q)([:-?beta,1:]^q)"
     by (simp only: linear smult_power)
   have scalar: "alpha^q\<noteq>0" using alpha by simp
   have poly_order: "Polynomial.order ?beta ?r=q"
     by (simp only: power Polynomial.order_smult[OF scalar] Polynomial.order_power_n_n)
   show ?thesis by (simp only: rootMultiplicity_eq_order[OF rnz] poly_order)
 qed
 have r0: "coeff ?r 0=1" by (simp add: coeff_0_power)
 have shape: "leading_form (int rho) (-int s) T=
   [:[:nu:]:]*(biv_monom 1 1 0*biv_univariate_eval ?r (biv_monom 1 s rho))^e"
   by (simp only: face crossing_primitive_base_binomial_form crossing_scalar_binomial_eval)
 have result: "max_root_mult(cut_poly (int rho) (-int s) T)=e*degree ?r"
   by (rule crossingFace_general_cutPoly_maxRootMult_of_full_scalar_root[where a=1 and b=0, OF nu rho e r0 beta])
     (use root rdegree q shape in auto)
 show ?thesis using result by (simp only: rdegree mult.commute)
qed

end
