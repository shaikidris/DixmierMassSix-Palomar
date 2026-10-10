theory Horizontal_Crossing
 imports "Horizontal_Mass_Six_Shape"
   "Pure_Power_Face_Exclusion"
begin

lemma horizontalCrossingExclusion_of_GGV:
 fixes P Q::"complex poly_operator"
 assumes inputs: GGVInputs and pair: "is_counterexample_pair P Q" and mass: "weyl_mass P\<le>6"
 shows "\<not>strict_crossing 1 0 P"
proof
 assume crossing: "strict_crossing 1 0 P"
 obtain mu c beta where mu: "mu\<noteq>0" and c: "c\<noteq>0" and beta: "beta\<noteq>0"
 and face: "leading_form 1 0 P=[:[:mu:]:]*(biv_monom 1 1 0*biv_univariate_eval ([:c:]*[:-beta,1:]^2)(biv_monom 1 0 1))^2"
  using horizontal_counterexample_mass_six_scalar_shape[OF inputs pair crossing mass] by blast
 have alpha: "-inverse beta\<noteq>0" using beta by simp
 have nu: "mu*(c*beta^2)^2\<noteq>0" using mu c beta by simp
 have face': "leading_form 1 0 P=[:[:mu*(c*beta^2)^2:]:]*(biv_monom 1 1 0)^2*
 (1+[:[:-inverse beta:]:]*biv_monom 1 0 1)^4"
  by (simp only: face horizontal_face_normalize[OF beta])
 have forbidden: "leading_form 1 0 P\<noteq>[:[:mu*(c*beta^2)^2:]:]*(biv_monom 1 1 0)^2*
 (1+[:[:-inverse beta:]:]*biv_monom 1 0 1)^4"
 proof -
  have X: "(biv_monom 1 1 0::complex bivariate)=[:[:0,1:]:]"
   by (simp add: biv_monom_def monom_altdef)
  have Y: "(biv_monom 1 0 1::complex bivariate)=[:0,1:]"
   by (simp add: biv_monom_def monom_altdef one_pCons)
  have two: "2\<le>(2::nat)" and parameter: "(2-1)*(1::nat)=2*0+1" and prime: "prime(2::nat)" by simp_all
  show ?thesis using purePowerFaceExclusion_of_GGV[OF inputs two parameter prime alpha nu pair]
   by (simp only: X Y; simp)
 qed
 show False using forbidden face' by blast
qed

end
