theory Homogeneous_Power_Ratio
  imports Bivariate_Ratio
begin

lemma homogeneous_poisson_derivative_identities:
  fixes B R :: "complex bivariate"
  assumes hB: "weighted_homogeneous rho sigma omega B"
    and hR: "weighted_homogeneous rho sigma m R"
    and hbr: "biv_poisson B R=0"
  shows "([:[:of_int m:]:]*(R*biv_dx B)=[:[:of_int omega:]:]*(B*biv_dx R)) \<and>
    ([:[:of_int m:]:]*(R*biv_dy B)=[:[:of_int omega:]:]*(B*biv_dy R))"
  using homogeneous_poisson_euler_bracket_identities[OF hB hR] hbr
  by (simp add: algebra_simps)

lemma joseph_cross_derivative_of_logarithmic_identity:
  fixes B R :: "complex bivariate"
  assumes h: "of_nat (Suc a)*(R*biv_deriv is_y B)=of_nat (Suc b)*(B*biv_deriv is_y R)"
  shows "R^Suc b*biv_deriv is_y (B^Suc a)=B^Suc a*biv_deriv is_y (R^Suc b)"
proof -
  have dpow: "biv_deriv is_y (T^Suc n)=of_nat (Suc n)*T^n*biv_deriv is_y T" for T n
    by (cases is_y) (simp_all only: biv_deriv_def if_True if_False biv_dx_power_Suc biv_dy_power_Suc)
  show ?thesis
  proof -
    have left: "R^Suc b*biv_deriv is_y (B^Suc a)=
        B^a*R^b*(of_nat (Suc a)*(R*biv_deriv is_y B))"
      by (simp only: dpow) (simp only: power_Suc; algebra)
    have right: "B^Suc a*biv_deriv is_y (R^Suc b)=
        B^a*R^b*(of_nat (Suc b)*(B*biv_deriv is_y R))"
      by (simp only: dpow) (simp only: power_Suc; algebra)
    show ?thesis by (simp only: left right h)
  qed
qed

lemma power_cross_derivative_identities:
  fixes B R :: "complex bivariate"
  assumes hm: "0<m" and ho: "0<omega"
    and hx: "of_nat m*(R*biv_dx B)=of_nat omega*(B*biv_dx R)"
    and hy: "of_nat m*(R*biv_dy B)=of_nat omega*(B*biv_dy R)"
  shows "(R^omega*biv_dx (B^m)=B^m*biv_dx (R^omega)) \<and>
    (R^omega*biv_dy (B^m)=B^m*biv_dy (R^omega))"
proof -
  obtain a where ma: "m=Suc a" using hm by (cases m) auto
  obtain b where ob: "omega=Suc b" using ho by (cases omega) auto
  have dx: "of_nat (Suc a)*(R*biv_deriv False B)=of_nat (Suc b)*(B*biv_deriv False R)"
    using hx by (simp add: ma ob biv_deriv_def)
  have dy: "of_nat (Suc a)*(R*biv_deriv True B)=of_nat (Suc b)*(B*biv_deriv True R)"
    using hy by (simp add: ma ob biv_deriv_def)
  show ?thesis
    using joseph_cross_derivative_of_logarithmic_identity[OF dx]
      joseph_cross_derivative_of_logarithmic_identity[OF dy]
    by (simp add: ma ob biv_deriv_def)
qed

lemma homogeneous_poisson_power_ratio:
  fixes B R :: "complex bivariate"
  assumes hm: "0<m" and ho: "0<omega"
    and hB0: "B\<noteq>0" and hR0: "R\<noteq>0"
    and hB: "weighted_homogeneous rho sigma (int omega) B"
    and hR: "weighted_homogeneous rho sigma (int m) R"
    and hbr: "biv_poisson B R=0"
  shows "\<exists>c::complex. c\<noteq>0 \<and> B^m=[:[:c:]:]*R^omega"
proof -
  note der = homogeneous_poisson_derivative_identities[OF hB hR hbr]
  have dx: "of_nat m*(R*biv_dx B)=of_nat omega*(B*biv_dx R)"
    and dy: "of_nat m*(R*biv_dy B)=of_nat omega*(B*biv_dy R)"
    using der by (simp_all add: of_nat_poly)
  note cross = power_cross_derivative_identities[OF hm ho dx dy]
  have rnz: "R^omega\<noteq>0" using hR0 by simp
  obtain c where scalar: "B^m=[:[:c:]:]*R^omega"
    using bivariate_cross_derivatives_constant[OF rnz cross[THEN conjunct1] cross[THEN conjunct2]]
    by blast
  have cnz: "c\<noteq>0" using scalar hB0 by auto
  show ?thesis using scalar cnz by blast
qed

end
