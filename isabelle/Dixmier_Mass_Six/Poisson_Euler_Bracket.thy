theory Poisson_Euler_Bracket
  imports Poisson_Fixed_Point_Weight
begin

lemma homogeneous_poisson_euler_bracket_identities:
  fixes f g :: "complex bivariate"
  assumes hf: "weighted_homogeneous rho sigma m f"
    and hg: "weighted_homogeneous rho sigma n g"
  shows "([:[:of_int m:]:]*f*biv_dx g-[:[:of_int n:]:]*g*biv_dx f =
      [:[:of_int sigma:]:]*biv_monom 1 0 1*biv_poisson f g) \<and>
    ([:[:of_int m:]:]*f*biv_dy g-[:[:of_int n:]:]*g*biv_dy f =
      -[:[:of_int rho:]:]*biv_monom 1 1 0*biv_poisson f g)"
proof -
  note Ef = fixedPointEuler_of_homogeneous[OF hf]
  note Eg = fixedPointEuler_of_homogeneous[OF hg]
  have Ef': "[:[:of_int rho:]:]*biv_monom 1 1 0*biv_dx f +
      [:[:of_int sigma:]:]*biv_monom 1 0 1*biv_dy f=[:[:of_int m:]:]*f"
    using Ef by (simp only: fixedPointEuler_def joseph_smult_constant) algebra
  have Eg': "[:[:of_int rho:]:]*biv_monom 1 1 0*biv_dx g +
      [:[:of_int sigma:]:]*biv_monom 1 0 1*biv_dy g=[:[:of_int n:]:]*g"
    using Eg by (simp only: fixedPointEuler_def joseph_smult_constant) algebra
  show ?thesis unfolding biv_poisson_def using Ef' Eg' by algebra
qed

lemma pderiv_power_cleared:
  fixes u :: "complex bivariate"
  shows "u*biv_deriv is_y (u^a)=of_nat a*u^a*biv_deriv is_y u"
proof (cases a)
  case 0
  show ?thesis by (simp add: 0 biv_deriv_def)
next
  case (Suc k)
  have dpow: "biv_deriv is_y (u^Suc k)=of_nat (Suc k)*u^k*biv_deriv is_y u"
    by (cases is_y)
      (simp_all only: biv_deriv_def if_True if_False biv_dx_power_Suc biv_dy_power_Suc)
  show ?thesis by (simp only: Suc dpow) (simp add: power_Suc algebra_simps)
qed

lemma cleared_factor_derivative_identity:
  fixes u F G :: "complex bivariate"
  shows "u*([:[:of_int m:]:]*(u^a*F)*biv_deriv is_y (u^b*G)-
      [:[:of_int n:]:]*(u^b*G)*biv_deriv is_y (u^a*F)) =
    u^(a+b)*([:[:of_int m*of_nat b-of_int n*of_nat a:]:]*F*G*biv_deriv is_y u +
      u*([:[:of_int m:]:]*F*biv_deriv is_y G-[:[:of_int n:]:]*G*biv_deriv is_y F))"
proof -
  note ha = pderiv_power_cleared[where u=u and is_y=is_y and a=a]
  note hb = pderiv_power_cleared[where u=u and is_y=is_y and a=b]
  have deriv_mult: "biv_deriv is_y (p*q)=biv_deriv is_y p*q+p*biv_deriv is_y q" for p q
    by (cases is_y) (simp_all add: biv_deriv_def biv_dx_mult biv_dy_mult)
  have scalar: "([:[:of_int m*of_nat b-of_int n*of_nat a:]:]::complex bivariate)=
      [:[:of_int m:]:]*of_nat b-[:[:of_int n:]:]*of_nat a"
    by (simp add: of_nat_poly)
  have "u*([:[:of_int m:]:]*(u^a*F)*biv_deriv is_y (u^b*G)-
      [:[:of_int n:]:]*(u^b*G)*biv_deriv is_y (u^a*F)) =
      [:[:of_int m:]:]*u^a*F*G*(u*biv_deriv is_y (u^b))-
      [:[:of_int n:]:]*u^b*G*F*(u*biv_deriv is_y (u^a))+
      u*([:[:of_int m:]:]*u^a*F*u^b*biv_deriv is_y G-
        [:[:of_int n:]:]*u^b*G*u^a*biv_deriv is_y F)"
    by (simp only: deriv_mult) (simp add: algebra_simps)
  also have "... = u^(a+b)*
      (([:[:of_int m:]:]*of_nat b-[:[:of_int n:]:]*of_nat a)*F*G*biv_deriv is_y u+
      u*([:[:of_int m:]:]*F*biv_deriv is_y G-[:[:of_int n:]:]*G*biv_deriv is_y F))"
    by (simp only: ha hb power_add) (simp add: algebra_simps)
  also have "... = u^(a+b)*
      ([:[:of_int m*of_nat b-of_int n*of_nat a:]:]*F*G*biv_deriv is_y u+
      u*([:[:of_int m:]:]*F*biv_deriv is_y G-[:[:of_int n:]:]*G*biv_deriv is_y F))"
    by (simp only: scalar)
  finally show ?thesis .
qed

lemma prime_high_bracket_forces_multiplicity_resonance:
  fixes u F G h t :: "complex bivariate"
  assumes hu: "prime_elem u"
    and hF: "\<not>u dvd F" and hG: "\<not>u dvd G"
    and hdu: "\<not>u dvd biv_deriv is_y u"
    and hhigh: "u^(a+b) dvd h"
    and he: "[:[:of_int m:]:]*(u^a*F)*biv_deriv is_y (u^b*G)-
      [:[:of_int n:]:]*(u^b*G)*biv_deriv is_y (u^a*F)=t*h"
  shows "m*int b=n*int a"
proof -
  obtain H where hH: "h=u^(a+b)*H" using hhigh by (auto simp: dvd_def)
  let ?c = "(of_int m::complex)*of_nat b-of_int n*of_nat a"
  let ?C = "([:[:?c:]:]::complex bivariate)"
  let ?K = "[:[:of_int m:]:]*F*biv_deriv is_y G-[:[:of_int n:]:]*G*biv_deriv is_y F"
  have nz: "u^(a+b)\<noteq>0" using hu by (simp add: prime_elem_def)
  have factor: "u^(a+b)*(?C*F*G*biv_deriv is_y u+u*?K)=u^(a+b)*(u*t*H)"
  proof -
    have "u^(a+b)*(?C*F*G*biv_deriv is_y u+u*?K)=
        u*([:[:of_int m:]:]*(u^a*F)*biv_deriv is_y (u^b*G)-
          [:[:of_int n:]:]*(u^b*G)*biv_deriv is_y (u^a*F))"
      by (rule cleared_factor_derivative_identity[symmetric])
    also have "...=u*(t*h)" by (simp only: he)
    also have "...=u^(a+b)*(u*t*H)" by (simp only: hH) (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have hc: "?C*F*G*biv_deriv is_y u+u*?K=u*t*H"
    using factor by (simp only: mult_left_cancel[OF nz])
  have hd: "u dvd ?C*F*G*biv_deriv is_y u"
  proof -
    have "?C*F*G*biv_deriv is_y u=u*t*H-u*?K" using hc by (simp only: eq_diff_eq)
    also have "...=u*(t*H-?K)" by (simp add: algebra_simps)
    finally have "?C*F*G*biv_deriv is_y u=u*(t*H-?K)" .
    then show ?thesis by (auto simp: dvd_def)
  qed
  have hcc: "u dvd ?C"
    using hd hF hG hdu by (simp only: prime_elem_dvd_mult_iff[OF hu]) blast
  have czero: "?c=0"
  proof (rule ccontr)
    assume "?c\<noteq>0"
    then have unit: "?C*[:[:inverse ?c:]:]=1" by (simp add: one_pCons)
    have "?C dvd 1" unfolding dvd_def
      by (rule exI[of _ "[:[:inverse ?c:]:]"]) (rule sym[OF unit])
    then have "u dvd 1" by (rule dvd_trans[OF hcc])
    then show False using prime_elem_not_unit[OF hu] by contradiction
  qed
  have cast: "(of_int (m*int b)::complex)=of_int (n*int a)"
    using czero by simp
  show ?thesis using cast by (simp only: of_int_eq_iff)
qed

end
