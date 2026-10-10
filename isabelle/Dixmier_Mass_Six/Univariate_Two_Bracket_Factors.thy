theory Univariate_Two_Bracket_Factors
 imports "Bivariate_Prime_Multiplicity"
begin

lemma polynomial_power_derivative_cleared:
 fixes u::"complex poly"
 shows "u*pderiv(u^a)=of_nat a*u^a*pderiv u"
proof(cases a)
 case 0 then show ?thesis by simp
next
 case(Suc k)
 have derivative: "pderiv(u^Suc k)=of_nat(Suc k)*u^k*pderiv u"
   by (subst pderiv_power_Suc) (simp only: of_nat_poly mult_pCons_left mult_zero_left pCons_0_0 add_0; simp)
 show ?thesis by(simp only: Suc derivative) (simp add: power_Suc algebra_simps)
qed

lemma polynomial_cleared_factor_derivative_identity:
  fixes u F G :: "complex poly"
  shows "u*([:of_int m:]*(u^a*F)*pderiv (u^b*G)-
      [:of_int n:]*(u^b*G)*pderiv (u^a*F)) =
    u^(a+b)*([:of_int m*of_nat b-of_int n*of_nat a:]*F*G*pderiv u +
      u*([:of_int m:]*F*pderiv G-[:of_int n:]*G*pderiv F))"
proof -
  note ha = polynomial_power_derivative_cleared[where u=u and a=a]
  note hb = polynomial_power_derivative_cleared[where u=u and a=b]
  have deriv_mult: "pderiv (p*q)=pderiv p*q+p*pderiv q" for p q
    by (simp add: pderiv_mult algebra_simps)
  have scalar: "([:of_int m*of_nat b-of_int n*of_nat a:]::complex poly)=
      [:of_int m:]*of_nat b-[:of_int n:]*of_nat a"
    by (simp add: of_nat_poly)
  have "u*([:of_int m:]*(u^a*F)*pderiv (u^b*G)-
      [:of_int n:]*(u^b*G)*pderiv (u^a*F)) =
      [:of_int m:]*u^a*F*G*(u*pderiv (u^b))-
      [:of_int n:]*u^b*G*F*(u*pderiv (u^a))+
      u*([:of_int m:]*u^a*F*u^b*pderiv G-
        [:of_int n:]*u^b*G*u^a*pderiv F)"
    by (simp only: deriv_mult) (simp add: algebra_simps)
  also have "... = u^(a+b)*
      (([:of_int m:]*of_nat b-[:of_int n:]*of_nat a)*F*G*pderiv u+
      u*([:of_int m:]*F*pderiv G-[:of_int n:]*G*pderiv F))"
    by (simp only: ha hb power_add) (simp add: algebra_simps)
  also have "... = u^(a+b)*
      ([:of_int m*of_nat b-of_int n*of_nat a:]*F*G*pderiv u+
      u*([:of_int m:]*F*pderiv G-[:of_int n:]*G*pderiv F))"
    by (simp only: scalar)
  finally show ?thesis .
qed

lemma polynomial_high_bracket_factor_resonance:
  fixes u F G h t :: "complex poly"
  assumes hu: "prime_elem u"
    and hF: "\<not>u dvd F" and hG: "\<not>u dvd G"
    and hdu: "\<not>u dvd pderiv u"
    and hhigh: "u^(a+b) dvd h"
    and he: "[:of_int m:]*(u^a*F)*pderiv (u^b*G)-
      [:of_int n:]*(u^b*G)*pderiv (u^a*F)=t*h"
  shows "m*int b=n*int a"
proof -
  obtain H where hH: "h=u^(a+b)*H" using hhigh by (auto simp: dvd_def)
  let ?c = "(of_int m::complex)*of_nat b-of_int n*of_nat a"
  let ?C = "([:?c:]::complex poly)"
  let ?K = "[:of_int m:]*F*pderiv G-[:of_int n:]*G*pderiv F"
  have nz: "u^(a+b)\<noteq>0" using hu by (simp add: prime_elem_def)
  have factor: "u^(a+b)*(?C*F*G*pderiv u+u*?K)=u^(a+b)*(u*t*H)"
  proof -
    have "u^(a+b)*(?C*F*G*pderiv u+u*?K)=
        u*([:of_int m:]*(u^a*F)*pderiv (u^b*G)-
          [:of_int n:]*(u^b*G)*pderiv (u^a*F))"
      by (rule polynomial_cleared_factor_derivative_identity[symmetric])
    also have "...=u*(t*h)" by (simp only: he)
    also have "...=u^(a+b)*(u*t*H)" by (simp only: hH) (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have hc: "?C*F*G*pderiv u+u*?K=u*t*H"
    using factor by (simp only: mult_left_cancel[OF nz])
  have hd: "u dvd ?C*F*G*pderiv u"
  proof -
    have "?C*F*G*pderiv u=u*t*H-u*?K" using hc by (simp only: eq_diff_eq)
    also have "...=u*(t*H-?K)" by (simp add: algebra_simps)
    finally have "?C*F*G*pderiv u=u*(t*H-?K)" .
    then show ?thesis by (auto simp: dvd_def)
  qed
  have hcc: "u dvd ?C"
    using hd hF hG hdu by (simp only: prime_elem_dvd_mult_iff[OF hu]) blast
  have czero: "?c=0"
  proof (rule ccontr)
    assume "?c\<noteq>0"
    then have unit: "?C*[:inverse ?c:]=1" by (simp add: one_pCons)
    have "?C dvd 1" unfolding dvd_def
      by (rule exI[of _ "[:inverse ?c:]"]) (rule sym[OF unit])
    then have "u dvd 1" by (rule dvd_trans[OF hcc])
    then show False using prime_elem_not_unit[OF hu] by contradiction
  qed
  have cast: "(of_int (m*int b)::complex)=of_int (n*int a)"
    using czero by simp
  show ?thesis using cast by (simp only: of_int_eq_iff)
qed

end
