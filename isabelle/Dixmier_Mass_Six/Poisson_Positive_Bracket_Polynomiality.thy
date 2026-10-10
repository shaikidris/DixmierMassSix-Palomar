theory Poisson_Positive_Bracket_Polynomiality
  imports Homogeneous_Power_Ratio
begin

lemma two_bracket_numerator_divisibility_of_positive_bracket_weight:
  fixes f g :: "complex bivariate"
  assumes hf: "weighted_homogeneous rho sigma m f"
    and hg: "weighted_homogeneous rho sigma n g"
    and hfne: "f\<noteq>0" and hm: "0<m" and hw: "0<rho+sigma"
    and hbr: "biv_poisson f g\<noteq>0"
    and hsecond: "biv_poisson f (biv_poisson f g)=0"
    and hr: "0<m+n-(rho+sigma)"
  shows "biv_poisson f g dvd f*g"
proof -
  let ?h = "biv_poisson f g"
  let ?r = "m+n-(rho+sigma)"
  have hgne: "g\<noteq>0" using hbr by (auto simp: biv_poisson_def)
  have hh: "weighted_homogeneous rho sigma ?r ?h"
    by (rule poisson_weighted_homogeneous_signed[OF hf hg])
  have swap: "biv_poisson ?h f=0"
    using hsecond by (simp add: biv_poisson_def algebra_simps)
  have hmnat: "0<nat m" and hrnat: "0<nat ?r" using hm hr by simp_all
  have hmcast: "int (nat m)=m" and hrcast: "int (nat ?r)=?r"
    using hm hr by simp_all
  obtain c where hc: "c\<noteq>0" and hpow: "?h^nat m=[:[:c:]:]*f^nat ?r"
    using homogeneous_poisson_power_ratio[OF hmnat hrnat hbr hfne,
      where rho=rho and sigma=sigma]
      hh hf swap hmcast hrcast by auto
  show ?thesis
  proof (rule multiplicity_le_imp_dvd[OF hbr])
    fix u :: "complex bivariate" assume prime: "prime u"
    have hu: "prime_elem u" using prime by (simp add: prime_def)
    have count_nat: "nat m*multiplicity u ?h=nat ?r*multiplicity u f"
      by (rule multiplicity_power_ratio[OF hbr hfne hc hpow hu])
    have count: "m*int (multiplicity u ?h)=?r*int (multiplicity u f)"
      using arg_cong[OF count_nat, of int] by (simp only: of_nat_mult hmcast hrcast)
    have small: "multiplicity u ?h\<le>multiplicity u f+multiplicity u g"
    proof (rule ccontr)
      assume not_small: "\<not>multiplicity u ?h\<le>multiplicity u f+multiplicity u g"
      obtain F where hF: "f=u^multiplicity u f*F" and huF: "\<not>u dvd F"
        by (rule bivariate_prime_power_decomposition[OF hfne hu])
      obtain G where hG: "g=u^multiplicity u g*G" and huG: "\<not>u dvd G"
        by (rule bivariate_prime_power_decomposition[OF hgne hu])
      obtain is_y where hdu: "\<not>u dvd biv_deriv is_y u"
        using prime_polynomial_pderiv_not_dvd[OF hu] by blast
      have high: "u^(multiplicity u f+multiplicity u g) dvd ?h"
        by (rule multiplicity_dvd') (use not_small in arith)
      note bracket_id = homogeneous_poisson_euler_bracket_identities[OF hf hg]
      obtain t :: "complex bivariate" where he:
        "[:[:of_int m:]:]*f*biv_deriv is_y g-[:[:of_int n:]:]*g*biv_deriv is_y f=t*?h"
      proof (cases is_y)
        case True
        show thesis by (rule that[of "-[:[:of_int rho:]:]*biv_monom 1 1 0"])
          (use bracket_id True in \<open>simp add: biv_deriv_def algebra_simps\<close>)
      next
        case False
        show thesis by (rule that[of "[:[:of_int sigma:]:]*biv_monom 1 0 1"])
          (use bracket_id False in \<open>simp add: biv_deriv_def algebra_simps\<close>)
      qed
      have expanded:
        "[:[:of_int m:]:]*(u^multiplicity u f*F)*biv_deriv is_y (u^multiplicity u g*G)-
          [:[:of_int n:]:]*(u^multiplicity u g*G)*biv_deriv is_y (u^multiplicity u f*F)=t*?h"
        using he by (simp only: hF[symmetric] hG[symmetric])

      have resonance: "m*int (multiplicity u g)=n*int (multiplicity u f)"
        by (rule prime_high_bracket_forces_multiplicity_resonance[OF hu huF huG hdu high expanded])
      have balance: "m*(int (multiplicity u ?h)-int (multiplicity u f)-int (multiplicity u g))=
          -(rho+sigma)*int (multiplicity u f)"
        using count resonance by algebra
      have delta: "0<int (multiplicity u ?h)-int (multiplicity u f)-int (multiplicity u g)"
        using not_small by arith
      have positive: "0<m*(int (multiplicity u ?h)-int (multiplicity u f)-int (multiplicity u g))"
        by (rule mult_pos_pos[OF hm delta])
      have nonpositive: "-(rho+sigma)*int (multiplicity u f)\<le>0"
        by (rule mult_nonpos_nonneg) (use hw in auto)
      show False using balance positive nonpositive by arith
    qed
    show "multiplicity u ?h\<le>multiplicity u (f*g)"
      using small prime_elem_multiplicity_mult_distrib[OF hu hfne hgne] by simp
  qed
qed

end
