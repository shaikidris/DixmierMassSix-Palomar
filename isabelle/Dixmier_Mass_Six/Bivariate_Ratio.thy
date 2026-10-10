theory Bivariate_Ratio
  imports Bivariate_Prime_Multiplicity "Wronskian_Ratio"
begin

instance fract :: ("{idom,ring_char_0}") field_char_0
  by standard (rule injI; simp add: of_nat_fract eq_fract)

lemma joseph_to_fract_of_nat:
  "to_fract (of_nat n::complex poly)=(of_nat n::complex poly fract)"
  by (induction n) (simp_all add: of_nat_Suc)

lemma joseph_fract_poly_pderiv:
  "pderiv (fract_poly (F::complex bivariate))=fract_poly (pderiv F)"
  by (rule poly_eqI)
    (simp add: coeff_pderiv coeff_map_poly joseph_to_fract_of_nat)

lemma y_cross_derivative_scalar_over_fraction_ring:
  fixes F G :: "complex bivariate"
  assumes hG: "G\<noteq>0" and hy: "G*biv_dy F=F*biv_dy G"
  shows "\<exists>c::complex poly fract. fract_poly F=[:c:]*fract_poly G"
proof -
  have gnz: "fract_poly G\<noteq>0" using hG by simp
  have wr: "polynomial_wronskian (fract_poly F) (fract_poly G)=0"
  proof -
    have "fract_poly G*pderiv (fract_poly F)=fract_poly F*pderiv (fract_poly G)"
      using arg_cong[OF hy, of "map_poly to_fract"]
      by (simp add: biv_dy_def joseph_fract_poly_pderiv)
    then show ?thesis by (simp add: polynomial_wronskian_def algebra_simps)
  qed
  show ?thesis by (rule polynomial_wronskian_zero_scalar_ratio[OF gnz wr])
qed

lemma bivariate_y_ratio_polynomial_relation:
  fixes F G :: "complex bivariate"
  assumes hG: "G\<noteq>0" and hy: "G*biv_dy F=F*biv_dy G"
  shows "\<exists>U V::complex poly. V\<noteq>0 \<and> [:V:]*F=[:U:]*G"
proof -
  obtain c :: "complex poly fract" where hc: "fract_poly F=[:c:]*fract_poly G"
    using y_cross_derivative_scalar_over_fraction_ring[OF hG hy] by blast
  let ?V = "lead_coeff G"
  let ?U = "coeff F (degree G)"
  have vnz: "?V\<noteq>0" using hG by simp
  have coefficient: "to_fract ?U=c*to_fract ?V"
    using arg_cong[OF hc, of "\<lambda>p. coeff p (degree G)"]
    by (simp add: coeff_map_poly)
  have "fract_poly ([:?V:]*F)=fract_poly ([:?U:]*G)"
  proof -
    have "fract_poly ([:?V:]*F)=[:to_fract ?V:]*([:c:]*fract_poly G)"
      by (simp only: fract_poly_mult hc) (simp add: map_poly_pCons)
    also have "...=[:c*to_fract ?V:]*fract_poly G"
      by (simp add: algebra_simps)
    also have "...=fract_poly ([:?U:]*G)"
      by (simp add: coefficient map_poly_pCons)
    finally show ?thesis .
  qed
  then have rel: "[:?V:]*F=[:?U:]*G" by (simp only: fract_poly_eq_iff)
  show ?thesis using vnz rel by blast
qed

lemma cleared_ratio_derivative_identity:
  fixes F G S T :: "complex bivariate"
  assumes hG: "G\<noteq>0" and hrel: "T*F=S*G"
    and hx: "G*biv_dx F=F*biv_dx G"
  shows "T*biv_dx S=S*biv_dx T"
proof -
  have hder: "biv_dx T*F+T*biv_dx F=biv_dx S*G+S*biv_dx G"
    using arg_cong[OF hrel, of biv_dx] by (simp only: biv_dx_mult)
  have hz: "(biv_dx T*F-biv_dx S*G)*G=0"
    using hder hx hrel by algebra
  have hd: "biv_dx T*F=biv_dx S*G" using hz hG by simp
  have last: "(T*biv_dx S-S*biv_dx T)*G=0"
    using hd hrel by algebra
  show ?thesis using last hG by simp
qed

lemma bivariate_cross_derivatives_constant:
  fixes F G :: "complex bivariate"
  assumes hG: "G\<noteq>0"
    and hx: "G*biv_dx F=F*biv_dx G"
    and hy: "G*biv_dy F=F*biv_dy G"
  shows "\<exists>c::complex. F=[:[:c:]:]*G"
proof -
  obtain U V :: "complex poly" where vnz: "V\<noteq>0" and rel: "[:V:]*F=[:U:]*G"
    using bivariate_y_ratio_polynomial_relation[OF hG hy] by blast
  have der: "[:V:]*biv_dx [:U:]=[:U:]*biv_dx [:V:]"
    by (rule cleared_ratio_derivative_identity[OF hG rel hx])
  have inner: "V*pderiv U=U*pderiv V"
    using der by (simp add: biv_dx_def map_poly_pCons algebra_simps)
  have inner_swapped: "U*pderiv V=pderiv U*V" using inner by algebra
  have wr: "polynomial_wronskian U V=0"
    by (simp only: polynomial_wronskian_def inner_swapped diff_self)
  obtain c where scalar: "U=[:c:]*V"
    using polynomial_wronskian_zero_scalar_ratio[OF vnz wr] by blast
  have scalar_outer: "[:U:]=[:[:c:]:]*[:V:]" using scalar by simp
  have factor: "[:V:]*F=[:V:] * ([:[:c:]:]*G)"
    using rel scalar_outer by algebra
  have outer_nz: "([:V:]::complex bivariate)\<noteq>0" using vnz by simp
  have "F=[:[:c:]:]*G" using factor
    by (simp only: mult_left_cancel[OF outer_nz])
  then show ?thesis by blast
qed

end
