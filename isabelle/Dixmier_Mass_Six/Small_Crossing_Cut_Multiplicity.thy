theory Small_Crossing_Cut_Multiplicity
 imports "Small_Scalar_Height"
   "Crossing_Cut_Multiplicity"
begin

lemma smallDegreeCrossing_cutPoly_maxRootMult:
 fixes P Q::"complex poly_operator"
 assumes data: "ggv_small_degree_crossing_data P Q H"
 shows "max_root_mult(cut_poly(int(ggv_rho H))(-int(ggv_s H))(ggv_left H))=ggv_d H * ggv_h H"
proof -
 let ?rho="ggv_rho H" let ?s="ggv_s H" let ?d="ggv_d H"
 let ?r="ggv_r H" let ?t="ggv_t H" let ?h="ggv_h H"
 let ?W="biv_monom 1 ?s ?rho::complex bivariate"
 obtain c p f alpha where c: "c\<noteq>0" and p0: "coeff p 0=1"
 and shape: "ggv_root H=biv_monom c 0 0 * (biv_monom 1 ?r ?t * biv_univariate_eval p ?W)"
 and degree: "degree p= ?h" and alpha: "alpha\<noteq>0" and multiplicity: "rootMultiplicity alpha p= ?h"
 using smallDegreeCrossing_scalar_root_at_height[OF data] by blast
 have nu: "ggv_nu H\<noteq>0" and rho: "0< ?rho" and d: "1< ?d" and h: "2\<le> ?h" and t: "?t\<le> ?h"
 and face: "leading_form(int ?rho)(-int ?s)(ggv_left H)=[:[:ggv_nu H:]:] * (ggv_root H) ^ ?d"
 using data unfolding ggv_small_degree_crossing_data_def by blast+
 have scalar: "ggv_nu H * c ^ ?d\<noteq>0" using nu c by simp
 have scalar_monom: "biv_monom c 0 0=[:[:c:]:]"
   by (simp only: biv_monom_def monom_0)
 have scalar_product: "([:[:ggv_nu H:]:]::complex bivariate) * [:[:c ^ ?d:]:]=[:[:ggv_nu H * c ^ ?d:]:]"
   by simp
 have actualface: "leading_form(int ?rho)(-int ?s)(ggv_left H)=[:[:ggv_nu H * c ^ ?d:]:] * (biv_monom 1 ?r ?t * biv_univariate_eval p ?W) ^ ?d"
   by (simp only: face shape scalar_monom power_mult_distrib poly_const_pow mult.assoc[symmetric] scalar_product)
 have positive_d: "0< ?d" using d by arith
 have positive_degree: "0<degree p" using degree h by arith
 have bound: "?t\<le>degree p" using t degree by simp
 have full: "rootMultiplicity alpha p=degree p" using multiplicity degree by simp
 have maximum: "max_root_mult(cut_poly(int ?rho)(-int ?s)(ggv_left H))= ?d * degree p"
  by (rule crossingFace_general_cutPoly_maxRootMult_of_full_scalar_root[where T="ggv_left H" and mu="ggv_nu H * c ^ ?d" and p=p and rho="?rho" and s="?s" and a="?r" and b="?t" and k="?d" and alpha=alpha, OF scalar rho positive_d p0 alpha full positive_degree bound actualface])
 show ?thesis using maximum degree by simp
qed

end
