theory Poisson_Prime_Derivative
  imports "Poisson_Euler_Bracket"
begin

lemma prime_polynomial_pderiv_not_dvd:
  fixes u :: "complex bivariate"
  assumes hu: "prime_elem u"
  shows "\<exists>is_y. \<not>u dvd biv_deriv is_y u"
proof (rule ccontr)
  assume hn: "\<not>(\<exists>is_y. \<not>u dvd biv_deriv is_y u)"
  have all: "\<forall>is_y. u dvd biv_deriv is_y u" using hn by blast
  have dy0: "u dvd biv_deriv True u" using all by (rule spec)
  have dx0: "u dvd biv_deriv False u" using all by (rule spec)
  have dy: "u dvd biv_dy u" using dy0 by (simp only: biv_deriv_def if_True)
  have dx: "u dvd biv_dx u" using dx0 by (simp only: biv_deriv_def if_False)
  have deg_u: "degree u=0" using dy by (simp add: biv_dy_def)
  let ?v = "coeff u 0"
  have outer: "u=[:?v:]" using degree_0_id[OF deg_u] by simp
  have deriv_outer: "biv_dx u=[:pderiv ?v:]"
  proof -
    have "biv_dx u=biv_dx [:?v:]" using outer by (rule arg_cong)
    then show ?thesis by (simp add: biv_dx_def map_poly_pCons)
  qed
  have constant_dvd: "[:?v:] dvd [:pderiv ?v:]" using dx outer deriv_outer by metis
  have all_coeff: "\<forall>n. ?v dvd coeff [:pderiv ?v:] n"
    by (rule const_poly_dvd_iff[THEN iffD1, OF constant_dvd])
  have at_zero: "?v dvd coeff [:pderiv ?v:] 0" using all_coeff by (rule spec)
  have inner_dvd: "?v dvd pderiv ?v" using at_zero by simp
  have deg_v: "degree ?v=0" using inner_dvd by simp
  let ?c = "coeff ?v 0"
  have inner: "?v=[:?c:]" using degree_0_id[OF deg_v] by simp
  have constant_inner: "[:?v:]=[:[:?c:]:]" using inner by (rule arg_cong)
  have double: "u=[:[:?c:]:]" by (rule trans[OF outer constant_inner])
  have unz: "u\<noteq>0" using hu by (simp add: prime_elem_def)
  have cnz: "?c\<noteq>0"
  proof
    assume cz: "?c=0"
    have "[:[:?c:]:]=(0::complex bivariate)" by (simp only: cz pCons_0_0)
    then show False using double unz by metis
  qed
  have product: "u*[:[:inverse ?c:]:]=[:[:?c:]:]*[:[:inverse ?c:]:]"
    using double by (rule arg_cong)
  have unit: "u*[:[:inverse ?c:]:]=1" using product cnz by (simp add: one_pCons)
  have "u dvd 1" by (rule dvdI[of _ _ "[:[:inverse ?c:]:]"]) (use unit in simp)
  then show False using prime_elem_not_unit[OF hu] by contradiction
qed

end
