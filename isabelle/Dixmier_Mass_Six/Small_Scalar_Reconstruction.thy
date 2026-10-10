theory Small_Scalar_Reconstruction
 imports "Small_Companion_Support"
   "Crossing_Poisson_Scalar"
begin

lemma smallDegreeCrossing_exact_scalar_reconstruction:
 fixes P Q::"complex poly_operator"
 assumes data: "ggv_small_degree_crossing_data P Q H"
 shows "\<exists>c::complex. \<exists>p f::complex poly.
 c\<noteq>0 \<and> coeff p 0=1 \<and>
 ggv_root H=biv_monom c 0 0*(biv_monom 1 (ggv_r H)(ggv_t H)*biv_univariate_eval p (biv_monom 1 (ggv_s H)(ggv_rho H))) \<and>
 ggv_companion H=biv_monom 1 1 1*biv_univariate_eval f (biv_monom 1 (ggv_s H)(ggv_rho H)) \<and>
 poly f 0\<noteq>0 \<and> degree f=1 \<and>
 GenComp(ggv_rho H-ggv_s H)(ggv_r H-ggv_t H)(ggv_rho H*ggv_r H-ggv_s H*ggv_t H) p f"
proof -
 let ?R = "ggv_root H" let ?F = "ggv_companion H"
 let ?rho = "ggv_rho H" let ?s = "ggv_s H"
 let ?r = "ggv_r H" let ?t = "ggv_t H"
 let ?W = "biv_monom 1 ?s ?rho::complex bivariate"
 have s: "0<?s" and rho: "0<?rho" and direction: "is_direction(int ?rho)(-int ?s)"
  and R: "?R\<noteq>0"
  and hom: "weighted_homogeneous(int ?rho)(-int ?s)(ggv_weight H) ?R"
  and start: "(?r,?t)\<in>biv_support ?R"
  and minimal: "\<forall>e\<in>biv_support ?R. ?r\<le>fst e"
  and crossing: "?t<?r" and bracket: "biv_poisson ?R ?F=?R"
  using data unfolding ggv_small_degree_crossing_data_def by blast+
 have strict: "?s<?rho" using direction by (simp add: is_direction_def)
 have primitive: "coprime ?rho ?s" using direction by (simp add: is_direction_def coprime_iff_gcd_eq_1)
 have homogeneous: "\<And>e. e\<in>biv_support ?R \<Longrightarrow> pair_weight(int ?rho)(-int ?s)e=ggv_weight H"
  using hom unfolding weighted_homogeneous_def by blast
 obtain a b q where q0: "coeff q 0\<noteq>0" and base: "(a,b)\<in>biv_support ?R"
  and ray: "\<forall>e\<in>biv_support ?R. \<exists>k::nat. e=(a+?s*k,b+?rho*k)"
  and shape: "?R=biv_monom 1 a b*biv_univariate_eval q ?W"
  using crossing_base_shape_with_occupied_base[OF s strict primitive R homogeneous] by blast
 obtain k where start_eq: "(?r,?t)=(a+?s*k,b+?rho*k)" using ray start by blast
 have lower: "?r\<le>a" using bspec[OF minimal base] by (simp only: fst_conv)
 have a: "a=?r" using start_eq lower by (simp add: prod_eq_iff; arith)
 have zero: "?s*k=0" using start_eq a by (simp add: prod_eq_iff)
 have k: "k=0" using zero s by simp
 have b: "b=?t" using start_eq k by simp
 let ?c = "coeff q 0"
 let ?p = "smult (inverse ?c) q"
 have p0: "coeff ?p 0=1" using q0 by simp
 have evaluated: "biv_univariate_eval ?p ?W=biv_monom (inverse ?c) 0 0*biv_univariate_eval q ?W"
  by (rule biv_univariate_eval_smult)
 have scalar_unit: "biv_monom ?c 0 0*biv_monom (inverse ?c) 0 0=1"
  using q0 by (simp add: biv_mult_monom biv_monom_def monom_0 one_pCons)
 have Rshape: "?R=biv_monom ?c 0 0*(biv_monom 1 ?r ?t*biv_univariate_eval ?p ?W)"
  using shape by (simp only: a b evaluated; simp add: mult_ac scalar_unit)
 obtain f where f0: "poly f 0\<noteq>0" and degree: "degree f=1"
  and Fshape: "?F=biv_monom 1 1 1*biv_univariate_eval f ?W"
  using small_crossing_companion_linear_shape[OF data] by blast
 have Rshape_const: "?R=[:[:?c:]:]*(biv_monom 1 ?r ?t*biv_univariate_eval ?p ?W)"
  using Rshape by (simp only: biv_monom_def monom_0)
 have scaled: "[:[:?c:]:]*biv_poisson (biv_monom 1 ?r ?t*biv_univariate_eval ?p ?W) ?F=
  [:[:?c:]:]*(biv_monom 1 ?r ?t*biv_univariate_eval ?p ?W)"
  using bracket by (simp only: Rshape_const biv_poisson_const_left)
 have scalar_nonzero: "[:[:?c:]:]\<noteq>(0::complex bivariate)" using q0 by simp
 have unscaled: "biv_poisson (biv_monom 1 ?r ?t*biv_univariate_eval ?p ?W) ?F=
   biv_monom 1 ?r ?t*biv_univariate_eval ?p ?W"
   using scaled by (simp only: mult_left_cancel[OF scalar_nonzero])
 have normalized: "biv_poisson (biv_monom 1 ?r ?t*biv_univariate_eval ?p ?W)
  (biv_monom 1 1 1*biv_univariate_eval f ?W)=biv_monom 1 ?r ?t*biv_univariate_eval ?p ?W"
  using unscaled by (simp only: Fshape)
 have scalar: "[:of_nat ?rho- of_nat ?s:]*[:0,1:]*f*pderiv ?p-
 (([:of_nat ?r- of_nat ?t:]*f+[:of_nat ?rho* of_nat ?r- of_nat ?s* of_nat ?t:]*[:0,1:]*pderiv f+1)*?p)=0"
  by (rule crossing_poisson_implies_scalar[OF rho normalized])
 have general: "GenComp(?rho-?s)(?r-?t)(?rho*?r-?s*?t) ?p f"
  by (rule crossing_scalar_to_GenComp[OF strict crossing scalar])
 show ?thesis by (rule exI[where x="?c"], rule exI[where x="?p"], rule exI[where x=f])
  (use q0 p0 Rshape Fshape f0 degree general in blast)
qed

end
