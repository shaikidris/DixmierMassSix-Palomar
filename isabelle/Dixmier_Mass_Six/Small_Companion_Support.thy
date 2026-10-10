theory Small_Companion_Support
 imports "Small_Crossing_Data_Carrier"
   "Crossing_Substitution_Derivatives"
   "Face_Mass_Geometry"
begin

text \<open>Native source formalization. No crossing-data existence is
assumed: statements consume the exact source data predicate.\<close>

lemma companion_weight_lattice:
 fixes rho s i j::nat
 assumes s: "0<s" and direction: "s<rho" and primitive: "coprime rho s"
   and weight: "int rho*int i-int s*int j=int rho-int s"
 shows "\<exists>k::nat. i=1+s*k \<and> j=1+rho*k"
proof -
 have rho: "0<rho" using s direction by arith
 have i: "1\<le>i"
 proof (rule ccontr)
  assume "\<not>1\<le>i"
  then have zero: "i=0" by arith
  have nonnegative: "0\<le>int s*int j" by simp
  have positive: "0<int rho-int s" using direction by simp
  show False using weight nonnegative positive by (simp add: zero; arith)
 qed
 have equation: "int rho*int i-int s*int j=int rho*int 1-int s*int 1"
  using weight by simp
 show ?thesis by (rule crossing_weight_lattice[OF s rho primitive i equation])
qed

lemma companion_support_lattice:
 fixes F::"complex bivariate" and rho s::nat
 assumes s: "0<s" and direction: "s<rho" and primitive: "coprime rho s"
   and homogeneous: "weighted_homogeneous(int rho)(-int s)(int rho-int s) F"
 shows "\<forall>e\<in>biv_support F. \<exists>k::nat. e=(1+s*k,1+rho*k)"
proof (intro ballI)
 fix e assume e: "e\<in>biv_support F"
 have weight: "int rho*int(fst e)-int s*int(snd e)=int rho-int s"
  using homogeneous e by (simp add: weighted_homogeneous_def pair_weight_def mult.commute)
 obtain k where first: "fst e=1+s*k" and second: "snd e=1+rho*k"
  using companion_weight_lattice[where rho=rho and s=s and i="fst e" and j="snd e", OF s direction primitive weight] by blast
 show "\<exists>k::nat. e=(1+s*k,1+rho*k)" using first second by (auto simp: prod_eq_iff)
qed

lemma companion_homogeneous_shape:
 fixes F::"complex bivariate" and rho s::nat
 assumes s: "0<s" and direction: "s<rho" and primitive: "coprime rho s"
   and homogeneous: "weighted_homogeneous(int rho)(-int s)(int rho-int s) F"
 shows "\<exists>f::complex poly. F=biv_monom 1 1 1*biv_univariate_eval f (biv_monom 1 s rho)"
proof -
 let ?S = "biv_support F"
 let ?tau = "\<lambda>d. SOME k::nat. d=(1+s*k,1+rho*k)"
 have ray: "\<forall>d\<in>?S. \<exists>k::nat. d=(1+s*k,1+rho*k)"
  by (rule companion_support_lattice[where F=F and rho=rho and s=s, OF s direction primitive homogeneous])
 have tau: "\<And>d. d\<in>?S \<Longrightarrow> d=(1+s*?tau d,1+rho*?tau d)"
  by (rule someI_ex) (use ray in blast)
 let ?f = "\<Sum>d\<in>?S. monom (biv_coeff F(fst d)(snd d)) (?tau d)"
 have terms: "\<And>d. d\<in>?S \<Longrightarrow>
  biv_monom (biv_coeff F(fst d)(snd d))(fst d)(snd d)=
  biv_monom 1 1 1*biv_univariate_eval (monom (biv_coeff F(fst d)(snd d)) (?tau d)) (biv_monom 1 s rho)"
 proof -
  fix d assume d: "d\<in>?S"
  have first: "fst d=1+s*?tau d"
   using arg_cong[where f=fst, OF tau[OF d]] by (simp only: fst_conv)
  have second: "snd d=1+rho*?tau d"
   using arg_cong[where f=snd, OF tau[OF d]] by (simp only: snd_conv)
  show "biv_monom (biv_coeff F(fst d)(snd d))(fst d)(snd d)=
   biv_monom 1 1 1*biv_univariate_eval (monom (biv_coeff F(fst d)(snd d)) (?tau d)) (biv_monom 1 s rho)"
   by (simp only: biv_univariate_eval_monom crossing_base_monomial first second)
 qed
 have "F=(\<Sum>d\<in>?S. biv_monom (biv_coeff F(fst d)(snd d))(fst d)(snd d))"
  using biv_reconstruct[of F] by simp
 also have "\<dots>=(\<Sum>d\<in>?S. biv_monom 1 1 1*biv_univariate_eval (monom (biv_coeff F(fst d)(snd d)) (?tau d)) (biv_monom 1 s rho))"
  by (rule sum.cong) (use terms in auto)
 also have "\<dots>=biv_monom 1 1 1*biv_univariate_eval ?f (biv_monom 1 s rho)"
  by (simp add: biv_univariate_eval_sum sum_distrib_left)
 finally show ?thesis by blast
qed

lemma smallDegreeCrossing_companion_endpoint:
 fixes P Q::"complex poly_operator"
 assumes data: "ggv_small_degree_crossing_data P Q H"
 shows "ggv_f1 H=ggv_s H+1 \<and> ggv_f2 H=ggv_rho H+1"
proof -
 have direction: "is_direction(int(ggv_rho H))(-int(ggv_s H))"
  and bound: "2\<le>ggv_f1 H"
  and homogeneous: "weighted_homogeneous(int(ggv_rho H))(-int(ggv_s H))(int(ggv_rho H)-int(ggv_s H))(ggv_companion H)"
  and base: "(1,1)\<in>biv_support(ggv_companion H)"
  and endpt: "(ggv_f1 H,ggv_f2 H)\<in>biv_support(ggv_companion H)"
  and primitive: "gcd(ggv_f1 H-1)(ggv_f2 H-1)=1"
  using data unfolding ggv_small_degree_crossing_data_def by blast+
 have normalized: "ggv_rho H=ggv_f2 H-1 \<and> ggv_s H=ggv_f1 H-1"
  using companion_support_recovers_primitive_direction[OF direction bound homogeneous base endpt] primitive by simp
 have positive: "0<ggv_rho H" using data unfolding ggv_small_degree_crossing_data_def by blast
 show ?thesis using normalized positive bound by arith
qed

lemma smallDegreeCrossing_companion_support:
 fixes P Q::"complex poly_operator"
 assumes data: "ggv_small_degree_crossing_data P Q H"
 shows "biv_support(ggv_companion H)={(1,1),(ggv_s H+1,ggv_rho H+1)}"
proof -
 have endpoint: "ggv_f1 H=ggv_s H+1 \<and> ggv_f2 H=ggv_rho H+1"
  by (rule smallDegreeCrossing_companion_endpoint[OF data])
 have s: "0<ggv_s H" and direction: "is_direction(int(ggv_rho H))(-int(ggv_s H))"
  and homogeneous: "weighted_homogeneous(int(ggv_rho H))(-int(ggv_s H))(int(ggv_rho H)-int(ggv_s H))(ggv_companion H)"
  and base: "(1,1)\<in>biv_support(ggv_companion H)"
  and endpt: "(ggv_f1 H,ggv_f2 H)\<in>biv_support(ggv_companion H)"
  and maximal: "\<forall>e\<in>biv_support(ggv_companion H). fst e\<le>ggv_f1 H"
  using data unfolding ggv_small_degree_crossing_data_def by blast+
 have strict: "ggv_s H<ggv_rho H" using direction by (simp add: is_direction_def)
 have primitive: "coprime(ggv_rho H)(ggv_s H)"
  using direction by (simp add: is_direction_def coprime_iff_gcd_eq_1)
 show ?thesis
 proof (rule Set.set_eqI)
  fix e
  show "e\<in>biv_support(ggv_companion H) \<longleftrightarrow> e\<in>{(1,1),(ggv_s H+1,ggv_rho H+1)}"
  proof
   assume member: "e\<in>biv_support(ggv_companion H)"
   obtain k where shape: "e=(1+ggv_s H*k,1+ggv_rho H*k)"
    using companion_support_lattice[OF s strict primitive homogeneous] member by blast
   have bound_e: "fst e\<le>ggv_f1 H" by (rule bspec[OF maximal member])
   have product: "ggv_s H*k\<le>ggv_s H"
     using bound_e by (simp only: shape fst_conv conjunct1[OF endpoint]; arith)
   have small: "k\<le>1" using product s by (simp add: mult_le_cancel1)
   have cases: "k=0 \<or> k=1" using small by arith
   show "e\<in>{(1,1),(ggv_s H+1,ggv_rho H+1)}" using shape cases by auto
  next
   assume "e\<in>{(1,1),(ggv_s H+1,ggv_rho H+1)}"
   then show "e\<in>biv_support(ggv_companion H)" using base endpt endpoint by auto
  qed
 qed
qed

lemma biv_degree_eq_of_occupied_max_y:
 fixes F::"complex bivariate"
 assumes endpt: "(a,b)\<in>biv_support F"
   and bound: "\<And>e. e\<in>biv_support F \<Longrightarrow> snd e\<le>b"
 shows "degree F=b"
proof (rule antisym)
 show "degree F\<le>b"
 proof (rule degree_le, intro allI impI)
  fix j assume j: "b<j"
  show "coeff F j=0"
  proof (rule poly_eqI)
   fix i
   have "(i,j)\<notin>biv_support F" using bound j by force
   then show "coeff(coeff F j)i=coeff 0 i" by (simp add: biv_support_def biv_coeff_def)
  qed
 qed
 have "coeff F b\<noteq>0" using endpt by (auto simp: biv_support_def biv_coeff_def)
 then show "b\<le>degree F" by (rule le_degree)
qed

lemma smallDegreeCrossing_companion_degreeOf_Y:
 fixes P Q::"complex poly_operator"
 assumes data: "ggv_small_degree_crossing_data P Q H"
 shows "degree(ggv_companion H)=ggv_rho H+1"
proof -
 have support: "biv_support(ggv_companion H)={(1,1),(ggv_s H+1,ggv_rho H+1)}"
  by (rule smallDegreeCrossing_companion_support[OF data])
 show ?thesis by (rule biv_degree_eq_of_occupied_max_y[where a="ggv_s H+1"]) (auto simp: support)
qed


lemma small_crossing_companion_linear_shape:
 fixes P Q::"complex poly_operator"
 assumes data: "ggv_small_degree_crossing_data P Q H"
 shows "\<exists>f::complex poly. poly f 0\<noteq>0 \<and> degree f=1 \<and>
 ggv_companion H=biv_monom 1 1 1*biv_univariate_eval f (biv_monom 1 (ggv_s H)(ggv_rho H))"
proof -
 let ?F = "ggv_companion H"
 let ?s = "ggv_s H" let ?rho = "ggv_rho H"
 let ?c = "biv_coeff ?F 1 1" let ?d = "biv_coeff ?F (?s+1)(?rho+1)"
 let ?f = "[:?c,?d:]"
 have rho: "0<?rho" using data unfolding ggv_small_degree_crossing_data_def by blast
 have support: "biv_support ?F={(1,1),(?s+1,?rho+1)}"
  by (rule smallDegreeCrossing_companion_support[OF data])
 have different: "(1,1)\<noteq>(?s+1,?rho+1)" using rho by auto
 have base: "(1,1)\<in>biv_support ?F" and endpt: "(?s+1,?rho+1)\<in>biv_support ?F" by (simp_all add: support)
 have c: "?c\<noteq>0" and d: "?d\<noteq>0" using base endpt by (simp_all add: biv_support_def)
 have reconstruction: "?F=biv_monom ?c 1 1+biv_monom ?d (?s+1)(?rho+1)"
 proof -
  let ?term="\<lambda>u. biv_monom (biv_coeff ?F (fst u) (snd u)) (fst u) (snd u)"
  have not_member: "(1,1)\<notin>{(?s+1,?rho+1)}" using different by simp
  have singleton: "(\<Sum>u\<in>{(?s+1,?rho+1)}. ?term u)=?term (?s+1,?rho+1)" by simp
  have finite_second: "finite {(?s+1,?rho+1)}" by simp
  have expansion: "(\<Sum>u\<in>{(1,1),(?s+1,?rho+1)}. ?term u)=
      ?term (1,1)+?term (?s+1,?rho+1)"
    using sum.insert[OF finite_second not_member, of ?term] by (simp only: singleton)
  have full: "?F=(\<Sum>u\<in>{(1,1),(?s+1,?rho+1)}. ?term u)"
    using biv_reconstruct[of ?F, symmetric] by (simp only: support)
  show ?thesis using trans[OF full expansion] by (simp only: fst_conv snd_conv)
 qed
 have evaluated: "biv_monom 1 1 1*biv_univariate_eval ?f (biv_monom 1 ?s ?rho)=
  biv_monom ?c 1 1+biv_monom ?d (?s+1)(?rho+1)"
  by (simp add: biv_univariate_eval_pCons biv_mult_monom algebra_simps)
 have degree: "degree ?f=1" using d by simp
 have constant_term: "poly ?f 0\<noteq>0" using c by simp
 show ?thesis by (intro exI[of _ ?f]) (use constant_term degree reconstruction evaluated in auto)
qed

lemma smallDegreeCrossing_scalar_companion_degree:
 fixes P Q::"complex poly_operator"
 fixes f::"complex poly"
 assumes data: "ggv_small_degree_crossing_data P Q H" and f0: "poly f 0\<noteq>0"
   and shape: "ggv_companion H=biv_monom 1 1 1*biv_univariate_eval f (biv_monom 1 (ggv_s H)(ggv_rho H))"
 shows "degree f=1"
proof -
 obtain g where degree: "degree g=1" and gshape:
  "ggv_companion H=biv_monom 1 1 1*biv_univariate_eval g (biv_monom 1 (ggv_s H)(ggv_rho H))"
  using small_crossing_companion_linear_shape[OF data] by blast
 have equal: "biv_univariate_eval f (biv_monom 1 (ggv_s H)(ggv_rho H))=
  biv_univariate_eval g (biv_monom 1 (ggv_s H)(ggv_rho H))"
  using shape gshape by simp
 have rho: "0<ggv_rho H" using data unfolding ggv_small_degree_crossing_data_def by blast
 have "f=g" by (rule crossing_substitution_injective[OF rho equal])
 then show ?thesis using degree by simp
qed

end
