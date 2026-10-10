theory Homogeneous_Power_Endpoints
 imports Homogeneous_Endpoint_Arithmetic
begin

lemma corner_biv_monom_power:
 "(biv_monom c i j)^m=biv_monom (c^m) (m*i) (m*j)" for c::complex
 by (induction m) (simp_all add: biv_monom_def monom_0 mult_monom one_pCons algebra_simps)

lemma corner_support_weight_power:
 fixes R::"complex bivariate" and rho sigma degree::int
 assumes bound: "\<And>d. d\<in>biv_support R \<Longrightarrow> pair_weight rho sigma d\<le>degree"
 shows "\<And>d. d\<in>biv_support(R^m) \<Longrightarrow> pair_weight rho sigma d\<le>int m*degree"
proof (induction m)
 case 0
 have one: "(1::complex bivariate)=biv_monom 1 0 0"
   by (simp add: biv_monom_def monom_0 one_pCons)
 have singleton: "biv_support (1::complex bivariate)={(0,0)}"
   by (simp only: one) (auto simp: biv_support_def prod_eq_iff)
 show ?case using 0 by (auto simp: singleton pair_weight_def) 
next
 case (Suc m)
 have inequality: "pair_weight rho sigma d\<le>degree+int m*degree"
   if "d\<in>biv_support(R*(R^m))" for d
   by (rule biv_support_weight_product[OF bound Suc.IH that])
 have member: "d\<in>biv_support(R*(R^m))" using Suc.prems by (simp only: power_Suc)
 show ?case using inequality[OF member] by (simp add: algebra_simps)
qed

lemma corner_weighted_component_power_top:
 fixes R::"complex bivariate" and rho sigma degree::int
 assumes bound: "\<And>d. d\<in>biv_support R \<Longrightarrow> pair_weight rho sigma d\<le>degree"
 shows "weighted_component rho sigma (int m*degree) (R^m)=(weighted_component rho sigma degree R)^m"
proof (induction m)
 case 0
 have one: "(1::complex bivariate)=biv_monom 1 0 0"
   by (simp add: biv_monom_def monom_0 one_pCons)
 have singleton: "biv_support (1::complex bivariate)={(0,0)}"
   by (simp only: one) (auto simp: biv_support_def prod_eq_iff)
 have component: "weighted_component rho sigma 0 (1::complex bivariate)=1"
   by (simp only: one weighted_component_monom; simp add: pair_weight_def)
 show ?case by (simp add: component)
next
 case (Suc m)
 have Rpower: "pair_weight rho sigma d\<le>int m*degree" if "d\<in>biv_support(R^m)" for d
   by (rule corner_support_weight_power[OF bound that])
 have product: "weighted_component rho sigma (degree+int m*degree) (R*R^m)=
   weighted_component rho sigma degree R * weighted_component rho sigma (int m*degree) (R^m)"
   by (rule weighted_component_product_of_bounds[OF bound Rpower])
 have exponent: "int(Suc m)*degree=degree+int m*degree" by (simp add: algebra_simps)
 show ?case by (simp only: exponent power_Suc product Suc.IH)
qed

lemma corner_unique_top_power_endpoint:
 fixes R::"complex bivariate" and rho sigma::int
 assumes d: "d\<in>biv_support R"
 and bound: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_weight rho sigma x\<le>pair_weight rho sigma d"
 and unique: "\<And>x. x\<in>biv_support R \<Longrightarrow> pair_weight rho sigma x=pair_weight rho sigma d \<Longrightarrow> x=d"
 shows "(m*fst d,m*snd d)\<in>biv_support(R^m)"
proof -
 have component: "weighted_component rho sigma (pair_weight rho sigma d) R=
   biv_monom(biv_coeff R (fst d)(snd d))(fst d)(snd d)"
   by (rule endpoint_unique_top_component[OF d unique])
 have power: "weighted_component rho sigma (int m*pair_weight rho sigma d) (R^m)=
   biv_monom((biv_coeff R (fst d)(snd d))^m)(m*fst d)(m*snd d)"
   by (simp only: corner_weighted_component_power_top[OF bound] component corner_biv_monom_power)
 have nonzero: "biv_coeff R (fst d)(snd d)\<noteq>0" using d by (simp add: biv_support_def)
 have target: "biv_coeff(weighted_component rho sigma (int m*pair_weight rho sigma d) (R^m)) (m*fst d)(m*snd d)\<noteq>0"
   using nonzero by (simp add: power)
 have raw: "biv_coeff(R^m) (m*fst d)(m*snd d)\<noteq>0"
   using target by (auto simp: weighted_component_coeff split: if_splits)
 show ?thesis using raw by (simp add: biv_support_def)
qed

lemma homogeneous_power_max_x_endpoint:
 fixes R::"complex bivariate" and rho s m u v::nat and degree::int
 assumes R: "R\<noteq>0" and s: "0<s"
 and homogeneous: "\<And>d. d\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) d=degree"
 and point: "(u,v)\<in>biv_support R"
 and max: "\<And>d. d\<in>biv_support R \<Longrightarrow> fst d\<le>u"
 shows "(m*u,m*v)\<in>biv_support(R^m)"
proof -
 have bound: "pair_weight 1 0 d\<le>pair_weight 1 0 (u,v)" if "d\<in>biv_support R" for d
   using max[OF that] by (simp add: pair_weight_def)
 have unique: "d=(u,v)" if d: "d\<in>biv_support R" and w: "pair_weight 1 0 d=pair_weight 1 0 (u,v)" for d
 proof -
   have x: "fst d=u" using w by (simp add: pair_weight_def)
   show ?thesis by (rule homogeneous_max_x_unique[where R=R and rho=rho and s=s and u=u and v=v and d=d and degree=degree, OF s homogeneous point d x])
 qed
 show ?thesis using corner_unique_top_power_endpoint[where R=R and rho=1 and sigma=0 and d="(u,v)" and m=m, OF point bound unique]
   by (simp only: fst_conv snd_conv)
qed

lemma homogeneous_power_min_x_endpoint:
 fixes R::"complex bivariate" and rho s m u v::nat and degree::int
 assumes R: "R\<noteq>0" and s: "0<s"
 and homogeneous: "\<And>d. d\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) d=degree"
 and point: "(u,v)\<in>biv_support R"
 and min: "\<And>d. d\<in>biv_support R \<Longrightarrow> u\<le>fst d"
 shows "(m*u,m*v)\<in>biv_support(R^m)"
proof -
 have bound: "pair_weight (-1) 0 d\<le>pair_weight (-1) 0 (u,v)" if "d\<in>biv_support R" for d
   using min[OF that] by (simp add: pair_weight_def)
 have unique: "d=(u,v)" if d: "d\<in>biv_support R" and w: "pair_weight (-1) 0 d=pair_weight (-1) 0 (u,v)" for d
 proof -
   have x: "fst d=u" using w by (simp add: pair_weight_def)
   show ?thesis by (rule homogeneous_max_x_unique[where R=R and rho=rho and s=s and u=u and v=v and d=d and degree=degree, OF s homogeneous point d x])
 qed
 show ?thesis using corner_unique_top_power_endpoint[where R=R and rho="-1" and sigma=0 and d="(u,v)" and m=m, OF point bound unique]
   by (simp only: fst_conv snd_conv)
qed

lemma homogeneous_power_max_x_bound:
 fixes R::"complex bivariate" and m u::nat
 assumes R: "R\<noteq>0" and max: "\<And>d. d\<in>biv_support R \<Longrightarrow> fst d\<le>u"
 shows "\<And>d. d\<in>biv_support(R^m) \<Longrightarrow> fst d\<le>m*u"
proof -
 have bound: "pair_weight 1 0 d\<le>int u" if "d\<in>biv_support R" for d
   using max[OF that] by (simp add: pair_weight_def)
 fix d assume d: "d\<in>biv_support(R^m)"
 have weighted: "pair_weight 1 0 d\<le>int m*int u"
   by (rule corner_support_weight_power[where R=R and m=m, OF bound d])
 have integer_bound: "int(fst d)\<le>int m*int u"
   using weighted by (simp only: pair_weight_def mult_1_right mult_0_right add_0_right)
 have cast_product: "int m*int u=int(m*u)" by simp
 have "int(fst d)\<le>int(m*u)" using integer_bound by (simp only: cast_product)
 then show "fst d\<le>m*u" by (simp only: of_nat_le_iff)
qed

lemma homogeneous_power_min_x_bound:
 fixes R::"complex bivariate" and m u::nat
 assumes R: "R\<noteq>0" and min: "\<And>d. d\<in>biv_support R \<Longrightarrow> u\<le>fst d"
 shows "\<And>d. d\<in>biv_support(R^m) \<Longrightarrow> m*u\<le>fst d"
proof -
 have bound: "pair_weight (-1) 0 d\<le> -int u" if "d\<in>biv_support R" for d
   using min[OF that] by (simp add: pair_weight_def)
 fix d assume d: "d\<in>biv_support(R^m)"
 have weighted: "pair_weight (-1) 0 d\<le>int m*(-int u)"
   by (rule corner_support_weight_power[where R=R and m=m, OF bound d])
 have integer_bound: "int m*int u\<le>int(fst d)"
   using weighted by (simp add: pair_weight_def)
 have cast_product: "int m*int u=int(m*u)" by simp
 have "int(m*u)\<le>int(fst d)" using integer_bound by (simp only: cast_product)
 then show "m*u\<le>fst d" by (simp only: of_nat_le_iff)
qed

lemma homogeneous_power_endpoint_pair:
 fixes R::"complex bivariate" and rho s m u v r t::nat and degree::int
 assumes R: "R\<noteq>0" and s: "0<s"
 and homogeneous: "\<And>d. d\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) d=degree"
 and endpt: "(u,v)\<in>biv_support R" and start: "(r,t)\<in>biv_support R"
 and max: "\<And>d. d\<in>biv_support R \<Longrightarrow> fst d\<le>u"
 and min: "\<And>d. d\<in>biv_support R \<Longrightarrow> r\<le>fst d"
 shows "(m*u,m*v)\<in>biv_support(R^m) \<and> (m*r,m*t)\<in>biv_support(R^m) \<and>
 (\<forall>d\<in>biv_support(R^m). fst d\<le>m*u) \<and> (\<forall>d\<in>biv_support(R^m). m*r\<le>fst d)"
 using homogeneous_power_max_x_endpoint[OF R s homogeneous endpt max]
   homogeneous_power_min_x_endpoint[OF R s homogeneous start min]
   homogeneous_power_max_x_bound[OF R max] homogeneous_power_min_x_bound[OF R min] by blast

lemma leadingFace_power_endpoint_pair:
 fixes P::"complex poly_operator" and R::"complex bivariate" and mu::complex and rho s m u v r t::nat and degree::int
 assumes P: "P\<in>weyl_algebra" and R: "R\<noteq>0" and mu: "mu\<noteq>0" and s: "0<s"
 and homogeneous: "\<And>d. d\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) d=degree"
 and endpt: "(u,v)\<in>biv_support R" and start: "(r,t)\<in>biv_support R"
 and max: "\<And>d. d\<in>biv_support R \<Longrightarrow> fst d\<le>u"
 and min: "\<And>d. d\<in>biv_support R \<Longrightarrow> r\<le>fst d"
 and face: "leading_form (int rho) (-int s) P=smult [:mu:] (R^m)"
 shows "(m*u,m*v)\<in>biv_support(leading_form (int rho) (-int s) P) \<and>
 (m*r,m*t)\<in>biv_support(leading_form (int rho) (-int s) P) \<and>
 (\<forall>d\<in>biv_support(leading_form (int rho) (-int s) P). fst d\<le>m*u) \<and>
 (\<forall>d\<in>biv_support(leading_form (int rho) (-int s) P). m*r\<le>fst d)"
proof -
 have support: "biv_support(leading_form (int rho) (-int s) P)=biv_support(R^m)"
   using mu by (auto simp: face biv_support_def biv_coeff_def)
 show ?thesis using homogeneous_power_endpoint_pair[where R=R and rho=rho and s=s and m=m and u=u and v=v and r=r and t=t and degree=degree, OF R s homogeneous endpt start max min]
   by (simp only: support) blast
qed
end
