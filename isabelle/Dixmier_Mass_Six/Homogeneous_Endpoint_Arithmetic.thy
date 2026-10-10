theory Homogeneous_Endpoint_Arithmetic
 imports Companion_Base
begin

lemma homogeneous_endpoints_weight_equation:
 fixes R::"complex bivariate" and rho s u v r t::nat and degree::int
 assumes homogeneous: "\<And>d. d\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) d=degree"
 and endpt: "(u,v)\<in>biv_support R" and start: "(r,t)\<in>biv_support R"
 shows "rho*u+s*t=rho*r+s*v"
proof -
 have eq: "int(rho*u+s*t)=int(rho*r+s*v)"
   using homogeneous[OF endpt] homogeneous[OF start] by (simp only: pair_weight_def fst_conv snd_conv of_nat_add of_nat_mult mult_minus_right mult.commute; linarith)
 show ?thesis using eq by (simp only: of_nat_eq_iff)
qed

lemma homogeneous_max_x_unique:
 fixes R::"complex bivariate" and rho s u v::nat and degree::int
 assumes s: "0<s"
 and homogeneous: "\<And>d. d\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) d=degree"
 and endpt: "(u,v)\<in>biv_support R" and d: "d\<in>biv_support R" and x: "fst d=u"
 shows "d=(u,v)"
proof -
 have product: "int s*int(snd d)=int s*int v"
   using homogeneous[OF endpt] homogeneous[OF d] by (simp only: pair_weight_def fst_conv snd_conv x mult_minus_right mult.commute; linarith)
 have y: "snd d=v" using product s by simp
 show ?thesis using x y by (simp add: prod_eq_iff)
qed

lemma homogeneous_companion_end_x_ge_two:
 fixes F::"complex bivariate" and rho s f1::nat and degree::int
 assumes s: "0<s" and direction: "is_direction (int rho) (-int s)"
 and homogeneous: "\<And>d. d\<in>biv_support F \<Longrightarrow> pair_weight (int rho) (-int s) d=degree"
 and base: "(1,1)\<in>biv_support F"
 and max: "\<And>d. d\<in>biv_support F \<Longrightarrow> fst d\<le>f1"
 and nonmonomial: "1<card(biv_support F)"
 shows "2\<le>f1"
proof (rule ccontr)
 assume no: "\<not>2\<le>f1"
 have bound: "fst d\<le>1" if "d\<in>biv_support F" for d using max[OF that] no by arith
 have degree: "degree=int rho-int s" using homogeneous[OF base] by (simp add: pair_weight_def)
 have unique: "d=(1,1)" if d: "d\<in>biv_support F" for d
 proof -
   have weight: "int rho*int(fst d)-int s*int(snd d)=int rho-int s"
     using homogeneous[OF d] by (simp add: pair_weight_def degree mult.commute)
   have x: "fst d=1"
   proof -
     have nonzero: "fst d\<noteq>0"
     proof
       assume zero: "fst d=0"
       have product: "0\<le>int s*int(snd d)" by simp
       show False using weight product direction by (simp add: zero is_direction_def; arith)
     qed
     show ?thesis using bound[OF d] nonzero by arith
   qed
   have product: "int s*int(snd d)=int s*1" using weight by (simp add: x; arith)
   have y: "snd d=1" using product s by simp
   show ?thesis using x y by (simp add: prod_eq_iff)
 qed
 have subset: "biv_support F\<subseteq>{(1,1)}" using unique by blast
 have card: "card(biv_support F)\<le>1" using card_mono[OF _ subset] by simp
 show False using card nonmonomial by arith
qed

lemma homogeneous_companion_end_proportional:
 fixes R F::"complex bivariate" and rho s u v f1 f2::nat and degree degreeF::int
 assumes s: "0<s" and f1: "2\<le>f1"
 and Rhom: "\<And>d. d\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) d=degree"
 and Fhom: "\<And>d. d\<in>biv_support F \<Longrightarrow> pair_weight (int rho) (-int s) d=degreeF"
 and Rend: "(u,v)\<in>biv_support R" and Fend: "(f1,f2)\<in>biv_support F"
 and Rmax: "\<And>d. d\<in>biv_support R \<Longrightarrow> fst d\<le>u"
 and Fmax: "\<And>d. d\<in>biv_support F \<Longrightarrow> fst d\<le>f1"
 and companion: "biv_poisson R F=R"
 shows "f1*v=f2*u"
proof -
 have weight: "pair_weight 1 0 d=int(fst d)" for d by (simp add: pair_weight_def)
 have topR: "weighted_component 1 0 (int u+int f1-1) R=0"
 proof (rule biv_eqI)
   fix i j
   have zero: "pair_weight 1 0 (i,j)=int u+int f1-1 \<Longrightarrow> biv_coeff R i j=0"
   proof -
     assume w: "pair_weight 1 0 (i,j)=int u+int f1-1"
     show "biv_coeff R i j=0"
     proof (rule ccontr)
       assume "biv_coeff R i j\<noteq>0"
       then have member: "(i,j)\<in>biv_support R" by (simp add: biv_support_def)
       have "i\<le>u" using Rmax[OF member] by simp
       then show False using w f1 by (simp add: weight; arith)
     qed
   qed
   show "biv_coeff(weighted_component 1 0 (int u+int f1-1) R) i j=biv_coeff 0 i j"
     using zero by (simp add: weighted_component_coeff)
 qed
 have top: "weighted_component 1 0 (pair_weight 1 0 (u,v)+pair_weight 1 0 (f1,f2)-(1+0)) (biv_poisson R F)=0"
   by (simp add: companion weight topR)
 have Rmaxw: "pair_weight 1 0 d\<le>pair_weight 1 0 (u,v)" if "d\<in>biv_support R" for d using Rmax[OF that] by (simp add: weight)
 have Fmaxw: "pair_weight 1 0 d\<le>pair_weight 1 0 (f1,f2)" if "d\<in>biv_support F" for d using Fmax[OF that] by (simp add: weight)
 have Ru: "d=(u,v)" if "d\<in>biv_support R" and "pair_weight 1 0 d=pair_weight 1 0 (u,v)" for d
 proof -
   have x: "fst d=u" using that(2) by (simp add: weight)
   show ?thesis by (rule homogeneous_max_x_unique[where R=R and rho=rho and s=s and u=u and v=v and d=d and degree=degree, OF s Rhom Rend that(1) x])
 qed
 have Fu: "d=(f1,f2)" if "d\<in>biv_support F" and "pair_weight 1 0 d=pair_weight 1 0 (f1,f2)" for d
 proof -
   have x: "fst d=f1" using that(2) by (simp add: weight)
   show ?thesis by (rule homogeneous_max_x_unique[where R=F and rho=rho and s=s and u=f1 and v=f2 and d=d and degree=degreeF, OF s Fhom Fend that(1) x])
 qed
 have det: "(of_nat v::complex)* of_nat f1- of_nat u* of_nat f2=0"
   using poisson_unique_maximizers_collinear_of_top_zero[where p=R and q=F and rho=1 and sigma=0 and d="(u,v)" and e="(f1,f2)", OF top Rend Fend Rmaxw Fmaxw Ru Fu]
   by (simp only: fst_conv snd_conv)
 have multiplied: "(of_nat v::complex)*of_nat f1=of_nat u*of_nat f2" using det by algebra
 have cast: "(of_nat(v*f1)::complex)= of_nat(u*f2)" using multiplied by (simp only: of_nat_mult)
 have eq: "v*f1=u*f2" using cast by (simp only: of_nat_eq_iff)
 show ?thesis using eq by (simp add: mult.commute)
qed
end
