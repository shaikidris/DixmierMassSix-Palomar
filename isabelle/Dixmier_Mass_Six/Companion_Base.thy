theory Companion_Base
 imports Poisson_Diagonal_Start
begin

lemma poisson_support_x_lower:
 fixes R F::"complex bivariate" and a b::nat
 assumes R: "\<And>d. d\<in>biv_support R \<Longrightarrow> a\<le>fst d"
 and F: "\<And>d. d\<in>biv_support F \<Longrightarrow> b\<le>fst d"
 and e: "e\<in>biv_support(biv_poisson R F)"
 shows "a+b\<le>fst e+1"
proof -
 have Rb: "pair_weight (-1) 0 d\<le> -int a" if "d\<in>biv_support R" for d
   using R[OF that] by (simp add: pair_weight_def)
 have Fb: "pair_weight (-1) 0 d\<le> -int b" if "d\<in>biv_support F" for d
   using F[OF that] by (simp add: pair_weight_def)
 have bound: "pair_weight (-1) 0 e\<le> -int a+(-int b)-((-1)+0)"
   by (rule poisson_support_weight_le[OF Rb Fb e])
 show ?thesis using bound by (simp add: pair_weight_def; arith)
qed

lemma poisson_companion_has_small_x:
 fixes R F::"complex bivariate"
 assumes R: "R\<noteq>0" and companion: "biv_poisson R F=R"
 shows "\<exists>d\<in>biv_support F. fst d\<le>1"
proof (rule ccontr)
 assume no: "\<not>(\<exists>d\<in>biv_support F. fst d\<le>1)"
 have Fb: "2\<le>fst d" if "d\<in>biv_support F" for d using no that by auto
 have nonempty: "biv_support R\<noteq>{}" using R by simp
 have minimum: "Min(fst ` biv_support R)\<in>fst ` biv_support R"
   by (rule Min_in) (use nonempty in auto)
 obtain e where e: "e\<in>biv_support R" and min: "fst e=Min(fst ` biv_support R)" using minimum by auto
 have Rb: "fst e\<le>fst d" if "d\<in>biv_support R" for d
   unfolding min by (rule Min_le) (use that in auto)
 have eb: "e\<in>biv_support(biv_poisson R F)" using e companion by simp
 have "fst e+2\<le>fst e+1" by (rule poisson_support_x_lower[OF Rb Fb eb])
 then show False by arith
qed

lemma homogeneous_companion_base_mem:
 fixes R F::"complex bivariate" and rho s::nat
 assumes s: "0<s" and direction: "s<rho" and R: "R\<noteq>0"
 and Fhom: "\<And>d. d\<in>biv_support F \<Longrightarrow> pair_weight (int rho) (-int s) d=int rho-int s"
 and companion: "biv_poisson R F=R"
 shows "(1,1)\<in>biv_support F"
proof -
 obtain d where d: "d\<in>biv_support F" and small: "fst d\<le>1"
   using poisson_companion_has_small_x[OF R companion] by blast
 have weight: "int rho*int(fst d)-int s*int(snd d)=int rho-int s"
   using Fhom[OF d] by (simp add: pair_weight_def mult.commute)
 have x: "fst d=1"
 proof -
   have nonzero: "fst d\<noteq>0"
   proof
     assume zero: "fst d=0"
     have nonnegative: "0\<le>int s*int(snd d)" by simp
     show False using weight nonnegative direction by (simp add: zero; arith)
   qed
   show ?thesis using small nonzero by arith
 qed
 have product: "int s*int(snd d)=int s*1" using weight by (simp add: x; arith)
 have y: "snd d=1" using product s by simp
 have eq: "d=(1,1)" using x y by (simp add: prod_eq_iff)
 show ?thesis using d eq by simp
qed
end
