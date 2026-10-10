theory Horizontal_Square
 imports "Horizontal_Companion"
begin

lemma square_factor_of_all_roots_double:
 fixes g::"complex poly"
 assumes g: "g\<noteq>0" and double: "\<And>beta. poly g beta=0 \<Longrightarrow> rootMultiplicity beta g=2"
 shows "\<exists>h. h=(\<Prod>beta\<in>set_mset(proots g). [:-beta,1:]) \<and>
   g=[:lead_coeff g:]*h^2 \<and> lead_coeff h=1"
proof -
 let ?S="set_mset(proots g)"
 let ?h="\<Prod>beta\<in>?S. [:-beta,1:]"
 have monic: "lead_coeff ?h=1" by (simp add: lead_coeff_prod)
 have product: "(\<Prod>beta\<in>?S. [:-beta,1:]^count(proots g)beta)=?h^2"
 proof -
   have counts: "count(proots g)beta=2" if "beta\<in>?S" for beta
     using double g that by (simp add: rootMultiplicity_eq_count_proots)
   show ?thesis by (simp only: prod_power_distrib; rule prod.cong) (simp, use counts in simp)
 qed
 have factor: "g=[:lead_coeff g:]*?h^2"
   using complex_poly_decompose_multiset[of g]
   by (simp only: image_prod_mset_multiplicity product; simp)
 show ?thesis using factor monic by blast
qed

lemma root_product_dvd_companion:
 fixes g f::"complex poly"
 assumes g: "g\<noteq>0" and roots: "\<And>beta. poly g beta=0 \<Longrightarrow> poly f beta=0"
 shows "(\<Prod>beta\<in>set_mset(proots g). [:-beta,1:]) dvd f"
proof (cases "f=0")
 case True then show ?thesis by simp
next
 case False
 let ?S="set_mset(proots g)" let ?h="\<Prod>beta\<in>?S. [:-beta,1:]"
 have hnz: "?h\<noteq>0" by simp
 have counts: "rootMultiplicity z ?h=(if z\<in>?S then 1 else 0)" for z
   by (simp add: rootMultiplicity_eq_count_proots proots_prod sum.delta)
 have bound: "rootMultiplicity z ?h\<le>rootMultiplicity z f" for z
 proof -
   have positive: "z\<in>?S \<Longrightarrow> 0<rootMultiplicity z f"
     using roots g False order_gt_0_iff[OF False] by (auto simp: rootMultiplicity_eq_order[OF False])
   show ?thesis using positive by (simp only: counts; split if_splits; arith)
 qed
 show ?thesis by (rule dvd_of_forall_rootMultiplicity_le[OF hnz bound])
qed

lemma HorizComp_square_reduces_wronskian:
 fixes g f h kappa::"complex poly" and c::complex
 assumes comp: "HorizComp 1 g f" and c: "c\<noteq>0" and h: "h\<noteq>0"
 and g: "g=[:c:]*h^2" and f: "f=h*kappa"
 shows "kappa*pderiv h-h*pderiv kappa=1"
proof -
 have derivative_g: "pderiv g=[:c:]*(pderiv h*h+h*pderiv h)"
   by (simp only: g power2_eq_square pderiv_mult; simp add: pderiv_pCons)
 have derivative_f: "pderiv f=pderiv h*kappa+h*pderiv kappa"
   by (simp only: f pderiv_mult; simp only: add.commute mult.commute)
 have transform: "f*pderiv g-pderiv f*g=
   ([:c:]*h^2)*(kappa*pderiv h-h*pderiv kappa)"
   by (simp only: derivative_g derivative_f; simp only: g f power2_eq_square; algebra)
 have unity: "([:of_nat(1::nat):]::complex poly)=1" by (simp add: one_pCons)
 have raw: "f*pderiv g-pderiv f*g=g"
   using comp by (simp only: HorizComp_def unity mult_1_left)
 have eq: "([:c:]*h^2)*(kappa*pderiv h-h*pderiv kappa)=([:c:]*h^2)*1"
 proof -
   have "([:c:]*h^2)*(kappa*pderiv h-h*pderiv kappa)=f*pderiv g-pderiv f*g"
     by (rule transform[symmetric])
   also have "...=g" by (rule raw)
   also have "...=[:c:]*h^2" by (rule g)
   also have "...=([:c:]*h^2)*1" by (simp only: mult_1_right)
   finally show ?thesis .
 qed
 have nonzero: "[:c:]*h^2\<noteq>0" using c h by simp
 show ?thesis using eq by (simp only: mult_left_cancel[OF nonzero])
qed

lemma native_horizontal_wronskian_coeff_top:
 fixes h kappa::"complex poly"
 assumes h: "0<degree h"
 shows "coeff(kappa*pderiv h-h*pderiv kappa)((degree h-1)+degree kappa)=
   (of_nat(degree h)-of_nat(degree kappa))*lead_coeff kappa*lead_coeff h"
proof -
 let ?e="degree h" let ?L="degree kappa"
 have one: "coeff(kappa*pderiv h)((?e-1)+?L)=coeff kappa ?L*coeff(pderiv h)(?e-1)"
   by (simp only: add.commute; rule coeff_mult_of_degree_le) (simp_all add: degree_pderiv)
 have dh: "coeff(pderiv h)(?e-1)=of_nat ?e*coeff h ?e" using h by (simp add: coeff_pderiv)
 show ?thesis
 proof (cases "?L=0")
   case True
   have dk: "pderiv kappa=0" using True by (simp add: pderiv_eq_0_iff)
   show ?thesis by (simp only: coeff_diff one; simp only: dh dk mult_zero_right coeff_0 diff_zero True of_nat_0
     ; algebra)
 next
   case False
   have index: "(?e-1)+?L=?e+(?L-1)" using h False by arith
   have two: "coeff(h*pderiv kappa)((?e-1)+?L)=coeff h ?e*coeff(pderiv kappa)(?L-1)"
     by (simp only: index; rule coeff_mult_of_degree_le) (simp_all add: degree_pderiv)
   have dk: "coeff(pderiv kappa)(?L-1)=of_nat ?L*coeff kappa ?L" using False by (simp add: coeff_pderiv)
   show ?thesis by (simp only: coeff_diff one two dh dk; algebra)
 qed
qed

lemma native_horizontal_wronskian_equal_degrees:
 fixes h kappa::"complex poly"
 assumes positive: "0<degree h" and index: "0<(degree h-1)+degree kappa"
 and wronskian: "kappa*pderiv h-h*pderiv kappa=1"
 shows "degree h=degree kappa"
proof -
 have hnz: "h\<noteq>0" using positive by auto
 have knz: "kappa\<noteq>0" using wronskian by auto
 have index_nonzero: "(degree h-1)+degree kappa\<noteq>0" using index by arith
 have constant_coeff: "coeff(1::complex poly)((degree h-1)+degree kappa)=0"
   using index_nonzero by simp
 have top: "coeff(kappa*pderiv h-h*pderiv kappa)((degree h-1)+degree kappa)=
   (of_nat(degree h)-of_nat(degree kappa))*lead_coeff kappa*lead_coeff h"
   by (rule native_horizontal_wronskian_coeff_top[OF positive])
 have eq: "(of_nat(degree h)-of_nat(degree kappa))*lead_coeff kappa*lead_coeff h=0"
 proof -
   have "(of_nat(degree h)-of_nat(degree kappa))*lead_coeff kappa*lead_coeff h=
     coeff(kappa*pderiv h-h*pderiv kappa)((degree h-1)+degree kappa)" by (rule top[symmetric])
   also have "...=coeff(1::complex poly)((degree h-1)+degree kappa)" by (simp only: wronskian)
   also have "...=0" by (rule constant_coeff)
   finally show ?thesis .
 qed
 have cast: "(of_nat(degree h)::complex)=of_nat(degree kappa)" using eq hnz knz by auto
 show ?thesis using cast by simp
qed

lemma degree_one_of_constant_wronskian:
 fixes h kappa::"complex poly"
 assumes monic: "lead_coeff h=1" and positive: "0<degree h"
 and wronskian: "kappa*pderiv h-h*pderiv kappa=1"
 shows "degree h=1"
proof (rule ccontr)
 assume "degree h\<noteq>1"
 then have large: "2\<le>degree h" using positive by arith
 have index: "0<(degree h-1)+degree kappa" using large by arith
 have equal: "degree h=degree kappa" by (rule native_horizontal_wronskian_equal_degrees[OF positive index wronskian])
 let ?q="kappa-smult (lead_coeff kappa) h"
 have lower: "degree ?q<degree h"
 proof (rule degree_lessI)
   show "?q\<noteq>0 \<or> 0<degree h" using positive by simp
   show "\<forall>n\<ge>degree h. coeff ?q n=0"
   proof (intro allI impI)
     fix n assume n: "degree h\<le>n"
     show "coeff ?q n=0"
     proof (cases "n=degree h")
       case True show ?thesis using monic equal by (simp add: True)
     next
       case False
       have beyond: "degree h<n" using n False by arith
       show ?thesis by (simp add: coeff_eq_0 beyond equal[symmetric])
     qed
   qed
 qed
 have scalar_as_product: "smult a p=[:a:]*p" for a::complex and p::"complex poly" by simp
 have algebra_eq: "?q*pderiv h-h*pderiv ?q=kappa*pderiv h-h*pderiv kappa"
   by (simp only: pderiv_diff pderiv_smult; simp only: scalar_as_product; algebra)
 have wronskian_q: "?q*pderiv h-h*pderiv ?q=1" by (simp only: algebra_eq wronskian)
 have qindex: "0<(degree h-1)+degree ?q" using large by arith
 have qe: "degree h=degree ?q" by (rule native_horizontal_wronskian_equal_degrees[OF positive qindex wronskian_q])
 show False using lower qe by arith
qed

lemma HorizComp_mass_six_square_linear:
 assumes comp: "HorizComp 1 g f" and g: "0<degree g"
 and zero: "rootMultiplicity 0 g<1" and terms: "termCount(g^2)\<le>6"
 shows "\<exists>h. lead_coeff h=1 \<and> degree h=1 \<and> g=[:lead_coeff g:]*h^2"
proof -
 have gnz: "g\<noteq>0" using g by auto
 obtain h where hproduct: "h=(\<Prod>beta\<in>set_mset(proots g). [:-beta,1:])"
   and square: "g=[:lead_coeff g:]*h^2" and monic: "lead_coeff h=1"
   using square_factor_of_all_roots_double[OF gnz] HorizComp_all_roots_double[OF comp g zero terms] by blast
 have roots: "poly f beta=0" if "poly g beta=0" for beta using HorizComp_root_slope[OF comp gnz that] by blast
 have divides: "h dvd f" by (simp only: hproduct; rule root_product_dvd_companion[OF gnz roots])
 obtain kappa where f: "f=h*kappa" using divides unfolding dvd_def by blast
 have hnz: "h\<noteq>0" using monic by auto
 have coefficient: "lead_coeff g\<noteq>0" using gnz by simp
 have degree_square: "degree g=2*degree h"
 proof -
   have "degree g=degree([:lead_coeff g:]*h^2)" by (rule arg_cong[OF square])
   also have "...=2*degree h" by (simp add: degree_mult_eq degree_power_eq hnz coefficient gnz)
   finally show ?thesis .
 qed
 have positive: "0<degree h" using g degree_square by arith
 have wronskian: "kappa*pderiv h-h*pderiv kappa=1"
   by (rule HorizComp_square_reduces_wronskian[OF comp coefficient hnz square f])
 have degree: "degree h=1" by (rule degree_one_of_constant_wronskian[OF monic positive wronskian])
 show ?thesis using monic degree square by blast
qed

lemma HorizComp_mass_six_quadratic:
 assumes comp: "HorizComp 1 g f" and g: "0<degree g"
 and zero: "rootMultiplicity 0 g<1" and terms: "termCount(g^2)\<le>6"
 shows "\<exists>c beta. c\<noteq>0 \<and> beta\<noteq>0 \<and> g=[:c:]*[:-beta,1:]^2"
proof -
 obtain h where monic: "lead_coeff h=1" and degree: "degree h=1" and square: "g=[:lead_coeff g:]*h^2"
   using HorizComp_mass_six_square_linear[OF comp g zero terms] by blast
 have shape: "h=[:coeff h 0,1:]"
 proof (rule poly_eqI)
   fix n
   show "coeff h n=coeff [:coeff h 0,1:] n"
   proof (cases n)
     case 0 then show ?thesis by simp
   next
     case (Suc m)
     show ?thesis using degree monic by (cases m) (simp_all add: Suc coeff_eq_0)
   qed
 qed
 let ?beta="-coeff h 0"
 have gnz: "g\<noteq>0" using g by auto
 have coefficient: "lead_coeff g\<noteq>0" using gnz by simp
 have beta: "?beta\<noteq>0"
 proof
   assume beta_zero: "?beta=0"
   have coefficient_zero: "coeff h 0=0" using beta_zero by simp
   have hzero: "poly h 0=0"
     using arg_cong[where f="\<lambda>p. poly p 0", OF shape] coefficient_zero by simp
   have root: "poly g 0=0"
     using arg_cong[where f="\<lambda>p. poly p 0", OF square] by (simp add: hzero)
   have order_positive: "0<order (0::complex) g" by (rule iffD2[OF order_gt_0_iff[OF gnz] root])
   have positive: "0<rootMultiplicity 0 g" using order_positive by (simp only: rootMultiplicity_eq_order[OF gnz])
   show False using positive zero by arith
 qed
 have hshape: "h=[:-?beta,1:]" by (simp only: minus_minus) (rule shape)
 have powered: "h^2=[:-?beta,1:]^2" by (rule arg_cong[where f="\<lambda>p. p^2", OF hshape])
 have scaled: "[:lead_coeff g:]*h^2=[:lead_coeff g:]*[:-?beta,1:]^2"
   by (rule arg_cong[where f="\<lambda>p. [:lead_coeff g:]*p", OF powered])
 have representation: "g=[:lead_coeff g:]*[:-?beta,1:]^2" by (rule trans[OF square scaled])
 show ?thesis by (rule exI[of _ "lead_coeff g"], rule exI[of _ "?beta"])
   (rule conjI[OF coefficient conjI[OF beta representation]])
qed

end
