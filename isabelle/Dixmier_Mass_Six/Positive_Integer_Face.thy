theory Positive_Integer_Face
 imports "First_Downward_Tilt"
   "Positive_Companion_Coordinates"
begin

lemma native_positive_rational_tie_integer_face:
 fixes P Q::"complex poly_operator" and t::rat and u v::"nat\<times>nat"
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
 and t: "1<t" and u: "u\<in>biv_support(pbw_symbol P)" and v: "v\<in>biv_support(pbw_symbol P)"
 and upper: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> rationalNewtonWeight t d\<le>rationalNewtonWeight t u"
 and tie: "rationalNewtonWeight t v=rationalNewtonWeight t u" and distinct: "u\<noteq>v"
 shows "\<exists>tau::nat. 1<tau \<and> (of_nat tau::rat)=t \<and> in_direction 1 (int tau) P \<and>
   u\<in>biv_support(leading_form 1 (int tau) P)"
proof -
 obtain rho tau::nat where rho: "0<rho" and slope: "rho<tau" and primitive: "coprime rho tau"
 and direction: "is_direction (int rho) (int tau)" and ratio: "(of_nat tau/ of_nat rho::rat)=t"
   using positive_rational_direction[OF t] by blast
 have rp: "0<int rho" using rho by simp
 have ratiocast: "(of_int(int tau)/ of_int(int rho)::rat)=t" using ratio by simp
 have uf: "u\<in>biv_support(leading_form (int rho) (int tau) P)"
   by (simp only: leadingForm_mem_iff_rational_slope[where P=P and rho="int rho" and sigma="int tau", OF rp] ratiocast;
     use u upper in blast)
 have vf: "v\<in>biv_support(leading_form (int rho) (int tau) P)"
   by (simp only: leadingForm_mem_iff_rational_slope[where P=P and rho="int rho" and sigma="int tau", OF rp] ratiocast;
     use v upper tie in auto)
 have face: "1<card(biv_support(leading_form (int rho) (int tau) P))"
 proof (rule ccontr)
   assume "\<not>1<card(biv_support(leading_form (int rho) (int tau) P))"
   then have small: "card(biv_support(leading_form (int rho) (int tau) P))\<le>1" by arith
   have smallSuc: "card(biv_support(leading_form (int rho) (int tau) P))\<le>Suc 0"
     using small by (simp only: One_nat_def)
   have same: "\<forall>x\<in>biv_support(leading_form (int rho) (int tau) P).
     \<forall>y\<in>biv_support(leading_form (int rho) (int tau) P). x=y"
     by (rule iffD1[OF card_le_Suc0_iff_eq[where A="biv_support(leading_form (int rho) (int tau) P)", OF finite_biv_support] smallSuc])
   show False using same uf vf distinct by blast
 qed
 have rhoone: "rho=1"
   using preliminary_positive_face_total_degree_axis_endpoint[OF source pair rho slope primitive direction face] by blast
 show ?thesis by (intro exI[of _ tau]) (use slope ratio face uf rhoone in \<open>auto simp: in_direction_def\<close>)
qed

lemma preliminary_positive_singleton_next_integer_face:
 fixes P Q::"complex poly_operator" and sigma a b::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
 and sigma: "1\<le>sigma" and bp: "0<b"
 and member: "(a,b)\<in>biv_support(leading_form 1 (int sigma) P)"
 and unique: "\<And>d. d\<in>biv_support(leading_form 1 (int sigma) P) \<Longrightarrow> d=(a,b)"
 and bad: "\<exists>d\<in>biv_support(pbw_symbol P). a+b<fst d+snd d"
 shows "\<exists>tau::nat. 1<tau \<and> tau<sigma \<and> in_direction 1 (int tau) P \<and>
   (a,b)\<in>biv_support(leading_form 1 (int tau) P)"
proof -
 have ybound: "\<forall>d\<in>biv_support(pbw_symbol P). snd d\<le>b"
   by (rule preliminary_positive_last_point_y_bound[OF source pair sigma member _ bp]) (use unique in auto)
 have old: "(a,b)\<in>biv_support(pbw_symbol P) \<and>
   (\<forall>d\<in>biv_support(pbw_symbol P). rationalNewtonWeight (of_nat sigma) d\<le>rationalNewtonWeight (of_nat sigma) (a,b))"
   using member by (simp only: leadingForm_mem_iff_rational_slope[where P=P and rho=1 and sigma="int sigma", OF zero_less_one]; simp)
 obtain d where d: "d\<in>biv_support(pbw_symbol P)" and excess: "a+b<fst d+snd d" using bad by blast
 have dy: "snd d\<le>b" using ybound d by blast
 have lower: "snd d<b"
 proof (rule ccontr)
   assume "\<not>snd d<b"
   then have equal: "snd d=b" using dy by arith
   have raw: "rationalNewtonWeight (of_nat sigma) d\<le>rationalNewtonWeight (of_nat sigma) (a,b)"
     by (rule bspec[OF conjunct2[OF old] d])
   have cast: "(of_nat(fst d)::rat)\<le> of_nat a"
     using raw by (simp only: rationalNewtonWeight_def fst_conv snd_conv equal; linarith)
   have dx: "fst d\<le>a" using cast by simp
   show False using dx equal excess by arith
 qed
 have first: "snd(a,b)\<le>snd p" if "p\<in>biv_support(leading_form 1 (int sigma) P)" for p
   using unique[OF that] by simp
 have below: "\<exists>p\<in>biv_support(pbw_symbol P). snd p<snd(a,b)"
   by (rule bexI[where x=d]) (use lower d in simp_all)
 have tilt: "\<exists>t::rat. t< of_nat sigma \<and>
   (\<forall>p\<in>biv_support(pbw_symbol P). rationalNewtonWeight t p\<le>rationalNewtonWeight t (a,b)) \<and>
   (\<exists>c\<in>biv_support(pbw_symbol P). snd c<b \<and> rationalNewtonWeight t c=rationalNewtonWeight t (a,b))"
   using leadingFace_exists_first_downward_tilt[where P=P and rho=1 and sigma="int sigma" and a="(a,b)",
     OF zero_less_one member first below] by simp
 obtain t c where small: "t<(of_nat sigma::rat)"
 and bound: "\<forall>z\<in>biv_support(pbw_symbol P). rationalNewtonWeight t z\<le>rationalNewtonWeight t (a,b)"
 and c: "c\<in>biv_support(pbw_symbol P)" and cy: "snd c<b"
 and tie: "rationalNewtonWeight t c=rationalNewtonWeight t (a,b)"
   using tilt by blast
 have tone: "1<t"
 proof (rule ccontr)
   assume "\<not>1<t"
   then have tl: "t\<le>1" by simp
   have dycast: "(of_nat(snd d)::rat)\<le> of_nat b" using dy by simp
   have prod: "0\<le>(1-t)*((of_nat b::rat)- of_nat(snd d))" by (rule mult_nonneg_nonneg) (use tl dycast in linarith)+
   have raw: "rationalNewtonWeight t d\<le>rationalNewtonWeight t (a,b)" using bound d by blast
   have sum: "(of_nat a::rat)+ of_nat b< of_nat(fst d)+ of_nat(snd d)" using excess by (simp only: of_nat_add[symmetric]; simp)
   show False using raw prod sum by (simp only: rationalNewtonWeight_def fst_conv snd_conv algebra_simps; linarith)
 qed
 have distinct: "(a,b)\<noteq>c" using cy by auto
 obtain tau::nat where tau: "1<tau" and ratio: "(of_nat tau::rat)=t"
 and face: "in_direction 1 (int tau) P" and point: "(a,b)\<in>biv_support(leading_form 1 (int tau) P)"
   using native_positive_rational_tie_integer_face[OF source pair tone _ c _ tie distinct] old bound by blast
 have decrease: "tau<sigma" using small by (simp only: ratio[symmetric]; simp)
 show ?thesis using tau decrease face point by blast
qed

lemma preliminary_axis_diagonal_first_positive_face:
 fixes P Q::"complex poly_operator" and a::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
 and member: "(a,0)\<in>biv_support(leading_form 1 1 P)"
 and unique: "\<And>d. d\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> d=(a,0)"
 and above: "\<exists>d\<in>biv_support(pbw_symbol P). 0<snd d"
 shows "\<exists>sigma::nat. 1<sigma \<and> in_direction 1 (int sigma) P \<and>
   (a,0)\<in>biv_support(leading_form 1 (int sigma) P)"
proof -
 obtain t c where t: "1<t"
 and bound: "\<forall>d\<in>biv_support(pbw_symbol P). rationalNewtonWeight t d\<le>rationalNewtonWeight t (a,0)"
 and c: "c\<in>biv_support(pbw_symbol P)" and cy: "0<snd c"
 and tie: "rationalNewtonWeight t c=rationalNewtonWeight t (a,0)"
   using leadingFace_exists_first_upward_tilt[where P=P and rho=1 and sigma=1 and a="(a,0)", OF zero_less_one member _] unique above by auto
 have raw: "(a,0)\<in>biv_support(pbw_symbol P)" using member by (simp add: leading_form_def weighted_component_support)
 have distinct: "(a,0)\<noteq>c" using cy by auto
 show ?thesis using native_positive_rational_tie_integer_face[OF source pair t raw c _ tie distinct] bound by blast
qed

lemma preliminary_axis_diagonal_positive_face:
 fixes P Q::"complex poly_operator" and a::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
 and member: "(a,0)\<in>biv_support(leading_form 1 1 P)"
 and unique: "\<And>d. d\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> d=(a,0)"
 shows "\<exists>sigma::nat. 1<sigma \<and> in_direction 1 (int sigma) P \<and>
   (a,0)\<in>biv_support(leading_form 1 (int sigma) P)"
proof -
 obtain d where d: "d\<in>biv_support(pbw_symbol P)" and negative: "pair_grade d<0"
   using ggv_grades_opposite_proved pair by blast
 have strict: "fst d<snd d" using negative by (simp add: pair_grade_def)
 have positive: "0<snd d" using strict by arith
 have above: "\<exists>d\<in>biv_support(pbw_symbol P). 0<snd d"
   by (rule bexI[where x=d]) (fact positive d)+
 show ?thesis by (rule preliminary_axis_diagonal_first_positive_face[OF source pair member unique above])
qed

end
