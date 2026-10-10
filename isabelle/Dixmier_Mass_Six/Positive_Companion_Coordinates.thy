theory Positive_Companion_Coordinates
 imports Positive_Companion_Axis
   "Rational_Leading_Face"
   "GGV_Case_Field_Adapter"
begin

lemma positive_companion_symbol_totalDegree_bound:
 fixes P::"complex poly_operator" and rho sigma k::nat and R F::"complex bivariate" and m::int and mu::complex
 assumes rho: "0<rho" and slope: "rho<sigma" and mu: "mu\<noteq>0" and primitive: "coprime rho sigma"
   and Rhom: "weighted_homogeneous (int rho) (int sigma) m R"
   and Fhom: "weighted_homogeneous (int rho) (int sigma) (int rho+int sigma) F"
   and face: "1<card(biv_support R)"
   and shape: "leading_form (int rho) (int sigma) P=smult [:mu:] (R^k)"
   and companion: "biv_poisson R F=R"
 shows "rho=1 \<and> (k*nat m,0)\<in>biv_support(pbw_symbol P) \<and>
   (\<forall>e\<in>biv_support(pbw_symbol P). fst e+snd e\<le>k*nat m)"
proof -
 have first: "rho=1" and endpoint: "(k*nat m,0)\<in>biv_support(leading_form (int rho) (int sigma) P)"
   using positive_companion_leadingFace_has_axis_endpoint[OF rho slope mu primitive Rhom Fhom face shape companion] by auto
 have endpoint1: "(k*nat m,0)\<in>biv_support(leading_form 1 (int sigma) P)"
   using endpoint first by simp
 have data: "(k*nat m,0)\<in>biv_support(pbw_symbol P) \<and>
   (\<forall>e\<in>biv_support(pbw_symbol P). rationalNewtonWeight (of_nat sigma) e\<le>of_nat(k*nat m))"
   using iffD1[OF leadingForm_mem_iff_rational_slope[where P=P and rho=1 and sigma="int sigma" and a="(k*nat m,0)", OF zero_less_one] endpoint1]
   by (simp add: rationalNewtonWeight_def)
 have lower: "(of_nat(fst e)+ of_nat(snd e)::rat)\<le>rationalNewtonWeight (of_nat sigma) e" for e
 proof -
   have sp: "(1::rat)\<le>of_nat sigma" using slope first by simp
   have sy: "(0::rat)\<le>of_nat(snd e)" by simp
   have "(of_nat(snd e)::rat)\<le>of_nat sigma* of_nat(snd e)"
     using mult_right_mono[OF sp sy] by simp
   then show ?thesis by (simp add: rationalNewtonWeight_def)
 qed
 have bound: "fst e+snd e\<le>k*nat m" if "e\<in>biv_support(pbw_symbol P)" for e
 proof -
   have "(of_nat(fst e)+ of_nat(snd e)::rat)\<le>of_nat(k*nat m)"
     using lower[of e] data that by (meson order_trans)
   then show ?thesis by (simp only: of_nat_add[symmetric] of_nat_le_iff)
 qed
 show ?thesis using first data bound by blast
qed

lemma positive_companion_totalDeg_eq_axis_intercept:
 fixes P::"complex poly_operator" and rho sigma k::nat and R F::"complex bivariate" and m::int and mu::complex
 assumes rho: "0<rho" and slope: "rho<sigma" and mu: "mu\<noteq>0" and primitive: "coprime rho sigma"
   and Rhom: "weighted_homogeneous (int rho) (int sigma) m R"
   and Fhom: "weighted_homogeneous (int rho) (int sigma) (int rho+int sigma) F"
   and face: "1<card(biv_support R)"
   and shape: "leading_form (int rho) (int sigma) P=smult [:mu:] (R^k)"
   and companion: "biv_poisson R F=R"
 shows "rho=1 \<and> total_degree P=k*nat m"
proof -
 have first: "rho=1" and endpoint: "(k*nat m,0)\<in>biv_support(pbw_symbol P)"
   and bound: "\<And>e. e\<in>biv_support(pbw_symbol P) \<Longrightarrow> fst e+snd e\<le>k*nat m"
   using positive_companion_symbol_totalDegree_bound[OF rho slope mu primitive Rhom Fhom face shape companion] by blast+
 let ?S="insert 0 ((\<lambda>e. fst e+snd e) ` biv_support(pbw_symbol P))"
 have finite: "finite ?S" by simp
 have member: "k*nat m\<in>?S" using imageI[OF endpoint, where f="\<lambda>e. fst e+snd e"] by simp
 have upper: "n\<le>k*nat m" if "n\<in>?S" for n using that bound by auto
 have maximum: "Max ?S=k*nat m"
 proof (rule Max_eqI)
  show "finite ?S" by (rule finite)
  show "\<And>y. y\<in>?S \<Longrightarrow> y\<le>k*nat m" by (rule upper)
  show "k*nat m\<in>?S" by (rule member)
 qed
 show ?thesis using first maximum by (simp only: total_degree_def)
qed

lemma positive_companion_shared_diagonal_point_y_eq_zero:
 fixes P::"complex poly_operator" and rho sigma k a b::nat and R F::"complex bivariate" and m::int and mu::complex
 assumes rho: "0<rho" and slope: "rho<sigma" and mu: "mu\<noteq>0" and primitive: "coprime rho sigma"
   and Rhom: "weighted_homogeneous (int rho) (int sigma) m R"
   and Fhom: "weighted_homogeneous (int rho) (int sigma) (int rho+int sigma) F"
   and face: "1<card(biv_support R)"
   and shape: "leading_form (int rho) (int sigma) P=smult [:mu:] (R^k)"
   and companion: "biv_poisson R F=R" and diagonal: "total_degree P=a+b"
   and shared: "(a,b)\<in>biv_support(leading_form (int rho) (int sigma) P)"
 shows "b=0"
proof -
 have first: "rho=1" and endpoint: "(k*nat m,0)\<in>biv_support(leading_form (int rho) (int sigma) P)"
   using positive_companion_leadingFace_has_axis_endpoint[OF rho slope mu primitive Rhom Fhom face shape companion] by auto
 have degree: "total_degree P=k*nat m"
   using positive_companion_totalDeg_eq_axis_intercept[OF rho slope mu primitive Rhom Fhom face shape companion] by blast
 have weights: "pair_weight (int rho) (int sigma) (a,b)=pair_weight (int rho) (int sigma) (k*nat m,0)"
   using shared endpoint by (simp add: leading_form_def weighted_component_support)
 have equation: "int a+int sigma*int b=int(k*nat m)"
   using weights first by (simp add: pair_weight_def mult.commute)
 have natural_total: "k*nat m=a+b" by (rule trans[OF degree[symmetric] diagonal])
 have total: "int(k*nat m)=int a+int b"
  using arg_cong[OF natural_total, where f=int] by (simp only: of_nat_add)
 have product: "(int sigma-1)*int b=0" using equation total by (simp add: algebra_simps; linarith)
 show ?thesis using product first slope by auto
qed

lemma preliminary_positive_face_shared_diagonal_point_y_eq_zero:
 fixes P Q::"complex poly_operator" and rho sigma a b::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and rho: "0<rho" and slope: "rho<sigma" and primitive: "coprime rho sigma"
   and direction: "is_direction (int rho) (int sigma)"
   and face: "1<card(biv_support(leading_form (int rho) (int sigma) P))"
   and diagonal: "total_degree P=a+b"
   and shared: "(a,b)\<in>biv_support(leading_form (int rho) (int sigma) P)"
 shows "b=0"
proof -
 obtain F where Fhom: "weighted_homogeneous (int rho) (int sigma) (int rho+int sigma) F"
   and companion: "biv_poisson (leading_form (int rho) (int sigma) P) F=leading_form (int rho) (int sigma) P"
   using source pair direction unfolding GGVPreliminaryCompanionInput_def by blast
 have Rhom: "weighted_homogeneous (int rho) (int sigma) (v_degree (int rho) (int sigma) P)
   (leading_form (int rho) (int sigma) P)"
   by (simp only: leading_form_def; rule weighted_component_homogeneous)
 show ?thesis
   by (rule positive_companion_shared_diagonal_point_y_eq_zero[where R="leading_form (int rho) (int sigma) P"
     and F=F and m="v_degree (int rho) (int sigma) P" and k=1 and mu=1,
     OF rho slope one_neq_zero primitive Rhom Fhom face _ companion diagonal shared])
     (simp only: power_one_right pCons_one smult_1_left)
qed

lemma positive_rational_direction:
 fixes t::rat
 assumes above: "1<t"
 shows "\<exists>rho sigma::nat. 0<rho \<and> rho<sigma \<and> coprime rho sigma \<and>
   is_direction (int rho) (int sigma) \<and> (of_nat sigma/ of_nat rho::rat)=t"
proof -
 obtain a b where quotient: "quotient_of t=(a,b)" by (cases "quotient_of t") auto
 have b: "0<b" by (rule quotient_of_denom_pos[OF quotient])
 have ratio: "t=(of_int a/ of_int b::rat)" by (rule quotient_of_div[OF quotient])
 have ab_cast: "(of_int b::rat)<of_int a" using above b by (simp add: ratio less_divide_eq)
 have ab: "b<a" using ab_cast by simp
 have a: "0<a" using b ab by arith
 have primitive: "coprime a b" by (rule quotient_of_coprime[OF quotient])
 have cast_a: "int(nat a)=a" using a by simp
 have cast_b: "int(nat b)=b" using b by simp
 have integer: "coprime (int(nat a)) (int(nat b))"
   using primitive by (simp only: cast_a cast_b)
 have natural: "coprime (nat b) (nat a)"
   using integer by (simp only: coprime_int_iff coprime_commute)
 have direction: "is_direction (int(nat b)) (int(nat a))"
   using natural a b by (simp add: is_direction_def coprime_iff_gcd_eq_1)
 show ?thesis by (intro exI[of _ "nat b"] exI[of _ "nat a"])
   (use a b ab ratio natural direction in auto)
qed

lemma preliminary_companion_support_second_coord_le:
 fixes P Q::"complex poly_operator" and a b::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and diagonal: "total_degree P=a+b" and diagonal_member: "(a,b)\<in>biv_support(leading_form 1 1 P)"
   and unique: "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> e=(a,b)"
   and b: "0<b"
 shows "\<forall>e\<in>biv_support(pbw_symbol P). snd e\<le>b"
proof (rule ballI)
 fix e assume e: "e\<in>biv_support(pbw_symbol P)"
 show "snd e\<le>b"
 proof (rule ccontr)
   assume negative: "\<not>snd e\<le>b"
   have strict: "b<snd e" using negative by arith
   have above: "\<exists>e\<in>biv_support(pbw_symbol P). snd(a,b)<snd e"
     by (rule bexI[where x=e]) (use strict e in simp_all)
   have last: "snd z\<le>snd(a,b)" if "z\<in>biv_support(leading_form 1 1 P)" for z
     using unique[OF that] by simp
   obtain t c where t: "1<t"
     and bound: "\<forall>z\<in>biv_support(pbw_symbol P). rationalNewtonWeight t z\<le>rationalNewtonWeight t (a,b)"
     and c: "c\<in>biv_support(pbw_symbol P)" and cb: "b<snd c"
     and tie: "rationalNewtonWeight t c=rationalNewtonWeight t (a,b)"
     using leadingFace_exists_first_upward_tilt[where P=P and rho=1 and sigma=1 and a="(a,b)", OF zero_less_one diagonal_member last above]
     by auto
   obtain rho sigma::nat where rho: "0<rho" and slope: "rho<sigma" and primitive: "coprime rho sigma"
     and direction: "is_direction (int rho) (int sigma)" and ratio: "(of_nat sigma/ of_nat rho::rat)=t"
     using positive_rational_direction[OF t] by blast
   have raw: "(a,b)\<in>biv_support(pbw_symbol P)"
     using diagonal_member by (simp add: leading_form_def weighted_component_support)
   have rho_int: "0<int rho" using rho by simp
   have ratio_int: "(of_int(int sigma)/ of_int(int rho)::rat)=t" using ratio by simp
   have ap: "(a,b)\<in>biv_support(leading_form (int rho) (int sigma) P)"
     by (simp only: leadingForm_mem_iff_rational_slope[where P=P and rho="int rho" and sigma="int sigma", OF rho_int] ratio_int;
       rule conjI[OF raw bound])
   have cbound: "\<forall>z\<in>biv_support(pbw_symbol P). rationalNewtonWeight t z\<le>rationalNewtonWeight t c"
     using bound tie by simp
   have cp: "c\<in>biv_support(leading_form (int rho) (int sigma) P)"
     by (simp only: leadingForm_mem_iff_rational_slope[where P=P and rho="int rho" and sigma="int sigma", OF rho_int] ratio_int;
       rule conjI[OF c cbound])
   have distinct: "(a,b)\<noteq>c" using cb by auto
   have face: "1<card(biv_support(leading_form (int rho) (int sigma) P))"
   proof (rule ccontr)
     assume "\<not>1<card(biv_support(leading_form (int rho) (int sigma) P))"
     then have small: "card(biv_support(leading_form (int rho) (int sigma) P))\<le>Suc 0" by arith
     have all_equal: "\<forall>x\<in>biv_support(leading_form (int rho) (int sigma) P).
       \<forall>y\<in>biv_support(leading_form (int rho) (int sigma) P). x=y"
       by (rule iffD1[OF card_le_Suc0_iff_eq[where A="biv_support(leading_form (int rho) (int sigma) P)", OF finite_biv_support] small])
     show False using all_equal ap cp distinct by blast
   qed
   have "b=0" by (rule preliminary_positive_face_shared_diagonal_point_y_eq_zero[OF source pair rho slope primitive direction face diagonal ap])
   then show False using b by arith
 qed
qed

lemma preliminary_positive_face_total_degree_axis_endpoint:
 fixes P Q::"complex poly_operator" and rho sigma::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and rho: "0<rho" and slope: "rho<sigma" and primitive: "coprime rho sigma"
   and direction: "is_direction (int rho) (int sigma)"
   and face: "1<card(biv_support(leading_form (int rho) (int sigma) P))"
 shows "rho=1 \<and> (total_degree P,0)\<in>biv_support(leading_form (int rho) (int sigma) P)"
proof -
 obtain F where Fhom: "weighted_homogeneous (int rho) (int sigma) (int rho+int sigma) F"
   and companion: "biv_poisson (leading_form (int rho) (int sigma) P) F=leading_form (int rho) (int sigma) P"
   using source pair direction unfolding GGVPreliminaryCompanionInput_def by blast
 have Rhom: "weighted_homogeneous (int rho) (int sigma) (v_degree (int rho) (int sigma) P)
   (leading_form (int rho) (int sigma) P)"
   by (simp only: leading_form_def; rule weighted_component_homogeneous)
 have shape: "leading_form (int rho) (int sigma) P=
   smult [:1:] ((leading_form (int rho) (int sigma) P)^1)"
   by (simp only: power_one_right pCons_one smult_1_left)
 have first: "rho=1" and endpoint: "(nat(v_degree (int rho) (int sigma) P),0)\<in>biv_support(leading_form (int rho) (int sigma) P)"
   using positive_companion_leadingFace_has_axis_endpoint[where R="leading_form (int rho) (int sigma) P"
     and F=F and m="v_degree (int rho) (int sigma) P" and k=1 and mu=1,
     OF rho slope one_neq_zero primitive Rhom Fhom face shape companion]
   by (auto simp only: mult_1_left)
 have degree: "total_degree P=nat(v_degree (int rho) (int sigma) P)"
   using positive_companion_totalDeg_eq_axis_intercept[where R="leading_form (int rho) (int sigma) P"
     and F=F and m="v_degree (int rho) (int sigma) P" and k=1 and mu=1,
     OF rho slope one_neq_zero primitive Rhom Fhom face shape companion]
   by (simp only: mult_1_left)
 show ?thesis using first endpoint degree by simp
qed

lemma preliminary_positive_last_point_y_bound:
 fixes P Q::"complex poly_operator" and sigma a b::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and sigma: "1\<le>sigma" and member: "(a,b)\<in>biv_support(leading_form 1 (int sigma) P)"
   and last: "\<And>e. e\<in>biv_support(leading_form 1 (int sigma) P) \<Longrightarrow> snd e\<le>b"
   and b: "0<b"
 shows "\<forall>e\<in>biv_support(pbw_symbol P). snd e\<le>b"
proof (rule ballI)
 fix e assume e: "e\<in>biv_support(pbw_symbol P)"
 show "snd e\<le>b"
 proof (rule ccontr)
   assume negative: "\<not>snd e\<le>b"
   have strict: "b<snd e" using negative by arith
   have above: "\<exists>e\<in>biv_support(pbw_symbol P). snd(a,b)<snd e"
     by (rule bexI[where x=e]) (use strict e in simp_all)
   obtain t c where t: "of_nat sigma<t"
     and bound: "\<forall>z\<in>biv_support(pbw_symbol P). rationalNewtonWeight t z\<le>rationalNewtonWeight t (a,b)"
     and c: "c\<in>biv_support(pbw_symbol P)" and cb: "b<snd c"
     and tie: "rationalNewtonWeight t c=rationalNewtonWeight t (a,b)"
     using leadingFace_exists_first_upward_tilt[where P=P and rho=1 and sigma="int sigma" and a="(a,b)",
       OF zero_less_one member _ above] last by auto
   have tone: "1<t" using t sigma by (simp; linarith)
   obtain rho tau::nat where rho: "0<rho" and slope: "rho<tau" and primitive: "coprime rho tau"
     and direction: "is_direction (int rho) (int tau)" and ratio: "(of_nat tau/ of_nat rho::rat)=t"
     using positive_rational_direction[OF tone] by blast
   have raw: "(a,b)\<in>biv_support(pbw_symbol P)"
     using member by (simp add: leading_form_def weighted_component_support)
   have rp: "0<int rho" using rho by simp
   have ratio_int: "(of_int(int tau)/ of_int(int rho)::rat)=t" using ratio by simp
   have ap: "(a,b)\<in>biv_support(leading_form (int rho) (int tau) P)"
     by (simp only: leadingForm_mem_iff_rational_slope[where P=P and rho="int rho" and sigma="int tau", OF rp] ratio_int;
       rule conjI[OF raw bound])
   have cp: "c\<in>biv_support(leading_form (int rho) (int tau) P)"
     by (simp only: leadingForm_mem_iff_rational_slope[where P=P and rho="int rho" and sigma="int tau", OF rp] ratio_int;
       use c bound tie in auto)
   have face: "1<card(biv_support(leading_form (int rho) (int tau) P))"
   proof (rule ccontr)
     assume "\<not>1<card(biv_support(leading_form (int rho) (int tau) P))"
     then have small: "card(biv_support(leading_form (int rho) (int tau) P))\<le>Suc 0" by arith
     have equal: "\<forall>x\<in>biv_support(leading_form (int rho) (int tau) P).
       \<forall>y\<in>biv_support(leading_form (int rho) (int tau) P). x=y"
       by (rule iffD1[OF card_le_Suc0_iff_eq[where A="biv_support(leading_form (int rho) (int tau) P)", OF finite_biv_support] small])
     show False using equal ap cp cb by auto
   qed
   have axis: "(total_degree P,0)\<in>biv_support(leading_form (int rho) (int tau) P)"
     using preliminary_positive_face_total_degree_axis_endpoint[OF source pair rho slope primitive direction face] by blast
   have axis_raw: "(total_degree P,0)\<in>biv_support(pbw_symbol P)"
     using axis by (simp add: leading_form_def weighted_component_support)
   have axis_bound: "rationalNewtonWeight t (a,b)\<le>of_nat(total_degree P)"
     using axis ap by (simp only: leadingForm_mem_iff_rational_slope[where P=P and rho="int rho" and sigma="int tau", OF rp] ratio_int;
       auto simp: rationalNewtonWeight_def)
   have old_bound: "of_nat(total_degree P)\<le>of_nat a+(of_nat sigma::rat)* of_nat b"
     using member axis_raw by (simp only: leadingForm_mem_iff_rational_slope[where P=P and rho=1 and sigma="int sigma", OF zero_less_one];
       auto simp: rationalNewtonWeight_def)
   have product: "0<(t- of_nat sigma)*(of_nat b::rat)" using t b by (intro mult_pos_pos) simp_all
   show False using axis_bound old_bound product by (simp add: rationalNewtonWeight_def algebra_simps; linarith)
 qed
qed

end
