theory Rational_Face_Direction
 imports Common_Face_Directions
   "Rational_Leading_Face"
begin

definition rational_numerator::"rat \<Rightarrow> int" where "rational_numerator t=fst(quotient_of t)"
definition rational_denominator::"rat \<Rightarrow> int" where "rational_denominator t=snd(quotient_of t)"
lemma rational_direction_quotient:
 "quotient_of t=(rational_numerator t,rational_denominator t)"
 by (simp add: rational_numerator_def rational_denominator_def)
lemma rational_denominator_positive:
 "0<rational_denominator t" by (rule quotient_of_denom_pos[OF rational_direction_quotient])
lemma rational_direction_ratio:
 "(of_int(rational_numerator t)/ of_int(rational_denominator t)::rat)=t"
 by (rule sym, rule quotient_of_div[OF rational_direction_quotient])
lemma rational_direction_coprime:
 "coprime (rational_denominator t) (rational_numerator t)"
 using quotient_of_coprime[OF rational_direction_quotient] by (simp add: coprime_commute)

lemma rationalSlope_primitive_negative_direction:
 fixes t::rat
 assumes left: "-1<t" and right: "t<0"
 shows "is_direction (rational_denominator t) (rational_numerator t) \<and>
   0<rational_denominator t \<and> rational_numerator t<0 \<and>
   (of_int(rational_numerator t)/ of_int(rational_denominator t)::rat)=t"
proof -
 have positive: "(0::rat)< of_int(rational_denominator t)" using rational_denominator_positive[of t] by simp
 have right_ratio: "(of_int(rational_numerator t)/ of_int(rational_denominator t)::rat)<0"
   using right by (simp only: rational_direction_ratio)
 have numerator: "rational_numerator t<0" using right_ratio positive by (simp add: divide_less_eq)
 have left_ratio: "(-1::rat)< of_int(rational_numerator t)/ of_int(rational_denominator t)"
   using left by (simp only: rational_direction_ratio)
 have sum: "0<rational_denominator t+rational_numerator t"
 proof -
   have "(0::rat)< of_int(rational_denominator t)+ of_int(rational_numerator t)"
     using left_ratio positive by (simp add: less_divide_eq; linarith)
   then show ?thesis by simp
 qed
 have primitive: "gcd (nat(abs(rational_denominator t))) (nat(abs(rational_numerator t)))=1"
   using rational_direction_coprime[of t] by (simp add: coprime_iff_gcd_eq_1[symmetric])
 show ?thesis using primitive sum numerator rational_denominator_positive[of t] rational_direction_ratio[of t]
   by (simp add: is_direction_def)
qed

lemma rationalSlope_maximizer_mem_leadingForm:
 fixes P::"complex poly_operator" and t::rat
 assumes a: "a\<in>biv_support(pbw_symbol P)"
   and maximal: "\<And>b. b\<in>biv_support(pbw_symbol P) \<Longrightarrow> rationalNewtonWeight t b\<le>rationalNewtonWeight t a"
 shows "a\<in>biv_support(leading_form (rational_denominator t) (rational_numerator t) P)"
 by (simp only: leadingForm_mem_iff_rational_slope[where P=P and rho="rational_denominator t" and sigma="rational_numerator t", OF rational_denominator_positive]
   rational_direction_ratio; rule conjI[OF a]; use maximal in blast)

lemma rationalSlope_two_maximizers_mem_ordered_negative_slopes:
 fixes P::"complex poly_operator" and t::rat
 assumes left: "-1<t" and right: "t<0" and a: "a\<in>biv_support(pbw_symbol P)" and b: "b\<in>biv_support(pbw_symbol P)"
   and maximal: "\<And>p. p\<in>biv_support(pbw_symbol P) \<Longrightarrow> rationalNewtonWeight t p\<le>rationalNewtonWeight t a"
   and tie: "rationalNewtonWeight t b=rationalNewtonWeight t a" and distinct: "a\<noteq>b"
 shows "is_direction (rational_denominator t) (rational_numerator t) \<and>
   in_direction (rational_denominator t) (rational_numerator t) P \<and>
   t\<in>set(ggv_ordered_negative_face_slopes P)"
proof -
 have direction: "is_direction (rational_denominator t) (rational_numerator t)"
   and rho: "0<rational_denominator t" and sigma: "rational_numerator t<0"
   using rationalSlope_primitive_negative_direction[OF left right] by auto
 have aface: "a\<in>biv_support(leading_form (rational_denominator t) (rational_numerator t) P)"
   by (rule rationalSlope_maximizer_mem_leadingForm[OF a maximal])
 have bmax: "rationalNewtonWeight t p\<le>rationalNewtonWeight t b" if "p\<in>biv_support(pbw_symbol P)" for p
   using maximal[OF that] tie by simp
 have bface: "b\<in>biv_support(leading_form (rational_denominator t) (rational_numerator t) P)"
   by (rule rationalSlope_maximizer_mem_leadingForm[OF b bmax])
 have large: "1<card(biv_support(leading_form (rational_denominator t) (rational_numerator t) P))"
 proof (rule ccontr)
   assume "\<not>1<card(biv_support(leading_form (rational_denominator t) (rational_numerator t) P))"
   then have small: "card(biv_support(leading_form (rational_denominator t) (rational_numerator t) P))\<le>Suc 0" by arith
   have same: "\<forall>x\<in>biv_support(leading_form (rational_denominator t) (rational_numerator t) P).
     \<forall>y\<in>biv_support(leading_form (rational_denominator t) (rational_numerator t) P). x=y"
     by (rule iffD1[OF card_le_Suc0_iff_eq[where A="biv_support(leading_form (rational_denominator t) (rational_numerator t) P)", OF finite_biv_support] small])
   show False using same aface bface distinct by blast
 qed
 have face: "in_direction (rational_denominator t) (rational_numerator t) P" by (simp only: in_direction_def; rule large)
 have entry: "t\<in>set(ggv_ordered_negative_face_slopes P)"
   by (simp only: mem_ggvOrderedNegativeFaceSlopes_iff; intro bexI[of _ "(rational_denominator t,rational_numerator t)"])
     (use direction rho sigma face rational_direction_ratio[of t] in \<open>auto simp: ggv_negative_primitive_directions_def\<close>)
 show ?thesis using direction face entry by blast
qed

lemma ggv_ordered_negative_entry_canonical_face:
 fixes P::"complex poly_operator" and t::rat
 assumes entry: "t\<in>set(ggv_ordered_negative_face_slopes P)"
 shows "is_direction (rational_denominator t) (rational_numerator t) \<and>
   0<rational_denominator t \<and> rational_numerator t<0 \<and>
   in_direction (rational_denominator t) (rational_numerator t) P"
proof -
 have left: "-1<t" and right: "t<0" using ggv_ordered_negative_slope_bounds[OF entry] by auto
 have canon: "is_direction (rational_denominator t) (rational_numerator t)"
   and rp: "0<rational_denominator t" and sn: "rational_numerator t<0"
   using rationalSlope_primitive_negative_direction[OF left right] by auto
 obtain v where v: "v\<in>ggv_negative_primitive_directions P" and ratio: "t=(of_int(snd v)/ of_int(fst v)::rat)"
   using entry by (simp only: mem_ggvOrderedNegativeFaceSlopes_iff; blast)
 have direction: "is_direction (fst v)(snd v)" and rho: "0<fst v" and face: "in_direction (fst v)(snd v) P"
   using v by (auto simp: ggv_negative_primitive_directions_def)
 have eq: "(of_int(snd v)/ of_int(fst v)::rat)= of_int(rational_numerator t)/ of_int(rational_denominator t)"
   using ratio rational_direction_ratio[of t] by simp
 have normalized: "fst v=rational_denominator t \<and> snd v=rational_numerator t"
   by (rule ggv_primitive_negative_normal_unique[OF direction canon rho rp eq])
 show ?thesis using canon rp sn face normalized by auto
qed

lemma ggv_ordered_negative_entry_nat_face:
 fixes P::"complex poly_operator" and t::rat
 assumes entry: "t\<in>set(ggv_ordered_negative_face_slopes P)"
 shows "\<exists>rho s::nat. 0<rho \<and> 0<s \<and> is_direction (int rho) (-int s) \<and>
   in_direction (int rho) (-int s) P \<and> t=(of_int(-int s)/ of_int(int rho)::rat) \<and>
   int rho=rational_denominator t \<and> -int s=rational_numerator t"
proof -
 have direction: "is_direction (rational_denominator t) (rational_numerator t)"
   and rho: "0<rational_denominator t" and sigma: "rational_numerator t<0"
   and face: "in_direction (rational_denominator t) (rational_numerator t) P"
   using ggv_ordered_negative_entry_canonical_face[OF entry] by auto
 let ?r="nat(rational_denominator t)" let ?s="nat(-rational_numerator t)"
 have rc: "int ?r=rational_denominator t" using rho by simp
 have sc: "-int ?s=rational_numerator t" using sigma by simp
 show ?thesis by (intro exI[of _ ?r] exI[of _ ?s])
   (use rho sigma direction face rational_direction_ratio[of t] in \<open>simp add: rc sc\<close>)
qed
end
