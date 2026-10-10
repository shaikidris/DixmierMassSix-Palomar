theory Actual_Face_Adjacency
 imports Rational_Face_Direction
begin

lemma sortedLT_next_le_of_mem_gt:
 fixes l::"rat list"
 assumes sorted: "sorted_wrt (<) l" and j: "j+1<length l"
   and member: "u\<in>set l" and gt: "l!j<u"
 shows "l!(j+1)\<le>u"
proof -
 obtain k where k: "k<length l" and eq: "l!k=u" using member by (simp only: in_set_conv_nth; blast)
 have jk: "j<k"
 proof (rule ccontr)
   assume "\<not>j<k"
   then have le: "k\<le>j" by arith
   have order: "l!k\<le>l!j" by (rule sorted_nth_mono) (use sorted j le in \<open>auto simp: strict_sorted_iff\<close>)
   show False using order eq gt by arith
 qed
 have "l!(j+1)\<le>l!k" by (rule sorted_nth_mono) (use sorted k jk in \<open>auto simp: strict_sorted_iff\<close>)
 then show ?thesis by (simp only: eq)
qed

lemma sortedLT_first_le_mem:
 fixes l::"rat list"
 assumes sorted: "sorted_wrt (<) l" and nonempty: "0<length l" and member: "u\<in>set l"
 shows "l!0\<le>u"
proof -
 obtain k where k: "k<length l" and eq: "l!k=u" using member by (simp only: in_set_conv_nth; blast)
 have "l!0\<le>l!k" by (rule sorted_nth_mono) (use sorted k in \<open>auto simp: strict_sorted_iff\<close>)
 then show ?thesis by (simp only: eq)
qed

lemma sortedLT_mem_le_last:
 fixes l::"rat list"
 assumes sorted: "sorted_wrt (<) l" and j: "j+1=length l" and member: "u\<in>set l"
 shows "u\<le>l!j"
proof -
 obtain k where k: "k<length l" and eq: "l!k=u" using member by (simp only: in_set_conv_nth; blast)
 have sorted_le: "sorted l" using sorted by (simp only: strict_sorted_iff; blast)
 have kj: "k\<le>j" using k j by arith
 have jbound: "j<length l" using j by arith
 have "l!k\<le>l!j" by (rule sorted_nth_mono[OF sorted_le kj jbound])
 then show ?thesis by (simp only: eq)
qed

lemma leadingFace_points_ordered_by_rational_slope:
 fixes P::"complex poly_operator" and rho1 sigma1 rho2 sigma2::int
 assumes rho1: "0<rho1" and rho2: "0<rho2"
   and slope: "(of_int sigma1/ of_int rho1::rat)< of_int sigma2/ of_int rho2"
   and a: "a\<in>biv_support(leading_form rho1 sigma1 P)" and b: "b\<in>biv_support(leading_form rho2 sigma2 P)"
 shows "snd a\<le>snd b \<and> (snd a=snd b \<longrightarrow> a=b)"
proof -
 let ?t1="(of_int sigma1/ of_int rho1::rat)" let ?t2="(of_int sigma2/ of_int rho2::rat)"
 have araw: "a\<in>biv_support(pbw_symbol P)" and eraw: "b\<in>biv_support(pbw_symbol P)"
   using a b by (auto simp: leading_form_def weighted_component_support)
 have amax: "\<forall>p\<in>biv_support(pbw_symbol P). rationalNewtonWeight ?t1 p\<le>rationalNewtonWeight ?t1 a"
   using a by (simp only: leadingForm_mem_iff_rational_slope[OF rho1]; blast)
 have bmax: "\<forall>p\<in>biv_support(pbw_symbol P). rationalNewtonWeight ?t2 p\<le>rationalNewtonWeight ?t2 b"
   using b by (simp only: leadingForm_mem_iff_rational_slope[OF rho2]; blast)
 have ab: "rationalNewtonWeight ?t1 b\<le>rationalNewtonWeight ?t1 a" using amax eraw by blast
 have ba: "rationalNewtonWeight ?t2 a\<le>rationalNewtonWeight ?t2 b" using bmax araw by blast
 have y: "snd a\<le>snd b"
 proof (rule ccontr)
   assume "\<not>snd a\<le>snd b" then have reverse: "snd b<snd a" by arith
   have positive: "0<(?t2-?t1)*(of_nat(snd a)- of_nat(snd b))" by (rule mult_pos_pos) (use slope reverse in auto)
   show False using positive ab ba by (simp add: rationalNewtonWeight_def algebra_simps; linarith)
 qed
 have same: "a=b" if eq: "snd a=snd b"
 proof -
   have cast: "(of_nat(fst a)::rat)= of_nat(fst b)"
     using ab ba eq by (simp add: rationalNewtonWeight_def; linarith)
   have x: "fst a=fst b" using cast by simp
   show ?thesis using x eq by (simp add: prod_eq_iff)
 qed
 show ?thesis using y same by blast
qed

lemma leadingFace_exists_intermediate_actual_negative_face:
 fixes P::"complex poly_operator" and rho1 sigma1 rho2 sigma2::int
 assumes rho1: "0<rho1" and rho2: "0<rho2"
   and left: "-1<(of_int sigma1/ of_int rho1::rat)" and right: "(of_int sigma2/ of_int rho2::rat)<0"
   and a: "a\<in>biv_support(leading_form rho1 sigma1 P)" and b: "b\<in>biv_support(leading_form rho2 sigma2 P)"
   and last: "\<And>p. p\<in>biv_support(leading_form rho1 sigma1 P) \<Longrightarrow> snd p\<le>snd a"
   and higher: "snd a<snd b"
 shows "\<exists>t::rat. of_int sigma1/ of_int rho1<t \<and> t\<le> of_int sigma2/ of_int rho2 \<and>
   t\<in>set(ggv_ordered_negative_face_slopes P) \<and>
   a\<in>biv_support(leading_form (rational_denominator t) (rational_numerator t) P) \<and>
   (\<exists>c\<in>biv_support(leading_form (rational_denominator t) (rational_numerator t) P). snd a<snd c)"
proof -
 let ?t1="(of_int sigma1/ of_int rho1::rat)" let ?t2="(of_int sigma2/ of_int rho2::rat)"
 have araw: "a\<in>biv_support(pbw_symbol P)" using a by (simp add: leading_form_def weighted_component_support)
 have braw: "b\<in>biv_support(pbw_symbol P)" and bmax: "\<forall>p\<in>biv_support(pbw_symbol P). rationalNewtonWeight ?t2 p\<le>rationalNewtonWeight ?t2 b"
   using b by (simp only: leadingForm_mem_iff_rational_slope[OF rho2]; blast)+
 have above: "\<exists>p\<in>biv_support(pbw_symbol P). snd a<snd p" using braw higher by blast
 obtain t c where after: "?t1<t"
   and maximal: "\<forall>p\<in>biv_support(pbw_symbol P). rationalNewtonWeight t p\<le>rationalNewtonWeight t a"
   and c: "c\<in>biv_support(pbw_symbol P)" and higherc: "snd a<snd c"
   and tie: "rationalNewtonWeight t c=rationalNewtonWeight t a"
   using leadingFace_exists_first_upward_tilt[OF rho1 a last above] by blast
 have later: "rationalNewtonWeight ?t2 a\<le>rationalNewtonWeight ?t2 b" using bmax araw by blast
 have before: "t\<le>?t2"
 proof (rule ccontr)
   assume "\<not>t\<le>?t2" then have greater: "?t2<t" by arith
   have positive: "0<(t-?t2)*(of_nat(snd b)- of_nat(snd a))"
     by (rule mult_pos_pos) (use greater higher in auto)
   have first: "rationalNewtonWeight t b\<le>rationalNewtonWeight t a" using maximal braw by blast
   show False using first later positive by (simp add: rationalNewtonWeight_def algebra_simps; linarith)
 qed
 have lt: "-1<t" using left after by arith
 have rt: "t<0" using before right by arith
 have distinct: "a\<noteq>c" using higherc by auto
 have entry: "t\<in>set(ggv_ordered_negative_face_slopes P)"
   using rationalSlope_two_maximizers_mem_ordered_negative_slopes[OF lt rt araw c _ tie distinct] maximal by blast
 have aface: "a\<in>biv_support(leading_form (rational_denominator t) (rational_numerator t) P)"
   by (rule rationalSlope_maximizer_mem_leadingForm[OF araw]) (use maximal in blast)
 have cmax: "rationalNewtonWeight t p\<le>rationalNewtonWeight t c" if "p\<in>biv_support(pbw_symbol P)" for p using maximal that tie by simp
 have cface: "c\<in>biv_support(leading_form (rational_denominator t) (rational_numerator t) P)"
   by (rule rationalSlope_maximizer_mem_leadingForm[OF c cmax])
 show ?thesis using after before entry aface cface higherc by blast
qed

lemma leadingFace_last_point_mem_next_face:
 fixes P::"complex poly_operator" and rho1 sigma1 rho2 sigma2::int
 assumes rho1: "0<rho1" and rho2: "0<rho2"
   and left: "-1<(of_int sigma1/ of_int rho1::rat)" and right: "(of_int sigma2/ of_int rho2::rat)<0"
   and a: "a\<in>biv_support(leading_form rho1 sigma1 P)" and b: "b\<in>biv_support(leading_form rho2 sigma2 P)"
   and last: "\<And>p. p\<in>biv_support(leading_form rho1 sigma1 P) \<Longrightarrow> snd p\<le>snd a" and higher: "snd a<snd b"
   and adjacent_bound: "\<And>u. u\<in>set(ggv_ordered_negative_face_slopes P) \<Longrightarrow> of_int sigma1/ of_int rho1<u \<Longrightarrow> of_int sigma2/ of_int rho2\<le>u"
 shows "a\<in>biv_support(leading_form rho2 sigma2 P)"
proof -
 obtain t where after: "(of_int sigma1/ of_int rho1::rat)<t" and before: "t\<le> of_int sigma2/ of_int rho2"
   and entry: "t\<in>set(ggv_ordered_negative_face_slopes P)"
   and aface: "a\<in>biv_support(leading_form (rational_denominator t) (rational_numerator t) P)"
   using leadingFace_exists_intermediate_actual_negative_face[OF rho1 rho2 left right a b last higher] by blast
 have eq: "t=(of_int sigma2/ of_int rho2::rat)" using before adjacent_bound[OF entry after] by arith
 have raw: "a\<in>biv_support(pbw_symbol P) \<and> (\<forall>p\<in>biv_support(pbw_symbol P).
   rationalNewtonWeight (of_int(rational_numerator t)/ of_int(rational_denominator t)) p\<le>
   rationalNewtonWeight (of_int(rational_numerator t)/ of_int(rational_denominator t)) a)"
   by (rule iffD1[OF leadingForm_mem_iff_rational_slope[where P=P and rho="rational_denominator t" and sigma="rational_numerator t" and a=a, OF rational_denominator_positive] aface])
 have raw_support: "a\<in>biv_support(pbw_symbol P)" by (rule conjunct1[OF raw])
 have raw_maximum: "\<forall>p\<in>biv_support(pbw_symbol P).
   rationalNewtonWeight (of_int(rational_numerator t)/ of_int(rational_denominator t)) p\<le>
   rationalNewtonWeight (of_int(rational_numerator t)/ of_int(rational_denominator t)) a"
   by (rule conjunct2[OF raw])
 have maximum: "\<forall>p\<in>biv_support(pbw_symbol P).
   rationalNewtonWeight (of_int sigma2/ of_int rho2) p\<le>rationalNewtonWeight (of_int sigma2/ of_int rho2) a"
   using raw_maximum by (simp only: rational_direction_ratio eq)
 have data: "a\<in>biv_support(pbw_symbol P) \<and> (\<forall>p\<in>biv_support(pbw_symbol P).
   rationalNewtonWeight (of_int sigma2/ of_int rho2) p\<le>rationalNewtonWeight (of_int sigma2/ of_int rho2) a)"
   by (rule conjI[OF raw_support maximum])
 show ?thesis
   by (rule iffD2[OF leadingForm_mem_iff_rational_slope[where P=P and rho=rho2 and sigma=sigma2 and a=a, OF rho2] data])
qed

lemma leadingFace_last_point_mem_successor_list_face:
 fixes P::"complex poly_operator" and rho1 sigma1 rho2 sigma2::int
 assumes rho1: "0<rho1" and rho2: "0<rho2"
   and left: "-1<(of_int sigma1/ of_int rho1::rat)" and right: "(of_int sigma2/ of_int rho2::rat)<0"
   and index: "j+1<length(ggv_ordered_negative_face_slopes P)"
   and first: "ggv_ordered_negative_face_slopes P!j=(of_int sigma1/ of_int rho1::rat)"
   and second: "ggv_ordered_negative_face_slopes P!(j+1)=(of_int sigma2/ of_int rho2::rat)"
   and a: "a\<in>biv_support(leading_form rho1 sigma1 P)" and b: "b\<in>biv_support(leading_form rho2 sigma2 P)"
   and last: "\<And>p. p\<in>biv_support(leading_form rho1 sigma1 P) \<Longrightarrow> snd p\<le>snd a"
 shows "a\<in>biv_support(leading_form rho2 sigma2 P)"
proof -
 have step: "ggv_ordered_negative_face_slopes P!j<ggv_ordered_negative_face_slopes P!(j+1)"
   by (rule sorted_wrt_nth_less[OF ggv_ordered_negative_slopes_strict]) (use index in auto)
 have slope: "(of_int sigma1/ of_int rho1::rat)< of_int sigma2/ of_int rho2" using step by (simp only: first second)
 have order: "snd a\<le>snd b \<and> (snd a=snd b \<longrightarrow> a=b)"
   by (rule leadingFace_points_ordered_by_rational_slope[OF rho1 rho2 slope a b])
 show ?thesis
 proof (cases "snd a<snd b")
   case True
   have successor_bound: "(of_int sigma2/ of_int rho2::rat)\<le>u" if entry: "u\<in>set(ggv_ordered_negative_face_slopes P)"
     and after: "(of_int sigma1/ of_int rho1::rat)<u" for u
   proof -
     have gt: "ggv_ordered_negative_face_slopes P!j<u" using after by (simp only: first)
     have "ggv_ordered_negative_face_slopes P!(j+1)\<le>u"
       by (rule sortedLT_next_le_of_mem_gt[OF ggv_ordered_negative_slopes_strict index entry gt])
     then show ?thesis by (simp only: second)
   qed
   show ?thesis by (rule leadingFace_last_point_mem_next_face[OF rho1 rho2 left right a b last True successor_bound])
 next
   case False
   have "a=b" using order False by auto
   then show ?thesis using b by simp
 qed
qed

lemma leadingFace_successor_shared_endpoint:
 fixes P::"complex poly_operator" and rho1 sigma1 rho2 sigma2::int
 assumes rho1: "0<rho1" and rho2: "0<rho2"
   and left: "-1<(of_int sigma1/ of_int rho1::rat)" and right: "(of_int sigma2/ of_int rho2::rat)<0"
   and index: "j+1<length(ggv_ordered_negative_face_slopes P)"
   and first: "ggv_ordered_negative_face_slopes P!j=(of_int sigma1/ of_int rho1::rat)"
   and second: "ggv_ordered_negative_face_slopes P!(j+1)=(of_int sigma2/ of_int rho2::rat)"
   and face1: "in_direction rho1 sigma1 P" and face2: "in_direction rho2 sigma2 P"
 shows "\<exists>a. a\<in>biv_support(leading_form rho1 sigma1 P) \<and>
   a\<in>biv_support(leading_form rho2 sigma2 P) \<and>
   (\<forall>p\<in>biv_support(leading_form rho1 sigma1 P). snd p\<le>snd a) \<and>
   (\<forall>q\<in>biv_support(leading_form rho2 sigma2 P). snd a\<le>snd q)"
proof -
 let ?S1="biv_support(leading_form rho1 sigma1 P)" let ?S2="biv_support(leading_form rho2 sigma2 P)"
 have nonempty1: "?S1\<noteq>{}" and nonempty2: "?S2\<noteq>{}" using face1 face2 by (auto simp: in_direction_def)
 have attained: "Max(snd ` ?S1)\<in>snd ` ?S1" by (rule Max_in) (use nonempty1 in auto)
 obtain a where max_eq: "Max(snd ` ?S1)=snd a" and a: "a\<in>?S1"
   using attained by (rule imageE)
 have ax: "snd a=Max(snd ` ?S1)" by (rule sym[OF max_eq])
 have last: "snd p\<le>snd a" if "p\<in>?S1" for p unfolding ax by (rule Max_ge) (simp, rule imageI[OF that])
 obtain b where b: "b\<in>?S2" using nonempty2 by blast
 have aface: "a\<in>?S2" by (rule leadingFace_last_point_mem_successor_list_face[OF rho1 rho2 left right index first second a b last])
 have step: "ggv_ordered_negative_face_slopes P!j<ggv_ordered_negative_face_slopes P!(j+1)"
   by (rule sorted_wrt_nth_less[OF ggv_ordered_negative_slopes_strict]) (use index in auto)
 have slope: "(of_int sigma1/ of_int rho1::rat)< of_int sigma2/ of_int rho2" using step by (simp only: first second)
 have minimum: "snd a\<le>snd q" if "q\<in>?S2" for q
   by (rule conjunct1[OF leadingFace_points_ordered_by_rational_slope[OF rho1 rho2 slope a that]])
 show ?thesis
 proof (rule exI[where x=a], intro conjI)
   show "a\<in>?S1" by (rule a)
   show "a\<in>?S2" by (rule aface)
   show "\<forall>p\<in>?S1. snd p\<le>snd a" by (rule ballI, rule last)
   show "\<forall>q\<in>?S2. snd a\<le>snd q" by (rule ballI, rule minimum)
 qed
qed
end
