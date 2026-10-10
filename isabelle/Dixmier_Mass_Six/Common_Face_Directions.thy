theory Common_Face_Directions
 imports Common_Face_Endpoints
   "Ordered_Face_Directions"
begin

lemma negative_face_distinct_x:
 fixes P::"complex poly_operator" and rho s::nat
 assumes s: "0<s" and a: "a\<in>biv_support(leading_form (int rho) (-int s) P)"
   and b: "b\<in>biv_support(leading_form (int rho) (-int s) P)" and distinct: "a\<noteq>b"
 shows "fst a\<noteq>fst b"
proof
 assume x: "fst a=fst b"
 have weight: "pair_weight (int rho) (-int s) a=pair_weight (int rho) (-int s) b"
   using a b by (simp add: leading_form_def weighted_component_support)
 have product: "int s*(int(snd a)-int(snd b))=0"
 proof -
   have "int s*(int(snd a)-int(snd b))=
     pair_weight (int rho) (-int s) b-pair_weight (int rho) (-int s) a"
     by (simp add: pair_weight_def x algebra_simps)
   also have "...=0" by (simp only: weight diff_self)
   finally show ?thesis .
 qed
 have y: "snd a=snd b" using product s by auto
 show False using distinct x y by (simp add: prod_eq_iff)
qed

lemma counterexample_negative_face_direction_of_first:
 fixes P Q::"complex poly_operator" and rho s::nat
 assumes pair: "is_counterexample_pair P Q" and s: "0<s"
   and direction: "is_direction (int rho) (-int s)" and face: "in_direction (int rho) (-int s) P"
 shows "in_direction (int rho) (-int s) Q"
proof -
 obtain n d u v r t::nat where n: "0<n" and d: "0<d"
   and Pend: "(d*u,d*v)\<in>biv_support(leading_form (int rho) (-int s) P)"
   and Qend: "(n*u,n*v)\<in>biv_support(leading_form (int rho) (-int s) Q)"
   and Pstart: "(d*r,d*t)\<in>biv_support(leading_form (int rho) (-int s) P)"
   and Qstart: "(n*r,n*t)\<in>biv_support(leading_form (int rho) (-int s) Q)"
   and Pbounds: "\<forall>e\<in>biv_support(leading_form (int rho) (-int s) P). d*r\<le>fst e \<and> fst e\<le>d*u"
   using counterexample_strict_negative_face_proportional_endpoints[OF pair s direction] by blast
 have less: "r<u"
 proof (rule ccontr)
   assume no: "\<not>r<u"
   have endpoint_bound: "d*r\<le>d*u"
     using bspec[OF Pbounds Pstart] by (simp only: fst_conv; blast)
   have le: "r\<le>u" using endpoint_bound d by simp
   have equal: "r=u" using no le by arith
   have all_equal: "a=b" if a: "a\<in>biv_support(leading_form (int rho) (-int s) P)"
     and b: "b\<in>biv_support(leading_form (int rho) (-int s) P)" for a b
   proof (rule ccontr)
     assume "a\<noteq>b"
     have distinct: "fst a\<noteq>fst b" by (rule negative_face_distinct_x[OF s a b \<open>a\<noteq>b\<close>])
     have abounds: "d*u\<le>fst a \<and> fst a\<le>d*u"
       using bspec[OF Pbounds a] by (simp only: equal)
     have bbounds: "d*u\<le>fst b \<and> fst b\<le>d*u"
       using bspec[OF Pbounds b] by (simp only: equal)
     have ax: "fst a=d*u" using abounds by arith
     have bx: "fst b=d*u" using bbounds by arith
     have same_x: "fst a=fst b" by (rule trans[OF ax bx[symmetric]])
     show False by (rule notE[OF distinct same_x])
   qed
   have small: "card(biv_support(leading_form (int rho) (-int s) P))\<le>Suc 0"
     by (rule iffD2[OF card_le_Suc0_iff_eq[where A="biv_support(leading_form (int rho) (-int s) P)", OF finite_biv_support]]) (use all_equal in blast)
   show False using face small by (simp add: in_direction_def)
 qed
 have distinct: "(n*r,n*t)\<noteq>(n*u,n*v)" using less n by auto
 have large: "1<card(biv_support(leading_form (int rho) (-int s) Q))"
 proof (rule ccontr)
   assume "\<not>1<card(biv_support(leading_form (int rho) (-int s) Q))"
   then have small: "card(biv_support(leading_form (int rho) (-int s) Q))\<le>Suc 0" by arith
   have same: "\<forall>a\<in>biv_support(leading_form (int rho) (-int s) Q).
     \<forall>b\<in>biv_support(leading_form (int rho) (-int s) Q). a=b"
     by (rule iffD1[OF card_le_Suc0_iff_eq[where A="biv_support(leading_form (int rho) (-int s) Q)", OF finite_biv_support] small])
   show False using same Qstart Qend distinct by blast
 qed
 show ?thesis by (simp only: in_direction_def; rule large)
qed

lemma counterexample_strict_negative_InDir_mate:
 fixes P Q::"complex poly_operator" and rho sigma::int
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma" and sigma: "sigma<0"
   and face: "in_direction rho sigma P"
 shows "in_direction rho sigma Q"
proof -
 have rho: "0<rho" using direction sigma by (simp add: is_direction_def; arith)
 have r: "int(nat rho)=rho" using rho by simp
 have s: "int(nat(-sigma))=-sigma" using sigma by simp
 have sp: "0<nat(-sigma)" using sigma by simp
 show ?thesis using counterexample_negative_face_direction_of_first[where rho="nat rho" and s="nat(-sigma)", OF pair sp]
   direction face by (simp only: r s minus_minus)
qed

lemma leadingForm_support_neg_A1:
 fixes P::"complex poly_operator"
 assumes P: "P\<in>weyl_algebra"
 shows "biv_support(leading_form rho sigma (-P))=biv_support(leading_form rho sigma P)"
proof -
 have symbol: "pbw_symbol(-P)=-pbw_symbol P" using weyl_symbol_sub[of 0 P] P by (simp add: weyl_algebra_def)
 have support: "biv_support(pbw_symbol(-P))=biv_support(pbw_symbol P)"
   by (simp add: symbol biv_support_def biv_coeff_def)
 have degree: "v_degree rho sigma (-P)=v_degree rho sigma P"
   by (simp add: v_degree_def weighted_degree_def support)
 show ?thesis by (simp add: leading_form_def weighted_component_support support degree)
qed

lemma counterexample_strict_negative_InDir_iff:
 fixes P Q::"complex poly_operator" and rho sigma::int
 assumes pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma" and sigma: "sigma<0"
 shows "in_direction rho sigma P \<longleftrightarrow> in_direction rho sigma Q"
proof
 assume face: "in_direction rho sigma P"
 show "in_direction rho sigma Q" by (rule counterexample_strict_negative_InDir_mate[OF pair direction sigma face])
next
 assume face: "in_direction rho sigma Q"
 have swap: "is_counterexample_pair Q (-P)" by (rule isCounterexamplePair_swap_neg[OF pair])
 have mapped: "in_direction rho sigma (-P)" by (rule counterexample_strict_negative_InDir_mate[OF swap direction sigma face])
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 show "in_direction rho sigma P" using mapped by (simp only: in_direction_def leadingForm_support_neg_A1[OF P])
qed

lemma counterexample_strict_negative_direction_sets_eq:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q"
 shows "{v::int\<times>int. is_direction (fst v)(snd v) \<and> 0<fst v \<and> snd v<0 \<and> in_direction (fst v)(snd v) P}=
   {v::int\<times>int. is_direction (fst v)(snd v) \<and> 0<fst v \<and> snd v<0 \<and> in_direction (fst v)(snd v) Q}"
proof (rule Set.set_eqI)
 fix v
 show "v\<in>{v. is_direction (fst v)(snd v) \<and> 0<fst v \<and> snd v<0 \<and> in_direction (fst v)(snd v) P} \<longleftrightarrow>
   v\<in>{v. is_direction (fst v)(snd v) \<and> 0<fst v \<and> snd v<0 \<and> in_direction (fst v)(snd v) Q}"
 proof (cases "is_direction (fst v)(snd v) \<and> snd v<0")
  case True
  then have direction: "is_direction (fst v)(snd v)" and sigma: "snd v<0" by auto
  have equivalent: "in_direction (fst v)(snd v) P\<longleftrightarrow>in_direction (fst v)(snd v) Q"
    by (rule counterexample_strict_negative_InDir_iff[OF pair direction sigma])
  show ?thesis by (simp only: mem_Collect_eq equivalent)
 next
  case False then show ?thesis by auto
 qed
qed

lemma ggv_ordered_negative_slopes_eq:
 fixes P Q::"complex poly_operator"
 assumes pair: "is_counterexample_pair P Q"
 shows "ggv_ordered_negative_face_slopes P=ggv_ordered_negative_face_slopes Q"
proof -
 have directions: "ggv_negative_primitive_directions P=ggv_negative_primitive_directions Q"
   unfolding ggv_negative_primitive_directions_def by (rule counterexample_strict_negative_direction_sets_eq[OF pair])
 show ?thesis by (simp only: ggv_ordered_negative_face_slopes_def ggv_negative_primitive_slopes_def directions)
qed
end
