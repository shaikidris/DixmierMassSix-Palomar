theory Finite_Face_Slopes
 imports Face_Order_Geometry
begin

definition ggv_face_candidate_slopes::"complex poly_operator \<Rightarrow> rat set" where
 "ggv_face_candidate_slopes P=(\<lambda>(d,e). (of_nat(fst e)-of_nat(fst d))/(of_nat(snd d)-of_nat(snd e))) `
   (biv_support(pbw_symbol P) \<times> biv_support(pbw_symbol P))"

lemma ggv_face_slope_mem_candidates:
 fixes P::"complex poly_operator" and rho sigma::int
 assumes rho: "rho\<noteq>0" and face: "in_direction rho sigma P"
 shows "(of_int sigma/of_int rho::rat)\<in>ggv_face_candidate_slopes P"
proof -
 have two: "1<card(biv_support(leading_form rho sigma P))" using face by (simp only: in_direction_def)
 have distinct: "\<exists>d\<in>biv_support(leading_form rho sigma P). \<exists>e\<in>biv_support(leading_form rho sigma P). d\<noteq>e"
 proof (rule ccontr)
   assume no: "\<not>(\<exists>d\<in>biv_support(leading_form rho sigma P). \<exists>e\<in>biv_support(leading_form rho sigma P). d\<noteq>e)"
   have bound: "card(biv_support(leading_form rho sigma P))\<le>Suc 0"
     by (rule iffD2[OF card_le_Suc0_iff_eq[OF finite_biv_support]]) (use no in blast)
   have "card(biv_support(leading_form rho sigma P))\<le>1" using bound by simp
   then show False using two by arith
 qed
 obtain d e where d: "d\<in>biv_support(leading_form rho sigma P)" and e: "e\<in>biv_support(leading_form rho sigma P)" and de: "d\<noteq>e" using distinct by blast
 have draw: "d\<in>biv_support(pbw_symbol P)" and eraw: "e\<in>biv_support(pbw_symbol P)"
   and weight: "pair_weight rho sigma d=pair_weight rho sigma e"
   using d e by (auto simp: leading_form_def weighted_component_support)
 have y: "snd d\<noteq>snd e"
 proof
   assume same: "snd d=snd e"
   have product: "rho*(int(fst d)-int(fst e))=0"
     using weight same by (simp add: pair_weight_def algebra_simps)
   have x: "fst d=fst e" using product rho by auto
   show False using de x same by (simp add: prod_eq_iff)
 qed
 have den: "(of_nat(snd d)-of_nat(snd e)::rat)\<noteq>0" using y by simp
 have rn: "(of_int rho::rat)\<noteq>0" using rho by simp
 have integral: "rho*(int(fst d)-int(fst e))+sigma*(int(snd d)-int(snd e))=0"
   using weight by (simp add: pair_weight_def algebra_simps)
 have cast: "(of_int(rho*(int(fst d)-int(fst e))+sigma*(int(snd d)-int(snd e)))::rat)=0"
   using integral by simp
 have rational: "(of_int rho::rat)*(of_nat(fst d)-of_nat(fst e))+of_int sigma*(of_nat(snd d)-of_nat(snd e))=0"
   using cast by simp
 have ratio: "(of_nat(fst e)-of_nat(fst d))/(of_nat(snd d)-of_nat(snd e))=(of_int sigma/of_int rho::rat)"
   using rational den rn by (simp add: field_simps algebra_simps; linarith)
 have member: "(d,e)\<in>biv_support(pbw_symbol P)\<times>biv_support(pbw_symbol P)" using draw eraw by simp
 have image: "(\<lambda>(d,e). (of_nat(fst e)-of_nat(fst d))/(of_nat(snd d)-of_nat(snd e))) (d,e)\<in>ggv_face_candidate_slopes P"
   unfolding ggv_face_candidate_slopes_def by (rule imageI[OF member])
 show ?thesis using image ratio by simp
qed

lemma ggv_negative_face_slopes_finite:
 fixes P::"complex poly_operator"
 shows "finite {t::rat. \<exists>rho sigma::int. 0<rho \<and> sigma<0 \<and> in_direction rho sigma P \<and> t=of_int sigma/of_int rho}"
proof -
 have finite: "finite(ggv_face_candidate_slopes P)" by (simp add: ggv_face_candidate_slopes_def)
 have subset: "{t::rat. \<exists>rho sigma::int. 0<rho \<and> sigma<0 \<and> in_direction rho sigma P \<and> t=of_int sigma/of_int rho}\<subseteq>ggv_face_candidate_slopes P"
   using ggv_face_slope_mem_candidates by auto
 show ?thesis by (rule finite_subset[OF subset finite])
qed

lemma ggv_primitive_negative_normal_unique:
 fixes rho sigma rho' sigma'::int
 assumes direction: "is_direction rho sigma" and direction': "is_direction rho' sigma'"
   and rho: "0<rho" and rho': "0<rho'"
   and slope: "(of_int sigma/of_int rho::rat)=of_int sigma'/of_int rho'"
 shows "rho=rho' \<and> sigma=sigma'"
proof -
 have rn: "(of_int rho::rat)\<noteq>0" and rn': "(of_int rho'::rat)\<noteq>0" using rho rho' by simp_all
 have cross_rat: "(of_int sigma*of_int rho'::rat)=of_int sigma'*of_int rho"
   using slope rn rn' by (simp add: field_simps)
 have cross: "sigma*rho'=sigma'*rho" using cross_rat by (simp only: of_int_mult[symmetric] of_int_eq_iff)
 have primitive: "coprime rho sigma"
 proof -
  have natural_gcd: "gcd(nat(abs rho))(nat(abs sigma))=1"
   using direction unfolding is_direction_def by blast
  have integer_gcd: "gcd rho sigma=1" using natural_gcd by (simp only: gcd_int_def; simp)
  show ?thesis using integer_gcd by (simp only: coprime_iff_gcd_eq_1)
 qed
 have primitive': "coprime rho' sigma'"
 proof -
  have natural_gcd: "gcd(nat(abs rho'))(nat(abs sigma'))=1"
   using direction' unfolding is_direction_def by blast
  have integer_gcd: "gcd rho' sigma'=1" using natural_gcd by (simp only: gcd_int_def; simp)
  show ?thesis using integer_gcd by (simp only: coprime_iff_gcd_eq_1)
 qed
 have mult_div: "rho dvd sigma*rho'" by (simp only: cross; rule dvd_triv_right)
 have mult_div': "rho' dvd sigma'*rho" by (simp only: cross[symmetric]; rule dvd_triv_right)
 have divides: "rho dvd rho'" using mult_div primitive by (simp add: coprime_dvd_mult_right_iff)
 have divides': "rho' dvd rho" using mult_div' primitive' by (simp add: coprime_dvd_mult_right_iff)
 have first: "rho=rho'" by (rule zdvd_antisym_nonneg[OF less_imp_le[OF rho] less_imp_le[OF rho'] divides divides'])
 have second: "sigma=sigma'" using cross first rho' by simp
 show ?thesis using first second by blast
qed

lemma ggv_negative_primitive_face_directions_finite:
 fixes P::"complex poly_operator"
 shows "finite {v::int\<times>int. is_direction (fst v)(snd v) \<and> 0<fst v \<and> snd v<0 \<and> in_direction (fst v)(snd v) P}"
proof -
 let ?S="{v::int\<times>int. is_direction (fst v)(snd v) \<and> 0<fst v \<and> snd v<0 \<and> in_direction (fst v)(snd v) P}"
 let ?slope="\<lambda>v::int\<times>int. (of_int(snd v)/of_int(fst v)::rat)"
 have subset: "?slope ` ?S\<subseteq>{t::rat. \<exists>rho sigma::int. 0<rho \<and> sigma<0 \<and> in_direction rho sigma P \<and> t=of_int sigma/of_int rho}" by auto
 have image: "finite(?slope ` ?S)" by (rule finite_subset[OF subset ggv_negative_face_slopes_finite])
 have injective: "inj_on ?slope ?S"
 proof (rule inj_onI)
   fix v w assume v: "v\<in>?S" and w: "w\<in>?S" and eq: "?slope v=?slope w"
   have direction: "is_direction (fst v)(snd v)" and direction': "is_direction (fst w)(snd w)"
     and rho: "0<fst v" and rho': "0<fst w" using v w by auto
   have "fst v=fst w \<and> snd v=snd w"
     by (rule ggv_primitive_negative_normal_unique[OF direction direction' rho rho' eq])
   then show "v=w" by (simp add: prod_eq_iff)
 qed
 show ?thesis using image by (simp only: finite_image_iff[OF injective])
qed
end
