theory Crossing_Face_Endpoints
 imports "Horizontal_Prime_Terminal"
  "Homogeneous_Power_Endpoints"
begin

lemma crossing_biv_coeff_one [simp]:
 "biv_coeff (1::'a::field bivariate) i j=(if i=0 \<and> j=0 then 1 else 0)"
 by (simp add: biv_coeff_def coeff_1 split: if_splits)

lemma crossing_biv_coeff_monom_left_mult:
 "biv_coeff (biv_monom c e 0*H) (e+i) j=c*biv_coeff H i j"
 by (simp add: biv_coeff_def biv_monom_def coeff_monom_mult smult_monom)

lemma crossing_primitive_base_binomial_form:
 "crossing_primitive_base alpha q rho s=biv_monom 1 1 0*(1+biv_monom alpha s rho)^q"
proof -
 have X: "([:[:0,1:]:]::complex bivariate)=biv_monom 1 1 0"
   by (simp add: biv_monom_def monom_0 monom_altdef)
 have Y: "([:0,1:]::complex bivariate)=biv_monom 1 0 1"
   by (simp add: biv_monom_def monom_0 monom_altdef one_pCons)
 have scalar: "([:[:alpha:]:]::complex bivariate)=biv_monom alpha 0 0"
   by (simp add: biv_monom_def monom_0)
 show ?thesis by (simp only: crossing_primitive_base_def X Y scalar corner_biv_monom_power; simp add: biv_monom_def mult_monom monom_0 smult_monom)
qed

lemma crossing_power_face_binomial_form:
 "([:[:nu:]:]::complex bivariate)*(crossing_primitive_base alpha q rho s)^e=
   biv_monom nu e 0*(1+biv_monom alpha s rho)^(q*e)"
 by (simp only: crossing_primitive_base_binomial_form power_mult_distrib
   corner_biv_monom_power power_mult[symmetric]; simp add: biv_monom_def monom_0 mult_monom smult_monom)

lemma crossing_binomial_top_point:
 assumes alpha: "alpha\<noteq>0" and rho: "0<rho"
 shows "(s,rho)\<in>biv_support(1+biv_monom alpha s rho)"
proof -
 have one: "(1::complex bivariate)=biv_monom 1 0 0"
   by (simp add: biv_monom_def monom_0 one_pCons)
 show ?thesis using alpha rho by (simp add: biv_support_def crossing_biv_coeff_one)
qed

lemma crossing_binomial_support_bound:
 "biv_support(1+biv_monom alpha s rho)\<subseteq>{(0,0),(s,rho)}"
proof -
 have one: "(1::complex bivariate)=biv_monom 1 0 0"
   by (simp add: biv_monom_def monom_0 one_pCons)
 show ?thesis by (auto simp: biv_support_def crossing_biv_coeff_one split: if_splits)
qed

lemma crossing_power_ending_support:
 fixes F::"complex bivariate"
 assumes alpha: "alpha\<noteq>0" and nu: "nu\<noteq>0" and rho: "0<rho"
 and face: "F=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^e"
 shows "(e+s*(q*e),rho*q*e)\<in>biv_support F"
proof -
 let ?H="1+biv_monom alpha s rho"
 have point: "(s,rho)\<in>biv_support ?H" by (rule crossing_binomial_top_point[OF alpha rho])
 have bound: "\<And>u. u\<in>biv_support ?H \<Longrightarrow>pair_weight 0 1 u\<le>pair_weight 0 1 (s,rho)"
   using crossing_binomial_support_bound[where alpha=alpha and s=s and rho=rho]
   by (auto simp: pair_weight_def)
 have unique: "\<And>u. u\<in>biv_support ?H \<Longrightarrow>pair_weight 0 1 u=pair_weight 0 1 (s,rho) \<Longrightarrow>u=(s,rho)"
   using crossing_binomial_support_bound[where alpha=alpha and s=s and rho=rho] rho
   by (auto simp: pair_weight_def)
 have occupied: "((q*e)*s,(q*e)*rho)\<in>biv_support(?H^(q*e))"
   using corner_unique_top_power_endpoint[where R="?H" and d="(s,rho)" and rho=0 and sigma=1 and m="q*e", OF point bound unique]
   by (simp only: fst_conv snd_conv)
 have coefficient: "biv_coeff(?H^(q*e)) ((q*e)*s) ((q*e)*rho)\<noteq>0"
   using occupied by (simp add: biv_support_def)
 have shifted: "biv_coeff (biv_monom nu e 0*?H^(q*e)) (e+(q*e)*s) ((q*e)*rho)\<noteq>0"
   using coefficient nu by (simp add: biv_coeff_def biv_monom_def coeff_monom_mult)
 have form: "F=biv_monom nu e 0*?H^(q*e)"
   using face by (simp only: crossing_power_face_binomial_form)
 show ?thesis using shifted by (simp only: form biv_support_def mem_Collect_eq fst_conv snd_conv mult.assoc mult.left_commute mult.commute not_False_eq_True)
qed

lemma crossing_power_starting_support:
 fixes F::"complex bivariate"
 assumes nu: "nu\<noteq>0" and rho: "0<rho"
 and face: "F=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^e"
 shows "(e,0)\<in>biv_support F"
proof -
 let ?H="1+biv_monom alpha s rho"
 have coeff0: "coeff ?H 0=1" using rho by (simp add: biv_monom_def)
 have form: "F=biv_monom nu e 0*?H^(q*e)"
   using face by (simp only: crossing_power_face_binomial_form)
 have power_coeff: "biv_coeff(?H^(q*e)) 0 0=1"
   by (simp only: biv_coeff_def coeff_0_power coeff0; simp)
 have coefficient: "biv_coeff F e 0=nu"
   using crossing_biv_coeff_monom_left_mult[where c=nu and e=e and H="?H^(q*e)" and i=0 and j=0]
   by (simp only: form add_0_right power_coeff mult_1_right)
 show ?thesis using coefficient nu by (simp add: biv_support_def)
qed

lemma crossingFace_starting_point:
 fixes T::"complex poly_operator" and q rho s e::nat
 assumes T: "T\<in>weyl_algebra" and nu: "nu\<noteq>0" and s: "0<s" and sr: "s<rho" and e: "0<e"
 and face: "leading_form (int rho) (-int s) T=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^e"
 shows "(e,0)\<in>biv_support(leading_form (int rho) (-int s) T) \<and>
   (\<forall>u\<in>biv_support(leading_form (int rho) (-int s) T). pair_grade u\<le>pair_grade(e,0))"
proof -
 have rho: "0<rho" using sr by arith
 have point: "(e,0)\<in>biv_support(leading_form (int rho) (-int s) T)"
   by (rule crossing_power_starting_support[OF nu rho face])
 have old: "v_degree (int rho) (-int s) T=int rho*int e"
   using weight_of_mem_leadingForm[OF T point] by (simp add: pair_weight_def mult.commute)
 have bounds: "pair_grade u\<le>pair_grade(e,0)" if member: "u\<in>biv_support(leading_form (int rho) (-int s) T)" for u
 proof -
   have weight: "int rho*int(fst u)-int s*int(snd u)=int rho*int e"
     using weight_of_mem_leadingForm[OF T member] by (simp add: old pair_weight_def mult.commute)
   have identity: "int rho*(pair_grade u-int e)=-(int rho-int s)*int(snd u)"
     using weight by (simp add: pair_grade_def algebra_simps; arith)
   have factor: "-(int rho-int s)\<le>0" using sr by simp
   have y_nonnegative: "0\<le>int(snd u)" by simp
   have sign: "-(int rho-int s)*int(snd u)\<le>0"
     by (rule mult_nonpos_nonneg[OF factor y_nonnegative])
   have product: "int rho*(pair_grade u-int e)\<le>0"
     by (simp only: identity; rule sign)
   have nonpos: "pair_grade u-int e\<le>0"
     using product rho by (simp only: mult_le_0_iff; simp; arith)
   show ?thesis using nonpos by (simp add: pair_grade_def)
 qed
 show ?thesis using point bounds by blast
qed

lemma crossingFace_ending_endpoint:
 fixes F::"complex bivariate" and q rho s e::nat
 assumes alpha: "alpha\<noteq>0" and nu: "nu\<noteq>0" and q: "2\<le>q" and s: "0<s" and e: "0<e"
 and parameter: "(q-1)*rho=q*s+1"
 and face: "F=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^e"
 shows "(e+s*(q*e),rho*q*e)\<in>biv_support F \<and>
   pair_grade(e+s*(q*e),rho*q*e)=-(int e*int rho)"
proof -
 have rho: "0<rho" by (rule purePower_rho_pos[OF q parameter])
 have point: "(e+s*(q*e),rho*q*e)\<in>biv_support F" by (rule crossing_power_ending_support[OF alpha nu rho face])
 have identity: "int q*(int rho-int s)=int rho+1" by (rule purePower_weight_identity[OF q parameter])
 have scaled: "int e*(int q*(int rho-int s))=int e*(int rho+1)" by (rule arg_cong[OF identity])
 have grade: "pair_grade(e+s*(q*e),rho*q*e)=-(int e*int rho)"
   unfolding pair_grade_def using scaled by (simp add: algebra_simps; arith)
 show ?thesis by (intro conjI) (rule point grade)+
qed


lemma crossing_power_support_weight_bound:
 fixes F::"complex bivariate" and r t D::int
 assumes face: "F=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^e"
 and bound: "\<And>u. u\<in>biv_support(1+biv_monom alpha s rho) \<Longrightarrow> pair_weight r t u\<le>D"
 and member: "u\<in>biv_support F"
 shows "pair_weight r t u\<le>r*int e+int(q*e)*D"
proof -
 have monomial: "\<And>v. v\<in>biv_support(biv_monom nu e 0) \<Longrightarrow>pair_weight r t v\<le>r*int e"
   by (auto simp: biv_support_def pair_weight_def mult.commute split: if_splits)
 have powers: "\<And>v. v\<in>biv_support((1+biv_monom alpha s rho)^(q*e)) \<Longrightarrow>pair_weight r t v\<le>int(q*e)*D"
   by (rule corner_support_weight_power[OF bound])
 have product: "u\<in>biv_support(biv_monom nu e 0*(1+biv_monom alpha s rho)^(q*e))"
   using member by (simp only: face crossing_power_face_binomial_form)
 show ?thesis by (rule biv_support_weight_product[OF monomial powers product])
qed

lemma horizontalFace_ending_endpoint:
 fixes F::"complex bivariate" and e::nat
 assumes alpha: "alpha\<noteq>0" and nu: "nu\<noteq>0" and e: "0<e"
 and face: "F=[:[:nu:]:]*(crossing_primitive_base alpha 2 1 0)^e"
 shows "(e,2*e)\<in>biv_support F \<and> (\<forall>u\<in>biv_support F. pair_grade(e,2*e)\<le>pair_grade u)"
proof -
 have endpoint: "(e,2*e)\<in>biv_support F"
   using crossing_power_ending_support[where q=2 and rho=1 and s=0, OF alpha nu _ face] by simp
 have bounds: "pair_grade(e,2*e)\<le>pair_grade u" if member: "u\<in>biv_support F" for u
 proof -
   have bx: "\<And>v. v\<in>biv_support(1+biv_monom alpha 0 1) \<Longrightarrow>pair_weight 1 0 v\<le>0"
     using crossing_binomial_support_bound[where alpha=alpha and s=0 and rho=1] by (auto simp: pair_weight_def)
   have bnx: "\<And>v. v\<in>biv_support(1+biv_monom alpha 0 1) \<Longrightarrow>pair_weight (-1) 0 v\<le>0"
     using crossing_binomial_support_bound[where alpha=alpha and s=0 and rho=1] by (auto simp: pair_weight_def)
   have ybound: "\<And>v. v\<in>biv_support(1+biv_monom alpha 0 1) \<Longrightarrow>pair_weight 0 1 v\<le>1"
     using crossing_binomial_support_bound[where alpha=alpha and s=0 and rho=1] by (auto simp: pair_weight_def)
   have x: "int(fst u)\<le>int e" using crossing_power_support_weight_bound[OF face bx member] by (simp add: pair_weight_def)
   have nx: "-int(fst u)\<le>-int e" using crossing_power_support_weight_bound[OF face bnx member] by (simp add: pair_weight_def)
   have y: "int(snd u)\<le>2*int e" using crossing_power_support_weight_bound[OF face ybound member] by (simp add: pair_weight_def)
   show ?thesis unfolding pair_grade_def using x nx y by (simp; arith)
 qed
 show ?thesis using endpoint bounds by blast
qed

lemma horizontalFace_support_two:
 fixes F::"complex bivariate" and e::nat
 assumes alpha: "alpha\<noteq>0" and nu: "nu\<noteq>0" and e: "0<e"
 and face: "F=[:[:nu:]:]*(crossing_primitive_base alpha 2 1 0)^e"
 shows "1<card(biv_support F)"
proof -
 have start: "(e,0)\<in>biv_support F" by (rule crossing_power_starting_support[OF nu _ face]) simp
 have finish: "(e,2*e)\<in>biv_support F" using horizontalFace_ending_endpoint[OF alpha nu e face] by blast
 have subset: "{(e,0),(e,2*e)}\<subseteq>biv_support F" using start finish by auto
 have cardinal: "card {(e,0),(e,2*e)}\<le>card(biv_support F)" by (rule card_mono[OF finite_biv_support subset])
 show ?thesis using cardinal e by simp
qed

lemma crossing_power_strict_endpoints:
 fixes F::"complex bivariate" and q rho s e::nat
 assumes alpha: "alpha\<noteq>0" and nu: "nu\<noteq>0" and s: "0<s"
 and face: "F=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^e"
 shows "(e,0)\<in>biv_support F \<and> (e+s*(q*e),rho*q*e)\<in>biv_support F"
proof -
 let ?H="1+biv_monom alpha s rho"
 have one_coeff: "biv_coeff (1::complex bivariate) 0 0=1" by (simp add: biv_coeff_def)
 have monomial_zero: "biv_coeff (biv_monom alpha s rho) 0 0=0"
   using s by (simp only: biv_coeff_monom; simp)
 have start0: "biv_coeff ?H 0 0=1"
   by (simp only: biv_coeff_add one_coeff monomial_zero add_0_right)
 have power_coeff: "biv_coeff(?H^(q*e)) 0 0=(biv_coeff ?H 0 0)^(q*e)"
   by (simp only: biv_coeff_def coeff_0_power)
 have startpow: "biv_coeff(?H^(q*e)) 0 0=1"
   by (simp only: power_coeff start0 power_one)
 have form: "F=biv_monom nu e 0*?H^(q*e)"
   using face by (simp only: crossing_power_face_binomial_form)
 have start_coeff: "biv_coeff F e 0=nu"
   using crossing_biv_coeff_monom_left_mult[where c=nu and e=e and H="?H^(q*e)" and i=0 and j=0]
   by (simp only: form add_0_right startpow mult_1_right)
 have start: "(e,0)\<in>biv_support F"
   using start_coeff nu by (simp only: biv_support_def mem_Collect_eq fst_conv snd_conv; simp)
 have one_top_zero: "biv_coeff (1::complex bivariate) s rho=0"
   using s by (simp add: biv_coeff_def)
 have top_coeff: "biv_coeff ?H s rho=alpha"
   by (simp only: biv_coeff_add one_top_zero biv_coeff_monom; simp)
 have top: "(s,rho)\<in>biv_support ?H"
   using top_coeff alpha by (simp only: biv_support_def mem_Collect_eq fst_conv snd_conv; simp)
 have bound: "\<And>u. u\<in>biv_support ?H \<Longrightarrow>pair_weight 1 0 u\<le>pair_weight 1 0 (s,rho)"
   using crossing_binomial_support_bound[where alpha=alpha and s=s and rho=rho] by (auto simp: pair_weight_def)
 have unique: "\<And>u. u\<in>biv_support ?H \<Longrightarrow>pair_weight 1 0 u=pair_weight 1 0 (s,rho) \<Longrightarrow>u=(s,rho)"
   using crossing_binomial_support_bound[where alpha=alpha and s=s and rho=rho] s by (auto simp: pair_weight_def)
 have occupied: "((q*e)*s,(q*e)*rho)\<in>biv_support(?H^(q*e))"
   using corner_unique_top_power_endpoint[where R="?H" and d="(s,rho)" and rho=1 and sigma=0 and m="q*e", OF top bound unique]
   by (simp only: fst_conv snd_conv)
 have nonzero: "biv_coeff(?H^(q*e)) ((q*e)*s) ((q*e)*rho)\<noteq>0" using occupied by (simp add: biv_support_def)
 have finish_coeff: "biv_coeff F (e+(q*e)*s) ((q*e)*rho)\<noteq>0"
   using nonzero nu by (simp only: form crossing_biv_coeff_monom_left_mult mult_eq_0_iff; simp)
 have finish: "(e+s*(q*e),rho*q*e)\<in>biv_support F"
   using finish_coeff by (simp only: biv_support_def mem_Collect_eq fst_conv snd_conv mult.assoc mult.left_commute mult.commute not_False_eq_True)
 show ?thesis using start finish by blast
qed

lemma crossingFace_support_two:
 fixes F::"complex bivariate" and q rho s e::nat
 assumes alpha: "alpha\<noteq>0" and nu: "nu\<noteq>0" and q: "0<q" and s: "0<s" and e: "0<e"
 and face: "F=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^e"
 shows "1<card(biv_support F)"
proof -
 have points: "(e,0)\<in>biv_support F" "(e+s*(q*e),rho*q*e)\<in>biv_support F"
   using crossing_power_strict_endpoints[OF alpha nu s face] by blast+
 have subset: "{(e,0),(e+s*(q*e),rho*q*e)}\<subseteq>biv_support F" using points by auto
 have distinct: "(e,0)\<noteq>(e+s*(q*e),rho*q*e)" using q s e by simp
 have cardinal: "card {(e,0),(e+s*(q*e),rho*q*e)}\<le>card(biv_support F)" by (rule card_mono[OF finite_biv_support subset])
 show ?thesis using cardinal distinct by simp
qed

lemma crossingFace_inDir:
 fixes T::"complex poly_operator" and q rho s e::nat
 assumes alpha: "alpha\<noteq>0" and nu: "nu\<noteq>0" and q: "0<q" and s: "0<s" and e: "0<e"
 and face: "leading_form (int rho) (-int s) T=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^e"
 shows "in_direction (int rho) (-int s) T"
 unfolding in_direction_def by (rule crossingFace_support_two[OF alpha nu q s e face])

lemma crossingPair_commonDirection:
 fixes P Q::"complex poly_operator" and p q j rho s::nat
 assumes alpha: "alpha\<noteq>0" and mu: "mu\<noteq>0" and nu: "nu\<noteq>0"
 and p: "0<p" and q: "0<q" and j: "0<j" and s: "0<s"
 and Pface: "leading_form (int rho) (-int s) P=[:[:mu:]:]*(crossing_primitive_base alpha q rho s)^p"
 and Qface: "leading_form (int rho) (-int s) Q=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^j"
 shows "in_direction (int rho) (-int s) P \<and> in_direction (int rho) (-int s) Q"
 using crossingFace_inDir[OF alpha mu q s p Pface] crossingFace_inDir[OF alpha nu q s j Qface] by blast

end
