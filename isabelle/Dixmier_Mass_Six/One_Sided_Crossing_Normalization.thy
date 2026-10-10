theory One_Sided_Crossing_Normalization
 imports "Strict_Crossing_Exclusion"
   "Horizontal_Crossing_Exclusion"
   "One_Sided_Generator_Extraction"
   "HOL.GCD"
begin

lemma global_leading_support_positive_scale:
 fixes T::"complex poly_operator" and c rho sigma::int
 assumes c: "0<c"
 shows "biv_support(leading_form (c*rho) (c*sigma) T)=biv_support(leading_form rho sigma T)"
proof (cases "biv_support(pbw_symbol T)={}")
 case True
 then show ?thesis by (simp add: leading_form_def weighted_component_support)
next
 case False
 have scaled: "pair_weight (c*rho) (c*sigma) u=c*pair_weight rho sigma u" for u
   by (simp add: pair_weight_def algebra_simps)
 have maximal: "u\<in>biv_support(leading_form r s T) \<longleftrightarrow>
   u\<in>biv_support(pbw_symbol T) \<and> (\<forall>v\<in>biv_support(pbw_symbol T). pair_weight r s v\<le>pair_weight r s u)" for r s u
 proof
   assume member: "u\<in>biv_support(leading_form r s T)"
   have full: "u\<in>biv_support(pbw_symbol T)" and weight: "pair_weight r s u=v_degree r s T"
     using member by (simp_all add: leading_form_def weighted_component_support)
   have bound: "pair_weight r s v\<le>pair_weight r s u" if "v\<in>biv_support(pbw_symbol T)" for v
     using symbol_weight_le_v_degree[where rho=r and sigma=s, OF that]
     by (simp only: weight)
   show "u\<in>biv_support(pbw_symbol T) \<and> (\<forall>v\<in>biv_support(pbw_symbol T). pair_weight r s v\<le>pair_weight r s u)"
     using full bound by auto
 next
   assume "u\<in>biv_support(pbw_symbol T) \<and> (\<forall>v\<in>biv_support(pbw_symbol T). pair_weight r s v\<le>pair_weight r s u)"
   then show "u\<in>biv_support(leading_form r s T)" by (intro symbol_maximizer_mem_leading_form) auto
 qed
 show ?thesis by (rule set_eqI) (simp only: maximal scaled mult_le_cancel_left_pos[OF c])
qed

lemma crossing_pair_coprime_nat_normal:
 fixes P Q::"complex poly_operator" and rho sigma::int
 assumes rho: "0<rho" and sigma: "sigma\<le>0" and sum: "0<rho+sigma"
 shows "\<exists>ell d::nat. 0<ell \<and> d<ell \<and> coprime ell d \<and>
 biv_support(leading_form rho sigma P)=biv_support(leading_form (int ell) (-int d) P) \<and>
 biv_support(leading_form rho sigma Q)=biv_support(leading_form (int ell) (-int d) Q)"
proof -
 let ?a="nat rho" let ?b="nat(-sigma)" let ?g="gcd ?a ?b"
 have a: "int ?a=rho" and b: "int ?b= -sigma" using rho sigma by simp_all
 have ap: "0<?a" using rho by simp
 have bp: "?b<?a" using sum a b by arith
 have gp: "0<?g" using ap by simp
 let ?ell="?a div ?g" let ?d="?b div ?g"
 have aa: "?g*?ell=?a" by (simp add: dvd_mult_div_cancel gcd_dvd1)
 have bb: "?g*?d=?b" by (simp add: dvd_mult_div_cancel gcd_dvd2)
 have ell: "0<?ell" using aa ap by (cases "?ell=0") auto
 have products: "?g*?d<?g*?ell" using bp by (simp only: aa bb)
 have cancelled: "0<?g \<and> ?d<?ell" using products by (simp only: mult_less_cancel1)
 have d: "?d<?ell" by (rule conjunct2[OF cancelled])
 have coprime: "coprime ?ell ?d" by (rule div_gcd_coprime) (use ap in auto)
 have r: "int ?g*int ?ell=rho" using aa a by (metis of_nat_mult)
 have sb: "int ?g*int ?d= -sigma" using bb b by (metis of_nat_mult)
 have s: "int ?g*(-int ?d)=sigma" using sb by (simp add: mult_minus_right)
 have gc: "0<int ?g" using gp by simp
 have faces: "biv_support(leading_form rho sigma T)=biv_support(leading_form (int ?ell) (-int ?d) T)" for T::"complex poly_operator"
   using global_leading_support_positive_scale[OF gc, where rho="int ?ell" and sigma="-int ?d" and T=T]
   by (simp only: r s)
 show ?thesis using ell d coprime faces[of P] faces[of Q] by blast
qed

lemma crossing_pair_bracket_one_impossible:
 fixes P Q::"complex poly_operator" and rho sigma::int
 assumes rho: "0<rho" and sigma: "sigma\<le>0" and sum: "0<rho+sigma"
 and gen: "(0,1)\<in>biv_support(leading_form rho sigma P)"
 and scalar: "biv_coeff(leading_form rho sigma P) 0 0=0"
 and nonmonomial: "1<card(biv_support(leading_form rho sigma P))"
 and bracket: "biv_poisson (leading_form rho sigma Q) (leading_form rho sigma P)=1"
 shows False
proof -
 obtain ell d where ell: "0<ell" and d: "d<ell" and coprime: "coprime ell d"
 and Ps: "biv_support(leading_form rho sigma P)=biv_support(leading_form (int ell) (-int d) P)"
 and Qs: "biv_support(leading_form rho sigma Q)=biv_support(leading_form (int ell) (-int d) Q)"
   using crossing_pair_coprime_nat_normal[where P=P and Q=Q, OF rho sigma sum] by auto
 have Pf: "leading_form rho sigma P=leading_form (int ell) (-int d) P"
   by (rule leading_form_eq_of_support_eq[OF Ps])
 have Qf: "leading_form rho sigma Q=leading_form (int ell) (-int d) Q"
   by (rule leading_form_eq_of_support_eq[OF Qs])
 let ?R="leading_form (int ell) (-int d) P"
 let ?F="-leading_form (int ell) (-int d) Q"
 have reverse: "biv_poisson ?R ?F=1" using bracket by (simp only: poisson_first_neg_second Pf Qf)
 have y: "(0,1)\<in>biv_support ?R" using gen by (simp only: Pf)
 have Pdeg: "v_degree (int ell) (-int d) P= -int d"
   by (rule leading_form_degree_of_y_term[OF y])
 have R_hom: "pair_weight (int ell) (-int d) u= -int d" if "u\<in>biv_support ?R" for u
   using that by (simp add: leading_form_def weighted_component_support Pdeg)
 have x: "(1,0)\<in>biv_support ?F"
   by (rule poisson_eq_one_forces_mate_position_term[OF ell _ reverse]) (use R_hom in blast)
 have xQ: "(1,0)\<in>biv_support(leading_form (int ell) (-int d) Q)"
   using x by (simp add: biv_support_def biv_coeff_def)
 have Qdeg: "v_degree (int ell) (-int d) Q=int ell"
   by (rule leading_form_degree_of_x_term[OF xQ])
 have F_hom: "pair_weight (int ell) (-int d) u=int ell" if "u\<in>biv_support ?F" for u
 proof -
   have raw: "u\<in>biv_support(leading_form (int ell) (-int d) Q)"
     using that by (simp add: biv_support_def biv_coeff_def)
   show ?thesis using raw by (simp add: leading_form_def weighted_component_support Qdeg)
 qed
 have card: "1<card(biv_support ?R)" using nonmonomial by (simp only: Pf)
 have scalarR: "biv_coeff ?R 0 0=0" using scalar by (simp only: Pf)
 show False
 proof (cases "d=0")
   case True
   have exclusion: "biv_poisson ?R ?F\<noteq>1"
     by (rule horizontal_nonmonomial_face_excludes_bracket_one[OF ell])
       (use coprime R_hom F_hom scalarR card True in auto)
   show False using reverse exclusion by contradiction
 next
   case False
   have dp: "0<d" using False by simp
   have exclusion: "biv_poisson ?R ?F\<noteq>1"
     by (rule strict_crossing_nonmonomial_face_excludes_bracket_one[OF dp d coprime R_hom F_hom card])
   show False using reverse exclusion by contradiction
 qed
qed
end
