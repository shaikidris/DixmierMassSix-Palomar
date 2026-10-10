theory Small_Scalar_Height
 imports "Small_Scalar_Reconstruction"
   "Crossing_Cut_Formula"
   "General_Root_Degree"
begin

lemma smallDegreeCrossing_root_degreeOf_Y:
 fixes P Q::"complex poly_operator"
 assumes data: "ggv_small_degree_crossing_data P Q H"
 shows "degree(ggv_root H)=ggv_v H"
proof -
 have s: "0<ggv_s H"
  and hom: "weighted_homogeneous(int(ggv_rho H))(-int(ggv_s H))(ggv_weight H)(ggv_root H)"
  and endpt: "(ggv_u H,ggv_v H)\<in>biv_support(ggv_root H)"
  and bound: "\<forall>e\<in>biv_support(ggv_root H). fst e\<le>ggv_u H"
  using data unfolding ggv_small_degree_crossing_data_def by blast+
 have ybound: "snd e\<le>ggv_v H" if e: "e\<in>biv_support(ggv_root H)" for e
 proof -
  have ew: "pair_weight(int(ggv_rho H))(-int(ggv_s H))e=ggv_weight H"
   by (rule bspec[OF hom[unfolded weighted_homogeneous_def] e])
  have cw: "pair_weight(int(ggv_rho H))(-int(ggv_s H))(ggv_u H,ggv_v H)=ggv_weight H"
   by (rule bspec[OF hom[unfolded weighted_homogeneous_def] endpt])
  have raw_e: "int(fst e)*int(ggv_rho H)-int(snd e)*int(ggv_s H)=ggv_weight H"
   using ew by (simp add: pair_weight_def)
  have raw_c: "int(ggv_u H)*int(ggv_rho H)-int(ggv_v H)*int(ggv_s H)=ggv_weight H"
   using cw by (simp add: pair_weight_def)
  have weight: "int(ggv_s H)*(int(snd e)-int(ggv_v H))=
   int(ggv_rho H)*(int(fst e)-int(ggv_u H))"
   using raw_e raw_c by (simp only: algebra_simps; linarith)
  have xbound: "fst e\<le>ggv_u H" by (rule bspec[OF bound e])
  have nonpositive: "int(ggv_rho H)*(int(fst e)-int(ggv_u H))\<le>0"
   by (rule mult_nonneg_nonpos) (use xbound in auto)
  show ?thesis
  proof (rule ccontr)
   assume "\<not>snd e\<le>ggv_v H"
   then have positive: "0<int(snd e)-int(ggv_v H)" by simp
   have product: "0<int(ggv_s H)*(int(snd e)-int(ggv_v H))"
    by (rule mult_pos_pos) (use s positive in auto)
   show False using weight product nonpositive by arith
  qed
 qed
 show ?thesis by (rule biv_degree_eq_of_occupied_max_y[OF endpt ybound])
qed

lemma smallDegreeCrossing_scalar_degree_eq_height:
 fixes P Q::"complex poly_operator"
 fixes c::complex and p::"complex poly"
 assumes data: "ggv_small_degree_crossing_data P Q H" and c: "c\<noteq>0" and p0: "coeff p 0=1"
   and shape: "ggv_root H=biv_monom c 0 0*(biv_monom 1 (ggv_r H)(ggv_t H)*biv_univariate_eval p (biv_monom 1 (ggv_s H)(ggv_rho H)))"
 shows "degree p=ggv_h H"
proof -
 have rho: "0<ggv_rho H"
  and hom: "weighted_homogeneous(int(ggv_rho H))(-int(ggv_s H))(ggv_weight H)(ggv_root H)"
  and height: "ggv_v H=ggv_t H+ggv_rho H*ggv_h H"
  using data unfolding ggv_small_degree_crossing_data_def by blast+
 have rp: "0<int(ggv_rho H)" using rho by simp
 have special_degree: "degree(map_poly (\<lambda>q. poly q 1)(ggv_root H))=ggv_v H"
  using homogeneous_specialization_natDegree_eq_degreeOf_Y[where F="ggv_root H", OF rp hom]
   smallDegreeCrossing_root_degreeOf_Y[OF data] by simp
 have mult: "map_poly (\<lambda>q. poly q 1) (F*G)=map_poly (\<lambda>q. poly q 1) F*map_poly (\<lambda>q. poly q 1) G" for F G::"complex bivariate"
  using cut_specialize_hom unfolding coefficient_hom_def by blast
 have special_shape: "map_poly (\<lambda>q. poly q 1)(ggv_root H)=
  [:c:]*([:0,1:]^(ggv_t H)*pcompose p ([:0,1:]^(ggv_rho H)))"
  by (simp only: shape crossing_cut_specialize_mult crossing_cut_specialize_monom
    crossing_substitution_eval power_0 mult_1_right one_pCons[symmetric] mult_1_left)
 have composition: "pcompose p ([:0,1:]^(ggv_rho H))\<noteq>0"
 proof (rule ccontr)
  assume "\<not>pcompose p ([:0,1:]^(ggv_rho H))\<noteq>0"
  then have evaluate: "poly(pcompose p ([:0,1:]^(ggv_rho H)))0=0" by simp
  have nz: "ggv_rho H\<noteq>0" using rho by arith
  have zero_power: "(0::complex)^(ggv_rho H)=0" using nz by simp
  have at_zero: "poly p 0=0"
   using evaluate by (simp only: poly_pcompose poly_power poly_pCons poly_0
     mult_zero_right mult_zero_left add_0_right add_0_left zero_power)
  have normalized: "poly p 0=1" using p0 by (simp only: poly_0_coeff_0)
  show False using at_zero normalized by simp
 qed
 have variable_nonzero: "([:0,1:]::complex poly)\<noteq>0" by simp
 have variable_degree: "degree([:0,1:]::complex poly)=1" by simp
 have power_degree: "degree(([:0,1:]::complex poly)^n)=n" for n
   by (simp only: degree_power_eq[OF variable_nonzero] variable_degree mult_1_right)
 have degree_equation: "ggv_t H+degree p*ggv_rho H=ggv_v H"
  using special_degree by (simp only: special_shape; simp add: degree_mult_eq c composition degree_pcompose power_degree)
 have product: "degree p*ggv_rho H=ggv_h H*ggv_rho H"
  using degree_equation height by (simp add: mult.commute)
 show ?thesis using product rho by simp
qed

lemma smallDegreeCrossing_scalar_root_at_height:
 fixes P Q::"complex poly_operator"
 assumes data: "ggv_small_degree_crossing_data P Q H"
 shows "\<exists>c::complex. \<exists>p f::complex poly. \<exists>alpha::complex.
 c\<noteq>0 \<and> coeff p 0=1 \<and>
 ggv_root H=biv_monom c 0 0*(biv_monom 1 (ggv_r H)(ggv_t H)*biv_univariate_eval p (biv_monom 1 (ggv_s H)(ggv_rho H))) \<and>
 ggv_companion H=biv_monom 1 1 1*biv_univariate_eval f (biv_monom 1 (ggv_s H)(ggv_rho H)) \<and>
 degree p=ggv_h H \<and> alpha\<noteq>0 \<and> poly p alpha=0 \<and> rootMultiplicity alpha p=ggv_h H"
proof -
 obtain c p f where c: "c\<noteq>0" and p0: "coeff p 0=1"
  and Rshape: "ggv_root H=biv_monom c 0 0*(biv_monom 1 (ggv_r H)(ggv_t H)*biv_univariate_eval p (biv_monom 1 (ggv_s H)(ggv_rho H)))"
  and Fshape: "ggv_companion H=biv_monom 1 1 1*biv_univariate_eval f (biv_monom 1 (ggv_s H)(ggv_rho H))"
  and degree: "degree f=1"
  and general: "GenComp(ggv_rho H-ggv_s H)(ggv_r H-ggv_t H)(ggv_rho H*ggv_r H-ggv_s H*ggv_t H) p f"
  using smallDegreeCrossing_exact_scalar_reconstruction[OF data] by blast
 have height: "degree p=ggv_h H" by (rule smallDegreeCrossing_scalar_degree_eq_height[OF data c p0 Rshape])
 have direction: "is_direction(int(ggv_rho H))(-int(ggv_s H))" and h: "2\<le>ggv_h H"
  using data unfolding ggv_small_degree_crossing_data_def by blast+
 have delta: "0<ggv_rho H-ggv_s H" using direction by (simp add: is_direction_def)
 have normalized: "poly p 0=1" using p0 by (simp add: poly_0_coeff_0)
 have positive: "0<degree p" using height h by arith
 obtain alpha where alpha: "alpha\<noteq>0" and root: "poly p alpha=0" and multiplicity: "rootMultiplicity alpha p=degree p"
  using GenComp_exists_full_multiplicity_root[OF general delta normalized positive degree] by blast
 have multiplicity_height: "rootMultiplicity alpha p=ggv_h H"
  using multiplicity height by simp
 have witness: "c\<noteq>0 \<and> coeff p 0=1 \<and>
  ggv_root H=biv_monom c 0 0*(biv_monom 1 (ggv_r H)(ggv_t H)*biv_univariate_eval p (biv_monom 1 (ggv_s H)(ggv_rho H))) \<and>
  ggv_companion H=biv_monom 1 1 1*biv_univariate_eval f (biv_monom 1 (ggv_s H)(ggv_rho H)) \<and>
  degree p=ggv_h H \<and> alpha\<noteq>0 \<and> poly p alpha=0 \<and> rootMultiplicity alpha p=ggv_h H"
  by (intro conjI; fact c p0 Rshape Fshape height alpha root multiplicity_height)
 show ?thesis
  by (rule exI[where x=c]; rule exI[where x=p]; rule exI[where x=f]; rule exI[where x=alpha]; fact witness)
qed

end
