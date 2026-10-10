theory Polynomial_Lift_Face_Transport
  imports "Polynomial_Ramified_Lift_Homomorphism"
    "Weighted_Newton_Definitions"
begin

lemma polynomialRamifiedLift_support_iff_scaled:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
  shows "(k,j)\<in>ramified_pbw_support l (polynomial_ramified_lift l P) \<longleftrightarrow>
    (\<exists>i::nat. k=int l*int i \<and> pbw_coeff P i j\<noteq>0)"
proof (cases "\<exists>i::nat. k=int l*int i")
  case True
  then obtain i where k: "k=int l*int i" by blast
  have unique: "\<And>a::nat. int l*int i=int l*int a \<longleftrightarrow> i=a" using l by simp
  show ?thesis using l by (simp add: k ramified_pbw_support_mem_iff[OF l polynomial_ramified_lift_carrier]
    polynomial_ramified_lift_pbwCoeff_scaled[OF l P] unique)
next
  case False
  have off: "\<And>i::nat. k\<noteq>int l*int i" using False by blast
  show ?thesis using False by (simp add: ramified_pbw_support_mem_iff[OF l polynomial_ramified_lift_carrier]
    polynomial_ramified_lift_pbwCoeff_zero_off_scaled[OF l off])
qed

lemma polynomialRamifiedLift_support_iff_symbol:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
  shows "(k,j)\<in>ramified_pbw_support l (polynomial_ramified_lift l P) \<longleftrightarrow>
    (\<exists>i::nat. k=int l*int i \<and> (i,j)\<in>biv_support (pbw_symbol P))"
  by (simp add: polynomialRamifiedLift_support_iff_scaled[OF l P] biv_support_def weyl_symbol_coeff[OF P])

lemma polynomialRamifiedLift_weight_scaled:
  "ramified_weight l rho sigma (int l*int i,j)=int l*pair_weight rho sigma (i,j)"
  by (simp add: ramified_weight_def pair_weight_def algebra_simps)

lemma polynomial_ramified_lift_support_image:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
  shows "ramified_pbw_support l (polynomial_ramified_lift l P)=
    (\<lambda>u. (int l*int(fst u),snd u)) ` biv_support (pbw_symbol P)"
proof (rule set_eqI)
  fix v::"int\<times>nat"
  obtain k j where v: "v=(k,j)" by (cases v) auto
  show "v\<in>ramified_pbw_support l (polynomial_ramified_lift l P) \<longleftrightarrow>
    v\<in>(\<lambda>u. (int l*int(fst u),snd u)) ` biv_support (pbw_symbol P)"
    by (auto simp: v polynomialRamifiedLift_support_iff_symbol[OF l P] image_iff;
      metis fst_conv snd_conv)
qed

lemma polynomial_ramified_lift_weight_degree:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
  shows "ramified_weight_deg l rho sigma (polynomial_ramified_lift l P)=int l*v_degree rho sigma P"
proof (cases "biv_support (pbw_symbol P)={}")
  case True
  have empty: "ramified_pbw_support l (polynomial_ramified_lift l P)={}"
    by (simp only: polynomial_ramified_lift_support_image[OF l P] True image_empty)
  show ?thesis by (simp add: ramified_weight_deg_def empty v_degree_def weighted_degree_def True)
next
  case False
  let ?S = "biv_support (pbw_symbol P)"
  let ?W = "pair_weight rho sigma ` ?S"
  have degree: "weighted_degree rho sigma (pbw_symbol P)=bot.Value (v_degree rho sigma P)"
    using False by (simp add: weighted_degree_def v_degree_def)
  obtain u where u: "u\<in>?S" and weight: "pair_weight rho sigma u=v_degree rho sigma P"
    using weighted_degree_attained[OF degree] by blast
  have point: "(int l*int(fst u),snd u)\<in>ramified_pbw_support l (polynomial_ramified_lift l P)"
    using u by (auto simp: polynomial_ramified_lift_support_image[OF l P])
  have attained: "ramified_weight l rho sigma (int l*int(fst u),snd u)=int l*v_degree rho sigma P"
    using weight by (simp add: polynomialRamifiedLift_weight_scaled prod.collapse)
  have bounded: "\<forall>v\<in>ramified_pbw_support l (polynomial_ramified_lift l P).
    ramified_weight l rho sigma v\<le>int l*v_degree rho sigma P"
  proof (intro ballI)
    fix v assume v: "v\<in>ramified_pbw_support l (polynomial_ramified_lift l P)"
    obtain w where w: "w\<in>?S" and v_eq: "v=(int l*int(fst w),snd w)"
      using v by (auto simp: polynomial_ramified_lift_support_image[OF l P])
    have bound: "pair_weight rho sigma w\<le>v_degree rho sigma P"
      by (rule weighted_degree_support_bound[OF degree w])
    have scaled: "int l*pair_weight rho sigma w\<le>int l*v_degree rho sigma P"
      by (rule mult_left_mono[OF bound]) simp
    show "ramified_weight l rho sigma v\<le>int l*v_degree rho sigma P"
      using scaled by (simp only: v_eq polynomialRamifiedLift_weight_scaled prod.collapse)
  qed
  show ?thesis by (rule ramified_weight_deg_eq_of_attained_upper)
    (use point attained bounded in auto)
qed

lemma polynomial_ramified_lift_leading_support:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
  shows "ramified_leading_support l rho sigma (polynomial_ramified_lift l P)=
    (\<lambda>u. (int l*int(fst u),snd u)) ` biv_support (leading_form rho sigma P)"
proof (rule set_eqI)
  fix v::"int\<times>nat"
  obtain k j where v: "v=(k,j)" by (cases v) auto
  have cancel: "\<And>a b::int. int l*a=int l*b \<longleftrightarrow> a=b" using l by simp
  show "v\<in>ramified_leading_support l rho sigma (polynomial_ramified_lift l P) \<longleftrightarrow>
    v\<in>(\<lambda>u. (int l*int(fst u),snd u)) ` biv_support (leading_form rho sigma P)"
    using l by (auto simp: v ramified_leading_support_def polynomialRamifiedLift_support_iff_symbol[OF l P]
      polynomial_ramified_lift_weight_degree[OF l P] polynomialRamifiedLift_weight_scaled
      leading_form_def weighted_component_support cancel image_iff)
qed

lemma polynomialRamifiedLift_weightDeg_scaled_of_pos:
  assumes "0<l" "P\<in>(weyl_algebra::complex poly_operator set)" "0<v_degree rho sigma P"
  shows "ramified_weight_deg l rho sigma (polynomial_ramified_lift l P)=int l*v_degree rho sigma P"
  by (rule polynomial_ramified_lift_weight_degree[OF assms(1,2)])

lemma polynomialRamifiedLift_leading_support_iff:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
    and positive: "0<v_degree rho sigma P"
  shows "(i,j)\<in>biv_support (leading_form rho sigma P) \<longleftrightarrow>
    ((int l*int i,j)\<in>ramified_pbw_support l (polynomial_ramified_lift l P) \<and>
      ramified_weight l rho sigma (int l*int i,j)=
        ramified_weight_deg l rho sigma (polynomial_ramified_lift l P))"
proof -
  have unique: "\<And>a::nat. int l*int i=int l*int a \<longleftrightarrow> i=a" using l by simp
  have cancel: "\<And>a b::int. int l*a=int l*b \<longleftrightarrow> a=b" using l by simp
  show ?thesis using l by (simp add: leading_form_def weighted_component_support
    polynomialRamifiedLift_support_iff_symbol[OF l P] unique cancel
    polynomialRamifiedLift_weight_scaled polynomial_ramified_lift_weight_degree[OF l P])
qed

lemma polynomialRamifiedLift_weight_le_scaled_vDeg:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
    and divides: "rho dvd int l"
    and member: "(u,n)\<in>ramified_pbw_support l (polynomial_ramified_lift l P)"
  shows "ramified_weight l rho sigma (u,n)\<le>rho*((int l div rho)*v_degree rho sigma P)"
proof -
  have bound: "ramified_weight l rho sigma (u,n)\<le>
    ramified_weight_deg l rho sigma (polynomial_ramified_lift l P)"
    by (rule ramified_weight_deg_upper[OF member])
  have index: "rho*(int l div rho)=int l" using divides by (simp add: dvd_mult_div_cancel mult.commute)
  show ?thesis using bound by (simp only: polynomial_ramified_lift_weight_degree[OF l P]
    mult.assoc[symmetric] index)
qed

lemma polynomialFace_point_source_data:
  assumes "(i,j)\<in>biv_support (leading_form rho sigma P)"
  shows "(i,j)\<in>biv_support (pbw_symbol P) \<and> pair_weight rho sigma (i,j)=v_degree rho sigma P"
  using assms by (simp add: leading_form_def weighted_component_support)

lemma polynomialRamifiedLift_face_point:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
    and divides: "rho dvd int l" and face: "(i,j)\<in>biv_support (leading_form rho sigma P)"
  shows "(int l*int i,j)\<in>ramified_pbw_support l (polynomial_ramified_lift l P) \<and>
    ramified_weight l rho sigma (int l*int i,j)=rho*((int l div rho)*v_degree rho sigma P)"
proof -
  have data: "(i,j)\<in>biv_support (pbw_symbol P)" "pair_weight rho sigma (i,j)=v_degree rho sigma P"
    using polynomialFace_point_source_data[OF face] by auto
  have index: "rho*(int l div rho)=int l" using divides by (simp add: dvd_mult_div_cancel mult.commute)
  show ?thesis using l by (auto simp: polynomialRamifiedLift_support_iff_symbol[OF l P]
    polynomialRamifiedLift_weight_scaled data mult.assoc[symmetric] index)
qed

lemma cutPoly_coeff_at_face_point:
  assumes rho: "0<rho" and weight: "pair_weight rho sigma (i,j)=v_degree rho sigma P"
  shows "coeff (cut_poly rho sigma P) j=biv_coeff (leading_form rho sigma P) i j"
proof -
  let ?F = "leading_form rho sigma P"
  have unique: "\<And>a::nat. pair_weight rho sigma (a,j)=v_degree rho sigma P \<Longrightarrow> a=i"
  proof -
    fix a :: nat assume aw: "pair_weight rho sigma (a,j)=v_degree rho sigma P"
    have mul: "int a*rho=int i*rho" using aw weight by (simp only: pair_weight_def fst_conv snd_conv; linarith)
    show "a=i" using mul rho by simp
  qed
  have inner: "coeff ?F j=monom (biv_coeff ?F i j) i"
  proof (rule poly_eqI)
    fix a
    have coefficient: "coeff (coeff ?F j) a=
      (if pair_weight rho sigma(a,j)=v_degree rho sigma P then biv_coeff(pbw_symbol P)a j else 0)"
      using weighted_component_coeff[where rho=rho and sigma=sigma and m="v_degree rho sigma P"
        and p="pbw_symbol P" and i=a and j=j]
      by (simp only: leading_form_def biv_coeff_def)
    have chosen: "biv_coeff ?F i j=biv_coeff(pbw_symbol P)i j"
      by (simp only: leading_form_def weighted_component_coeff weight; simp)
    show "coeff (coeff ?F j) a=coeff (monom (biv_coeff ?F i j) i) a"
      using unique[of a] weight by (simp only: coefficient chosen coeff_monom; auto)
  qed
  show ?thesis by (simp only: cut_poly_coeff inner poly_monom power_one mult_1_right)
qed

lemma cutPoly_coeff_at_weight:
  assumes P: "P\<in>(weyl_algebra::complex poly_operator set)"
    and rho: "0<rho" and weight: "pair_weight rho sigma (i,j)=v_degree rho sigma P"
  shows "coeff (cut_poly rho sigma P) j=pbw_coeff P i j"
  by (simp add: cutPoly_coeff_at_face_point[OF rho weight] leading_form_def weighted_component_coeff
    weight weyl_symbol_coeff[OF P])

lemma cutPoly_coeff_nonzero_has_face_point:
  assumes nonzero: "coeff (cut_poly rho sigma P) j\<noteq>0"
  shows "\<exists>i::nat. pair_weight rho sigma (i,j)=v_degree rho sigma P"
proof -
  let ?q = "coeff (leading_form rho sigma P) j"
  have q: "?q\<noteq>0" using nonzero by (auto simp: cut_poly_coeff)
  have c: "coeff ?q (degree ?q)\<noteq>0" using q by simp
  have "pair_weight rho sigma (degree ?q,j)=v_degree rho sigma P"
    using c by (auto simp: leading_form_def biv_coeff_def[symmetric] weighted_component_coeff split: if_splits)
  then show ?thesis by blast
qed

lemma polynomialRamifiedFace_coeff_at_weight:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
    and rho: "0<rho" and divides: "rho dvd int l"
    and weight: "pair_weight rho sigma (i,j)=v_degree rho sigma P"
  shows "coeff (ramified_face_polynomial l (polynomial_ramified_lift l P)
    ((int l div rho)*v_degree rho sigma P) (ramified_cut_exponent l rho sigma)) j=
    coeff (cut_poly rho sigma P) j"
proof -
  have index: "rho*(int l div rho)=int l" using divides by (simp add: dvd_mult_div_cancel mult.commute)
  have line: "(int l div rho)*v_degree rho sigma P-ramified_cut_exponent l rho sigma*int j=int l*int i"
  proof -
    have "(int l div rho)*v_degree rho sigma P-ramified_cut_exponent l rho sigma*int j=
      (rho*(int l div rho))*int i"
      by (simp only: weight[symmetric] pair_weight_def ramified_cut_exponent_def fst_conv snd_conv)
        (simp add: algebra_simps)
    then show ?thesis by (simp only: index)
  qed
  show ?thesis by (simp only: ramified_face_polynomial_coeff line
    polynomial_ramified_lift_pbwCoeff_scaled[OF l P] cutPoly_coeff_at_weight[OF P rho weight])
qed

lemma polynomialRamifiedFace_coeff_nonzero_has_face_point:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
    and divides: "rho dvd int l"
    and nonzero: "coeff (ramified_face_polynomial l (polynomial_ramified_lift l P)
      ((int l div rho)*v_degree rho sigma P) (ramified_cut_exponent l rho sigma)) j\<noteq>0"
  shows "\<exists>i::nat. pair_weight rho sigma (i,j)=v_degree rho sigma P"
proof -
  have member: "((int l div rho)*v_degree rho sigma P-ramified_cut_exponent l rho sigma*int j,j)
    \<in>ramified_pbw_support l (polynomial_ramified_lift l P)"
    using nonzero by (simp only: ramified_face_polynomial_coeff
      ramified_pbw_support_mem_iff[OF l polynomial_ramified_lift_carrier]) auto
  obtain i where line: "(int l div rho)*v_degree rho sigma P-ramified_cut_exponent l rho sigma*int j=int l*int i"
    using member by (auto simp: polynomialRamifiedLift_support_iff_scaled[OF l P])
  have index: "rho*(int l div rho)=int l" using divides by (simp add: dvd_mult_div_cancel mult.commute)
  have rearranged: "(int l div rho)*v_degree rho sigma P=
    ramified_cut_exponent l rho sigma*int j+int l*int i" using line by arith
  have multiplied: "rho*((int l div rho)*v_degree rho sigma P)=
    rho*(ramified_cut_exponent l rho sigma*int j+int l*int i)"
    using rearranged by simp
  have equality: "int l*v_degree rho sigma P=int l*pair_weight rho sigma (i,j)"
  proof -
    have left: "rho*((int l div rho)*v_degree rho sigma P)=int l*v_degree rho sigma P"
      by (simp only: mult.assoc[symmetric] index)
    have right: "rho*(ramified_cut_exponent l rho sigma*int j+int l*int i)=
      int l*pair_weight rho sigma (i,j)"
      by (simp only: distrib_left mult.assoc[symmetric] ramified_cut_exponent_weight[OF divides]
        pair_weight_def fst_conv snd_conv) (simp add: algebra_simps)
    show ?thesis using multiplied by (simp only: left right)
  qed
  have "pair_weight rho sigma (i,j)=v_degree rho sigma P" using equality l by simp
  then show ?thesis by blast
qed

lemma polynomialRamifiedFace_eq_cutPoly:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
    and rho: "0<rho" and divides: "rho dvd int l"
  shows "ramified_face_polynomial l (polynomial_ramified_lift l P)
    ((int l div rho)*v_degree rho sigma P) (ramified_cut_exponent l rho sigma)=cut_poly rho sigma P"
proof (rule poly_eqI)
  fix j
  let ?F = "ramified_face_polynomial l (polynomial_ramified_lift l P)
    ((int l div rho)*v_degree rho sigma P) (ramified_cut_exponent l rho sigma)"
  show "coeff ?F j=coeff (cut_poly rho sigma P) j"
  proof (cases "\<exists>i::nat. pair_weight rho sigma (i,j)=v_degree rho sigma P")
    case True
    then obtain i where weight: "pair_weight rho sigma (i,j)=v_degree rho sigma P" by blast
    show ?thesis by (rule polynomialRamifiedFace_coeff_at_weight[OF l P rho divides weight])
  next
    case False
    have c: "coeff (cut_poly rho sigma P) j=0"
      using cutPoly_coeff_nonzero_has_face_point[where rho=rho and sigma=sigma and P=P and j=j] False by blast
    have f: "coeff ?F j=0"
      using polynomialRamifiedFace_coeff_nonzero_has_face_point[OF l P divides, where j=j] False by blast
    show ?thesis by (simp only: c f)
  qed
qed

lemma polynomialRamifiedFace_ne_zero_iff_cutPoly:
  assumes "0<l" "P\<in>(weyl_algebra::complex poly_operator set)" "0<rho" "rho dvd int l"
  shows "ramified_face_polynomial l (polynomial_ramified_lift l P)
    ((int l div rho)*v_degree rho sigma P) (ramified_cut_exponent l rho sigma)\<noteq>0 \<longleftrightarrow>
      cut_poly rho sigma P\<noteq>0"
  by (simp only: polynomialRamifiedFace_eq_cutPoly[OF assms])

lemma polynomialRamifiedCut_root_start_on_old_face:
  fixes c :: complex
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
    and rho: "0<rho" and divides: "rho dvd int l" and positive: "0<rho+sigma"
    and face: "(i,j)\<in>biv_support (leading_form rho sigma P)"
  defines "r\<equiv>(int l div rho)*v_degree rho sigma P"
    and "k\<equiv>ramified_cut_exponent l rho sigma"
    and "m\<equiv>rootMultiplicity c (cut_poly rho sigma P)"
  shows "((r-k*int m,m)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c (polynomial_ramified_lift l P)) \<and>
      ramified_weight l rho sigma (r-k*int m,m)=rho*r) \<and>
    (\<forall>u n. (u,n)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c (polynomial_ramified_lift l P)) \<longrightarrow>
      ramified_weight l rho sigma (u,n)=rho*r \<longrightarrow> m\<le>n)"
proof -
  have point: "(int l*int i,j)\<in>ramified_pbw_support l (polynomial_ramified_lift l P)"
    and top: "ramified_weight l rho sigma (int l*int i,j)=rho*r"
    using polynomialRamifiedLift_face_point[OF l P divides face] by (auto simp only: r_def)
  have bounded: "\<And>u n. (u,n)\<in>ramified_pbw_support l (polynomial_ramified_lift l P) \<Longrightarrow>
      ramified_weight l rho sigma (u,n)\<le>rho*r"
    using polynomialRamifiedLift_weight_le_scaled_vDeg[OF l P divides] by (simp only: r_def)
  have result: "((r-k*int(rootMultiplicity c (ramified_face_polynomial l (polynomial_ramified_lift l P) r k)),
      rootMultiplicity c (ramified_face_polynomial l (polynomial_ramified_lift l P) r k))
        \<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c (polynomial_ramified_lift l P)) \<and>
      ramified_weight l rho sigma
        (r-k*int(rootMultiplicity c (ramified_face_polynomial l (polynomial_ramified_lift l P) r k)),
          rootMultiplicity c (ramified_face_polynomial l (polynomial_ramified_lift l P) r k))=rho*r) \<and>
      (\<forall>u n. (u,n)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c (polynomial_ramified_lift l P)) \<longrightarrow>
        ramified_weight l rho sigma (u,n)=rho*r \<longrightarrow>
        rootMultiplicity c (ramified_face_polynomial l (polynomial_ramified_lift l P) r k)\<le>n)"
    unfolding k_def by (rule ramifiedCutAut_root_start_on_old_face[OF l polynomial_ramified_lift_carrier rho divides positive point top])
      (rule bounded)
  show ?thesis using result by (simp only: r_def k_def polynomialRamifiedFace_eq_cutPoly[OF l P rho divides] m_def) auto
qed

end
