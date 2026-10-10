theory Dixmier_Mass_Six_Real_Roots
  imports "Polynomial_Scaling"
begin

text \<open>Exact five-theorem port of DixmierFormal/Scalar/RealRoots.lean.
The root predicate is represented by polynomial evaluation equal to zero.\<close>

lemma exists_isRoot_of_odd_natDegree:
  fixes p :: "real poly"
  assumes hp: "odd (degree p)"
  shows "\<exists>x. poly p x = 0"
proof -
  have positive_lead_case: "\<exists>x. poly q x = 0"
    if hq: "odd (degree q)" and hlc: "0 < lead_coeff q"
    for q :: "real poly"
  proof -
    let ?r = "- pcompose q [:0,-1:]"
    have deg: "degree (pcompose q [:0,-1:]) = degree q"
      by (rule natDegree_comp_C_mul_X) simp
    have lc: "lead_coeff ?r = lead_coeff q"
      using hq by (simp add: lead_coeff_minus deg coeff_comp_C_mul_X)
    have rlc: "0 < lead_coeff ?r" using hlc lc by simp
    obtain a where ha: "\<forall>x\<ge>a. lead_coeff ?r \<le> poly ?r x"
      using poly_pinfty_gt_lc[OF rlc] by blast
    obtain b where hb: "\<forall>x\<ge>b. lead_coeff q \<le> poly q x"
      using poly_pinfty_gt_lc[OF hlc] by blast
    let ?t = "max 1 (max a b)"
    have tpos: "0 < ?t" by simp
    have rb: "lead_coeff q \<le> poly q ?t"
      by (rule hb[rule_format]) simp
    have lb: "lead_coeff ?r \<le> poly ?r ?t"
      by (rule ha[rule_format]) simp
    have right: "0 < poly q ?t" using rb hlc by linarith
    have left: "poly q (-?t) < 0"
      using lb hlc lc by (simp add: poly_pcompose; linarith)
    obtain x where "poly q x = 0"
      using poly_IVT_pos[of "-?t" ?t q] left right tpos by auto
    then show ?thesis by blast
  qed
  have p0: "p \<noteq> 0" using hp by auto
  have lc0: "lead_coeff p \<noteq> 0" using p0 by simp
  show ?thesis
  proof (cases "0 < lead_coeff p")
    case True
    then show ?thesis by (rule positive_lead_case[OF hp])
  next
    case False
    have nlc: "0 < lead_coeff (-p)"
      using False lc0 by (simp only: lead_coeff_minus; linarith)
    have nodd: "odd (degree (-p))" using hp by simp
    have "\<exists>x. poly (-p) x = 0" by (rule positive_lead_case[OF nodd nlc])
    then show ?thesis by simp
  qed
qed

lemma even_natDegree_of_forall_not_isRoot:
  fixes p :: "real poly"
  assumes h: "\<forall>x. poly p x \<noteq> 0"
  shows "even (degree p)"
  using h exists_isRoot_of_odd_natDegree[of p] by blast

lemma not_isRoot_of_pos:
  fixes F :: "real poly" and gamma :: real
  assumes hF0: "poly F 0 < 0"
    and hslope: "\<forall>g. poly F g = 0 \<longrightarrow> g * poly (pderiv F) g < 0"
    and hgamma: "0 < gamma"
  shows "poly F gamma \<noteq> 0"
proof
  assume hroot: "poly F gamma = 0"
  have F0: "F \<noteq> 0" using hF0 by auto
  let ?P = "{x. poly F x = 0 \<and> 0 < x}"
  have fin: "finite ?P"
    by (rule finite_subset[OF _ poly_roots_finite[OF F0]]) auto
  have nonempty: "?P \<noteq> {}" using hroot hgamma by auto
  define g where "g = Min ?P"
  have mem: "g \<in> ?P" unfolding g_def by (rule Min_in[OF fin nonempty])
  then have groot: "poly F g = 0" and gpos: "0 < g" by auto
  have minimal: "g \<le> x" if "poly F x = 0" "0 < x" for x
    using that unfolding g_def by (intro Min_le[OF fin]) auto
  obtain G where factor: "F = [:-g,1:] * G"
    using groot by (auto simp: poly_eq_0_iff_dvd dvd_def)
  have deriv: "poly (pderiv F) g = poly G g"
    by (subst factor, subst pderiv_mult) (simp add: pderiv_pCons)
  have radial: "g * poly (pderiv F) g < 0" using hslope groot by blast
  have Gneg: "poly G g < 0"
    using radial gpos by (auto simp: deriv mult_less_0_iff)
  have at0: "poly F 0 = -g * poly G 0" by (simp add: factor)
  have Gpos: "0 < poly G 0" using hF0 gpos unfolding at0 mult_less_0_iff by auto
  obtain x where xpos: "0 < x" and xless: "x < g" and xroot: "poly G x = 0"
    using poly_IVT_neg[OF gpos Gpos Gneg] by blast
  have "poly F x = 0" by (simp add: factor xroot)
  then have "g \<le> x" by (rule minimal[OF _ xpos])
  with xless show False by simp
qed

lemma forall_not_isRoot_of_slope_neg:
  fixes F :: "real poly"
  assumes hF0: "poly F 0 < 0"
    and hslope: "\<forall>g. poly F g = 0 \<longrightarrow> g * poly (pderiv F) g < 0"
  shows "\<forall>gamma. poly F gamma \<noteq> 0"
proof (intro allI notI)
  fix gamma
  assume hroot: "poly F gamma = 0"
  consider "gamma < 0" | "gamma = 0" | "0 < gamma" by linarith
  then show False
  proof cases
    case 1
    let ?H = "pcompose F [:0,-1:]"
    have H0: "poly ?H 0 < 0" using hF0 by (simp add: poly_pcompose)
    have Hslope: "\<forall>y. poly ?H y = 0 \<longrightarrow> y * poly (pderiv ?H) y < 0"
    proof (intro allI impI)
      fix y
      assume "poly ?H y = 0"
      then have root: "poly F (-y) = 0" by (simp add: poly_pcompose)
      have "(-y) * poly (pderiv F) (-y) < 0" using hslope root by blast
      then show "y * poly (pderiv ?H) y < 0"
        by (simp add: pderiv_pcompose pderiv_pCons poly_pcompose)
    qed
    have "poly ?H (-gamma) \<noteq> 0"
      by (rule not_isRoot_of_pos[OF H0 Hslope]) (use 1 in simp)
    with hroot show False by (simp add: poly_pcompose)
  next
    case 2
    with hF0 hroot show False by simp
  next
    case 3
    with not_isRoot_of_pos[OF hF0 hslope] hroot show False by blast
  qed
qed

lemma exists_map_ofReal_eq:
  fixes p :: "complex poly"
  assumes h: "\<forall>n. Im (coeff p n) = 0"
  shows "\<exists>q :: real poly. map_poly of_real q = p"
proof -
  have "map_poly of_real (map_poly Re p) = p"
    by (rule poly_eqI) (use h in \<open>simp add: coeff_map_poly complex_eq_iff\<close>)
  then show ?thesis by blast
qed

end
