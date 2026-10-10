theory General_Companion
 imports "Companion_Roots"
begin

definition GenComp::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex poly \<Rightarrow> complex poly \<Rightarrow> bool" where
 "GenComp delta H W r f \<longleftrightarrow> [:of_nat delta:]*[:0,1:]*f*pderiv r=
   ([:of_nat H:]*f+[:of_nat W:]*[:0,1:]*pderiv f+1)*r"

lemma GenComp_constant_relation:
 assumes h: "GenComp delta H W r f" and r0: "poly r 0=1"
 shows "of_nat H*poly f 0+1=0"
proof -
 have eq: "poly ([:of_nat delta:]*[:0,1:]*f*pderiv r) 0=
   poly (([:of_nat H:]*f+[:of_nat W:]*[:0,1:]*pderiv f+1)*r) 0"
   using h unfolding GenComp_def by simp
 show ?thesis using eq r0 by simp
qed

lemma GenComp_euler_form:
 assumes h: "GenComp delta H W r f"
 shows "[:of_nat delta:]*(f*euler r)=([:of_nat H:]*f+[:of_nat W:]*euler f+1)*r"
 using h by (simp add: GenComp_def euler_def monom_altdef mult_ac)

lemma GenComp_natDegree_f_pos:
 assumes h: "GenComp delta H W r f" and delta: "0<delta"
 and r0: "poly r 0=1" and r: "0<degree r"
 shows "0<degree f"
proof (rule ccontr)
 assume "\<not>0<degree f"
 then have f0: "degree f=0" by simp
 obtain c where fc: "f=[:c:]" using degree_eq_zeroE[OF f0] by blast
 have rel: "of_nat H*c+1=0" using GenComp_constant_relation[OF h r0] by (simp add: fc)
 have cnz: "c\<noteq>0" using rel by auto
 have dnz: "(of_nat delta::complex)\<noteq>0" using delta by simp
 have sumzero: "[:of_nat H:]*[:c:]+[:of_nat W:]*[:0,1:]*0+1=(0::complex poly)"
   using rel by (simp add: one_pCons mult.commute)
 have rel_reverse: "c*of_nat H+1=0" using rel by (simp only: mult.commute)
 have reduced: "pCons 0 (smult (c*of_nat delta) (pderiv r))=0"
   using h by (simp add: GenComp_def fc one_pCons rel_reverse)
 have scalar_nonzero: "c*of_nat delta\<noteq>0" using cnz dnz by simp
 have derivative: "pderiv r=0" using reduced scalar_nonzero by simp
 show False using derivative r by (simp add: pderiv_eq_0_iff)
qed

lemma GenComp_degree_identity:
  assumes h: "GenComp delta H W r f"
    and hr: "0 < degree r" and hf: "0 < degree f"
  shows "delta * degree r = H + W * degree f"
proof -
  let ?L = "degree f"
  let ?e = "degree r"
  have fnz: "f \<noteq> 0" using hf by auto
  have rnz: "r \<noteq> 0" using hr by auto
  have lead: "coeff f ?L * coeff r ?e \<noteq> 0" using fnz rnz by simp
  have bound: "degree ([:of_nat H:]*f + [:of_nat W:] * euler f + 1) \<le> ?L"
    by (intro degree_add_le) (auto intro: order_trans[OF degree_smult_le] natDegree_euler_le)
  have hc: "coeff ([:of_nat delta:] * (f * euler r)) (?L+?e) =
      coeff (([:of_nat H:]*f + [:of_nat W:] * euler f + 1) * r) (?L+?e)"
    using GenComp_euler_form[OF h] by simp
  have rhs: "coeff (([:of_nat H:]*f + [:of_nat W:] * euler f + 1) * r) (?L+?e) =
      coeff ([:of_nat H:]*f + [:of_nat W:] * euler f + 1) ?L * coeff r ?e"
    by (rule coeff_mult_of_degree_le[OF bound order_refl])
  have equation: "of_nat delta * (coeff f ?L * (of_nat ?e * coeff r ?e)) =
    (of_nat H*coeff f ?L + of_nat W * (of_nat ?L * coeff f ?L)) * coeff r ?e"
    using hc hf unfolding rhs
    by (simp add: coeff_mult_of_degree_le[OF order_refl natDegree_euler_le] coeff_euler)
  have algebra: "(a * (b * (c*d)) - (v*b + e*(f*b))*d) =
      (a*c-(v+e*f))*(b*d)" for a b c d e f v :: complex
    by (simp add: algebra_simps)
  have product_zero: "(of_nat delta * of_nat ?e -
      (of_nat H + of_nat W * of_nat ?L)) * (coeff f ?L * coeff r ?e) = 0"
    using equation by (simp only: algebra[symmetric] diff_self)
  have cast_eq: "(of_nat delta :: complex) * of_nat ?e =
      of_nat H + of_nat W * of_nat ?L"
    using product_zero lead by auto
  have "(of_nat (delta*?e) :: complex) = of_nat (H+W*?L)"
    unfolding of_nat_mult of_nat_add
    by (rule cast_eq)
  then show ?thesis by (simp only: of_nat_eq_iff)
qed

lemma GenComp_natDegree_f_lt:
 assumes h: "GenComp delta H W r f" and H: "0<H" and bound: "delta\<le>W"
 and r: "0<degree r" and f: "0<degree f"
 shows "degree f<degree r"
proof (rule ccontr)
 assume "\<not>degree f<degree r"
 then have le: "degree r\<le>degree f" by simp
 have lo: "delta*degree r\<le>delta*degree f" by (rule mult_le_mono2[OF le])
 have hi: "delta*degree f\<le>W*degree f" by (rule mult_le_mono1[OF bound])
 have eq: "delta*degree r=H+W*degree f" by (rule GenComp_degree_identity[OF h r f])
 show False using lo hi eq H by arith
qed

lemma GenComp_root_slope:
  assumes h: "GenComp delta H W r f" and delta: "0<delta"
    and hr0: "poly r 0 = 1" and ha: "poly r a = 0"
  shows "poly f a = 0 \<and>
    a * poly (pderiv f) a * ((of_nat delta) * of_nat (rootMultiplicity a r)-of_nat W) = 1"
proof -
  have rnz: "r \<noteq> 0" using hr0 by auto
  have anz: "a \<noteq> 0" using hr0 ha by auto
  have dnz: "(of_nat delta :: complex) \<noteq> 0" using delta by simp
  have jpos: "0 < Polynomial.order a r" using ha order_gt_0_iff[OF rnz] by simp
  obtain k where jk: "Polynomial.order a r = Suc k" using jpos by (cases "Polynomial.order a r") auto
  obtain u where ru: "r = [:-a,1:] ^ Suc k * u" and und: "\<not> [:-a,1:] dvd u"
    using order_decomp[OF rnz, of a] unfolding jk by blast
  have unz: "poly u a \<noteq> 0" using und by (simp add: poly_eq_0_iff_dvd)
  let ?B = "[:-a,1:]"
  have bnz: "?B \<noteq> 0" by simp
  have bknz: "?B^k \<noteq> 0" using bnz by simp
  let ?D = "[:of_nat (Suc k):] * u + ?B * pderiv u"
  let ?A = "[:of_nat delta:]"
  let ?R = "[:of_nat W:]"
  let ?C = "[:of_nat H:]"
  let ?X = "[:0,1:] :: complex poly"
  have dr: "pderiv r = ?B ^ k * ?D"
    unfolding ru pderiv_mult pderiv_power_Suc
    by (simp add: pderiv_pCons algebra_simps smult_add_right smult_diff_right)
  have e1: "?B^k * (?A * ?X * f * ?D) =
      ?B^k * ((?C*f + ?R * ?X * pderiv f + 1) * ?B * u)"
    using h unfolding GenComp_def dr
    by (simp only: ru power_Suc mult_ac)
  have h1: "?A * ?X * f * ?D = (?C*f + ?R * ?X * pderiv f + 1) * ?B * u"
    using e1 by (simp only: mult_left_cancel[OF bknz])
  have ev1: "(of_nat delta) * a * poly f a * (of_nat (Suc k) * poly u a) = 0"
    using arg_cong[OF h1, of "\<lambda>p. poly p a"] by (simp add: mult_ac)
  have knz: "(of_nat (Suc k)::complex) \<noteq> 0" by (rule of_nat_neq_0)
  have fa: "poly f a = 0" using ev1 dnz anz unz knz by auto
  obtain g where fg: "f = ?B * g"
    using fa unfolding poly_eq_0_iff_dvd dvd_def by blast
  have df: "pderiv f = g + ?B * pderiv g"
    unfolding fg pderiv_mult by (simp add: pderiv_pCons)
  have e2: "?B * (?A * ?X * g * ?D) =
      ?B * ((?C*(?B*g) + ?R * ?X * (g + ?B*pderiv g) + 1) * u)"
    using h1 unfolding df by (simp only: fg mult_ac)
  have h2: "?A * ?X * g * ?D = (?C*(?B*g) + ?R * ?X * (g + ?B*pderiv g) + 1) * u"
    using e2 by (simp only: mult_left_cancel[OF bnz])
  have ev2: "(of_nat delta) * a * poly g a * (of_nat (Suc k)*poly u a) =
      (of_nat W*a*poly g a+1)*poly u a"
    using arg_cong[OF h2, of "\<lambda>p. poly p a"] by (simp add: mult_ac)
  have alg: "(d*a*b*(j*u) - (v*a*b+1)*u) = (a*b*(d*j-v)-1)*u"
    for d a b j u v :: complex by (simp add: algebra_simps)
  have z: "(a * poly g a * ((of_nat delta)*of_nat (Suc k)-of_nat W)-1)*poly u a=0"
    using ev2 by (simp only: alg[symmetric] diff_self)
  have slope: "a * poly g a * ((of_nat delta)*of_nat (Suc k)-of_nat W)=1"
    using z unz by auto
  show ?thesis using fa slope rnz by (simp add: df rootMultiplicity_eq_order jk)
qed

lemma GenComp_isRoot_f:
 assumes "GenComp delta H W r f" "0<delta" "poly r 0=1" "poly r a=0"
 shows "poly f a=0"
 using GenComp_root_slope[OF assms] by blast

end
