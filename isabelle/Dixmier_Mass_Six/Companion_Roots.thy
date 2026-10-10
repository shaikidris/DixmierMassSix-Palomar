theory Companion_Roots
  imports "Companion_Degree"
    "Polynomial_Scaling" Root_Multiplicity_Adapter
begin

lemma Comp_root_slope:
  assumes h: "Comp rho s r f" and hs: "s < rho"
    and hr0: "poly r 0 = 1" and ha: "poly r a = 0"
  shows "poly f a = 0 \<and>
    a * poly (pderiv f) a * ((of_nat rho-of_nat s) * of_nat (rootMultiplicity a r)-of_nat rho) = 1"
proof -
  have rnz: "r \<noteq> 0" using hr0 by auto
  have anz: "a \<noteq> 0" using hr0 ha by auto
  have dnz: "(of_nat rho-of_nat s :: complex) \<noteq> 0" using hs by simp
  have jpos: "0 < Polynomial.order a r" using ha order_gt_0_iff[OF rnz] by simp
  obtain k where jk: "Polynomial.order a r = Suc k" using jpos by (cases "Polynomial.order a r") auto
  obtain u where ru: "r = [:-a,1:] ^ Suc k * u" and und: "\<not> [:-a,1:] dvd u"
    using order_decomp[OF rnz, of a] unfolding jk by blast
  have unz: "poly u a \<noteq> 0" using und by (simp add: poly_eq_0_iff_dvd)
  let ?B = "[:-a,1:]"
  have bnz: "?B \<noteq> 0" by simp
  have bknz: "?B^k \<noteq> 0" using bnz by simp
  let ?D = "[:of_nat (Suc k):] * u + ?B * pderiv u"
  let ?A = "[:of_nat rho-of_nat s:]"
  let ?R = "[:of_nat rho:]"
  let ?X = "[:0,1:] :: complex poly"
  have dr: "pderiv r = ?B ^ k * ?D"
    unfolding ru pderiv_mult pderiv_power_Suc
    by (simp add: pderiv_pCons algebra_simps smult_add_right smult_diff_right)
  have e1: "?B^k * (?A * ?X * f * ?D) =
      ?B^k * ((f + ?R * ?X * pderiv f + 1) * ?B * u)"
    using h unfolding Comp_def dr
    by (simp only: ru power_Suc mult_ac)
  have h1: "?A * ?X * f * ?D = (f + ?R * ?X * pderiv f + 1) * ?B * u"
    using e1 by (simp only: mult_left_cancel[OF bknz])
  have ev1: "(of_nat rho-of_nat s) * a * poly f a * (of_nat (Suc k) * poly u a) = 0"
    using arg_cong[OF h1, of "\<lambda>p. poly p a"] by (simp add: mult_ac)
  have knz: "(of_nat (Suc k)::complex) \<noteq> 0" by (rule of_nat_neq_0)
  have fa: "poly f a = 0" using ev1 dnz anz unz knz by auto
  obtain g where fg: "f = ?B * g"
    using fa unfolding poly_eq_0_iff_dvd dvd_def by blast
  have df: "pderiv f = g + ?B * pderiv g"
    unfolding fg pderiv_mult by (simp add: pderiv_pCons)
  have e2: "?B * (?A * ?X * g * ?D) =
      ?B * ((?B*g + ?R * ?X * (g + ?B*pderiv g) + 1) * u)"
    using h1 unfolding df by (simp only: fg mult_ac)
  have h2: "?A * ?X * g * ?D = (?B*g + ?R * ?X * (g + ?B*pderiv g) + 1) * u"
    using e2 by (simp only: mult_left_cancel[OF bnz])
  have ev2: "(of_nat rho-of_nat s) * a * poly g a * (of_nat (Suc k)*poly u a) =
      (of_nat rho*a*poly g a+1)*poly u a"
    using arg_cong[OF h2, of "\<lambda>p. poly p a"] by (simp add: mult_ac)
  have alg: "(d*a*b*(j*u) - (v*a*b+1)*u) = (a*b*(d*j-v)-1)*u"
    for d a b j u v :: complex by (simp add: algebra_simps)
  have z: "(a * poly g a * ((of_nat rho-of_nat s)*of_nat (Suc k)-of_nat rho)-1)*poly u a=0"
    using ev2 by (simp only: alg[symmetric] diff_self)
  have slope: "a * poly g a * ((of_nat rho-of_nat s)*of_nat (Suc k)-of_nat rho)=1"
    using z unz by auto
  show ?thesis using fa slope rnz by (simp add: df rootMultiplicity_eq_order jk)
qed

lemma Comp_slope_of_not_root:
  assumes h: "Comp rho s r f" and hf: "poly f gamma = 0" and hr: "poly r gamma \<noteq> 0"
  shows "of_nat rho * gamma * poly (pderiv f) gamma = -1"
proof -
  have e: "poly ([:of_nat rho-of_nat s:] * [:0,1:] * f * pderiv r) gamma =
    poly ((f + [:of_nat rho:] * [:0,1:] * pderiv f + 1) * r) gamma"
    using h unfolding Comp_def by simp
  have "of_nat rho * gamma * poly (pderiv f) gamma + 1 = 0"
    using e hf hr by (auto simp: mult_ac)
  then show ?thesis by (simp add: eq_neg_iff_add_eq_0)
qed

lemma Comp_isRoot_f:
  assumes "Comp rho s r f" "s<rho" "poly r 0=1" "poly r a=0"
  shows "poly f a=0"
  using Comp_root_slope[OF assms] by blast

lemma Comp_unique:
  assumes h1: "Comp rho s r f1" and h2: "Comp rho s r f2" and hr0: "poly r 0=1"
  shows "f1=f2"
proof (rule ccontr)
  assume "f1 \<noteq> f2"
  then have dnz: "f1-f2 \<noteq> 0" by simp
  obtain q where dq: "f1-f2 = [:0,1:] ^ Polynomial.order 0 (f1-f2) * q"
    and qnd: "\<not> [:0,1:] dvd q" using order_decomp[OF dnz, of 0] by simp blast
  have qnz: "poly q 0 \<noteq> 0" using qnd by (simp add: dvd_iff_poly_eq_0)
  let ?A = "[:of_nat rho-of_nat s:]"
  let ?R = "[:of_nat rho:]"
  let ?X = "[:0,1:] :: complex poly"
  have subeq: "?A*?X*f1*pderiv r - ?A*?X*f2*pderiv r =
    (f1+?R*?X*pderiv f1+1)*r - (f2+?R*?X*pderiv f2+1)*r"
    using h1 h2 unfolding Comp_def by simp
  have deq: "?A*?X*(f1-f2)*pderiv r = ((f1-f2)+?R*?X*pderiv(f1-f2))*r"
    using subeq by (simp only: pderiv_diff algebra_simps mult_1_left add_left_cancel add_right_cancel)
  show False
  proof (cases "Polynomial.order 0 (f1-f2)")
    case 0
    have "f1-f2=q" using dq 0 by simp
    then have key0: "?A*?X*q*pderiv r = (q+?R*?X*pderiv q)*r" using deq by simp
    have "poly q 0 = 0" using arg_cong[OF key0, of "\<lambda>p. poly p 0"] hr0 by simp
    then show False using qnz by contradiction
  next
    case (Suc k)
    have d: "f1-f2=?X^Suc k*q" using dq Suc by simp
    have der: "pderiv (?X^Suc k*q) = ?X^k * ([:of_nat (Suc k):]*q+?X*pderiv q)"
      unfolding pderiv_mult pderiv_power_Suc
      by (simp add: pderiv_pCons algebra_simps smult_add_right smult_diff_right)
    have e: "?X^Suc k * (?A*?X*q*pderiv r) =
      ?X^Suc k * ((q+?R*([:of_nat (Suc k):]*q+?X*pderiv q))*r)"
      using deq unfolding d der by (simp add: power_Suc algebra_simps smult_add_right smult_diff_right)
    have xnz: "?X^Suc k \<noteq> 0" by simp
    have key: "?A*?X*q*pderiv r = (q+?R*([:of_nat (Suc k):]*q+?X*pderiv q))*r"
      using e by (simp only: mult_left_cancel[OF xnz])
    have ev: "poly q 0 + of_nat rho*(of_nat (Suc k)*poly q 0)=0"
      using arg_cong[OF key, of "\<lambda>p. poly p 0"] hr0 by simp
    have alg: "q + v*(j*q) = (1+v*j)*q" for q v j :: complex
      by (simp add: algebra_simps)
    have cast: "(1+of_nat rho*of_nat (Suc k) :: complex) = of_nat (1+rho*Suc k)" by (simp add: algebra_simps)
    have cnz: "(1+of_nat rho*of_nat (Suc k) :: complex) \<noteq> 0"
      by (simp only: cast of_nat_eq_0_iff)
    show False using ev qnz cnz by (simp only: alg mult_eq_0_iff; blast)
  qed
qed

lemma Comp_comp_C_mul_X:
  assumes h: "Comp rho s r f"
  shows "Comp rho s (pcompose r [:0,c:]) (pcompose f [:0,c:])"
proof -
  have e: "poly ([:of_nat rho-of_nat s:]*[:0,1:]*f*pderiv r) (c*z) =
    poly ((f+[:of_nat rho:]*[:0,1:]*pderiv f+1)*r) (c*z)" for z
    using h unfolding Comp_def by simp
  have pointwise: "poly ([:of_nat rho-of_nat s:]*[:0,1:]*pcompose f [:0,c:]*pderiv (pcompose r [:0,c:])) z =
    poly ((pcompose f [:0,c:]+[:of_nat rho:]*[:0,1:]*pderiv (pcompose f [:0,c:])+1)*pcompose r [:0,c:]) z" for z
    using e[of z] by (simp add: pderiv_pcompose pderiv_pCons poly_pcompose mult_ac)
  show ?thesis unfolding Comp_def
    by (rule poly_eq_poly_eq_iff[THEN iffD1]) (rule ext, rule pointwise)
qed

lemma companion_cnj_deriv:
  "pderiv (map_poly cnj p) = map_poly cnj (pderiv p)"
  by (rule poly_eqI) (simp add: coeff_pderiv coeff_map_poly)

lemma Comp_map_conj:
  assumes h: "Comp rho s r f"
  shows "Comp rho s (map_poly cnj r) (map_poly cnj f)"
proof -
  have e: "cnj (poly ([:of_nat rho-of_nat s:]*[:0,1:]*f*pderiv r) (cnj z)) =
    cnj (poly ((f+[:of_nat rho:]*[:0,1:]*pderiv f+1)*r) (cnj z))" for z
    using h unfolding Comp_def by simp
  have pointwise: "poly ([:of_nat rho-of_nat s:]*[:0,1:]*map_poly cnj f*pderiv (map_poly cnj r)) z =
    poly ((map_poly cnj f+[:of_nat rho:]*[:0,1:]*pderiv (map_poly cnj f)+1)*map_poly cnj r) z" for z
    using e[of z] by (simp add: companion_cnj_deriv)
  show ?thesis unfolding Comp_def
    by (rule poly_eq_poly_eq_iff[THEN iffD1]) (rule ext, rule pointwise)
qed

lemma Comp_sq_support_rigid:
  assumes h: "Comp rho s r f" and hs: "s<rho" and hr0: "poly r 0=1" and hr: "0<degree r"
  shows "\<forall>zeta::complex. (\<forall>n\<in>sparse_support (r^2). zeta^n=1) \<longrightarrow> zeta=1"
proof (intro allI impI)
  fix zeta :: complex
  assume hz: "\<forall>n\<in>sparse_support (r^2). zeta^n=1"
  have rnz: "r \<noteq> 0" using hr by auto
  have hf: "0<degree f" by (rule Comp_natDegree_f_pos[OF h hs hr0 hr])
  have fnz: "f \<noteq> 0" using hf by auto
  have power_comp: "pcompose (p^n) [:0,zeta:] = pcompose p [:0,zeta:] ^ n"
    for p :: "complex poly" and n by (induction n) (simp_all add: pcompose_mult pcompose_1)
  have sq: "pcompose r [:0,zeta:] ^ 2 = r^2"
  proof (unfold power_comp[symmetric], rule poly_eqI)
    fix n
    show "coeff (pcompose (r^2) [:0,zeta:]) n = coeff (r^2) n"
      using hz by (cases "coeff (r^2) n=0") (auto simp: coeff_comp_C_mul_X)
  qed
  have alg: "(a-b)*(a+b)=a^2-b^2" for a b :: "complex poly"
    by (simp add: power2_eq_square algebra_simps)
  have prod: "(pcompose r [:0,zeta:]-r)*(pcompose r [:0,zeta:]+r)=0"
    by (simp only: alg sq diff_self)
  have rscale: "pcompose r [:0,zeta:]=r"
  proof (cases "pcompose r [:0,zeta:]-r=0")
    case True
    then show ?thesis by simp
  next
    case False
    with prod have sum: "pcompose r [:0,zeta:]+r=0" by auto
    have "(2::complex)=0" using arg_cong[OF sum, of "\<lambda>p. poly p 0"] hr0
      by (simp add: eval_zero_comp_C_mul_X)
    then show ?thesis by simp
  qed
  have fscale: "pcompose f [:0,zeta:]=f"
    by (rule Comp_unique[OF _ h hr0]) (use Comp_comp_C_mul_X[OF h, of zeta] rscale in simp)
  have re: "zeta ^ degree r = 1"
    using arg_cong[OF rscale, of "\<lambda>p. coeff p (degree r)"] rnz
    by (simp add: coeff_comp_C_mul_X)
  have fe: "zeta ^ degree f = 1"
    using arg_cong[OF fscale, of "\<lambda>p. coeff p (degree f)"] fnz
    by (simp add: coeff_comp_C_mul_X)
  have di: "(rho-s)*degree r=1+rho*degree f" by (rule Comp_degree_identity[OF h hs hr hf])
  have "zeta = zeta^(1+rho*degree f)"
    by (simp only: power_add mult.commute[of rho "degree f"] power_mult fe power_one power_one_right mult_1_right)
  also have "\<dots> = zeta^((rho-s)*degree r)" by (simp only: di)
  also have "\<dots> = 1" by (simp only: mult.commute[of "rho-s" "degree r"] power_mult re power_one)
  finally show "zeta=1" .
qed

end
