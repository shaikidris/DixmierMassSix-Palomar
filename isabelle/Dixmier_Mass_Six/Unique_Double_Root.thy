theory Unique_Double_Root
  imports "Multiplicity_Transport"
    "Companion_Roots"
    "Five_Term_Rigidity"
    "Two_Root_Normalization"
    "Dixmier_Mass_Six_Real_Roots"
begin

lemma eval_ofReal_map_ofRealHom:
  fixes q :: "real poly" and x :: real
  shows "poly (map_poly of_real q) (of_real x) = (of_real (poly q x) :: complex)"
  by (simp add: poly_altdef degree_map_poly coeff_map_poly)

lemma real_of_map_conj_eq:
  fixes p :: "complex poly"
  assumes hp: "map_poly cnj p = p"
  shows "Im (coeff p n) = 0"
  using arg_cong[OF hp, of "\<lambda>q. coeff q n"]
  by (simp add: coeff_map_poly cnj_eq_self_iff_Im_zero)

lemma unique_double_of_real_deriv:
  fixes p :: "real poly"
  shows "pderiv (map_poly of_real p) = (map_poly of_real (pderiv p) :: complex poly)"
  by (rule poly_eqI) (simp add: coeff_pderiv coeff_map_poly)

lemma Comp_eq_of_double_roots:
  assumes h: "Comp rho s r f" and hs: "1 \<le> s" and hsr: "s < rho"
    and hr0: "poly r 0 = 1" and hr: "0 < degree r" and ht: "termCount (r ^ 2) \<le> 6"
    and ha: "2 \<le> rootMultiplicity alpha r" and hb: "2 \<le> rootMultiplicity beta r"
  shows "alpha = beta"
proof (rule ccontr)
  assume hab: "alpha \<noteq> beta"
  have rnz: "r \<noteq> 0" using hr0 by auto
  have hf: "0 < degree f" by (rule Comp_natDegree_f_pos[OF h hsr hr0 hr])
  have nonzero: "gamma \<noteq> 0" if hm: "2 \<le> rootMultiplicity gamma r" for gamma
  proof -
    have "0 < Polynomial.order gamma r" using hm rnz
      by (simp add: rootMultiplicity_eq_order)
    then have "poly r gamma = 0" using order_gt_0_iff[OF rnz] by simp
    then show ?thesis using hr0 by auto
  qed
  have an: "alpha \<noteq> 0" by (rule nonzero[OF ha])
  have bn: "beta \<noteq> 0" by (rule nonzero[OF hb])
  have fourth: "([:0,1:] - [:gamma:]) ^ 4 dvd r ^ 2"
    if hm: "2 \<le> rootMultiplicity gamma r" for gamma
  proof -
    have d: "[:-gamma,1:] ^ 2 dvd r"
      using hm rnz by (simp add: Polynomial.order_divides rootMultiplicity_eq_order)
    have "([:-gamma,1:] ^ 2) ^ 2 dvd r ^ 2" by (rule dvd_power_same[OF d])
    then show ?thesis by (simp add: power_mult[symmetric])
  qed
  have a4: "([:0,1:] - [:alpha:]) ^ 4 dvd r ^ 2" by (rule fourth[OF ha])
  have b4: "([:0,1:] - [:beta:]) ^ 4 dvd r ^ 2" by (rule fourth[OF hb])
  have s1: "coeff (r ^ 2) 0 = 1" using hr0 by (simp add: poly_0_coeff_0[symmetric])
  have rigid: "\<And>z :: complex. (\<And>n. n \<in> sparse_support (r ^ 2) \<Longrightarrow> z ^ n = 1) \<Longrightarrow> z = 1"
    using Comp_sq_support_rigid[OF h hsr hr0 hr] by blast
  have t4: "4 < termCount (r ^ 2)"
    by (rule pow_dvd_imp_lt_termCount[OF _ an a4]) (use rnz in simp)
  consider (five) "termCount (r ^ 2) = 5" | (six) "termCount (r ^ 2) = 6"
    using t4 ht by linarith
  then show False
  proof cases
    case five
    have "alpha = beta" by (rule eq_of_five_terms[OF five _ rigid bn a4 b4]) (simp add: s1)
    with hab show False by contradiction
  next
    case six
    note normal = six_term_two_roots[OF six s1 rigid an hab a4 b4]
    have roots: "\<And>gamma. ([:0,1:] - [:gamma:]) ^ 4 dvd r ^ 2 \<Longrightarrow>
      gamma = alpha \<or> gamma = beta" using normal by blast
    obtain c :: complex where cnz: "c \<noteq> 0"
      and real_square: "\<forall>n. Im (coeff (pcompose (r ^ 2) [:0,c:]) n) = 0"
      and ac: "Im (alpha / c) \<noteq> 0" and bc: "beta / c = cnj (alpha / c)"
      using normal by blast
    define r2 where "r2 = pcompose r [:0,c:]"
    define f2 where "f2 = pcompose f [:0,c:]"
    have h2: "Comp rho s r2 f2"
      unfolding r2_def f2_def by (rule Comp_comp_C_mul_X[OF h])
    have r20: "poly r2 0 = 1" by (simp add: r2_def eval_zero_comp_C_mul_X hr0)
    have r2nz: "r2 \<noteq> 0" using r20 by auto
    have real_sq: "\<And>n. Im (coeff (r2 ^ 2) n) = 0"
      using real_square by (simp add: r2_def pcompose_mult power2_eq_square)
    have conj_sq: "(map_poly cnj r2) ^ 2 = r2 ^ 2"
    proof -
      have eq: "map_poly cnj (r2 ^ 2) = r2 ^ 2"
        by (rule poly_eqI) (simp add: coeff_map_poly cnj_eq_self_iff_Im_zero real_sq)
      have "(map_poly cnj r2) ^ 2 = map_poly cnj (r2 ^ 2)"
        by (rule poly_eq_poly_eq_iff[THEN iffD1]) (simp add: fun_eq_iff)
      then show ?thesis using eq by simp
    qed
    have rconj: "map_poly cnj r2 = r2"
    proof -
      have alg: "(a-b)*(a+b) = a^2-b^2" for a b :: "complex poly"
        by (simp add: power2_eq_square algebra_simps)
      have prod: "(map_poly cnj r2-r2)*(map_poly cnj r2+r2)=0"
        by (simp only: alg conj_sq diff_self)
      show ?thesis
      proof (cases "map_poly cnj r2-r2=0")
        case True
        then show ?thesis by simp
      next
        case False
        with prod have sum: "map_poly cnj r2+r2=0" by auto
        have "(2::complex)=0" using arg_cong[OF sum, of "\<lambda>p. poly p 0"] r20 by simp
        then show ?thesis by simp
      qed
    qed
    have fconj: "map_poly cnj f2 = f2"
      by (rule Comp_unique[OF _ h2 r20]) (use Comp_map_conj[OF h2] rconj in simp)
    obtain F :: "real poly" where hF: "map_poly of_real F = f2"
      using exists_map_ofReal_eq[of f2] real_of_map_conj_eq[OF fconj] by blast
    obtain R :: "real poly" where hR: "map_poly of_real R = r2"
      using exists_map_ofReal_eq[of r2] real_of_map_conj_eq[OF rconj] by blast
    have evF: "\<And>x::real. poly f2 (of_real x) = of_real (poly F x)"
      by (simp only: hF[symmetric] eval_ofReal_map_ofRealHom)
    have evR: "\<And>x::real. poly r2 (of_real x) = of_real (poly R x)"
      by (simp only: hR[symmetric] eval_ofReal_map_ofRealHom)
    have evdF: "\<And>x::real. poly (pderiv f2) (of_real x) = of_real (poly (pderiv F) x)"
      by (simp only: hF[symmetric] unique_double_of_real_deriv eval_ofReal_map_ofRealHom)
    have simple: "rootMultiplicity (of_real x) r2 \<le> 1" for x :: real
    proof (rule ccontr)
      assume "\<not> rootMultiplicity (of_real x) r2 \<le> 1"
      then have htwo: "2 \<le> rootMultiplicity (c*of_real x) r"
        by (simp add: r2_def rootMultiplicity_comp_C_mul_X[OF rnz cnz])
      have roots_split: "c*of_real x=alpha \<or> c*of_real x=beta"
        by (rule roots[OF fourth[OF htwo]])
      have divc: "(c*of_real x)/c = (of_real x :: complex)" using cnz by simp
      consider (a) "c*of_real x=alpha" | (b) "c*of_real x=beta" using roots_split by blast
      then show False
      proof cases
        case a
        then have "alpha/c = of_real x" using divc by simp
        with ac show False by simp
      next
        case b
        then have "beta/c = of_real x" using divc by simp
        then have "cnj (alpha/c) = of_real x" using bc by simp
        then have "alpha/c = of_real x" by (metis complex_cnj_cnj complex_cnj_complex_of_real)
        with ac show False by simp
      qed
    qed
    have spos: "0 < (of_nat s :: real)" using hs by simp
    have rpos: "0 < (of_nat rho :: real)" using hs hsr by simp
    have slope: "\<forall>gamma. poly F gamma=0 \<longrightarrow> gamma*poly (pderiv F) gamma<0"
    proof (intro allI impI)
      fix gamma :: real
      assume fg: "poly F gamma=0"
      have f2g: "poly f2 (of_real gamma)=0" using fg by (simp add: evF)
      show "gamma*poly (pderiv F) gamma<0"
      proof (cases "poly r2 (of_real gamma)=0")
        case True
        have jpos: "0 < rootMultiplicity (of_real gamma) r2"
          using order_gt_0_iff[OF r2nz] True by (simp add: rootMultiplicity_eq_order[OF r2nz])
        have j: "rootMultiplicity (of_real gamma) r2=1" using simple[of gamma] jpos by arith
        have sl: "of_real gamma * poly (pderiv f2) (of_real gamma) *
          ((of_nat rho-of_nat s)*of_nat (rootMultiplicity (of_real gamma) r2)-of_nat rho)=1"
          using Comp_root_slope[OF h2 hsr r20 True] by blast
        have re: "gamma*poly (pderiv F) gamma * (-(of_nat s :: real))=1"
          using arg_cong[OF sl, of Re] by (simp add: j evdF)
        have pos: "0 < gamma*poly (pderiv F) gamma * (-(of_nat s :: real))"
          using re by simp
        have neg: "gamma*poly (pderiv F) gamma * (of_nat s :: real) < 0"
          using pos by simp
        show ?thesis using neg spos by (auto simp: mult_less_0_iff)
      next
        case False
        have sl: "of_nat rho * of_real gamma * poly (pderiv f2) (of_real gamma) = -1"
          by (rule Comp_slope_of_not_root[OF h2 f2g False])
        have re: "(of_nat rho :: real)*gamma*poly (pderiv F) gamma = -1"
          using arg_cong[OF sl, of Re] by (simp add: evdF)
        have neg: "(of_nat rho :: real) * (gamma*poly (pderiv F) gamma) < 0"
          using re by (simp add: mult.assoc[symmetric])
        show ?thesis using neg rpos by (auto simp: mult_less_0_iff)
      qed
    qed
    have F0: "poly F 0 < 0"
    proof -
      have "(of_real (poly F 0) :: complex) = -1"
        using Comp_f_eval_zero[OF h2 r20] evF[of 0] by simp
      then have "poly F 0 = -1" by (metis of_real_eq_iff of_real_minus of_real_1)
      then show ?thesis by simp
    qed
    have Fno: "\<forall>x. poly F x \<noteq> 0" by (rule forall_not_isRoot_of_slope_neg[OF F0 slope])
    have Rno: "\<forall>x. poly R x \<noteq> 0"
    proof (intro allI notI)
      fix x :: real
      assume rx: "poly R x=0"
      have rg: "poly r2 (of_real x)=0" using rx by (simp add: evR)
      have "poly f2 (of_real x)=0" by (rule Comp_isRoot_f[OF h2 hsr r20 rg])
      then have "poly F x=0" by (simp add: evF)
      with Fno show False by blast
    qed
    have Fe: "even (degree F)" by (rule even_natDegree_of_forall_not_isRoot[OF Fno])
    have Re: "even (degree R)" by (rule even_natDegree_of_forall_not_isRoot[OF Rno])
    have Fdeg: "degree F = degree f"
    proof -
      have "degree F = degree f2" by (simp only: hF[symmetric]) (simp add: degree_map_poly)
      also have "\<dots> = degree f" unfolding f2_def by (rule natDegree_comp_C_mul_X[OF cnz])
      finally show ?thesis .
    qed
    have Rdeg: "degree R = degree r"
    proof -
      have "degree R = degree r2" by (simp only: hR[symmetric]) (simp add: degree_map_poly)
      also have "\<dots> = degree r" unfolding r2_def by (rule natDegree_comp_C_mul_X[OF cnz])
      finally show ?thesis .
    qed
    have di: "(rho-s)*degree r = 1+rho*degree f" by (rule Comp_degree_identity[OF h hsr hr hf])
    have er: "even (degree r)" using Re Rdeg by simp
    have ef: "even (degree f)" using Fe Fdeg by simp
    have "even ((rho-s)*degree r)" using er by simp
    moreover have "odd (1+rho*degree f)" using ef by simp
    ultimately show False using di by simp
  qed
qed

end
