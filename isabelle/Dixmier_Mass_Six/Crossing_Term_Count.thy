theory Crossing_Term_Count
 imports "Crossing_Cut_Formula"
   "Diagonal_Binomial_Face"
begin

lemma crossing_pcompose_power:
 "pcompose (p^k) q=(pcompose p q)^k" for p q::"complex poly"
 by (induction k) (simp_all add: pcompose_mult pcompose_1)

lemma crossing_pcompose_monom:
 "pcompose (monom c n) ([:0,1:]^rho)=monom c (n*rho)" for c::complex
proof -
 have power: "(([:0,1:]::complex poly)^rho)^n=[:0,1:]^(n*rho)"
   by (simp only: power_mult[symmetric] mult.commute)
 show ?thesis
   by (simp add: monom_altdef pcompose_smult crossing_pcompose_power pcompose_pCons power)
qed

lemma crossing_expand_reconstruction:
 "pcompose r ([:0,1:]^rho)=(\<Sum>n\<le>degree r. monom (coeff r n)(n*rho))" for r::"complex poly"
proof -
 have "r=(\<Sum>n\<le>degree r. monom (coeff r n)n)" using poly_as_sum_of_monoms[of r] by simp
 then have evaluated: "pcompose r ([:0,1:]^rho)=pcompose (\<Sum>n\<le>degree r. monom (coeff r n)n) ([:0,1:]^rho)"
  by (rule arg_cong)
 show ?thesis by (simp only: evaluated pcompose_sum crossing_pcompose_monom)
qed

lemma crossing_expand_coeff:
 fixes r::"complex poly"
 assumes rho: "0<rho"
 shows "coeff(pcompose r ([:0,1:]^rho))(n*rho)=coeff r n"
proof -
 have indices: "k*rho=n*rho \<longleftrightarrow> n=k" for k using rho by auto
 have coefficient: "coeff(pcompose r ([:0,1:]^rho))(n*rho)=
 (\<Sum>k\<le>degree r. if n=k then coeff r k else 0)"
  by (simp only: crossing_expand_reconstruction coeff_sum coeff_monom indices)
 show ?thesis
 proof (cases "n\<le>degree r")
  case True then show ?thesis by (simp add: coefficient sum.delta')
 next
  case False
  have zero: "coeff r n=0" by (rule coeff_eq_0) (use False in arith)
  show ?thesis using False zero by (simp add: coefficient sum.delta')
 qed
qed

lemma support_expand_eq:
 fixes r::"complex poly"
 assumes rho: "0<rho"
 shows "sparse_support(pcompose r ([:0,1:]^rho))=(\<lambda>n. n*rho) ` sparse_support r"
proof (rule Set.set_eqI)
 fix n
 show "n\<in>sparse_support(pcompose r ([:0,1:]^rho)) \<longleftrightarrow> n\<in>(\<lambda>k. k*rho) ` sparse_support r"
 proof
  assume member: "n\<in>sparse_support(pcompose r ([:0,1:]^rho))"
  have coefficient: "coeff(pcompose r ([:0,1:]^rho)) n=
    (\<Sum>k\<le>degree r. if n=k*rho then coeff r k else 0)"
    by (simp only: crossing_expand_reconstruction coeff_sum coeff_monom eq_commute)
  have nonzero: "(\<Sum>k\<le>degree r. if n=k*rho then coeff r k else 0)\<noteq>0"
    using member by (simp add: sparse_support_def coefficient)
  have exists: "\<exists>k\<le>degree r. n=k*rho \<and> coeff r k\<noteq>0"
  proof (rule ccontr)
   assume "\<not>(\<exists>k\<le>degree r. n=k*rho \<and> coeff r k\<noteq>0)"
   then have zero: "\<And>k. k\<le>degree r \<Longrightarrow> (if n=k*rho then coeff r k else 0)=0" by auto
   have "(\<Sum>k\<le>degree r. if n=k*rho then coeff r k else 0)=0" by (rule sum.neutral) (use zero in auto)
   then show False using nonzero by contradiction
  qed
  then show "n\<in>(\<lambda>k. k*rho) ` sparse_support r" by auto
 next
  assume "n\<in>(\<lambda>k. k*rho) ` sparse_support r"
  then obtain k where k: "k\<in>sparse_support r" and n: "n=k*rho" by blast
  show "n\<in>sparse_support(pcompose r ([:0,1:]^rho))" using k by (simp add: n crossing_expand_coeff[OF rho])
 qed
qed

lemma termCount_expand_eq:
 assumes rho: "0<rho"
 shows "termCount(pcompose(r::complex poly)([:0,1:]^rho))=termCount r"
proof -
 have injective: "inj_on (\<lambda>n::nat. n*rho) (sparse_support r)" using rho by (auto simp: inj_on_def)
 show ?thesis by (simp only: termCount_def support_expand_eq[OF rho] card_image[OF injective])
qed

lemma support_X_pow_mul_eq:
 "sparse_support([:0,1:]^k*(r::complex poly))=(\<lambda>n. k+n) ` sparse_support r"
proof -
 have X: "[:0,1:]^k=monom (1::complex) k" by (simp add: monom_altdef)
 show ?thesis
 proof (rule Set.set_eqI)
   fix x
   show "x\<in>sparse_support([:0,1:]^k*r) \<longleftrightarrow> x\<in>(\<lambda>n. k+n) ` sparse_support r"
   proof
     assume member: "x\<in>sparse_support([:0,1:]^k*r)"
     have lower: "k\<le>x" and coefficient: "coeff r (x-k)\<noteq>0"
       using member by (auto simp: X sparse_support_def coeff_monom_mult mult_1_left split: if_splits)
     have eq: "x=k+(x-k)" using lower by arith
     show "x\<in>(\<lambda>n. k+n) ` sparse_support r"
       by (rule image_eqI[where x="x-k"]) (use eq coefficient in \<open>auto simp: sparse_support_def\<close>)
   next
     assume member: "x\<in>(\<lambda>n. k+n) ` sparse_support r"
     then obtain n where n: "n\<in>sparse_support r" and x: "x=k+n" by (rule imageE)
     show "x\<in>sparse_support([:0,1:]^k*r)"
       using n by (simp add: x X sparse_support_def coeff_monom_mult)
   qed
 qed
qed

lemma termCount_X_pow_mul_eq:
 "termCount([:0,1:]^k*(r::complex poly))=termCount r"
proof -
 have injective: "inj_on (\<lambda>n::nat. k+n) (sparse_support r)" by (simp add: inj_on_def)
 show ?thesis by (simp only: termCount_def support_X_pow_mul_eq card_image[OF injective])
qed

lemma support_C_mul_eq:
 assumes c: "c\<noteq>0"
 shows "sparse_support([:c:]*(r::complex poly))=sparse_support r"
 using c by (auto simp: sparse_support_def)

lemma termCount_C_mul_eq:
 assumes c: "c\<noteq>0"
 shows "termCount([:c:]*(r::complex poly))=termCount r"
 by (simp only: termCount_def support_C_mul_eq[OF c])

lemma crossingFace_general_termCount_eq:
 fixes T::"complex poly_operator" and mu::complex and r::"complex poly"
 assumes mu: "mu\<noteq>0" and rho: "0<rho"
 and face: "leading_form(int rho)(-int s)T=[:[:mu:]:]*(biv_monom 1 a b*biv_univariate_eval r(biv_monom 1 s rho))^k"
 shows "termCount(cut_poly(int rho)(-int s)T)=termCount(r^k)"
 by (simp only: crossingFace_general_cutPoly[OF face] mult.assoc termCount_C_mul_eq[OF mu] termCount_X_pow_mul_eq termCount_expand_eq[OF rho])

lemma crossingFace_general_termCount_le_mass:
 fixes T::"complex poly_operator" and mu::complex and r::"complex poly"
 assumes T: "T\<in>weyl_algebra" and mu: "mu\<noteq>0" and direction: "s<rho"
 and face: "leading_form(int rho)(-int s)T=[:[:mu:]:]*(biv_monom 1 a b*biv_univariate_eval r(biv_monom 1 s rho))^k"
 shows "termCount(r^k)\<le>weyl_mass T"
proof -
 have rho: "0<rho" using direction by arith
 have eq: "termCount(cut_poly(int rho)(-int s)T)=termCount(r^k)"
  by (rule crossingFace_general_termCount_eq[OF mu rho face])
 have bound: "termCount(cut_poly(int rho)(-int s)T)\<le>weyl_mass T"
  by (rule cutPoly_termCount_le_mass[OF T]) (use direction in simp)
 show ?thesis using eq bound by simp
qed

end
