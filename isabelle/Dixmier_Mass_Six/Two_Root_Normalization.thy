theory Two_Root_Normalization
  imports Six_Term_Complex_Core "Polynomial_Scaling"
begin

lemma six_term_two_roots:
  fixes S :: "complex poly"
  assumes h6: "termCount S = 6" and h1: "coeff S 0 = 1"
    and hrig: "\<And>z :: complex. (\<And>n. n \<in> sparse_support S \<Longrightarrow> z ^ n = 1) \<Longrightarrow> z = 1"
    and ha: "alpha \<noteq> 0" and hab: "alpha \<noteq> beta"
    and ha4: "([:0,1:] - [:alpha:]) ^ 4 dvd S"
    and hb4: "([:0,1:] - [:beta:]) ^ 4 dvd S"
  shows "(\<forall>gamma :: complex. ([:0,1:] - [:gamma:]) ^ 4 dvd S \<longrightarrow>
      gamma = alpha \<or> gamma = beta) \<and>
    (\<exists>c :: complex. c \<noteq> 0 \<and>
      (\<forall>n. Im (coeff (pcompose S [:0,c:]) n) = 0) \<and>
      Im (alpha / c) \<noteq> 0 \<and> beta / c = cnj (alpha / c) \<and>
      norm (alpha / c) ^ 2 = 1)"
proof -
  let ?S1 = "pcompose S [:0,alpha:]"
  have supp: "sparse_support ?S1 = sparse_support S" by (rule support_comp_C_mul_X[OF ha])
  have h61: "termCount ?S1 = 6" using termCount_comp_C_mul_X[OF ha, of S] h6 by simp
  have h11: "coeff ?S1 0 = 1" by (simp add: coeff_comp_C_mul_X h1 poly_0_coeff_0)
  have rigid1: "\<And>z :: complex. (\<And>n. n \<in> sparse_support ?S1 \<Longrightarrow> z ^ n = 1) \<Longrightarrow> z = 1"
    using hrig supp by blast
  have hone: "([:0,1:] - [:1:]) ^ 4 dvd ?S1"
    using pow_dvd_comp_C_mul_X[OF ha, where a=alpha and m=4 and S=S] ha4 ha by simp
  have core: "\<And>gamma. ([:0,1:] - [:gamma:]) ^ 4 dvd S \<Longrightarrow> gamma \<noteq> alpha \<Longrightarrow>
      norm (gamma / alpha) ^ 2 = 1 \<and> (\<forall>n. coeff ?S1 n * (gamma / alpha) ^ n = cnj (coeff ?S1 n))"
  proof -
    fix gamma
    assume hg4: "([:0,1:] - [:gamma:]) ^ 4 dvd S" and hga: "gamma \<noteq> alpha"
    have d: "([:0,1:] - [:gamma / alpha:]) ^ 4 dvd ?S1"
      using pow_dvd_comp_C_mul_X[OF ha, where a=gamma and m=4 and S=S] hg4 by simp
    have ne: "gamma / alpha \<noteq> 1" using ha hga by simp
    show "norm (gamma / alpha) ^ 2 = 1 \<and> (\<forall>n. coeff ?S1 n * (gamma / alpha) ^ n = cnj (coeff ?S1 n))"
      by (rule normSq_eq_one_and_coeff_mul_pow_eq_conj[OF h61 h11 rigid1 hone d ne])
  qed
  have beta_core: "norm (beta / alpha) ^ 2 = 1 \<and> (\<forall>n. coeff ?S1 n * (beta / alpha) ^ n = cnj (coeff ?S1 n))"
    by (rule core[OF hb4]) (use hab in auto)
  have bn: "norm (beta / alpha) ^ 2 = 1" using beta_core by blast
  have bc: "\<And>n. coeff ?S1 n * (beta / alpha) ^ n = cnj (coeff ?S1 n)" using beta_core by blast
  have hb: "beta \<noteq> 0" using bn by auto
  have roots: "\<And>gamma. ([:0,1:] - [:gamma:]) ^ 4 dvd S \<Longrightarrow> gamma = alpha \<or> gamma = beta"
  proof -
    fix gamma
    assume hg4: "([:0,1:] - [:gamma:]) ^ 4 dvd S"
    show "gamma = alpha \<or> gamma = beta"
    proof (cases "gamma = alpha")
      case True
      then show ?thesis by simp
    next
      case False
      have gc: "\<And>n. coeff ?S1 n * (gamma / alpha) ^ n = cnj (coeff ?S1 n)"
        using core[OF hg4 False] by blast
      have ratio: "gamma / beta = 1"
      proof (rule hrig)
        fix n
        assume hn: "n \<in> sparse_support S"
        have coeffnz: "coeff ?S1 n \<noteq> 0" using hn supp by auto
        have eq: "coeff ?S1 n * (gamma / alpha) ^ n = coeff ?S1 n * (beta / alpha) ^ n"
          by (simp only: gc bc)
        have powers: "gamma ^ n = beta ^ n" using eq coeffnz ha by (simp add: power_divide)
        show "(gamma / beta) ^ n = 1" using hb powers by (simp add: power_divide)
      qed
      then have "gamma = beta" using hb by simp
      then show ?thesis by simp
    qed
  qed
  define eta where "eta = csqrt (beta / alpha)"
  have eta_square: "eta ^ 2 = beta / alpha" by (simp add: eta_def)
  have normratio: "norm (beta / alpha) = 1"
    by (rule power2_eq_imp_eq) (use bn in auto)
  have normeta: "norm eta ^ 2 = 1" by (simp add: normratio eta_def)
  have etanz: "eta \<noteq> 0" using hb ha by (simp add: eta_def)
  have etamul: "eta * cnj eta = 1" using complex_norm_square[of eta] normeta by simp
  have cnjeta: "cnj eta = inverse eta" using etamul etanz by (simp add: field_simps)
  have ac: "alpha / (alpha * eta) = cnj eta" using ha etanz by (simp add: cnjeta field_simps)
  have realcoeff: "\<And>n. Im (coeff (pcompose S [:0,alpha * eta:]) n) = 0"
  proof -
    fix n
    have hc: "coeff S n * alpha ^ n * (beta / alpha) ^ n = cnj (coeff S n * alpha ^ n)"
      using bc[of n] by (simp only: coeff_comp_C_mul_X)
    have "cnj (coeff (pcompose S [:0,alpha * eta:]) n) =
        cnj (coeff S n * alpha ^ n) * (cnj eta) ^ n"
      by (simp add: coeff_comp_C_mul_X power_mult_distrib mult.assoc)
    also have "... = coeff S n * alpha ^ n * (beta / alpha) ^ n * (inverse eta) ^ n"
      by (simp only: hc[symmetric] cnjeta)
    also have "... = coeff S n * (alpha * eta) ^ n"
    proof -
      have sq: "(beta / alpha) ^ n = eta ^ n * eta ^ n"
        by (subst eta_square[symmetric]) (simp only: power2_eq_square power_mult_distrib)
      have "coeff S n * alpha ^ n * (beta / alpha) ^ n * (inverse eta) ^ n =
          (coeff S n * alpha ^ n) * ((eta ^ n * eta ^ n) * inverse (eta ^ n))"
        by (simp only: sq power_inverse mult.assoc)
      also have "... = (coeff S n * alpha ^ n) * eta ^ n"
        using etanz by (simp add: mult.assoc)
      also have "... = coeff S n * (alpha * eta) ^ n"
        by (simp only: power_mult_distrib mult.assoc)
      finally show ?thesis .
    qed
    also have "... = coeff (pcompose S [:0,alpha * eta:]) n"
      by (simp only: coeff_comp_C_mul_X)
    finally show "Im (coeff (pcompose S [:0,alpha * eta:]) n) = 0"
      by (simp only: cnj_eq_self_iff_Im_zero)
  qed
  have nonreal: "Im (alpha / (alpha * eta)) \<noteq> 0"
  proof
    assume "Im (alpha / (alpha * eta)) = 0"
    then have im: "Im eta = 0" by (simp add: ac)
    have re: "Re eta ^ 2 = 1" using normeta by (simp add: norm_sq_Re_Im im)
    have "eta ^ 2 = 1" by (simp add: complex_eq_iff Re_power2 Im_power2 im re)
    then have "beta / alpha = 1" using eta_square by simp
    then have "beta = alpha" using ha by simp
    with hab show False by simp
  qed
  have conjugates: "beta / (alpha * eta) = cnj (alpha / (alpha * eta))"
  proof -
    have "beta / (alpha * eta) = (beta / alpha) / eta" by simp
    also have "... = eta" by (simp only: eta_square[symmetric]) (simp add: power2_eq_square etanz)
    also have "... = cnj (alpha / (alpha * eta))" by (simp add: ac)
    finally show ?thesis .
  qed
  have normalized: "norm (alpha / (alpha * eta)) ^ 2 = 1"
    by (simp add: ac normeta)
  show ?thesis
  proof (rule conjI)
    show "\<forall>gamma :: complex. ([:0,1:] - [:gamma:]) ^ 4 dvd S \<longrightarrow> gamma = alpha \<or> gamma = beta"
      using roots by blast
    show "\<exists>c :: complex. c \<noteq> 0 \<and> (\<forall>n. Im (coeff (pcompose S [:0,c:]) n) = 0) \<and>
      Im (alpha / c) \<noteq> 0 \<and> beta / c = cnj (alpha / c) \<and> norm (alpha / c) ^ 2 = 1"
      by (rule exI[of _ "alpha * eta"]) (use ha etanz realcoeff nonreal conjugates normalized in auto)
  qed
qed

end
