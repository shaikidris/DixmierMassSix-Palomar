theory Six_Term_Complex_Core
  imports Complex_Norm_Square_Bridge
    "Exponential_Quadratic_Rigidity"
    "Vanishing_Moments"
begin

lemma normSq_eq_one_and_coeff_mul_pow_eq_conj:
  fixes S :: "complex poly"
  assumes h6: "termCount S = 6" and h1: "coeff S 0 = 1"
    and hrig: "\<And>z :: complex. (\<And>n. n \<in> sparse_support S \<Longrightarrow> z ^ n = 1) \<Longrightarrow> z = 1"
    and hone: "([:0,1:] - [:1:]) ^ 4 dvd S"
    and hbeta: "([:0,1:] - [:beta:]) ^ 4 dvd S" and hb1: "beta \<noteq> 1"
  shows "norm beta ^ 2 = 1 \<and> (\<forall>n. coeff S n * beta ^ n = cnj (coeff S n))"
proof -
  let ?N = "sparse_support S"
  let ?D = "\<lambda>n. (\<Prod>m\<in>?N-{n}. (of_nat n - of_nat m :: complex))"
  have fin: "finite ?N" by simp
  have h0: "0 \<in> ?N" using h1 by simp
  have cardN: "card ?N = 6" using h6 by (simp add: termCount_def)
  have hb0: "beta \<noteq> 0"
  proof
    assume "beta = 0"
    then obtain q where q: "S = ([:0,1:] :: complex poly)^4 * q"
      using hbeta by (auto simp: dvd_def)
    have "poly S 0 = 0" by (simp add: q poly_mult poly_power)
    with h1 show False by (simp add: poly_0_coeff_0)
  qed
  have Dnz: "\<And>n. n \<in> ?N \<Longrightarrow> ?D n \<noteq> 0" by auto
  have Dcnj: "\<And>n. cnj (?D n) = ?D n" by simp
  have ex: "\<exists>A B :: complex. \<forall>n\<in>?N. coeff S n * ?D n = A + B * of_nat n"
  proof (rule exists_affine_of_moments[OF fin cardN h0])
    fix g :: "complex poly"
    assume "degree g < 4"
    then show "(\<Sum>m\<in>?N. coeff S m * poly g (of_nat m)) = 0"
      using moment_eq_zero[OF hone] by simp
  qed
  then obtain A B where AB: "\<And>n. n \<in> ?N \<Longrightarrow> coeff S n * ?D n = A + B * of_nat n" by blast
  have ex': "\<exists>A' B' :: complex. \<forall>n\<in>?N. (coeff S n * beta ^ n) * ?D n = A' + B' * of_nat n"
  proof (rule exists_affine_of_moments[OF fin cardN h0])
    fix g :: "complex poly"
    assume "degree g < 4"
    then show "(\<Sum>m\<in>?N. coeff S m * beta ^ m * poly g (of_nat m)) = 0"
      by (rule moment_eq_zero[OF hbeta])
  qed
  then obtain A' B' where AB': "\<And>n. n \<in> ?N \<Longrightarrow> (coeff S n * beta ^ n) * ?D n = A' + B' * of_nat n" by blast
  have A: "A = ?D 0" using AB[OF h0] h1 by simp
  have A': "A' = ?D 0" using AB'[OF h0] h1 by simp
  let ?r = "Re (?D 0)"
  have rD: "of_real ?r = ?D 0" using real_Re_of_cnj_fixed[OF Dcnj] .
  have rnz: "?r \<noteq> 0"
  proof
    assume rz: "?r = 0"
    have "?D 0 = 0" using rD rz by (metis of_real_0)
    with Dnz[OF h0] show False by contradiction
  qed
  have SD: "\<And>n. n \<in> ?N \<Longrightarrow> coeff S n * ?D n = of_real ?r + B * of_nat n"
    using AB A rD by simp
  have rel: "\<And>n. n \<in> ?N \<Longrightarrow>
    beta ^ n * (of_real ?r + B * of_nat n) = of_real ?r + B' * of_nat n"
  proof -
    fix n
    assume hn: "n \<in> ?N"
    have "beta ^ n * (of_real ?r + B * of_nat n) = (coeff S n * beta ^ n) * ?D n"
      unfolding SD[OF hn, symmetric] by algebra
    also have "... = of_real ?r + B' * of_nat n" using AB'[OF hn] A' rD by simp
    finally show "beta ^ n * (of_real ?r + B * of_nat n) = of_real ?r + B' * of_nat n" .
  qed
  have NR: "\<And>n. n \<in> ?N \<Longrightarrow>
    (norm beta ^ 2) ^ n * (?r ^ 2 + 2 * ?r * Re B * of_nat n +
      (Re B ^ 2 + Im B ^ 2) * (of_nat n :: real) ^ 2) =
    ?r ^ 2 + 2 * ?r * Re B' * of_nat n + (Re B' ^ 2 + Im B' ^ 2) * (of_nat n :: real) ^ 2"
  proof -
    fix n
    assume hn: "n \<in> ?N"
    have "norm (beta ^ n * (of_real ?r + B * of_nat n)) ^ 2 =
      norm (of_real ?r + B' * of_nat n) ^ 2" using rel[OF hn] by simp
    then show "(norm beta ^ 2) ^ n * (?r ^ 2 + 2 * ?r * Re B * of_nat n +
      (Re B ^ 2 + Im B ^ 2) * (of_nat n :: real) ^ 2) =
      ?r ^ 2 + 2 * ?r * Re B' * of_nat n + (Re B' ^ 2 + Im B' ^ 2) * (of_nat n :: real) ^ 2"
      by (simp only: norm_sq_mult norm_sq_power norm_sq_affine)
  qed
  let ?R = "(of_nat :: nat \<Rightarrow> real) ` ?N"
  have finR: "finite ?R" by simp
  have cardR: "card ?R = 6"
    using cardN by (simp add: card_image inj_on_def)
  have normone: "norm beta ^ 2 = 1"
  proof (rule ccontr)
    assume notone: "norm beta ^ 2 \<noteq> 1"
    have pos: "0 < norm beta ^ 2" using hb0 by simp
    have tau: "ln (norm beta ^ 2) \<noteq> 0" using pos notone by simp
    have vanish: "?r ^ 2 = 0 \<and> 2 * ?r * Re B = 0 \<and> Re B ^ 2 + Im B ^ 2 = 0"
    proof (rule expQuad_coeffs_eq_zero[OF tau finR])
      show "6 \<le> card ?R" using cardR by simp
      fix t
      assume "t \<in> ?R"
      then obtain n where hn: "n \<in> ?N" and t: "t = of_nat n" by blast
      have exponential: "exp (ln (norm beta ^ 2) * of_nat n) = (norm beta ^ 2) ^ n"
        using pos by (simp add: exp_of_nat2_mult)
      show "exp (ln (norm beta ^ 2) * t) * (?r ^ 2 + 2 * ?r * Re B * t + (Re B ^ 2 + Im B ^ 2) * t ^ 2) =
        ?r ^ 2 + 2 * ?r * Re B' * t + (Re B' ^ 2 + Im B' ^ 2) * t ^ 2"
        using NR[OF hn] by (simp only: t exponential)
    qed
    then show False using rnz by simp
  qed
  have Q: "\<And>t. t \<in> ?R \<Longrightarrow>
    0 + (2 * ?r * (Re B - Re B')) * t +
      ((Re B ^ 2 + Im B ^ 2) - (Re B' ^ 2 + Im B' ^ 2)) * t ^ 2 = 0"
  proof -
    fix t
    assume "t \<in> ?R"
    then obtain n where hn: "n \<in> ?N" and t: "t = of_nat n" by blast
    have eq: "?r ^ 2 + 2 * ?r * Re B * t + (Re B ^ 2 + Im B ^ 2) * t ^ 2 =
      ?r ^ 2 + 2 * ?r * Re B' * t + (Re B' ^ 2 + Im B' ^ 2) * t ^ 2"
      using NR[OF hn] normone by (simp add: t)
    show "0 + (2 * ?r * (Re B - Re B')) * t +
      ((Re B ^ 2 + Im B ^ 2) - (Re B' ^ 2 + Im B' ^ 2)) * t ^ 2 = 0"
    proof -
      have "0 + (2 * ?r * (Re B - Re B')) * t +
          ((Re B ^ 2 + Im B ^ 2) - (Re B' ^ 2 + Im B' ^ 2)) * t ^ 2 =
        (?r ^ 2 + 2 * ?r * Re B * t + (Re B ^ 2 + Im B ^ 2) * t ^ 2) -
        (?r ^ 2 + 2 * ?r * Re B' * t + (Re B' ^ 2 + Im B' ^ 2) * t ^ 2)" by algebra
      also have "... = 0" using eq by simp
      finally show ?thesis .
    qed
  qed
  have coefficients: "0 = (0::real) \<and> 2 * ?r * (Re B - Re B') = 0 \<and>
    (Re B ^ 2 + Im B ^ 2) - (Re B' ^ 2 + Im B' ^ 2) = 0"
    by (rule quadratic_eq_zero_of_three_zeros[OF finR _ Q]) (simp add: cardR)
  have re: "Re B' = Re B" using coefficients rnz by auto
  have imsq: "Im B' ^ 2 = Im B ^ 2" using coefficients re by simp
  have imcases: "Im B' = Im B \<or> Im B' = - Im B" using imsq by (simp only: power2_eq_iff)
  have conjcoeff: "\<forall>n. coeff S n * beta ^ n = cnj (coeff S n)"
  proof (cases "Im B' = Im B")
    case True
    have BB: "B' = B" using re True by (simp add: complex_eq_iff)
    have "beta = 1"
    proof (rule hrig)
      fix n
      assume hn: "n \<in> ?N"
      have nz: "of_real ?r + B * of_nat n \<noteq> 0"
        using SD[OF hn] Dnz[OF hn] hn by auto
      show "beta ^ n = 1" using rel[OF hn] BB nz by simp
    qed
    with hb1 show ?thesis by simp
  next
    case False
    have BB: "B' = cnj B" using re imcases False by (simp add: complex_eq_iff)
    show ?thesis
    proof
      fix n
      show "coeff S n * beta ^ n = cnj (coeff S n)"
      proof (cases "n \<in> ?N")
        case True
        have eq: "(coeff S n * beta ^ n) * ?D n = cnj (coeff S n) * ?D n"
        proof -
          have "(coeff S n * beta ^ n) * ?D n = beta ^ n * (coeff S n * ?D n)" by algebra
          also have "... = of_real ?r + B' * of_nat n" using SD[OF True] rel[OF True] by simp
          also have "... = cnj (of_real ?r + B * of_nat n)" by (simp add: BB)
          also have "... = cnj (coeff S n) * ?D n"
            by (simp only: SD[OF True, symmetric] complex_cnj_mult Dcnj)
          finally show ?thesis .
        qed
        show ?thesis using eq Dnz[OF True] by simp
      next
        case False
        then show ?thesis by simp
      qed
    qed
  qed
  show ?thesis using normone conjcoeff by simp
qed

end
