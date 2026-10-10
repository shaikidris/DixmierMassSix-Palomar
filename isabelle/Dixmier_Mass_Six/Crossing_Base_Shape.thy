theory Crossing_Base_Shape
  imports Crossing_Base_Lattice "Bivariate_Universal"
begin

definition biv_univariate_eval :: "complex poly \<Rightarrow> complex bivariate \<Rightarrow> complex bivariate" where
  "biv_univariate_eval A W=poly (map_poly (\<lambda>c. [:[:c:]:]) A) W"

lemma biv_univariate_eval_hom:
  "coefficient_hom (\<lambda>A. biv_univariate_eval A W)"
proof -
  have coeff_hom: "coefficient_hom (\<lambda>c::complex. [:[:c:]:])"
    by (simp add: coefficient_hom_def one_pCons)
  have "coefficient_hom ((\<lambda>p. poly p W) \<circ> map_poly (\<lambda>c::complex. [:[:c:]:]))"
    by (rule coefficient_hom_comp[OF coefficient_hom_poly_eval coefficient_hom_map_poly[OF coeff_hom]])
  then show ?thesis by (simp add: biv_univariate_eval_def[abs_def] comp_def)
qed

lemma biv_univariate_eval_monom:
  "biv_univariate_eval (monom c t) W=biv_monom c 0 0*W^t"
  by (simp add: biv_univariate_eval_def map_poly_monom poly_monom biv_monom_def monom_0)

lemma biv_univariate_eval_const [simp]:
  "biv_univariate_eval [:c:] W=biv_monom c 0 0"
  using biv_univariate_eval_monom[of c 0 W] by (simp add: monom_0)

lemma biv_univariate_eval_sum:
  "biv_univariate_eval (\<Sum>u\<in>S. f u) W=(\<Sum>u\<in>S. biv_univariate_eval (f u) W)"
  by (rule coefficient_hom_sum[OF biv_univariate_eval_hom])

lemma crossing_base_monomial:
  "biv_monom 1 a b*(biv_monom c 0 0*(biv_monom 1 s rho)^t)=biv_monom c (a+s*t) (b+rho*t)"
  by (simp add: biv_monom_def monom_power mult_monom algebra_simps)

lemma crossing_base_shape_with_occupied_base:
  fixes R::"complex bivariate" and rho s::nat and m::int
  assumes s: "0<s" and direction: "s<rho" and coprime: "coprime rho s"
    and nonzero: "R\<noteq>0"
    and homogeneous: "\<And>d. d\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) d=m"
  shows "\<exists>a b::nat. \<exists>r::complex poly. coeff r 0\<noteq>0 \<and> (a,b)\<in>biv_support R \<and>
    (\<forall>d\<in>biv_support R. \<exists>t::nat. d=(a+s*t,b+rho*t)) \<and>
    R=biv_monom 1 a b*biv_univariate_eval r (biv_monom 1 s rho)"
proof -
  obtain a b where base: "(a,b)\<in>biv_support R"
    and ray: "\<forall>d\<in>biv_support R. \<exists>t::nat. d=(a+s*t,b+rho*t)"
    using crossing_base_support_ray[OF s direction coprime nonzero homogeneous] by blast
  let ?S = "biv_support R"
  let ?tau = "\<lambda>d. SOME t::nat. d=(a+s*t,b+rho*t)"
  have tau: "\<And>d. d\<in>?S \<Longrightarrow> d=(a+s*?tau d,b+rho*?tau d)"
    by (rule someI_ex) (use ray in blast)
  let ?r = "\<Sum>d\<in>?S. monom (biv_coeff R (fst d) (snd d)) (?tau d)"
  have tau_base: "?tau (a,b)=0"
  proof -
    have "a=a+s*?tau (a,b)" using arg_cong[OF tau[OF base], where f=fst] by simp
    then have "s*?tau (a,b)=0" by arith
    then show ?thesis using s by simp
  qed
  have tau_zero: "\<And>d. d\<in>?S \<Longrightarrow> ?tau d=0 \<Longrightarrow> d=(a,b)"
  proof -
    fix d assume d: "d\<in>?S" and zero: "?tau d=0"
    show "d=(a,b)" using tau[OF d] by (simp only: zero; simp)
  qed
  have coeff0: "coeff ?r 0=biv_coeff R a b"
  proof -
    have pointwise: "\<And>d. d\<in>?S \<Longrightarrow>
      coeff (monom (biv_coeff R (fst d) (snd d)) (?tau d)) 0=
      (if d=(a,b) then biv_coeff R a b else 0)"
    proof -
      fix d assume d: "d\<in>?S"
      show "coeff (monom (biv_coeff R (fst d) (snd d)) (?tau d)) 0=
        (if d=(a,b) then biv_coeff R a b else 0)"
      proof (cases "d=(a,b)")
        case True
        show ?thesis by (simp only: True tau_base; simp add: coeff_monom)
      next
        case False
        have nonzero: "?tau d\<noteq>0" using tau_zero[OF d] False by blast
        show ?thesis using nonzero False by (simp add: coeff_monom)
      qed
    qed
    have "(\<Sum>d\<in>?S. coeff (monom (biv_coeff R (fst d) (snd d)) (?tau d)) 0)=
      (\<Sum>d\<in>?S. if d=(a,b) then biv_coeff R a b else 0)"
      by (rule sum.cong) (use pointwise in auto)
    also have "\<dots>=biv_coeff R a b"
      by (simp only: sum.delta[OF finite_biv_support] base if_True)
    finally have "(\<Sum>d\<in>?S. coeff (monom (biv_coeff R (fst d) (snd d)) (?tau d)) 0)=biv_coeff R a b" .
    then show ?thesis by (simp add: coeff_sum)
  qed
  have base_nonzero: "biv_coeff R a b\<noteq>0" using base by (simp add: biv_support_def)
  have coeff_ne: "coeff ?r 0\<noteq>0" using base_nonzero by (simp only: coeff0; simp)
  have reconstruction: "R=(\<Sum>d\<in>?S. biv_monom (biv_coeff R (fst d) (snd d)) (fst d) (snd d))"
    using biv_reconstruct[of R] by simp
  have shape: "R=biv_monom 1 a b*biv_univariate_eval ?r (biv_monom 1 s rho)"
  proof -
    have terms: "\<And>d. d\<in>?S \<Longrightarrow>
      biv_monom (biv_coeff R (fst d) (snd d)) (fst d) (snd d)=
      biv_monom 1 a b*biv_univariate_eval (monom (biv_coeff R (fst d) (snd d)) (?tau d)) (biv_monom 1 s rho)"
    proof -
      fix d assume d: "d\<in>?S"
      have pair: "d=(a+s*?tau d,b+rho*?tau d)" by (rule tau[OF d])
      have first: "fst d=a+s*?tau d" using arg_cong[OF pair, of fst] by simp
      have second: "snd d=b+rho*?tau d" using arg_cong[OF pair, of snd] by simp
      show "biv_monom (biv_coeff R (fst d) (snd d)) (fst d) (snd d)=
        biv_monom 1 a b*biv_univariate_eval (monom (biv_coeff R (fst d) (snd d)) (?tau d)) (biv_monom 1 s rho)"
        by (simp only: biv_univariate_eval_monom crossing_base_monomial first second)
    qed
    have "R=(\<Sum>d\<in>?S. biv_monom 1 a b*biv_univariate_eval (monom (biv_coeff R (fst d) (snd d)) (?tau d)) (biv_monom 1 s rho))"
      using reconstruction by (intro trans[OF reconstruction] sum.cong) (use terms in auto)
    also have "\<dots>=biv_monom 1 a b*biv_univariate_eval ?r (biv_monom 1 s rho)"
      by (simp add: biv_univariate_eval_sum sum_distrib_left)
    finally show ?thesis .
  qed
  show ?thesis by (intro exI[of _ a] exI[of _ b] exI[of _ ?r]) (use coeff_ne base ray shape in auto)
qed

lemma crossing_base_shape:
  fixes R::"complex bivariate" and rho s::nat and m::int
  assumes s: "0<s" and direction: "s<rho" and coprime: "coprime rho s"
    and nonzero: "R\<noteq>0"
    and homogeneous: "\<And>d. d\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) d=m"
  shows "\<exists>a b::nat. \<exists>r::complex poly. coeff r 0\<noteq>0 \<and>
    (\<forall>d\<in>biv_support R. \<exists>t::nat. d=(a+s*t,b+rho*t)) \<and>
    R=biv_monom 1 a b*biv_univariate_eval r (biv_monom 1 s rho)"
  using crossing_base_shape_with_occupied_base[OF s direction coprime nonzero homogeneous] by blast

lemma biv_univariate_eval_mult:
  "biv_univariate_eval (A*B) W=biv_univariate_eval A W*biv_univariate_eval B W"
  using biv_univariate_eval_hom[of W] by (simp add: coefficient_hom_def one_pCons)

lemma biv_univariate_eval_smult:
  "biv_univariate_eval (smult c A) W=biv_monom c 0 0*biv_univariate_eval A W"
proof -
  have scalar_product: "[:c:]*A=smult c A" by simp
  show ?thesis using biv_univariate_eval_mult[where A="[:c:]" and B=A and W=W]
    by (simp only: scalar_product biv_univariate_eval_const)
qed

lemma crossing_base_normalized_shape:
  fixes R::"complex bivariate" and rho s::nat and m::int
  assumes s: "0<s" and direction: "s<rho" and coprime: "coprime rho s"
    and nonzero: "R\<noteq>0"
    and homogeneous: "\<And>d. d\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) d=m"
  shows "\<exists>a b::nat. \<exists>c::complex. \<exists>r::complex poly. c\<noteq>0 \<and> coeff r 0=1 \<and>
    (\<forall>d\<in>biv_support R. \<exists>t::nat. d=(a+s*t,b+rho*t)) \<and>
    R=biv_monom c 0 0*(biv_monom 1 a b*biv_univariate_eval r (biv_monom 1 s rho))"
proof -
  obtain a b r where coeff: "coeff r 0\<noteq>0"
    and ray: "\<forall>d\<in>biv_support R. \<exists>t::nat. d=(a+s*t,b+rho*t)"
    and shape: "R=biv_monom 1 a b*biv_univariate_eval r (biv_monom 1 s rho)"
    using crossing_base_shape[OF s direction coprime nonzero homogeneous] by blast
  let ?c = "coeff r 0"
  let ?rn = "[:inverse ?c:]*r"
  have normalized: "coeff ?rn 0=1" using coeff by (simp add: coeff_mult)
  have scalar: "biv_monom ?c 0 0*biv_monom (inverse ?c) 0 0=1"
    using coeff by (simp add: biv_mult_monom biv_monom_def monom_0 one_pCons)
  have normalized_eval: "biv_univariate_eval ?rn (biv_monom 1 s rho)=
    biv_monom (inverse ?c) 0 0*biv_univariate_eval r (biv_monom 1 s rho)"
    by (simp only: biv_univariate_eval_mult biv_univariate_eval_const)
  have normalized_shape: "R=biv_monom ?c 0 0*(biv_monom 1 a b*biv_univariate_eval ?rn (biv_monom 1 s rho))"
  proof -
    have "R=biv_monom 1 a b*biv_univariate_eval r (biv_monom 1 s rho)" by (rule shape)
    also have "\<dots>=(biv_monom ?c 0 0*biv_monom (inverse ?c) 0 0)*
      (biv_monom 1 a b*biv_univariate_eval r (biv_monom 1 s rho))"
      by (simp only: scalar; simp)
    also have "\<dots>=biv_monom ?c 0 0*(biv_monom 1 a b*
      (biv_monom (inverse ?c) 0 0*biv_univariate_eval r (biv_monom 1 s rho)))"
      by (simp only: mult_ac)
    finally show ?thesis by (simp only: normalized_eval)
  qed
  show ?thesis by (intro exI[of _ a] exI[of _ b] exI[of _ ?c] exI[of _ ?rn])
    (use coeff normalized ray normalized_shape in auto)
qed

end
