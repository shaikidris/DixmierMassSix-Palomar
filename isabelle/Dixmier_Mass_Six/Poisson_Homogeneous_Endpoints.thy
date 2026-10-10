theory Poisson_Homogeneous_Endpoints
  imports Poisson_Endpoint_Maximizers
begin

definition perp_weight :: "int \<Rightarrow> int \<Rightarrow> int\<times>int" where
  "perp_weight rho sigma=(sigma,-rho)"

lemma exponent_eq_of_weights_eq_of_perp_eq:
  fixes rho sigma :: int and d e :: "nat\<times>nat"
  assumes nonzero: "rho\<noteq>0 \<or> sigma\<noteq>0"
    and original: "pair_weight rho sigma d=pair_weight rho sigma e"
    and perpendicular: "pair_weight sigma (-rho) d=pair_weight sigma (-rho) e"
  shows "d=e"
proof -
  let ?dx = "int(fst d)-int(fst e)"
  let ?dy = "int(snd d)-int(snd e)"
  have first: "rho*?dx+sigma*?dy=0"
    using original by (simp add: pair_weight_def algebra_simps)
  have second: "sigma*?dx-rho*?dy=0"
    using perpendicular by (simp add: pair_weight_def algebra_simps)
  have dx: "(rho*rho+sigma*sigma)*?dx=0"
  proof -
    have "(rho*rho+sigma*sigma)*?dx=rho*(rho*?dx+sigma*?dy)+sigma*(sigma*?dx-rho*?dy)"
      by (simp add: algebra_simps)
    then show ?thesis using first second by simp
  qed
  have dy: "(rho*rho+sigma*sigma)*?dy=0"
  proof -
    have "(rho*rho+sigma*sigma)*?dy=sigma*(rho*?dx+sigma*?dy)-rho*(sigma*?dx-rho*?dy)"
      by (simp add: algebra_simps)
    then show ?thesis using first second by simp
  qed
  have square_nonzero: "rho*rho+sigma*sigma\<noteq>0"
    using nonzero by (simp add: sum_squares_eq_zero_iff)
  have fst_eq: "fst d=fst e" using dx square_nonzero by auto
  have snd_eq: "snd d=snd e" using dy square_nonzero by auto
  show ?thesis using fst_eq snd_eq by (simp add: prod_eq_iff)
qed

lemma endpoint_pair_weight_neg:
  "pair_weight (-rho) (-sigma) u=-pair_weight rho sigma u"
  by (simp add: pair_weight_def algebra_simps)

lemma endpoint_of_homogeneous_support:
  fixes p :: "complex bivariate" and rho sigma aux_rho aux_sigma degree :: int
  assumes nonzero: "rho\<noteq>0 \<or> sigma\<noteq>0"
    and auxiliary: "(aux_rho,aux_sigma)=(sigma,-rho) \<or> (aux_rho,aux_sigma)=(-sigma,rho)"
    and homogeneous: "\<And>u. u\<in>biv_support p \<Longrightarrow> pair_weight rho sigma u=degree"
    and p_nonzero: "p\<noteq>0"
  shows "\<exists>d\<in>biv_support p.
    (\<forall>x\<in>biv_support p. pair_weight aux_rho aux_sigma x\<le>pair_weight aux_rho aux_sigma d) \<and>
    (\<forall>x\<in>biv_support p. pair_weight aux_rho aux_sigma x=pair_weight aux_rho aux_sigma d \<longrightarrow> x=d)"
proof -
  have support_nonempty: "biv_support p\<noteq>{}" using p_nonzero by simp
  have maximum_member: "Max (pair_weight aux_rho aux_sigma ` biv_support p)\<in>
    pair_weight aux_rho aux_sigma ` biv_support p"
    by (rule Max_in) (use support_nonempty in auto)
  obtain d where d: "d\<in>biv_support p"
    and maximum: "Max (pair_weight aux_rho aux_sigma ` biv_support p)=pair_weight aux_rho aux_sigma d"
    using maximum_member by auto
  have bound: "pair_weight aux_rho aux_sigma x\<le>pair_weight aux_rho aux_sigma d"
    if x: "x\<in>biv_support p" for x
    unfolding maximum[symmetric] by (rule Max_ge) (use x in auto)
  have unique: "x=d" if x: "x\<in>biv_support p"
    and equal: "pair_weight aux_rho aux_sigma x=pair_weight aux_rho aux_sigma d" for x
  proof (rule exponent_eq_of_weights_eq_of_perp_eq[OF nonzero])
    show "pair_weight rho sigma x=pair_weight rho sigma d"
      using homogeneous[OF x] homogeneous[OF d] by simp
    show "pair_weight sigma (-rho) x=pair_weight sigma (-rho) d"
      using auxiliary equal by (auto simp: prod_eq_iff pair_weight_def algebra_simps)
  qed
  show ?thesis using d bound unique by blast
qed

lemma poisson_homogeneous_support_endpoints_collinear:
  fixes rho sigma degreeP degreeQ :: int and p q :: "complex bivariate"
  assumes nonzero: "rho\<noteq>0 \<or> sigma\<noteq>0"
    and p_homogeneous: "\<And>d. d\<in>biv_support p \<Longrightarrow> pair_weight rho sigma d=degreeP"
    and q_homogeneous: "\<And>e. e\<in>biv_support q \<Longrightarrow> pair_weight rho sigma e=degreeQ"
    and p_nonzero: "p\<noteq>0" and q_nonzero: "q\<noteq>0"
    and bracket: "biv_poisson p q=0"
  shows "\<exists>dp dm ep em.
    dp\<in>biv_support p \<and> dm\<in>biv_support p \<and>
    ep\<in>biv_support q \<and> em\<in>biv_support q \<and>
    (\<forall>x\<in>biv_support p. pair_weight sigma (-rho) x\<le>pair_weight sigma (-rho) dp) \<and>
    (\<forall>x\<in>biv_support p. pair_weight sigma (-rho) dm\<le>pair_weight sigma (-rho) x) \<and>
    (\<forall>x\<in>biv_support q. pair_weight sigma (-rho) x\<le>pair_weight sigma (-rho) ep) \<and>
    (\<forall>x\<in>biv_support q. pair_weight sigma (-rho) em\<le>pair_weight sigma (-rho) x) \<and>
    (of_nat(snd dp)::complex)*of_nat(fst ep)-of_nat(fst dp)*of_nat(snd ep)=0 \<and>
    (of_nat(snd dm)::complex)*of_nat(fst em)-of_nat(fst dm)*of_nat(snd em)=0"
proof -
  obtain dp where dp: "dp\<in>biv_support p"
    and dpmax: "\<And>x. x\<in>biv_support p \<Longrightarrow> pair_weight sigma (-rho) x\<le>pair_weight sigma (-rho) dp"
    and dpuniq: "\<And>x. x\<in>biv_support p \<Longrightarrow>
      pair_weight sigma (-rho) x=pair_weight sigma (-rho) dp \<Longrightarrow> x=dp"
    using endpoint_of_homogeneous_support[OF nonzero _ p_homogeneous p_nonzero,
      where aux_rho=sigma and aux_sigma="-rho"] by blast
  obtain ep where ep: "ep\<in>biv_support q"
    and epmax: "\<And>x. x\<in>biv_support q \<Longrightarrow> pair_weight sigma (-rho) x\<le>pair_weight sigma (-rho) ep"
    and epuniq: "\<And>x. x\<in>biv_support q \<Longrightarrow>
      pair_weight sigma (-rho) x=pair_weight sigma (-rho) ep \<Longrightarrow> x=ep"
    using endpoint_of_homogeneous_support[OF nonzero _ q_homogeneous q_nonzero,
      where aux_rho=sigma and aux_sigma="-rho"] by blast
  obtain dm where dm: "dm\<in>biv_support p"
    and dmmax: "\<And>x. x\<in>biv_support p \<Longrightarrow> pair_weight (-sigma) rho x\<le>pair_weight (-sigma) rho dm"
    and dmuniq: "\<And>x. x\<in>biv_support p \<Longrightarrow>
      pair_weight (-sigma) rho x=pair_weight (-sigma) rho dm \<Longrightarrow> x=dm"
    using endpoint_of_homogeneous_support[OF nonzero _ p_homogeneous p_nonzero,
      where aux_rho="-sigma" and aux_sigma=rho] by blast
  obtain em where em: "em\<in>biv_support q"
    and emmax: "\<And>x. x\<in>biv_support q \<Longrightarrow> pair_weight (-sigma) rho x\<le>pair_weight (-sigma) rho em"
    and emuniq: "\<And>x. x\<in>biv_support q \<Longrightarrow>
      pair_weight (-sigma) rho x=pair_weight (-sigma) rho em \<Longrightarrow> x=em"
    using endpoint_of_homogeneous_support[OF nonzero _ q_homogeneous q_nonzero,
      where aux_rho="-sigma" and aux_sigma=rho] by blast
  have plus: "(of_nat(snd dp)::complex)*of_nat(fst ep)-of_nat(fst dp)*of_nat(snd ep)=0"
    by (rule poisson_unique_maximizers_collinear[OF bracket dp ep dpmax epmax dpuniq epuniq])
  have minus: "(of_nat(snd dm)::complex)*of_nat(fst em)-of_nat(fst dm)*of_nat(snd em)=0"
    by (rule poisson_unique_maximizers_collinear[OF bracket dm em dmmax emmax dmuniq emuniq])
  have neg_weight: "pair_weight (-sigma) rho x=-pair_weight sigma (-rho) x" for x
    by (simp add: pair_weight_def algebra_simps)
  have dmmin: "\<forall>x\<in>biv_support p. pair_weight sigma (-rho) dm\<le>pair_weight sigma (-rho) x"
    using dmmax by (simp add: neg_weight)
  have emmin: "\<forall>x\<in>biv_support q. pair_weight sigma (-rho) em\<le>pair_weight sigma (-rho) x"
    using emmax by (simp add: neg_weight)
  show ?thesis using dp dm ep em dpmax dmmin epmax emmin plus minus by blast
qed

end
