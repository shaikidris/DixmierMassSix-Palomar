theory Word_Span_Signed_Bounds
  imports Signed_Weight_Filtration
begin

lemma span_signed_weight_abs_le:
  fixes v :: "'i \<Rightarrow> complex bivariate"
  assumes hv: "\<And>i u. u\<in>biv_support (v i) \<Longrightarrow> abs (pair_weight rho sigma u)\<le>B"
    and hp: "p\<in>joseph_bivariate.span (range v)"
  shows "\<And>u. u\<in>biv_support p \<Longrightarrow> abs (pair_weight rho sigma u)\<le>B"
proof -
  have hz: "\<forall>u. B<abs (pair_weight rho sigma u) \<longrightarrow> biv_coeff p (fst u) (snd u)=0"
    using hp
  proof (induction rule: joseph_bivariate.span_induct_alt)
    case base
    show ?case by simp
  next
    case (step c x y)
    obtain i where xi: "x=v i" using step.hyps(1) by blast
    have xz: "biv_coeff x (fst u) (snd u)=0"
      if excessive: "B<abs (pair_weight rho sigma u)" for u
    proof (rule ccontr)
      assume "biv_coeff x (fst u) (snd u)\<noteq>0"
      then have "u\<in>biv_support (v i)" by (simp add: xi biv_support_def)
      then have "abs (pair_weight rho sigma u)\<le>B" by (rule hv)
      then show False using excessive by arith
    qed
    show ?case using step.IH xz by (auto simp: joseph_biv_scale_def)
  qed
  fix u assume mem: "u\<in>biv_support p"
  show "abs (pair_weight rho sigma u)\<le>B"
  proof (rule ccontr)
    assume "\<not>abs (pair_weight rho sigma u)\<le>B"
    then have "B<abs (pair_weight rho sigma u)" by arith
    then have "biv_coeff p (fst u) (snd u)=0" using hz by blast
    then show False using mem by (simp add: biv_support_def)
  qed
qed

end
