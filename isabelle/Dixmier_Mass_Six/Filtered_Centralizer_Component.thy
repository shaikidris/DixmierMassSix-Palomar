theory Filtered_Centralizer_Component
  imports "Finite_Filtered_Spanning"
    "Homogeneous_Centralizer_Line"
begin

lemma filtered_centralizer_component_representative:
  fixes S :: "complex bivariate set" and f :: "complex bivariate"
  assumes S: "joseph_bivariate.subspace S"
    and hf: "weighted_homogeneous rho sigma m f" and hfne: "f\<noteq>0" and hm: "m\<noteq>0"
    and hc: "\<And>p. p\<in>restrictedWeightBelow S rho sigma (b+1) \<Longrightarrow>
      biv_poisson f (weighted_component rho sigma b p)=0"
  shows "\<exists>t\<in>restrictedWeightBelow S rho sigma (b+1).
    \<forall>p\<in>restrictedWeightBelow S rho sigma (b+1). \<exists>c.
      weighted_component rho sigma b p=
        joseph_biv_scale c (weighted_component rho sigma b t)"
proof (cases "\<exists>t\<in>restrictedWeightBelow S rho sigma (b+1). weighted_component rho sigma b t\<noteq>0")
  case True
  then obtain t where t: "t\<in>restrictedWeightBelow S rho sigma (b+1)"
    and nz: "weighted_component rho sigma b t\<noteq>0" by blast
  have ratio: "\<exists>c. weighted_component rho sigma b p=
      joseph_biv_scale c (weighted_component rho sigma b t)"
    if p: "p\<in>restrictedWeightBelow S rho sigma (b+1)" for p
  proof -
    obtain c where c: "weighted_component rho sigma b p=
        [:[:c:]:]*weighted_component rho sigma b t"
      using homogeneous_poisson_centralizer_scalar_ratio[OF hf
        weighted_component_homogeneous weighted_component_homogeneous hfne hm nz hc[OF p] hc[OF t]] by blast
    show ?thesis by (intro exI[of _ c]) (use c in \<open>simp add: joseph_biv_scale_def\<close>)
  qed
  show ?thesis using t ratio by blast
next
  case False
  have z: "0\<in>restrictedWeightBelow S rho sigma (b+1)"
    using S by (auto simp: restrictedWeightBelow_def signedWeightBelow_def joseph_bivariate.subspace_def)
  show ?thesis by (intro bexI[of _ 0] z)
    (use False in \<open>auto simp: joseph_biv_scale_def\<close>)
qed

lemma filtered_centralizer_finrank_le_interval:
  fixes S :: "complex bivariate set" and f :: "complex bivariate"
  assumes S: "joseph_bivariate.subspace S"
    and hf: "weighted_homogeneous rho sigma m f" and hfne: "f\<noteq>0" and hm: "m\<noteq>0"
    and hlo: "\<And>p u. p\<in>S \<Longrightarrow> pair_weight rho sigma u<b \<Longrightarrow>
      biv_coeff p (fst u) (snd u)=0"
    and hhi: "\<And>p u. p\<in>S \<Longrightarrow> b+int N\<le>pair_weight rho sigma u \<Longrightarrow>
      biv_coeff p (fst u) (snd u)=0"
    and hc: "\<And>i p. p\<in>restrictedWeightBelow S rho sigma (b+int i+1) \<Longrightarrow>
      biv_poisson f (weighted_component rho sigma (b+int i) p)=0"
  shows "joseph_bivariate.dim S\<le>N"
proof -
  have bottom: "restrictedWeightBelow S rho sigma b={0}"
    by (rule restrictedWeightBelow_eq_bot_of_lower_bound[OF S hlo])
  have top: "restrictedWeightBelow S rho sigma (b+int N)=S"
    by (rule restrictedWeightBelow_eq_top_of_upper_bound[OF hhi])
  have step: "\<exists>t\<in>restrictedWeightBelow S rho sigma (b+int k+1).
      \<forall>p\<in>restrictedWeightBelow S rho sigma (b+int k+1). \<exists>c.
        weighted_component rho sigma (b+int k) p=
          joseph_biv_scale c (weighted_component rho sigma (b+int k) t)" for k
    by (rule filtered_centralizer_component_representative[OF S hf hfne hm hc])
  show ?thesis using finite_restricted_filtration_rank_le[OF S bottom, of N] step
    by (simp only: top)
qed

lemma filtered_centralizer_finrank_le_abs_interval:
  fixes S :: "complex bivariate set" and f :: "complex bivariate"
  assumes S: "joseph_bivariate.subspace S"
    and hf: "weighted_homogeneous rho sigma m f" and hfne: "f\<noteq>0" and hm: "m\<noteq>0"
    and bound: "\<And>p u. p\<in>S \<Longrightarrow> u\<in>biv_support p \<Longrightarrow>
      abs (pair_weight rho sigma u)\<le>int B"
    and hc: "\<And>b p. p\<in>restrictedWeightBelow S rho sigma (b+1) \<Longrightarrow>
      biv_poisson f (weighted_component rho sigma b p)=0"
  shows "joseph_bivariate.dim S\<le>2*B+1"
proof -
  have lo: "biv_coeff p (fst u) (snd u)=0"
    if "p\<in>S" "pair_weight rho sigma u< -int B" for p u
  proof (rule ccontr)
    assume "biv_coeff p (fst u) (snd u)\<noteq>0"
    then have "u\<in>biv_support p" by (simp add: biv_support_def)
    then have "abs (pair_weight rho sigma u)\<le>int B" by (rule bound[OF that(1)])
    then show False using that(2) by arith
  qed
  have hi: "biv_coeff p (fst u) (snd u)=0"
    if "p\<in>S" "int B+1\<le>pair_weight rho sigma u" for p u
  proof (rule ccontr)
    assume "biv_coeff p (fst u) (snd u)\<noteq>0"
    then have "u\<in>biv_support p" by (simp add: biv_support_def)
    then have "abs (pair_weight rho sigma u)\<le>int B" by (rule bound[OF that(1)])
    then show False using that(2) by arith
  qed
  have bottom: "restrictedWeightBelow S rho sigma (-int B)={0}"
    by (rule restrictedWeightBelow_eq_bot_of_lower_bound[OF S lo])
  have top: "restrictedWeightBelow S rho sigma (-int B+int (2*B+1))=S"
    using restrictedWeightBelow_eq_top_of_upper_bound[OF hi]
    by (simp add: algebra_simps)
  have step: "\<exists>t\<in>restrictedWeightBelow S rho sigma (-int B+int k+1).
      \<forall>p\<in>restrictedWeightBelow S rho sigma (-int B+int k+1). \<exists>c.
        weighted_component rho sigma (-int B+int k) p=
          joseph_biv_scale c (weighted_component rho sigma (-int B+int k) t)" for k
    by (rule filtered_centralizer_component_representative[OF S hf hfne hm hc])
  show ?thesis using finite_restricted_filtration_rank_le[OF S bottom, of "2*B+1"] step
    by (simp only: top)
qed

lemma filtered_centralizer_component_finrank_le_one:
  fixes S :: "complex bivariate set" and f :: "complex bivariate"
  assumes hf: "weighted_homogeneous rho sigma m f"
    and hfne: "f\<noteq>0" and hm: "m\<noteq>0"
    and hc: "\<And>p. p\<in>restrictedWeightBelow S rho sigma (b+1) \<Longrightarrow>
      biv_poisson f (weighted_component rho sigma b p)=0"
  shows "joseph_bivariate.dim (weighted_component rho sigma b ` restrictedWeightBelow S rho sigma (b+1))\<le>1"
proof -
  let ?A = "weighted_component rho sigma b ` restrictedWeightBelow S rho sigma (b+1)"
  show ?thesis
  proof (cases "\<exists>h\<in>?A. h\<noteq>0")
    case True
    then obtain h where hA: "h\<in>?A" and hnz: "h\<noteq>0" by blast
    obtain q where q: "q\<in>restrictedWeightBelow S rho sigma (b+1)"
      and heq: "h=weighted_component rho sigma b q" using hA by blast
    have hhom: "weighted_homogeneous rho sigma b h"
      by (simp only: heq) (rule weighted_component_homogeneous)
    have hcentral: "biv_poisson f h=0" by (simp only: heq) (rule hc[OF q])
    have subset: "?A\<subseteq>joseph_bivariate.span {h}"
    proof
      fix g assume gA: "g\<in>?A"
      obtain p where p: "p\<in>restrictedWeightBelow S rho sigma (b+1)"
        and geq: "g=weighted_component rho sigma b p" using gA by blast
      have ghom: "weighted_homogeneous rho sigma b g"
        by (simp only: geq) (rule weighted_component_homogeneous)
      have gcentral: "biv_poisson f g=0" by (simp only: geq) (rule hc[OF p])
      obtain c where ratio: "g=[:[:c:]:]*h"
        using homogeneous_poisson_centralizer_scalar_ratio[OF hf ghom hhom hfne hm hnz gcentral hcentral] by blast
      have scale: "g=joseph_biv_scale c h" using ratio by (simp add: joseph_biv_scale_def)
      show "g\<in>joseph_bivariate.span {h}"
        using joseph_bivariate.span_scale[OF joseph_bivariate.span_base[of h "{h}"], of c] scale by simp
    qed
    show ?thesis using joseph_bivariate.dim_le_card[OF subset] by simp
  next
    case False
    have subset: "?A\<subseteq>joseph_bivariate.span {0}"
      using False joseph_bivariate.span_zero[of "{0}"] by auto
    show ?thesis using joseph_bivariate.dim_le_card[OF subset] by simp
  qed
qed

end
