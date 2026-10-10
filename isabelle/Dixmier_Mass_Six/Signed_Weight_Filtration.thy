theory Signed_Weight_Filtration
  imports "Weyl_Leading_Forms" "HOL.Vector_Spaces"
begin

definition joseph_biv_scale :: "complex \<Rightarrow> complex bivariate \<Rightarrow> complex bivariate" where
  "joseph_biv_scale c p=smult [:c:] p"

interpretation joseph_bivariate: vector_space joseph_biv_scale
proof standard
  fix a b :: complex and x y :: "complex bivariate"
  show "joseph_biv_scale a (x+y)=joseph_biv_scale a x+joseph_biv_scale a y"
    by (simp add: joseph_biv_scale_def smult_add_right)
  have add: "[:a+b:]=[:a:]+[:b:]" by simp
  show "joseph_biv_scale (a+b) x=joseph_biv_scale a x+joseph_biv_scale b x"
    by (simp only: joseph_biv_scale_def add smult_add_left)
  show "joseph_biv_scale a (joseph_biv_scale b x)=joseph_biv_scale (a*b) x"
    by (simp add: joseph_biv_scale_def mult.commute)
  show "joseph_biv_scale 1 x=x"
    by (rule biv_eqI) (simp add: joseph_biv_scale_def)
qed

definition signedWeightBelow :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> complex bivariate set" where
  "signedWeightBelow rho sigma b =
    {p. \<forall>u. b\<le>pair_weight rho sigma u \<longrightarrow> biv_coeff p (fst u) (snd u)=0}"

lemma signedWeightBelow_subspace:
  "joseph_bivariate.subspace (signedWeightBelow rho sigma b)"
  by (auto simp: joseph_bivariate.subspace_def signedWeightBelow_def joseph_biv_scale_def)

lemma signedWeightBelow_mono:
  assumes "b\<le>c"
  shows "signedWeightBelow rho sigma b\<subseteq>signedWeightBelow rho sigma c"
  using assms by (auto simp: signedWeightBelow_def)

lemma signedWeightBelow_component_kernel:
  "{p\<in>signedWeightBelow rho sigma (b+1). weighted_component rho sigma b p=0}=
    signedWeightBelow rho sigma b"
proof (rule set_eqI)
  fix p
  show "p\<in>{p\<in>signedWeightBelow rho sigma (b+1). weighted_component rho sigma b p=0}
      \<longleftrightarrow> p\<in>signedWeightBelow rho sigma b"
  proof
    assume p: "p\<in>{p\<in>signedWeightBelow rho sigma (b+1). weighted_component rho sigma b p=0}"
    have below: "p\<in>signedWeightBelow rho sigma (b+1)" and zero: "weighted_component rho sigma b p=0"
      using p by auto
    show "p\<in>signedWeightBelow rho sigma b"
    proof (unfold signedWeightBelow_def, intro CollectI allI impI)
      fix u assume ub: "b\<le>pair_weight rho sigma u"
      show "biv_coeff p (fst u) (snd u)=0"
      proof (cases "pair_weight rho sigma u=b")
        case True
        have "biv_coeff (weighted_component rho sigma b p) (fst u) (snd u)=0"
          using zero by simp
        then show ?thesis using True by (simp add: weighted_component_coeff)
      next
        case False
        have "b+1\<le>pair_weight rho sigma u" using ub False by arith
        then show ?thesis using below by (simp add: signedWeightBelow_def)
      qed
    qed
  next
    assume below: "p\<in>signedWeightBelow rho sigma b"
    have upper_step: "p\<in>signedWeightBelow rho sigma (b+1)"
      using signedWeightBelow_mono[where b=b and c="b+1" and rho=rho and sigma=sigma] below by auto
    have zero: "weighted_component rho sigma b p=0"
    proof (rule biv_eqI)
      fix i j
      have coeff: "pair_weight rho sigma (i,j)=b \<Longrightarrow> biv_coeff p i j=0"
        using below by (auto simp: signedWeightBelow_def)
      show "biv_coeff (weighted_component rho sigma b p) i j=biv_coeff 0 i j"
        using coeff by (auto simp: weighted_component_coeff)
    qed
    show "p\<in>{p\<in>signedWeightBelow rho sigma (b+1). weighted_component rho sigma b p=0}"
      using upper_step zero by auto
  qed
qed

definition restrictedWeightBelow :: "complex bivariate set \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> complex bivariate set" where
  "restrictedWeightBelow S rho sigma b=S\<inter>signedWeightBelow rho sigma b"

definition restrictedWeightComponent :: "complex bivariate set \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> complex bivariate \<Rightarrow> complex bivariate" where
  "restrictedWeightComponent S rho sigma b p=weighted_component rho sigma b p"

lemma restrictedWeightBelow_mono:
  assumes "b\<le>c"
  shows "restrictedWeightBelow S rho sigma b\<subseteq>restrictedWeightBelow S rho sigma c"
  unfolding restrictedWeightBelow_def using signedWeightBelow_mono[OF assms] by blast

lemma restrictedWeightComponent_kernel:
  "{p\<in>restrictedWeightBelow S rho sigma (b+1). restrictedWeightComponent S rho sigma b p=0}=
    restrictedWeightBelow S rho sigma b"
  using signedWeightBelow_component_kernel[of rho sigma b]
  by (auto simp: restrictedWeightBelow_def restrictedWeightComponent_def)

lemma restrictedWeightBelow_eq_bot_of_lower_bound:
  assumes S: "joseph_bivariate.subspace S"
    and hlo: "\<And>p u. p\<in>S \<Longrightarrow> pair_weight rho sigma u<b \<Longrightarrow> biv_coeff p (fst u) (snd u)=0"
  shows "restrictedWeightBelow S rho sigma b={0}"
proof (rule set_eqI)
  fix p
  have zero: "p=0" if "p\<in>restrictedWeightBelow S rho sigma b"
  proof (rule biv_eqI)
    fix i j
    have ps: "p\<in>S" and below: "p\<in>signedWeightBelow rho sigma b"
      using that by (auto simp: restrictedWeightBelow_def)
    show "biv_coeff p i j=biv_coeff 0 i j"
    proof (cases "pair_weight rho sigma (i,j)<b")
      case True
      show ?thesis using hlo[OF ps True] by simp
    next
      case False
      show ?thesis using below False by (simp add: signedWeightBelow_def)
    qed
  qed
  have zs: "0\<in>S" using S by (simp add: joseph_bivariate.subspace_def)
  show "p\<in>restrictedWeightBelow S rho sigma b \<longleftrightarrow> p\<in>{0}"
    using zero zs by (auto simp: restrictedWeightBelow_def signedWeightBelow_def)
qed

lemma restrictedWeightBelow_eq_top_of_upper_bound:
  assumes hhi: "\<And>p u. p\<in>S \<Longrightarrow> b\<le>pair_weight rho sigma u \<Longrightarrow> biv_coeff p (fst u) (snd u)=0"
  shows "restrictedWeightBelow S rho sigma b=S"
  using hhi by (auto simp: restrictedWeightBelow_def signedWeightBelow_def)

end
