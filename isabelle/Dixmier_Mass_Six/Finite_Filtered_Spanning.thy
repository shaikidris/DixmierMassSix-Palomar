theory Finite_Filtered_Spanning
  imports Signed_Weight_Filtration
begin

lemma restrictedWeightBelow_subspace:
  assumes "joseph_bivariate.subspace S"
  shows "joseph_bivariate.subspace (restrictedWeightBelow S rho sigma b)"
  using assms signedWeightBelow_subspace[of rho sigma b]
  by (auto simp: joseph_bivariate.subspace_def restrictedWeightBelow_def)

lemma restricted_component_span_extension:
  fixes S A :: "complex bivariate set"
  assumes S: "joseph_bivariate.subspace S"
    and lower: "restrictedWeightBelow S rho sigma b\<subseteq>joseph_bivariate.span A"
    and t: "t\<in>restrictedWeightBelow S rho sigma (b+1)"
    and image: "\<And>p. p\<in>restrictedWeightBelow S rho sigma (b+1) \<Longrightarrow>
      \<exists>c. weighted_component rho sigma b p=
        joseph_biv_scale c (weighted_component rho sigma b t)"
  shows "restrictedWeightBelow S rho sigma (b+1)\<subseteq>joseph_bivariate.span (insert t A)"
proof
  fix p assume p: "p\<in>restrictedWeightBelow S rho sigma (b+1)"
  obtain c where c: "weighted_component rho sigma b p=
    joseph_biv_scale c (weighted_component rho sigma b t)" using image[OF p] by blast
  let ?d = "p-joseph_biv_scale c t"
  have upper: "?d\<in>restrictedWeightBelow S rho sigma (b+1)"
    by (intro joseph_bivariate.subspace_diff[OF restrictedWeightBelow_subspace[OF S]]
      p joseph_bivariate.subspace_scale[OF restrictedWeightBelow_subspace[OF S] t])
  have zero: "weighted_component rho sigma b ?d=0"
  proof (rule biv_eqI)
    fix i j
    have ce: "biv_coeff (weighted_component rho sigma b p) i j=
      biv_coeff (joseph_biv_scale c (weighted_component rho sigma b t)) i j"
      using c by (rule arg_cong)
    show "biv_coeff (weighted_component rho sigma b ?d) i j=biv_coeff 0 i j"
      using ce by (auto simp: weighted_component_coeff joseph_biv_scale_def)
  qed
  have d: "?d\<in>restrictedWeightBelow S rho sigma b"
    using upper zero restrictedWeightComponent_kernel[of S rho sigma b]
    by (auto simp: restrictedWeightComponent_def)
  have ds: "?d\<in>joseph_bivariate.span (insert t A)"
    using lower d joseph_bivariate.span_mono[of A "insert t A"] by blast
  have ts: "joseph_biv_scale c t\<in>joseph_bivariate.span (insert t A)"
    by (intro joseph_bivariate.span_scale joseph_bivariate.span_base) simp
  have "?d+joseph_biv_scale c t\<in>joseph_bivariate.span (insert t A)"
    by (rule joseph_bivariate.span_add[OF ds ts])
  then show "p\<in>joseph_bivariate.span (insert t A)" by simp
qed

lemma finite_restricted_filtration_spanning:
  fixes S :: "complex bivariate set"
  assumes S: "joseph_bivariate.subspace S"
    and bottom: "restrictedWeightBelow S rho sigma a={0}"
    and step: "\<And>k. k<n \<Longrightarrow> \<exists>t\<in>restrictedWeightBelow S rho sigma (a+int k+1).
      \<forall>p\<in>restrictedWeightBelow S rho sigma (a+int k+1). \<exists>c.
        weighted_component rho sigma (a+int k) p=
          joseph_biv_scale c (weighted_component rho sigma (a+int k) t)"
  shows "\<exists>A. finite A \<and> card A\<le>n \<and>
    restrictedWeightBelow S rho sigma (a+int n)\<subseteq>joseph_bivariate.span A"
  using step
proof (induction n)
  case 0
  show ?case by (intro exI[of _ "{}"])
    (simp add: bottom joseph_bivariate.span_zero)
next
  case (Suc n)
  obtain A where A: "finite A" "card A\<le>n"
    "restrictedWeightBelow S rho sigma (a+int n)\<subseteq>joseph_bivariate.span A"
    using Suc.IH Suc.prems by force
  obtain t where t: "t\<in>restrictedWeightBelow S rho sigma (a+int n+1)"
    and image: "\<forall>p\<in>restrictedWeightBelow S rho sigma (a+int n+1). \<exists>c.
      weighted_component rho sigma (a+int n) p=
        joseph_biv_scale c (weighted_component rho sigma (a+int n) t)"
    using Suc.prems[of n] by auto
  have subset: "restrictedWeightBelow S rho sigma (a+int (Suc n))\<subseteq>
      joseph_bivariate.span (insert t A)"
    using restricted_component_span_extension[OF S A(3) t] image
    by (simp add: algebra_simps)
  have card: "card (insert t A)\<le>Suc n" using A(1,2) by (simp add: card_insert_if)
  show ?case by (intro exI[of _ "insert t A"]) (use A card subset in auto)
qed

lemma finite_restricted_filtration_rank_le:
  fixes S :: "complex bivariate set"
  assumes S: "joseph_bivariate.subspace S"
    and bottom: "restrictedWeightBelow S rho sigma a={0}"
    and step: "\<And>k. k<n \<Longrightarrow> \<exists>t\<in>restrictedWeightBelow S rho sigma (a+int k+1).
      \<forall>p\<in>restrictedWeightBelow S rho sigma (a+int k+1). \<exists>c.
        weighted_component rho sigma (a+int k) p=
          joseph_biv_scale c (weighted_component rho sigma (a+int k) t)"
  shows "joseph_bivariate.dim (restrictedWeightBelow S rho sigma (a+int n))\<le>n"
proof -
  obtain A where A: "finite A" "card A\<le>n"
    "restrictedWeightBelow S rho sigma (a+int n)\<subseteq>joseph_bivariate.span A"
    using finite_restricted_filtration_spanning[OF S bottom step] by blast
  show ?thesis using joseph_bivariate.dim_le_card[OF A(3) A(1)] A(2) by arith
qed

end
