theory Fourier_Grade_Mass imports "Fourier_Automorphism" begin

declare id_def [simp del]

definition symbol_linear_map :: "'k::field_char_0 poly_operator \<Rightarrow> 'k bivariate" where
  "symbol_linear_map = pbw_symbol"
definition weyl_symbol_linear_contract :: "('k::field_char_0 poly_operator \<Rightarrow> 'k bivariate) \<Rightarrow> bool" where
  "weyl_symbol_linear_contract L \<longleftrightarrow>
    (\<forall>T\<in>weyl_algebra. \<forall>U\<in>weyl_algebra. T+U\<in>weyl_algebra \<and> L(T+U)=L T+L U) \<and>
    (\<forall>T\<in>weyl_algebra. \<forall>c. (\<lambda>p. smult c (T p))\<in>weyl_algebra \<and>
      L(\<lambda>p. smult c (T p))=smult [:c:] (L T))"
lemma symbol_linear_map_contract: "weyl_symbol_linear_contract (symbol_linear_map :: 'k::field_char_0 poly_operator \<Rightarrow> 'k bivariate)"
  unfolding weyl_symbol_linear_contract_def symbol_linear_map_def
  using weyl_symbol_add weyl_symbol_smult fourier_weyl_scale op_adjoin.add
  by (auto simp only: weyl_algebra_def)
lemma fourier_symbol_sum:
  assumes fin: "finite S" and cl: "\<And>u. u\<in>S \<Longrightarrow> f u\<in>(weyl_algebra :: 'k::field_char_0 poly_operator set)"
  shows "pbw_symbol (\<Sum>u\<in>S. f u) = (\<Sum>u\<in>S. pbw_symbol (f u))"
  using fin cl
proof (induction S rule: finite_induct)
  case empty show ?case by (simp only: sum.empty pbw_symbol_zero)
next
  case (insert x S)
  have fx: "f x\<in>weyl_algebra" by (rule insert.prems) simp
  have fs: "f u\<in>weyl_algebra" if "u\<in>S" for u by (rule insert.prems) (use that in simp)
  have sc: "(\<Sum>u\<in>S. f u)\<in>weyl_algebra" by (rule fourier_weyl_sum[OF fs])
  show ?case by (simp only: sum.insert[OF insert.hyps] weyl_symbol_add[OF fx sc] insert.IH[OF fs])
qed
lemma symbol_fourierAlgHom_eq_sum:
  fixes T :: "'k::field_char_0 poly_operator" and c :: "(nat\<times>nat,'k) poly_mapping"
  assumes hT: "T\<in>weyl_algebra" and hc: "finite_normal_sum (Poly_Mapping.keys c) (Poly_Mapping.lookup c)=T"
  shows "pbw_symbol (fourier_alg_hom T) = (\<Sum>u\<in>Poly_Mapping.keys c.
    smult [:Poly_Mapping.lookup c u:] (smult [:(-1)^snd u:]
      (pbw_symbol (op_comp (y_op ^^ fst u) (x_op ^^ snd u)))))"
proof -
  let ?A = "\<lambda>u. op_comp (y_op ^^ fst u) (x_op ^^ snd u) :: 'k poly_operator"
  let ?f = "\<lambda>u. (\<lambda>p. smult (Poly_Mapping.lookup c u) (smult ((-1)^snd u) (?A u p)))"
  have ac: "?A u\<in>weyl_algebra" for u by (rule fourier_antinormal_in_weyl)
  have sc: "(\<lambda>p. smult ((-1)^snd u) (?A u p))\<in>weyl_algebra" for u
    by (rule fourier_weyl_scale[OF ac])
  have fc: "?f u\<in>weyl_algebra" for u by (rule fourier_weyl_scale[OF sc])
  have eq: "fourier_alg_hom T = (\<Sum>u\<in>Poly_Mapping.keys c. ?f u)"
    using fourier_eq_finitePBWSum[OF hT hc] fourier_eq_algHom[OF hT] by simp
  show ?thesis by (simp only: eq fourier_symbol_sum[OF Poly_Mapping.finite_keys fc]
    weyl_symbol_smult[OF sc] weyl_symbol_smult[OF ac])
qed
lemma fourier_gradeSupport_subset:
  assumes hT: "T\<in>(weyl_algebra :: 'k::field_char_0 poly_operator set)"
  shows "pair_grade ` biv_support (pbw_symbol (fourier_alg_hom T)) \<subseteq>
    uminus ` (pair_grade ` biv_support (pbw_symbol T))"
proof -
  obtain c :: "(nat\<times>nat,'k) poly_mapping" where hc:
    "finite_normal_sum (Poly_Mapping.keys c) (Poly_Mapping.lookup c)=T"
    using fourier_exists_poly_mapping[OF hT] by blast
  have coeff: "pbw_coeff T (fst u) (snd u) = Poly_Mapping.lookup c u" for u
    by (simp add: hc[symmetric] pbw_coeff_finite_normal_sum Poly_Mapping.in_keys_iff)
  have support: "biv_support (pbw_symbol T) = Poly_Mapping.keys c"
    by (auto simp: biv_support_def weyl_symbol_coeff[OF hT] coeff Poly_Mapping.in_keys_iff)
  show ?thesis
  proof
    fix g assume "g\<in>pair_grade ` biv_support (pbw_symbol (fourier_alg_hom T))"
    then obtain e where eg: "g=pair_grade e" and es: "e\<in>biv_support (pbw_symbol (fourier_alg_hom T))" by blast
    have nz: "(\<Sum>u\<in>Poly_Mapping.keys c. biv_coeff
      (smult [:Poly_Mapping.lookup c u:] (smult [:(-1)^snd u:]
       (pbw_symbol (op_comp (y_op ^^ fst u) (x_op ^^ snd u))))) (fst e) (snd e)) \<noteq> 0"
      using es by (simp add: biv_support_def symbol_fourierAlgHom_eq_sum[OF hT hc] biv_coeff_sum)
    obtain u where uk: "u\<in>Poly_Mapping.keys c" and un:
      "biv_coeff (smult [:Poly_Mapping.lookup c u:] (smult [:(-1)^snd u:]
       (pbw_symbol (op_comp (y_op ^^ fst u) (x_op ^^ snd u))))) (fst e) (snd e) \<noteq> 0"
      using sum.not_neutral_contains_not_neutral[OF nz] by blast
    have esanti: "e\<in>biv_support (pbw_symbol (op_comp (y_op ^^ fst u) (x_op ^^ snd u) :: 'k poly_operator))"
      using un by (auto simp: biv_support_def)
    have grade: "pair_grade e = -pair_grade u"
      using grade_symbol_concreteAntiNormalMonomial[OF esanti]
      by (simp add: pair_grade_def)
    have us: "u\<in>biv_support (pbw_symbol T)" using uk by (simp only: support)
    show "g\<in>uminus ` (pair_grade ` biv_support (pbw_symbol T))"
      using us eg grade by blast
  qed
qed
lemma mass_fourierAlgHom_le:
  assumes "T\<in>(weyl_algebra :: 'k::field_char_0 poly_operator set)"
  shows "weyl_mass (fourier_alg_hom T) \<le> weyl_mass T"
proof -
  have fin: "finite (pair_grade ` biv_support (pbw_symbol T))" by simp
  have a: "card (pair_grade ` biv_support (pbw_symbol (fourier_alg_hom T))) \<le>
    card (uminus ` (pair_grade ` biv_support (pbw_symbol T)))"
    by (rule card_mono[OF finite_imageI[OF fin] fourier_gradeSupport_subset[OF assms]])
  have b: "card (uminus ` (pair_grade ` biv_support (pbw_symbol T))) \<le>
    card (pair_grade ` biv_support (pbw_symbol T))" by (rule card_image_le[OF fin])
  show ?thesis unfolding weyl_mass_def by (rule order_trans[OF a b])
qed
lemma mass_fourierAlgHom:
  assumes "T\<in>(weyl_algebra :: 'k::field_char_0 poly_operator set)"
  shows "weyl_mass (fourier_alg_hom T) = weyl_mass T"
proof -
  note a = mass_fourierAlgHom_le[OF assms]
  note b = mass_fourierAlgHom_le[OF fourier_alg_hom_closed[OF assms]]
  note c = mass_fourierAlgHom_le[OF fourier_alg_hom_closed[OF fourier_alg_hom_closed[OF assms]]]
  note d = mass_fourierAlgHom_le[OF fourier_alg_hom_closed[OF fourier_alg_hom_closed[OF fourier_alg_hom_closed[OF assms]]]]
  have d': "weyl_mass T \<le> weyl_mass (fourier_alg_hom (fourier_alg_hom (fourier_alg_hom T)))"
    using d by (simp only: fourierAlgHom_fourth[OF assms])
  show ?thesis using a b c d' by linarith
qed
lemma mass_fourier_A1:
  assumes "T\<in>(weyl_algebra :: 'k::field_char_0 poly_operator set)"
  shows "weyl_mass (fourier_op T) = weyl_mass T"
  by (simp only: fourier_eq_algHom[OF assms] mass_fourierAlgHom[OF assms])

end
