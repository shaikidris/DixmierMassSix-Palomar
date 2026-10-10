theory Fourier_Automorphism
  imports "Fourier_Algebra_Hom"
    "Fourier_Monomial_Symbols"
begin

declare id_def [simp del]

lemma fourier_weyl_neg:
  assumes "T \<in> weyl_algebra"
  shows "-T \<in> weyl_algebra"
proof -
  have "0-T \<in> weyl_algebra" unfolding weyl_algebra_def
    by (rule op_adjoin.diff[OF op_adjoin_zero assms[unfolded weyl_algebra_def]])
  then show ?thesis by (simp only: diff_0)
qed
lemma fourier_alg_hom_diff:
  assumes "T \<in> (weyl_algebra :: 'k::field_char_0 poly_operator set)" "U \<in> weyl_algebra"
  shows "fourier_alg_hom (T-U) = fourier_alg_hom T - fourier_alg_hom U"
  using fourier_alg_hom_add[OF assms(1) fourier_weyl_neg[OF assms(2)]]
  by (simp only: diff_conv_add_uminus fourierAlgHom_map_neg[OF assms(2)])
lemma fourier_alg_hom_sum:
  assumes fin: "finite S" and cl: "\<And>u. u \<in> S \<Longrightarrow> f u \<in> (weyl_algebra :: 'k::field_char_0 poly_operator set)"
  shows "fourier_alg_hom (\<Sum>u\<in>S. f u) = (\<Sum>u\<in>S. fourier_alg_hom (f u))"
  using fin cl
proof (induction S rule: finite_induct)
  case empty show ?case by (simp only: sum.empty fourier_alg_hom_zero)
next
  case (insert x S)
  have fx: "f x \<in> weyl_algebra" by (rule insert.prems) simp
  have fs: "f u \<in> weyl_algebra" if "u\<in>S" for u by (rule insert.prems) (use that in simp)
  have sc: "(\<Sum>u\<in>S. f u) \<in> weyl_algebra" by (rule fourier_weyl_sum[OF fs])
  have ih: "fourier_alg_hom (\<Sum>u\<in>S. f u) = (\<Sum>u\<in>S. fourier_alg_hom (f u))"
    by (rule insert.IH[OF fs])
  show ?case by (simp only: sum.insert[OF insert.hyps] fourier_alg_hom_add[OF fx sc] ih)
qed
lemma fourier_exists_poly_mapping:
  assumes "T \<in> (weyl_algebra :: 'k::field_char_0 poly_operator set)"
  shows "\<exists>c :: (nat\<times>nat,'k) poly_mapping.
    finite_normal_sum (Poly_Mapping.keys c) (Poly_Mapping.lookup c) = T"
proof -
  obtain c where fin: "finite {u. c u\<noteq>0}" and rep: "finite_normal_sum {u. c u\<noteq>0} c = T"
    using weyl_exists_finite_coordinates[OF assms] by blast
  have look: "Poly_Mapping.lookup (Poly_Mapping.Abs_poly_mapping c) = c"
    by (rule Poly_Mapping.lookup_Abs_poly_mapping[OF fin])
  have keys: "Poly_Mapping.keys (Poly_Mapping.Abs_poly_mapping c) = {u. c u\<noteq>0}"
    by (auto simp only: Poly_Mapping.in_keys_iff look)
  show ?thesis by (rule exI[of _ "Poly_Mapping.Abs_poly_mapping c"]) (simp only: keys look rep)
qed
lemma fourier_eq_algHom:
  assumes hT: "T \<in> (weyl_algebra :: 'k::field_char_0 poly_operator set)"
  shows "fourier_op T = fourier_alg_hom T"
proof -
  obtain c :: "(nat\<times>nat,'k) poly_mapping" where rep:
    "finite_normal_sum (Poly_Mapping.keys c) (Poly_Mapping.lookup c) = T"
    using fourier_exists_poly_mapping[OF hT] by blast
  let ?f = "\<lambda>u. (\<lambda>p. smult (Poly_Mapping.lookup c u) (normal_monomial (fst u) (snd u) p))"
  have cl: "?f u \<in> weyl_algebra" for u
    by (rule fourier_weyl_scale[OF normal_monomial_in_weyl])
  have fs: "finite_normal_sum (Poly_Mapping.keys c) (Poly_Mapping.lookup c) =
    (\<Sum>u\<in>Poly_Mapping.keys c. ?f u)"
    by (rule ext) (simp only: finite_normal_sum_def operator_sum_apply)
  have sumrep: "T = (\<Sum>u\<in>Poly_Mapping.keys c. ?f u)" using rep fs by simp
  have image: "fourier_alg_hom (?f u) = (\<lambda>p.
    smult (Poly_Mapping.lookup c u) (smult ((-1)^snd u) (op_comp (y_op ^^ fst u) (x_op ^^ snd u) p)))" for u
  proof -
    have mon: "fourier_alg_hom (normal_monomial (fst u) (snd u)) =
      (\<lambda>p. smult ((-1)^snd u) (op_comp (y_op ^^ fst u) (x_op ^^ snd u) p))"
      by (simp only: normal_monomial_def fourierAlgHom_normalMonomial)
    show ?thesis by (simp only: fourier_alg_hom_scale[OF normal_monomial_in_weyl] mon)
  qed
  have F: "fourier_alg_hom T = (\<Sum>u\<in>Poly_Mapping.keys c. (\<lambda>p.
    smult (Poly_Mapping.lookup c u) (smult ((-1)^snd u) (op_comp (y_op ^^ fst u) (x_op ^^ snd u) p))))"
    by (simp only: sumrep fourier_alg_hom_sum[OF Poly_Mapping.finite_keys cl] image)
  show ?thesis using fourier_eq_finitePBWSum[OF hT rep] F by simp
qed
lemma fourier_mul_A1:
  fixes P Q :: "'k::field_char_0 poly_operator"
  assumes "P \<in> (weyl_algebra :: 'k::field_char_0 poly_operator set)" "Q \<in> weyl_algebra"
  shows "fourier_op (op_comp P Q) = op_comp (fourier_op P) (fourier_op Q)"
  by (simp only: fourier_eq_algHom[OF fourier_weyl_comp[OF assms]]
    fourier_eq_algHom[OF assms(1)] fourier_eq_algHom[OF assms(2)] fourier_alg_hom_comp[OF assms])
lemma fourierAlgHom_fourth:
  assumes "T \<in> (weyl_algebra :: 'k::field_char_0 poly_operator set)"
  shows "fourier_alg_hom (fourier_alg_hom (fourier_alg_hom (fourier_alg_hom T))) = T"
proof -
  have gx: "fourier_alg_hom (fourier_alg_hom (fourier_alg_hom (fourier_alg_hom (x_op :: 'k poly_operator)))) = x_op"
    by (simp only: fourierAlgHom_concreteX fourierAlgHom_concreteY
      fourierAlgHom_map_neg[OF weyl_x] fourierAlgHom_map_neg[OF weyl_y] minus_minus)
  have gy: "fourier_alg_hom (fourier_alg_hom (fourier_alg_hom (fourier_alg_hom (y_op :: 'k poly_operator)))) = y_op"
    by (simp only: fourierAlgHom_concreteX fourierAlgHom_concreteY
      fourierAlgHom_map_neg[OF weyl_x] fourierAlgHom_map_neg[OF weyl_y] minus_minus)
  show ?thesis using assms[unfolded weyl_algebra_def]
  proof (induction rule: op_adjoin.induct)
    case (generator U)
    then show ?case using gx gy by auto
  next
    case (scalar c)
    show ?case by (simp only: fourier_alg_hom_scalar)
  next
    case (add P Q)
    have p: "P\<in>weyl_algebra" and q: "Q\<in>weyl_algebra"
      using add.hyps by (simp_all only: weyl_algebra_def)
    show ?case by (simp only: fourier_alg_hom_add fourier_alg_hom_closed p q add.IH)
  next
    case (diff P Q)
    have p: "P\<in>weyl_algebra" and q: "Q\<in>weyl_algebra"
      using diff.hyps by (simp_all only: weyl_algebra_def)
    show ?case by (simp only: fourier_alg_hom_diff fourier_alg_hom_closed p q diff.IH)
  next
    case (comp P Q)
    have p: "P\<in>weyl_algebra" and q: "Q\<in>weyl_algebra"
      using comp.hyps by (simp_all only: weyl_algebra_def)
    show ?case by (simp only: fourier_alg_hom_comp fourier_alg_hom_closed p q comp.IH)
  qed
qed

definition fourier_alg_equiv :: "'k::field_char_0 poly_operator \<Rightarrow> 'k poly_operator" where
  "fourier_alg_equiv = fourier_alg_hom"
definition fourier_alg_inverse :: "'k::field_char_0 poly_operator \<Rightarrow> 'k poly_operator" where
  "fourier_alg_inverse T = fourier_alg_hom (fourier_alg_hom (fourier_alg_hom T))"
lemma fourier_alg_inverse_closed:
  "T\<in>weyl_algebra \<Longrightarrow> fourier_alg_inverse T\<in>weyl_algebra"
  unfolding fourier_alg_inverse_def by (intro fourier_alg_hom_closed)
lemma fourier_alg_inverse_left:
  "T\<in>weyl_algebra \<Longrightarrow> fourier_alg_inverse (fourier_alg_equiv T) = T"
  by (simp only: fourier_alg_inverse_def fourier_alg_equiv_def fourierAlgHom_fourth)
lemma fourier_alg_inverse_right:
  "T\<in>weyl_algebra \<Longrightarrow> fourier_alg_equiv (fourier_alg_inverse T) = T"
  by (simp only: fourier_alg_inverse_def fourier_alg_equiv_def fourierAlgHom_fourth)
lemma fourier_alg_equiv_bijective:
  "bij_betw (fourier_alg_equiv :: 'k::field_char_0 poly_operator \<Rightarrow> 'k poly_operator) weyl_algebra weyl_algebra"
proof (rule bij_betwI)
  show "fourier_alg_equiv \<in> weyl_algebra \<rightarrow> weyl_algebra"
    by (auto simp only: Pi_def fourier_alg_equiv_def intro: fourier_alg_hom_closed)
  show "fourier_alg_inverse \<in> weyl_algebra \<rightarrow> weyl_algebra"
    by (auto simp only: Pi_def intro: fourier_alg_inverse_closed)
  show "\<And>T. T\<in>weyl_algebra \<Longrightarrow> fourier_alg_inverse (fourier_alg_equiv T)=T"
    by (rule fourier_alg_inverse_left)
  show "\<And>T. T\<in>weyl_algebra \<Longrightarrow> fourier_alg_equiv (fourier_alg_inverse T)=T"
    by (rule fourier_alg_inverse_right)
qed
lemma fourier_alg_equiv_ring_iso:
  "fourier_alg_equiv \<in> ring_iso (weyl_operator_ring :: 'k::field_char_0 poly_operator ring) weyl_operator_ring"
  by (simp only: ring_iso_def mem_Collect_eq weyl_operator_ring_simps
    fourier_alg_equiv_def fourier_alg_hom_ring_hom fourier_alg_equiv_bijective[unfolded fourier_alg_equiv_def] simp_thms)
lemma fourier_alg_equiv_scalar:
  "fourier_alg_equiv (op_scalar c) = op_scalar c"
  by (simp only: fourier_alg_equiv_def fourier_alg_hom_scalar)
lemma fourier_add_A1:
  fixes P Q :: "'k::field_char_0 poly_operator"
  assumes "P \<in> (weyl_algebra :: 'k::field_char_0 poly_operator set)" "Q \<in> weyl_algebra"
  shows "fourier_op (P+Q) = fourier_op P + fourier_op Q"
proof -
  have cl: "P+Q\<in>weyl_algebra" using assms
    unfolding weyl_algebra_def by (rule op_adjoin.add)
  show ?thesis by (simp only: fourier_eq_algHom[OF cl] fourier_eq_algHom[OF assms(1)]
    fourier_eq_algHom[OF assms(2)] fourier_alg_hom_add[OF assms])
qed

end
