theory Fourier_Algebra_Hom
  imports "Fourier_Free_Lift"
    "Abstract_Faithfulness"
    "Fourier_Operator"
begin

declare id_def [simp del]

definition fourier_alg_hom :: "'k::field_char_0 poly_operator \<Rightarrow> 'k poly_operator" where
  "fourier_alg_hom T = fourier_abstract_to_concrete (concrete_to_abstract T)"

lemma fourier_alg_hom_closed:
  "T \<in> (weyl_algebra :: 'k::field_char_0 poly_operator set) \<Longrightarrow> fourier_alg_hom T \<in> weyl_algebra"
  unfolding fourier_alg_hom_def
  by (intro fourier_abstract_to_concrete_in_weyl concrete_to_abstract_closed)
lemma fourier_alg_hom_linear_ring_hom:
  "fourier_alg_hom \<in> ring_hom (weyl_operator_ring :: 'k::field_char_0 poly_operator ring) linear_operator_ring"
  using ring_hom_trans[OF concrete_to_abstract_ring_hom fourier_abstract_to_concrete_ring_hom]
  by (simp only: fourier_alg_hom_def[abs_def] comp_def)
lemma fourier_alg_hom_ring_hom:
  "fourier_alg_hom \<in> ring_hom (weyl_operator_ring :: 'k::field_char_0 poly_operator ring) weyl_operator_ring"
  using fourier_alg_hom_linear_ring_hom[where 'k='k] fourier_alg_hom_closed[where 'k='k]
  by (auto simp add: ring_hom_def weyl_operator_ring_def)
lemma fourier_alg_hom_scalar:
  "fourier_alg_hom (op_scalar c) = op_scalar c"
  by (simp only: fourier_alg_hom_def concrete_to_abstract_scalar fourier_abstract_to_concrete_scalar)
lemma fourier_alg_hom_add:
  assumes "T \<in> (weyl_algebra :: 'k::field_char_0 poly_operator set)" "U \<in> weyl_algebra"
  shows "fourier_alg_hom (T+U) = fourier_alg_hom T + fourier_alg_hom U"
  using ring_hom_add[OF fourier_alg_hom_ring_hom, of T U] assms
  by (simp only: weyl_operator_ring_simps; blast)
lemma fourier_alg_hom_comp:
  assumes "T \<in> (weyl_algebra :: 'k::field_char_0 poly_operator set)" "U \<in> weyl_algebra"
  shows "fourier_alg_hom (op_comp T U) = op_comp (fourier_alg_hom T) (fourier_alg_hom U)"
  using ring_hom_mult[OF fourier_alg_hom_ring_hom, of T U] assms
  by (simp only: weyl_operator_ring_simps; blast)
lemma fourier_alg_hom_id [simp]: "fourier_alg_hom id = id"
  using fourier_alg_hom_scalar[of 1] by (simp only: free_op_scalar_one)
lemma fourier_alg_hom_zero [simp]: "fourier_alg_hom 0 = 0"
  using fourier_alg_hom_scalar[of 0] by (simp only: free_op_scalar_zero)
lemma fourier_alg_hom_scale:
  assumes "T \<in> (weyl_algebra :: 'k::field_char_0 poly_operator set)"
  shows "fourier_alg_hom (\<lambda>p. smult c (T p)) = (\<lambda>p. smult c (fourier_alg_hom T p))"
proof -
  have sc: "op_scalar c \<in> (weyl_algebra :: 'k poly_operator set)"
    unfolding weyl_algebra_def by (rule op_adjoin.scalar)
  have eq: "fourier_alg_hom (op_comp (op_scalar c) T) = op_comp (op_scalar c) (fourier_alg_hom T)"
    by (simp only: fourier_alg_hom_comp[OF sc assms] fourier_alg_hom_scalar)
  show ?thesis using eq by (simp only: op_comp_def op_scalar_def)
qed
lemma fourier_alg_hom_power:
  assumes "T \<in> (weyl_algebra :: 'k::field_char_0 poly_operator set)"
  shows "fourier_alg_hom (T ^^ n) = (fourier_alg_hom T ^^ n)"
proof (induction n)
  case 0 show ?case by (simp only: funpow.simps fourier_alg_hom_id)
next
  case (Suc n)
  have p: "(T ^^ n) \<in> weyl_algebra" by (rule fourier_weyl_power[OF assms])
  show ?case using fourier_alg_hom_comp[OF assms p] Suc.IH
    by (simp only: funpow.simps op_comp_def comp_def)
qed

lemma fourierAlgHom_concreteX:
  "fourier_alg_hom (x_op :: 'k::field_char_0 poly_operator) = y_op"
  by (simp only: fourier_alg_hom_def concrete_to_abstract_X fourierAbstractToConcrete_abstractX)
lemma fourierAlgHom_concreteY:
  "fourier_alg_hom (y_op :: 'k::field_char_0 poly_operator) = -x_op"
  by (simp only: fourier_alg_hom_def concrete_to_abstract_Y fourierAbstractToConcrete_abstractY)

lemma fourier_linear_scaled_power:
  assumes "poly_linear (T :: 'k::field poly_operator)"
  shows "((\<lambda>p. smult c (T p)) ^^ n) = (\<lambda>p. smult (c^n) ((T ^^ n) p))"
proof (induction n)
  case 0 show ?case by (rule ext) simp
next
  case (Suc n)
  have lin: "T (smult d p) = smult d (T p)" for d p
    using assms by (auto simp: poly_linear_def)
  show ?case by (rule ext) (simp only: funpow.simps comp_apply Suc.IH lin smult_smult power_Suc)
qed
lemma fourier_neg_concreteX_pow:
  "((-x_op) ^^ j :: 'k::field poly_operator) = (\<lambda>p. smult ((-1)^j) ((x_op ^^ j) p))"
proof -
  have neg: "(-x_op :: 'k poly_operator) = (\<lambda>p. smult (-1) (x_op p))"
    by (rule ext) simp
  show ?thesis by (simp only: neg fourier_linear_scaled_power[OF poly_linear_x])
qed
lemma fourierAlgHom_normalMonomial:
  "fourier_alg_hom (op_comp (x_op ^^ i) (y_op ^^ j) :: 'k::field_char_0 poly_operator) =
    (\<lambda>p. smult ((-1)^j) (op_comp (y_op ^^ i) (x_op ^^ j) p))"
proof -
  have eq: "fourier_alg_hom (op_comp (x_op ^^ i) (y_op ^^ j) :: 'k poly_operator) =
    op_comp (y_op ^^ i) ((-x_op) ^^ j)"
    by (simp only: fourier_alg_hom_comp[OF fourier_weyl_power[OF weyl_x] fourier_weyl_power[OF weyl_y]]
      fourier_alg_hom_power[OF weyl_x] fourier_alg_hom_power[OF weyl_y]
      fourierAlgHom_concreteX fourierAlgHom_concreteY)
  have lin: "(y_op ^^ i) (smult c p) = smult c ((y_op ^^ i) p)" for c p
    using poly_linear_power[OF poly_linear_y, of i] by (auto simp: poly_linear_def)
  show ?thesis by (simp only: eq fourier_neg_concreteX_pow; rule ext; simp only: op_comp_def lin)
qed
lemma fourierAlgHom_map_neg:
  assumes "T \<in> (weyl_algebra :: 'k::field_char_0 poly_operator set)"
  shows "fourier_alg_hom (-T) = -fourier_alg_hom T"
proof -
  have neg: "-T = (\<lambda>p. smult (-1) (T p))" by (rule ext) simp
  show ?thesis by (simp only: neg fourier_alg_hom_scale[OF assms]; rule ext; simp)
qed
lemma fourier_neg_neg:
  assumes "T \<in> (weyl_algebra :: 'k::field poly_operator set)"
  shows "-(-T) = T"
  by simp

end
