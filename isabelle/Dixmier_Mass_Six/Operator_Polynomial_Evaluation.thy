theory Operator_Polynomial_Evaluation
  imports "Weyl_Adjunction"
begin

text \<open>Native functional calculus for the native linear-operator
carrier. Horner evaluation supplies scalar constants and composition as
multiplication. Source: ShiftIntertwining.lean at commit
61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff.\<close>

definition op_poly_eval :: "'k::field poly_operator \<Rightarrow> 'k poly \<Rightarrow> 'k poly_operator" where
  "op_poly_eval S p = fold_coeffs (\<lambda>a T. op_scalar a + op_comp S T) p 0"

lemma op_poly_eval_zero [simp]: "op_poly_eval S 0 = 0"
  by (simp add: op_poly_eval_def)

lemma op_poly_eval_pCons:
  assumes linear: "poly_linear S"
  shows "op_poly_eval S (pCons a p) = op_scalar a + op_comp S (op_poly_eval S p)"
  by (cases "p=0"; cases "a=0")
    (use linear in \<open>simp_all add: op_poly_eval_def fold_coeffs_pCons_coeff_not_0_eq
      fold_coeffs_pCons_not_0_0_eq op_comp_def op_scalar_def fun_eq_iff
      poly_linear_zero_image\<close>)

lemma op_poly_eval_const:
  "poly_linear S \<Longrightarrow> op_poly_eval S [:a:] = op_scalar a"
  by (simp add: op_poly_eval_pCons op_comp_def fun_eq_iff poly_linear_zero_image)

lemma op_poly_eval_linear:
  "poly_linear S \<Longrightarrow> poly_linear (op_poly_eval S p)"
  by (induction p) (auto simp: op_poly_eval_pCons intro: poly_linear_add poly_linear_comp)

lemma op_poly_eval_add:
  assumes linear: "poly_linear S"
  shows "op_poly_eval S (p+q) = op_poly_eval S p + op_poly_eval S q"
proof (induction p q rule: poly_induct2)
  case 0
  show ?case by simp
next
  case (pCons a p b q)
  show ?case
    by (simp only: add_pCons op_poly_eval_pCons[OF linear] pCons.IH
      op_comp_add_right[OF linear];
      simp add: op_scalar_def fun_eq_iff smult_add_left add_ac)
qed


lemma op_poly_eval_smult:
  assumes linear: "poly_linear S"
  shows "op_poly_eval S (smult a p) = (\<lambda>v. smult a (op_poly_eval S p v))"
  by (induction p)
    (use linear in \<open>auto simp: op_poly_eval_pCons op_comp_def op_scalar_def
      fun_eq_iff poly_linear_def smult_add_right smult_smult algebra_simps\<close>)

lemma op_poly_eval_mult:
  assumes linear: "poly_linear S"
  shows "op_poly_eval S (p*q) = op_comp (op_poly_eval S p) (op_poly_eval S q)"
  by (induction p)
    (use linear in \<open>auto simp: op_poly_eval_pCons op_poly_eval_add op_poly_eval_smult
      op_comp_def op_scalar_def fun_eq_iff poly_linear_zero_image
      smult_add_right smult_smult\<close>)

lemma op_poly_eval_one:
  "poly_linear S \<Longrightarrow> op_poly_eval S 1 = id"
  by (simp add: one_pCons op_poly_eval_const op_scalar_def fun_eq_iff)

lemma op_poly_eval_X:
  "poly_linear S \<Longrightarrow> op_poly_eval S [:0,1:] = S"
  by (simp add: op_poly_eval_pCons op_poly_eval_const op_comp_def op_scalar_def fun_eq_iff poly_linear_zero_image)

lemma op_poly_eval_diff:
  assumes linear: "poly_linear S"
  shows "op_poly_eval S (p-q) = op_poly_eval S p - op_poly_eval S q"
proof -
  have "op_poly_eval S p = op_poly_eval S (p-q) + op_poly_eval S q"
    using op_poly_eval_add[OF linear, of "p-q" q] by simp
  then show ?thesis by simp
qed

lemma op_poly_eval_pcompose:
  assumes linear: "poly_linear S"
  shows "op_poly_eval S (pcompose p q) = op_poly_eval (op_poly_eval S q) p"
proof -
  have evaluated_linear: "poly_linear (op_poly_eval S q)"
    by (rule op_poly_eval_linear[OF linear])
  show ?thesis
    by (induction p)
      (simp_all add: pcompose_pCons op_poly_eval_add[OF linear]
        op_poly_eval_mult[OF linear] op_poly_eval_const[OF linear]
        op_poly_eval_pCons[OF evaluated_linear])
qed

lemma op_poly_eval_commute:
  assumes "poly_linear S"
  shows "op_comp (op_poly_eval S p) (op_poly_eval S q) =
    op_comp (op_poly_eval S q) (op_poly_eval S p)"
  using op_poly_eval_mult[OF assms, of p q] op_poly_eval_mult[OF assms, of q p]
  by (simp add: mult.commute)

lemma op_poly_eval_weyl_carrier:
  assumes carrier: "S \<in> weyl_algebra"
  shows "op_poly_eval S p \<in> weyl_algebra"
proof -
  have linear: "poly_linear S" by (rule weyl_linear[OF carrier])
  show ?thesis
  proof (induction p)
    case 0
    show ?case unfolding weyl_algebra_def by (simp only: op_poly_eval_zero; rule op_adjoin_zero)
  next
    case (pCons a p)
    have scalar: "op_scalar a \<in> weyl_algebra"
      unfolding weyl_algebra_def by (rule op_adjoin.scalar)
    have composed: "op_comp S (op_poly_eval S p) \<in> weyl_algebra"
      using carrier pCons.IH unfolding weyl_algebra_def by (rule op_adjoin.comp)
    show ?case unfolding op_poly_eval_pCons[OF linear]
      using scalar composed unfolding weyl_algebra_def by (rule op_adjoin.add)
  qed
qed

lemma op_poly_eval_eigen:
  assumes linear: "poly_linear S" and eigen: "S v = smult c v"
  shows "op_poly_eval S p v = smult (poly p c) v"
  by (induction p)
    (use linear eigen in \<open>auto simp: op_poly_eval_pCons op_comp_def op_scalar_def
      poly_linear_def smult_add_left smult_smult algebra_simps\<close>)

definition euler_yx :: "'k::field poly_operator" where
  "euler_yx = op_comp y_op x_op"

lemma euler_yx_linear: "poly_linear (euler_yx :: 'k::field poly_operator)"
  unfolding euler_yx_def by (intro poly_linear_comp) simp_all

lemma euler_yx_eigen:
  "(euler_yx :: 'k::field poly_operator) ([:0,1:]^n) = smult (of_nat (Suc n)) ([:0,1:]^n)"
proof -
  have power: "[:0,1:] * ([:0,1:]^n) = ([:0,1:]::'k poly)^Suc n" by simp
  show ?thesis unfolding euler_yx_def op_comp_def x_op_def y_op_def
    by (simp only: power pderiv_power_Suc pderiv_pCons pderiv_singleton; simp)
qed

lemma aeval_yx_apply_Xpow:
  "op_poly_eval (euler_yx :: 'k::field poly_operator) p ([:0,1:]^n) =
    smult (poly p (of_nat (Suc n))) ([:0,1:]^n)"
  by (rule op_poly_eval_eigen[OF euler_yx_linear euler_yx_eigen])

lemma aeval_yx_injective:
  "inj (op_poly_eval (euler_yx :: 'k::field_char_0 poly_operator))"
proof (rule injI)
  fix p q :: "'k poly"
  assume equal_eval: "op_poly_eval (euler_yx :: 'k poly_operator) p = op_poly_eval euler_yx q"
  have eigenvalue_equalities: "poly p (of_nat (Suc n)) = poly q (of_nat (Suc n))" for n
  proof -
    have eval: "smult (poly p (of_nat (Suc n))) ([:0,1:]^n) =
      smult (poly q (of_nat (Suc n))) ([:0,1:]^n)"
      using fun_cong[OF equal_eval, of "[:0,1:]^n"] by (simp only: aeval_yx_apply_Xpow)
    show ?thesis using arg_cong[OF eval, of "\<lambda>r. coeff r n"] by (simp add: coeff_linear_power)
  qed
  have eigeneigenvalue_equalities_injective: "inj (\<lambda>n::nat. (of_nat (Suc n)::'k))"
    by (auto intro: injI)
  have eigeneigenvalue_equalities_inj_on: "inj_on (\<lambda>n::nat. (of_nat (Suc n)::'k)) UNIV"
    using eigeneigenvalue_equalities_injective unfolding inj_def inj_on_def by blast
  have eigeneigenvalue_equalities_infinite: "infinite (range (\<lambda>n::nat. (of_nat (Suc n)::'k)))"
    using finite_image_iff[OF eigeneigenvalue_equalities_inj_on]
    by simp
  have all_roots: "range (\<lambda>n::nat. (of_nat (Suc n)::'k)) \<subseteq> {x. poly (p-q) x = 0}"
    using eigenvalue_equalities by auto
  have "p-q=0"
  proof (rule ccontr)
    assume nonzero: "p-q \<noteq> 0"
    have "finite {x. poly (p-q) x = 0}" by (rule poly_roots_finite[OF nonzero])
    then have "finite (range (\<lambda>n::nat. (of_nat (Suc n)::'k)))"
      by (rule finite_subset[OF all_roots])
    then show False using eigeneigenvalue_equalities_infinite by simp
  qed
  then show "p=q" by simp
qed

text \<open>The next theorem is the linear-operator specialization of the
source's generic algebra theorem. Its explicit linearity premises encode
membership of the source endomorphism carrier.\<close>

lemma polynomial_aeval_intertwining:
  assumes s_linear: "poly_linear s" and u_linear: "poly_linear u"
    and c_linear: "poly_linear c"
    and intertwines: "op_comp u s = op_comp (s+c) u"
  shows "op_comp u (op_poly_eval s p) = op_comp (op_poly_eval (s+c) p) u"
proof -
  have shifted_linear: "poly_linear (s+c)" by (rule poly_linear_add[OF s_linear c_linear])
  show ?thesis
  proof (induction p)
    case 0
    show ?case using poly_linear_zero_image[OF u_linear]
      by (simp add: op_comp_def fun_eq_iff)
  next
    case (pCons a p)
    have scalars: "op_comp u (op_scalar a) = op_comp (op_scalar a) u"
      using op_scalar_central[OF u_linear, of a] by simp
    have step: "op_comp u (op_comp s (op_poly_eval s p)) =
      op_comp (s+c) (op_comp u (op_poly_eval s p))"
      using intertwines op_comp_assoc by metis
    show ?case
      by (simp only: op_poly_eval_pCons[OF s_linear]
        op_poly_eval_pCons[OF shifted_linear] op_comp_add_right[OF u_linear]
        op_comp_add_left scalars step pCons.IH op_comp_assoc)
  qed
qed

lemma yOp_aeval_yx_shift:
  fixes p :: "'k::field poly"
  shows "op_comp y_op (op_poly_eval euler_yx p) =
    op_comp (op_poly_eval (euler_yx+id) p) y_op"
proof -
  have intertwines: "op_comp y_op euler_yx = op_comp (euler_yx+id) y_op"
    by (rule ext) (simp add: euler_yx_def op_comp_def x_op_def y_op_def
      pderiv_mult pderiv_add pderiv_pCons algebra_simps)
  show ?thesis by (rule polynomial_aeval_intertwining[OF euler_yx_linear
    poly_linear_y poly_linear_id intertwines])
qed

lemma xOp_aeval_yx_shift:
  fixes p :: "'k::field poly"
  shows "op_comp x_op (op_poly_eval euler_yx p) =
    op_comp (op_poly_eval (euler_yx-id) p) x_op"
proof -
  have minus_identity_linear: "poly_linear (-id :: 'k poly_operator)"
    by (rule poly_linear_diff[where T="0 :: 'k poly_operator" and U=id, simplified])
  have intertwines: "op_comp x_op euler_yx = op_comp (euler_yx+(-id)) x_op"
    by (rule ext) (simp add: euler_yx_def op_comp_def x_op_def y_op_def
      pderiv_mult pderiv_pCons algebra_simps)
  have shift: "op_comp x_op (op_poly_eval euler_yx p) =
    op_comp (op_poly_eval (euler_yx+(-id)) p) x_op"
    by (rule polynomial_aeval_intertwining[OF euler_yx_linear
      poly_linear_x minus_identity_linear intertwines])
  show ?thesis using shift by simp
qed

end
