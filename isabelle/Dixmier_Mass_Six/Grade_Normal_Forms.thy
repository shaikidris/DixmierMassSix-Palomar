theory Grade_Normal_Forms
  imports "Operator_Polynomial_Evaluation"
    "PBW_Symbol"
begin

text \<open>Native shifted PBW representations for GradeNormalForms.lean and
PositiveGradeNormalForms.lean at commit
61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff.
The shifted PBW bases and finite support architecture follow the source.\<close>

primrec lower_shift_poly :: "nat \<Rightarrow> 'k::field poly" where
  "lower_shift_poly 0 = 1"
| "lower_shift_poly (Suc i) = lower_shift_poly i * ([:0,1:] - [:of_nat (Suc i):])"

primrec upper_shift_poly_of :: "nat \<Rightarrow> nat \<Rightarrow> 'k::field poly" where
  "upper_shift_poly_of k 0 = 1"
| "upper_shift_poly_of k (Suc i) = upper_shift_poly_of k i * ([:0,1:] - [:of_nat (Suc (i+k)):])"

lemma euler_shift_pbw:
  "op_comp (euler_yx - op_scalar (of_nat (Suc n))) (normal_monomial n i) =
    (normal_monomial (Suc n) (Suc i) :: 'k::field poly_operator)"
proof -
  have advance: "op_comp euler_yx (normal_monomial n i) =
    (\<lambda>p. smult (of_nat (Suc n)) (normal_monomial n i p)) + normal_monomial (Suc n) (Suc i)"
    unfolding euler_yx_def op_comp_assoc x_normal_monomial
    by (simp only: y_normal_monomial; simp)
  show ?thesis
  proof (rule ext)
    fix p
    have applied: "euler_yx (normal_monomial n i p) =
      smult (of_nat (Suc n)) (normal_monomial n i p) + normal_monomial (Suc n) (Suc i) p"
      using fun_cong[OF advance, of p] by (simp add: op_comp_def)
    show "op_comp (euler_yx - op_scalar (of_nat (Suc n))) (normal_monomial n i) p =
      normal_monomial (Suc n) (Suc i) p"
      by (simp add: op_comp_def op_scalar_def applied)
  qed
qed

lemma eval_shifted_factor:
  "op_poly_eval (euler_yx :: 'k::field poly_operator) ([:0,1:] - [:c:]) = euler_yx - op_scalar c"
  by (simp only: op_poly_eval_diff[OF euler_yx_linear]
    op_poly_eval_X[OF euler_yx_linear] op_poly_eval_const[OF euler_yx_linear])

lemma lower_shift_basis:
  "op_comp (op_poly_eval euler_yx (lower_shift_poly i)) (y_op ^^ k) =
    (normal_monomial i (i+k) :: 'k::field poly_operator)"
proof (induction i)
  case 0
  show ?case by (simp add: op_poly_eval_one[OF euler_yx_linear] normal_monomial_def op_comp_def fun_eq_iff)
next
  case (Suc i)
  have reordered: "op_poly_eval euler_yx (lower_shift_poly (Suc i)) =
    op_comp (euler_yx-op_scalar (of_nat (Suc i))) (op_poly_eval euler_yx (lower_shift_poly i))"
    by (simp only: lower_shift_poly.simps(2) mult.commute[of "lower_shift_poly i"]
      op_poly_eval_mult[OF euler_yx_linear] eval_shifted_factor)
  show ?case
    by (simp only: reordered op_comp_assoc Suc.IH euler_shift_pbw; simp add: add_Suc)
qed

lemma upper_shift_of_basis:
  "op_comp (op_poly_eval euler_yx (upper_shift_poly_of k i)) (x_op ^^ k) =
    (normal_monomial (i+k) i :: 'k::field poly_operator)"
proof (induction i)
  case 0
  show ?case by (simp add: op_poly_eval_one[OF euler_yx_linear] normal_monomial_def op_comp_def fun_eq_iff)
next
  case (Suc i)
  have reordered: "op_poly_eval euler_yx (upper_shift_poly_of k (Suc i)) =
    op_comp (euler_yx-op_scalar (of_nat (Suc (i+k)))) (op_poly_eval euler_yx (upper_shift_poly_of k i))"
    by (simp only: upper_shift_poly_of.simps(2) mult.commute[of "upper_shift_poly_of k i"]
      op_poly_eval_mult[OF euler_yx_linear] eval_shifted_factor)
  show ?case
    by (simp only: reordered op_comp_assoc Suc.IH euler_shift_pbw; simp add: add_Suc)
qed

lemma op_poly_eval_sum:
  assumes "poly_linear S" "finite I"
  shows "op_poly_eval S (\<Sum>i\<in>I. f i) = (\<Sum>i\<in>I. op_poly_eval S (f i))"
  using assms(2) by (induction I)
    (simp_all add: op_poly_eval_add[OF assms(1)])

lemma grade_operator_sum_apply:
  assumes "finite I"
  shows "(\<Sum>i\<in>I. F i) p = (\<Sum>i\<in>I. F i p)"
  using assms by (induction I) simp_all

lemma grade_neg_representation:
  fixes T :: "'k::field_char_0 poly_operator"
  assumes T: "T \<in> weyl_algebra"
    and grade: "\<And>u. u \<in> biv_support (pbw_symbol T) \<Longrightarrow> pair_grade u = -int k"
  shows "\<exists>f::'k poly. T = op_comp (op_poly_eval euler_yx f) (y_op ^^ k)"
proof -
  obtain c where finite: "finite {u. c u \<noteq> 0}"
    and reconstruct: "finite_normal_sum {u. c u \<noteq> 0} c = T"
    and support: "biv_support (pbw_symbol T) = {u. c u \<noteq> 0}"
    using symbol_support_finite_expansion[OF T] by blast
  let ?I = "{u. c u \<noteq> 0}"
  let ?f = "\<Sum>u\<in>?I. smult (c u) (lower_shift_poly (fst u))"
  have indices: "snd u = fst u + k" if "u \<in> ?I" for u
    using grade[of u] that support by (simp add: pair_grade_def; presburger)
  have terms: "smult (c u) (op_poly_eval euler_yx (lower_shift_poly (fst u)) ((y_op ^^ k) p)) =
    smult (c u) (normal_monomial (fst u) (snd u) p)" if "u \<in> ?I" for u p
    using fun_cong[OF lower_shift_basis[of "fst u" k, where 'k='k], of p] indices[OF that]
    by (simp only: op_comp_def indices[OF that])
  have equality: "op_comp (op_poly_eval euler_yx ?f) (y_op ^^ k) = finite_normal_sum ?I c"
    by (rule ext) (simp only: op_poly_eval_sum[OF euler_yx_linear finite]
      op_poly_eval_smult[OF euler_yx_linear] op_comp_def finite_normal_sum_def grade_operator_sum_apply[OF finite];
      rule sum.cong[OF refl]; use terms in auto)
  show ?thesis by (rule exI[of _ ?f]) (use equality reconstruct in simp)
qed

lemma grade_nat_representation:
  fixes T :: "'k::field_char_0 poly_operator"
  assumes T: "T \<in> weyl_algebra"
    and grade: "\<And>u. u \<in> biv_support (pbw_symbol T) \<Longrightarrow> pair_grade u = int k"
  shows "\<exists>f::'k poly. T = op_comp (op_poly_eval euler_yx f) (x_op ^^ k)"
proof -
  obtain c where finite: "finite {u. c u \<noteq> 0}"
    and reconstruct: "finite_normal_sum {u. c u \<noteq> 0} c = T"
    and support: "biv_support (pbw_symbol T) = {u. c u \<noteq> 0}"
    using symbol_support_finite_expansion[OF T] by blast
  let ?I = "{u. c u \<noteq> 0}"
  let ?f = "\<Sum>u\<in>?I. smult (c u) (upper_shift_poly_of k (snd u))"
  have indices: "fst u = snd u + k" if "u \<in> ?I" for u
    using grade[of u] that support by (simp add: pair_grade_def; presburger)
  have terms: "smult (c u) (op_poly_eval euler_yx (upper_shift_poly_of k (snd u)) ((x_op ^^ k) p)) =
    smult (c u) (normal_monomial (fst u) (snd u) p)" if "u \<in> ?I" for u p
    using fun_cong[OF upper_shift_of_basis[of k "snd u", where 'k='k], of p] indices[OF that]
    by (simp only: op_comp_def indices[OF that])
  have equality: "op_comp (op_poly_eval euler_yx ?f) (x_op ^^ k) = finite_normal_sum ?I c"
    by (rule ext) (simp only: op_poly_eval_sum[OF euler_yx_linear finite]
      op_poly_eval_smult[OF euler_yx_linear] op_comp_def finite_normal_sum_def grade_operator_sum_apply[OF finite];
      rule sum.cong[OF refl]; use terms in auto)
  show ?thesis by (rule exI[of _ ?f]) (use equality reconstruct in simp)
qed

lemma grade_minus_one_representation:
  fixes T :: "'k::field_char_0 poly_operator"
  assumes "T \<in> weyl_algebra"
    "\<And>u. u \<in> biv_support (pbw_symbol T) \<Longrightarrow> pair_grade u = -1"
  shows "\<exists>f::'k poly. T = op_comp (op_poly_eval euler_yx f) y_op"
  using grade_neg_representation[OF assms(1), where k=1] assms(2) by simp

lemma grade_plus_one_representation:
  fixes T :: "'k::field_char_0 poly_operator"
  assumes "T \<in> weyl_algebra"
    "\<And>u. u \<in> biv_support (pbw_symbol T) \<Longrightarrow> pair_grade u = 1"
  shows "\<exists>f::'k poly. T = op_comp (op_poly_eval euler_yx f) x_op"
  using grade_nat_representation[OF assms(1), where k=1] assms(2) by simp

end
