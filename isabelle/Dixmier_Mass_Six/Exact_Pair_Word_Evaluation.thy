theory Exact_Pair_Word_Evaluation
  imports Derivative_Stable_Kernel Exact_Pair_Word_Derivatives
begin

definition wordEvaluation :: "complex poly_operator \<Rightarrow> complex poly_operator \<Rightarrow>
  complex bivariate \<Rightarrow> complex poly_operator" where
  "wordEvaluation P Q f = (\<Sum>d\<in>biv_support f.
    (\<lambda>r. smult (biv_coeff f (fst d) (snd d)) (op_comp (P^^fst d) (Q^^snd d) r)))"

lemma wordEvaluation_on_finite_support_bound:
  assumes finite: "finite S" and bound: "biv_support f\<subseteq>S"
  shows "wordEvaluation P Q f = (\<Sum>d\<in>S.
    (\<lambda>r. smult (biv_coeff f (fst d) (snd d)) (op_comp (P^^fst d) (Q^^snd d) r)))"
  unfolding wordEvaluation_def
proof (rule sum.mono_neutral_cong_left[OF finite bound])
  show "\<forall>d\<in>S-biv_support f.
    (\<lambda>r. smult (biv_coeff f (fst d) (snd d)) (op_comp (P^^fst d) (Q^^snd d) r))=0"
    by (auto simp: biv_support_def)
  show "(\<lambda>r. smult (biv_coeff f (fst d) (snd d)) (op_comp (P^^fst d) (Q^^snd d) r))=
    (\<lambda>r. smult (biv_coeff f (fst d) (snd d)) (op_comp (P^^fst d) (Q^^snd d) r))"
    if "d\<in>biv_support f" for d by (rule refl)
qed

lemma wordEvaluation_monomial:
  "wordEvaluation P Q (biv_monom c i j)=(\<lambda>r. smult c (op_comp (P^^i) (Q^^j) r))"
proof -
  have bound: "biv_support (biv_monom c i j)\<subseteq>{(i,j)}"
    by (auto simp: biv_support_def)
  have finite: "finite {(i,j)}" by simp
  show ?thesis by (simp only: wordEvaluation_on_finite_support_bound[OF finite bound]; simp)
qed

lemma wordEvaluation_C:
  "wordEvaluation P Q (biv_monom c 0 0)=op_scalar c"
  by (simp add: wordEvaluation_monomial op_scalar_def)

lemma word_operator_sum_apply:
  "(\<Sum>d\<in>S. T d) r=(\<Sum>d\<in>S. T d r)" for T :: "'i\<Rightarrow>complex poly_operator"
  by (induction S rule: infinite_finite_induct) simp_all


lemma wordEvaluation_add:
  "wordEvaluation P Q (f+g)=wordEvaluation P Q f+wordEvaluation P Q g"
proof -
  let ?S = "biv_support f\<union>biv_support g"
  have finite: "finite ?S" by simp
  have fg: "biv_support (f+g)\<subseteq>?S" by (auto simp: biv_support_def)
  have f: "biv_support f\<subseteq>?S" and g: "biv_support g\<subseteq>?S" by auto
  show ?thesis
    by (simp only: wordEvaluation_on_finite_support_bound[OF finite fg]
      wordEvaluation_on_finite_support_bound[OF finite f]
      wordEvaluation_on_finite_support_bound[OF finite g] biv_coeff_add;
      simp add: smult_add_left word_operator_sum_apply sum.distrib fun_eq_iff)
qed

lemma wordEvaluation_diff:
  "wordEvaluation P Q (f-g)=wordEvaluation P Q f-wordEvaluation P Q g"
proof -
  let ?S = "biv_support f\<union>biv_support g"
  have finite: "finite ?S" by simp
  have fg: "biv_support (f-g)\<subseteq>?S" by (auto simp: biv_support_def)
  have f: "biv_support f\<subseteq>?S" and g: "biv_support g\<subseteq>?S" by auto
  show ?thesis
    by (simp only: wordEvaluation_on_finite_support_bound[OF finite fg]
      wordEvaluation_on_finite_support_bound[OF finite f]
      wordEvaluation_on_finite_support_bound[OF finite g] biv_coeff_diff;
      simp add: smult_diff_left word_operator_sum_apply sum_subtractf fun_eq_iff)
qed

lemma wordEvaluation_zero [simp]: "wordEvaluation P Q 0=0"
  by (simp add: wordEvaluation_def)

lemma wordEvaluation_sum:
  "wordEvaluation P Q (\<Sum>d\<in>S. f d)=(\<Sum>d\<in>S. wordEvaluation P Q (f d))"
  by (induction S rule: infinite_finite_induct) (simp_all add: wordEvaluation_add)

lemma wordEvaluation_constants_kernel:
  assumes "wordEvaluation P Q (biv_monom c 0 0)=0"
  shows "c=0"
proof -
  have scalar: "op_scalar c=0" using assms by (simp only: wordEvaluation_C)
  have "smult c (1::complex poly)=0" using fun_cong[OF scalar, of 1]
    by (simp add: op_scalar_def)
  then show ?thesis by simp
qed



lemma word_biv_dx_sum:
  "biv_dx (\<Sum>d\<in>S. f d)=(\<Sum>d\<in>S. biv_dx (f d))"
  by (rule biv_eqI) (simp add: biv_dx_coeff biv_coeff_sum sum_distrib_left)
lemma word_biv_dy_sum:
  "biv_dy (\<Sum>d\<in>S. f d)=(\<Sum>d\<in>S. biv_dy (f d))"
  by (rule biv_eqI) (simp add: biv_dy_coeff biv_coeff_sum sum_distrib_left)

lemma wordEvaluation_pderiv_x_monomial:
  assumes P: "poly_linear P" and Q: "poly_linear Q"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "wordEvaluation P Q (biv_dx (biv_monom c i j))=
    op_comp Q (wordEvaluation P Q (biv_monom c i j))-
    op_comp (wordEvaluation P Q (biv_monom c i j)) Q"
proof (cases i)
  case 0
  show ?thesis by (rule ext)
    (use Q in \<open>simp add: 0 biv_dx_monom wordEvaluation_monomial
      op_comp_def poly_linear_def funpow_swap1\<close>)
next
  case (Suc k)
  show ?thesis
  proof (rule ext)
    fix r
    note scaled = arg_cong[OF fun_cong[OF exact_pair_commutator_Q_word[OF P exact, where i=k and j=j], of r], where f="smult c"]
    show "wordEvaluation P Q (biv_dx (biv_monom c i j)) r=
      (op_comp Q (wordEvaluation P Q (biv_monom c i j))-
      op_comp (wordEvaluation P Q (biv_monom c i j)) Q) r"
      using scaled Q by (simp add: Suc biv_dx_monom wordEvaluation_monomial
        op_comp_def poly_linear_def smult_diff_right mult.commute)
  qed
qed

lemma wordEvaluation_pderiv_y_monomial:
  assumes P: "poly_linear P" and Q: "poly_linear Q"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "wordEvaluation P Q (biv_dy (biv_monom c i j))=
    -(op_comp P (wordEvaluation P Q (biv_monom c i j))-
    op_comp (wordEvaluation P Q (biv_monom c i j)) P)"
proof (cases j)
  case 0
  show ?thesis by (rule ext)
    (use P in \<open>simp add: 0 biv_dy_monom wordEvaluation_monomial
      op_comp_def poly_linear_def funpow_swap1\<close>)
next
  case (Suc k)
  show ?thesis
  proof (rule ext)
    fix r
    note scaled = arg_cong[OF fun_cong[OF exact_pair_commutator_P_word[OF P Q exact, where i=i and j=k], of r], where f="\<lambda>p. -smult c p"]
    show "wordEvaluation P Q (biv_dy (biv_monom c i j)) r=
      (-(op_comp P (wordEvaluation P Q (biv_monom c i j))-
      op_comp (wordEvaluation P Q (biv_monom c i j)) P)) r"
      using scaled P by (simp add: Suc biv_dy_monom wordEvaluation_monomial
        op_comp_def poly_linear_def smult_diff_right mult.commute)
  qed
qed

lemma wordEvaluation_pderiv_x:
  assumes P: "poly_linear P" and Q: "poly_linear Q"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "wordEvaluation P Q (biv_dx f)=op_comp Q (wordEvaluation P Q f)-op_comp (wordEvaluation P Q f) Q"
proof -
  let ?m = "\<lambda>d. biv_monom (biv_coeff f (fst d) (snd d)) (fst d) (snd d)"
  have "wordEvaluation P Q (biv_dx f)=wordEvaluation P Q (biv_dx (\<Sum>d\<in>biv_support f. ?m d))"
    by (simp only: biv_reconstruct)
  also have "...=(\<Sum>d\<in>biv_support f. op_comp Q (wordEvaluation P Q (?m d))-op_comp (wordEvaluation P Q (?m d)) Q)"
    by (simp only: word_biv_dx_sum wordEvaluation_sum wordEvaluation_pderiv_x_monomial[OF P Q exact])
  also have "...=op_comp Q (\<Sum>d\<in>biv_support f. wordEvaluation P Q (?m d))-
    op_comp (\<Sum>d\<in>biv_support f. wordEvaluation P Q (?m d)) Q"
    by (rule ext) (simp add: op_comp_def word_operator_sum_apply poly_linear_sum[OF Q] sum_subtractf)
  also have "...=op_comp Q (wordEvaluation P Q f)-op_comp (wordEvaluation P Q f) Q"
    by (simp only: wordEvaluation_sum[symmetric] biv_reconstruct)
  finally show ?thesis .
qed

lemma wordEvaluation_pderiv_y:
  assumes P: "poly_linear P" and Q: "poly_linear Q"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "wordEvaluation P Q (biv_dy f)= -(op_comp P (wordEvaluation P Q f)-op_comp (wordEvaluation P Q f) P)"
proof -
  let ?m = "\<lambda>d. biv_monom (biv_coeff f (fst d) (snd d)) (fst d) (snd d)"
  have "wordEvaluation P Q (biv_dy f)=wordEvaluation P Q (biv_dy (\<Sum>d\<in>biv_support f. ?m d))"
    by (simp only: biv_reconstruct)
  also have "...=(\<Sum>d\<in>biv_support f. -(op_comp P (wordEvaluation P Q (?m d))-op_comp (wordEvaluation P Q (?m d)) P))"
    by (simp only: word_biv_dy_sum wordEvaluation_sum wordEvaluation_pderiv_y_monomial[OF P Q exact])
  also have "...= -(op_comp P (\<Sum>d\<in>biv_support f. wordEvaluation P Q (?m d))-
    op_comp (\<Sum>d\<in>biv_support f. wordEvaluation P Q (?m d)) P)"
    by (rule ext) (simp add: op_comp_def word_operator_sum_apply poly_linear_sum[OF P] sum_subtractf)
  also have "...= -(op_comp P (wordEvaluation P Q f)-op_comp (wordEvaluation P Q f) P)"
    by (simp only: wordEvaluation_sum[symmetric] biv_reconstruct)
  finally show ?thesis .
qed

lemma wordEvaluation_injective:
  assumes P: "poly_linear P" and Q: "poly_linear Q"
    and exact: "op_comp Q P-op_comp P Q=id"
  shows "inj (wordEvaluation P Q)"
proof (rule bivariate_linearMap_injective_of_derivative_stable_kernel)
  show "wordEvaluation P Q (f-g)=wordEvaluation P Q f-wordEvaluation P Q g" for f g
    by (rule wordEvaluation_diff)
  show "wordEvaluation P Q (biv_deriv is_y f)=0" if zero: "wordEvaluation P Q f=0" for f is_y
    by (cases is_y) (use P Q zero in \<open>simp_all add: biv_deriv_def
      wordEvaluation_pderiv_x[OF P Q exact] wordEvaluation_pderiv_y[OF P Q exact]
      op_comp_def poly_linear_zero_image\<close>)
  show "c=0" if "wordEvaluation P Q (biv_monom c 0 0)=0" for c
    by (rule wordEvaluation_constants_kernel[OF that])
qed

end
