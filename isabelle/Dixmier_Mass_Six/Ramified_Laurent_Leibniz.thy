theory Ramified_Laurent_Leibniz
  imports "Ramified_Laurent_Core"
begin

lemma laurent_single_expansion:
  "f = (\<Sum>n\<in>Poly_Mapping.keys f. Poly_Mapping.single n (Poly_Mapping.lookup f n))"
  for f :: ramified_laurent
  by (rule poly_mapping_eqI)
     (simp add: Poly_Mapping.lookup_sum Poly_Mapping.lookup_single when_def
       sum.delta Poly_Mapping.in_keys_iff)

lemma laurent_induct [case_names zero add single]:
  assumes zero: "P 0"
    and add: "\<And>f g. P f \<Longrightarrow> P g \<Longrightarrow> P (f + g)"
    and single: "\<And>n c. P (Poly_Mapping.single n c)"
  shows "P (f :: ramified_laurent)"
proof -
  have "P (\<Sum>n\<in>S. Poly_Mapping.single n (Poly_Mapping.lookup f n))" if "finite S" for S
    using that by (induction S rule: finite_induct) (auto intro: zero add single)
  then show ?thesis by (subst laurent_single_expansion) simp
qed

lemma ramified_derivative_single_coefficient:
  "ramified_derivative l (Poly_Mapping.single n c) =
    Poly_Mapping.single (n - int l) (((of_int n :: complex) / of_nat l) * c)"
  by (simp only: ramified_derivative_single laurent_T_def laurent_smult_single mult_1_right)

lemma ramified_derivative_single_product:
  "ramified_derivative l (Poly_Mapping.single m c * Poly_Mapping.single n d) =
    ramified_derivative l (Poly_Mapping.single m c) * Poly_Mapping.single n d +
    Poly_Mapping.single m c * ramified_derivative l (Poly_Mapping.single n d)"
  by (simp only: Poly_Mapping.mult_single ramified_derivative_single_coefficient)
     (simp add: algebra_simps add_divide_distrib Poly_Mapping.single_add [symmetric])

lemma ramified_derivative_mul:
  "ramified_derivative l (f * g) =
    ramified_derivative l f * g + f * ramified_derivative l g"
proof (induction f rule: laurent_induct)
  case zero
  then show ?case by simp
next
  case (add f h)
  then show ?case by (simp add: ramified_derivative_add algebra_simps)
next
  case (single n c)
  show ?case
  proof (induction g rule: laurent_induct)
    case zero
    then show ?case by simp
  next
    case (add g h)
    then show ?case by (simp add: ramified_derivative_add algebra_simps)
  next
    case (single m d)
    then show ?case by (rule ramified_derivative_single_product)
  qed
qed

lemma ramified_derivative_T_mul:
  "ramified_derivative l (laurent_T m * g) =
    ramified_derivative l (laurent_T m) * g + laurent_T m * ramified_derivative l g"
  by (rule ramified_derivative_mul)

lemma ramified_derivative_T_mul_T:
  "ramified_derivative l (laurent_T m * laurent_T n) =
    ramified_derivative l (laurent_T m) * laurent_T n +
    laurent_T m * ramified_derivative l (laurent_T n)"
  by (rule ramified_derivative_mul)

end
