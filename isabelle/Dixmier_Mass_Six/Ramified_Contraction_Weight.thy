theory Ramified_Contraction_Weight
  imports Ramified_First_Contraction
begin
lemmas laurent_upper_mul_for_contraction = laurent_upper_mul
lemmas laurent_upper_finset_sum_for_contraction = laurent_upper_finset_sum

lemma laurent_upper_double_sum_coeff_zero:
  assumes "finite S" "finite U"
    "\<And>a b. a\<in>S \<Longrightarrow> b\<in>U \<Longrightarrow> laurent_upper (F a b) B" "B<v"
  shows "Poly_Mapping.lookup (\<Sum>a\<in>S. \<Sum>b\<in>U. F a b) v=0"
  by (intro laurent_upper_coeff_zero_above[OF _ assms(4)]
    laurent_upper_finset_sum[OF assms(1)] laurent_upper_finset_sum[OF assms(2)])
    (use assms(3) in auto)

lemma ramified_weight_double_sum_coeff_zero:
  assumes "finite S" "finite U" "0<rho"
    "\<And>a b u. a\<in>S \<Longrightarrow> b\<in>U \<Longrightarrow> u\<in>Poly_Mapping.keys (F a b::ramified_laurent) \<Longrightarrow>
      ramified_weight l rho sigma (u,r)<W"
    "W\<le>ramified_weight l rho sigma (v,r)"
  shows "Poly_Mapping.lookup (\<Sum>a\<in>S. \<Sum>b\<in>U. F a b) v=0"
proof (rule laurent_upper_double_sum_coeff_zero[OF assms(1,2), where B="v-1"])
  fix a b assume ab: "a\<in>S" "b\<in>U"
  show "laurent_upper (F a b) (v-1)"
  proof (unfold laurent_upper_def, intro ballI)
    fix u assume u: "u\<in>Poly_Mapping.keys (F a b::ramified_laurent)"
    have "rho*u<rho*v" using assms(4)[OF ab u] assms(5)
      by (simp add: ramified_weight_def)
    then have "u<v" using assms(3) by simp
    then show "u\<le>v-1" by arith
  qed
next
  show "v-1<v" by simp
qed

lemma ramified_derivative_pbw_power_upper:
  assumes "laurent_upper f B"
  shows "laurent_upper (Poly_Mapping.lookup (ramified_derivative_pbw_power l f n) j)
    (B-int l*(int n-int j))"
proof (induction n arbitrary: j)
  case 0
  show ?case by (cases "j=0")
    (use assms in \<open>simp_all add: ramified_derivative_pbw_power.simps Poly_Mapping.lookup_single
      when_def laurent_upper_zero\<close>)
next
  case (Suc n)
  let ?B = "B-int l*(int (Suc n)-int j)"
  have previous: "laurent_upper (if j=0 then 0 else
      Poly_Mapping.lookup (ramified_derivative_pbw_power l f n) (j-1)) ?B"
  proof (cases "j=0")
    case True then show ?thesis by (simp add: laurent_upper_zero)
  next
    case False
    have cast: "int (j-1)=int j-1" using False by presburger
    have bound: "B-int l*(int n-int (j-1))=?B" by (subst cast) (simp add: algebra_simps)
    show ?thesis using Suc.IH[of "j-1"] by (simp only: False if_False bound)
  qed
  have deriv: "laurent_upper (ramified_derivative l
    (Poly_Mapping.lookup (ramified_derivative_pbw_power l f n) j)) ?B"
    using laurent_upper_derivative[OF Suc.IH[of j], where l=l]
    by (simp add: algebra_simps)
  show ?case by (subst ramified_derivative_pbw_power.simps(2))
    (simp only: ramified_derivative_left_linear_apply;
      rule laurent_upper_add[OF previous deriv])
qed

lemma laurent_upper_T:
  "laurent_upper (laurent_T u) u"
  by (simp add: laurent_upper_def laurent_T_def)

lemma ramified_derivative_pbw_power_monomial_exponent_upper:
  assumes "v\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_derivative_pbw_power l (laurent_T u) n) j)"
  shows "v\<le>u-int l*(int n-int j)"
proof -
  have bound: "laurent_upper (Poly_Mapping.lookup (ramified_derivative_pbw_power l (laurent_T u) n) j) (u-int l*(int n-int j))"
    by (rule ramified_derivative_pbw_power_upper[OF laurent_upper_T])
  show ?thesis using bound assms by (auto simp: laurent_upper_def)
qed
end
