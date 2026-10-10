theory Ramified_Shear_PBW_Sum
  imports Ramified_Face_Polynomial
begin
definition ramified_shear_pbw_sum ::
  "nat \<Rightarrow> ramified_laurent \<Rightarrow> ramified_pbw_coefficients \<Rightarrow> ramified_pbw_coefficients" where
  "ramified_shear_pbw_sum l h a =
    (\<Sum>n\<in>Poly_Mapping.keys a.
      ramified_coeff_left_linear (Poly_Mapping.lookup a n) (ramified_shift_pbw_power l h n))"
lemma ramified_shear_pbw_sum_eval:
  "ramified_normal_eval l (ramified_shear_pbw_sum l h a) = ramified_shift_eval l h a"
  by (simp add: ramified_shear_pbw_sum_def ramified_normal_eval_sum
      ramified_normal_eval_coeff_left ramified_shift_pbw_power_eval ramified_shift_eval_def)
lemma ramified_cut_aut_mem:
  "0<l \<Longrightarrow> T\<in>ramified_operator_algebra l \<Longrightarrow>
    ramified_cut_aut l rho sigma c T \<in> ramified_operator_algebra l"
  by (simp add: ramified_cut_aut_def ramified_shear_hom_def ramified_shear_candidate_mem)
lemma ramified_cut_aut_pbw_coeffs_sum:
  "0<l \<Longrightarrow> T\<in>ramified_operator_algebra l \<Longrightarrow>
   ramified_pbw_coeffs l (ramified_cut_aut l rho sigma c T) =
   ramified_shear_pbw_sum l (ramified_cut_shift l rho sigma c) (ramified_pbw_coeffs l T)"
  by (rule ramified_pbw_coeffs_eq_of_eval)
     (simp_all add: ramified_cut_aut_mem ramified_shear_pbw_sum_eval
       ramified_cut_aut_def ramified_shear_hom_def ramified_shear_candidate_def ramified_shift_eval_mem)
lemma ramified_cut_aut_pbw_coeff_finset:
  "0<l \<Longrightarrow> T\<in>ramified_operator_algebra l \<Longrightarrow>
   ramified_pbw_coeff l (ramified_cut_aut l rho sigma c T) i j =
   (\<Sum>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
    Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n *
      Poly_Mapping.lookup (ramified_shift_pbw_power l (ramified_cut_shift l rho sigma c) n) j) i)"
  by (simp add: ramified_pbw_coeff_def ramified_cut_aut_pbw_coeffs_sum
      ramified_shear_pbw_sum_def Poly_Mapping.lookup_sum ramified_coeff_left_linear_apply)

lemma laurent_mult_coeff_finset:
  "Poly_Mapping.lookup (f*g) i =
    (\<Sum>u\<in>Poly_Mapping.keys f. Poly_Mapping.lookup f u * Poly_Mapping.lookup g (i-u))"
  for f g :: ramified_laurent and i :: int
proof -
  have index: "\<And>u q. i=u+q \<longleftrightarrow> q=i-u" by arith
  have "Poly_Mapping.lookup (f*g) i =
    Sum_any (\<lambda>u. Poly_Mapping.lookup f u * Poly_Mapping.lookup g (i-u))"
    by (simp add: Poly_Mapping.lookup_mult index)
  also have "... = (\<Sum>u\<in>Poly_Mapping.keys f. Poly_Mapping.lookup f u * Poly_Mapping.lookup g (i-u))"
    by (rule Sum_any.expand_superset) (auto simp: Poly_Mapping.in_keys_iff)
  finally show ?thesis .
qed
lemma laurent_upper_mul_edge:
  assumes "laurent_upper f B" "laurent_upper g C"
  shows "Poly_Mapping.lookup (f*g) (B+C) = Poly_Mapping.lookup f B * Poly_Mapping.lookup g C"
proof -
  have atom: "Poly_Mapping.lookup f u * Poly_Mapping.lookup g (B+C-u) =
    (if u=B then Poly_Mapping.lookup f B * Poly_Mapping.lookup g C else 0)"
    if "u\<in>Poly_Mapping.keys f" for u
  proof (cases "u=B")
    case True then show ?thesis by simp
  next
    case False
    have "u\<le>B" using assms(1) that unfolding laurent_upper_def by blast
    then have "C<B+C-u" using False by arith
    then show ?thesis using laurent_upper_coeff_zero_above[OF assms(2)] False by simp
  qed
  show ?thesis
    by (simp only: laurent_mult_coeff_finset)
       (simp add: atom Poly_Mapping.in_keys_iff)
qed
lemma laurent_upper_mul:
  "laurent_upper f B \<Longrightarrow> laurent_upper g C \<Longrightarrow> laurent_upper (f*g) (B+C)"
  using Poly_Mapping.keys_mult[of f g] unfolding laurent_upper_def by force
lemma laurent_upper_finset_sum:
  "finite S \<Longrightarrow> (\<And>x. x\<in>S \<Longrightarrow> laurent_upper (f x) B) \<Longrightarrow> laurent_upper (sum f S) B"
  by (induction S rule: finite_induct) (auto intro: laurent_upper_zero laurent_upper_add)
lemma ramified_cut_aut_edge_coeff_finset:
  assumes "0<l" "T\<in>ramified_operator_algebra l" "0<rho" "rho dvd int l" "0<rho+sigma"
    and upper: "\<And>n. laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n)
      (r-ramified_cut_exponent l rho sigma*int n)"
  shows "ramified_pbw_coeff l (ramified_cut_aut l rho sigma c T)
      (r-ramified_cut_exponent l rho sigma*int j) j =
    (\<Sum>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
      ramified_pbw_coeff l T (r-ramified_cut_exponent l rho sigma*int n) n *
      (of_nat (n choose j) * c^(n-j)))"
proof -
  let ?k = "ramified_cut_exponent l rho sigma"
  have atom: "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n *
      Poly_Mapping.lookup (ramified_shift_pbw_power l (ramified_cut_shift l rho sigma c) n) j)
      (r-?k*int j) =
      ramified_pbw_coeff l T (r-?k*int n) n * (of_nat (n choose j)*c^(n-j))" for n
  proof -
    have index: "r-?k*int j = (r-?k*int n)+(int n-int j)*?k" by (simp add: algebra_simps)
    show ?thesis
      by (simp only: index laurent_upper_mul_edge[OF upper[of n]
        ramified_cut_power_upper[OF assms(1,3,4,5), of c n j]]
        ramified_cut_edge_coeff_binomial[OF assms(1,3,4,5), unfolded ramified_cut_edge_coeff_def]
        ramified_pbw_coeff_def)
  qed
  show ?thesis by (simp only: ramified_cut_aut_pbw_coeff_finset[OF assms(1,2)] atom)
qed

definition polynomial_support :: "complex poly \<Rightarrow> nat set" where
  "polynomial_support p = {n. coeff p n \<noteq> 0}"
lemma polynomial_support_finite: "finite (polynomial_support p)"
  unfolding polynomial_support_def
  by (rule finite_subset[where B="{..degree p}"]) (auto dest: le_degree)
lemma polynomial_support_expansion:
  "p = (\<Sum>n\<in>polynomial_support p. monom (coeff p n) n)"
proof -
  have "(\<Sum>n\<in>polynomial_support p. monom (coeff p n) n) =
    (\<Sum>n\<le>degree p. monom (coeff p n) n)"
    by (rule sum.mono_neutral_cong_left) (auto simp: polynomial_support_def dest: le_degree)
  then show ?thesis by (simp add: poly_as_sum_of_monoms)
qed
lemma pcompose_power:
  "pcompose (p^n) q = (pcompose p q)^n"
  for p q :: "complex poly"
  by (induction n) (simp_all add: pcompose_1 pcompose_mult)
lemma monomial_translate_coeff:
  "coeff (pcompose (monom a n) [:c,1:]) j = a * (of_nat (n choose j) * c^(n-j))"
  for a c :: complex
proof (cases "j\<le>n")
  case True
  then show ?thesis by (simp add: monom_altdef pcompose_smult pcompose_power pcompose_pCons
      coeff_linear_poly_power)
next
  case False
  then have above: "n<j" by simp
  have degree: "degree ([:c,1:]^n) \<le> n"
    using degree_power_le[of "[:c,1:]" n] by simp
  show ?thesis using above degree
    by (simp add: monom_altdef pcompose_smult pcompose_power pcompose_pCons coeff_eq_0 binomial_eq_0)
qed
lemma polynomial_translate_coeff_finset:
  "coeff (pcompose p [:c,1:]) j =
    (\<Sum>n\<in>polynomial_support p. coeff p n * (of_nat (n choose j)*c^(n-j)))"
proof -
  have "coeff (pcompose p [:c,1:]) j =
    coeff (pcompose (\<Sum>n\<in>polynomial_support p. monom (coeff p n) n) [:c,1:]) j"
    by (simp only: polynomial_support_expansion[symmetric])
  then show ?thesis by (simp add: pcompose_sum coeff_sum monomial_translate_coeff)
qed
lemma ramified_face_polynomial_support_subset:
  "polynomial_support (ramified_face_polynomial l T r k) \<subseteq> Poly_Mapping.keys (ramified_pbw_coeffs l T)"
  by (auto simp: polynomial_support_def ramified_face_polynomial_coeff
      ramified_pbw_coeff_def Poly_Mapping.in_keys_iff)
lemma ramified_cut_aut_face_polynomial_eq_translate:
  assumes "0<l" "T\<in>ramified_operator_algebra l" "0<rho" "rho dvd int l" "0<rho+sigma"
    and upper: "\<And>n. laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n)
      (r-ramified_cut_exponent l rho sigma*int n)"
  shows "ramified_face_polynomial l (ramified_cut_aut l rho sigma c T) r (ramified_cut_exponent l rho sigma) =
    pcompose (ramified_face_polynomial l T r (ramified_cut_exponent l rho sigma)) [:c,1:]"
proof (rule poly_eqI)
  fix j
  let ?p = "ramified_face_polynomial l T r (ramified_cut_exponent l rho sigma)"
  have expansion: "(\<Sum>n\<in>polynomial_support ?p. coeff ?p n * (of_nat (n choose j)*c^(n-j))) =
    (\<Sum>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T). coeff ?p n * (of_nat (n choose j)*c^(n-j)))"
    by (rule sum.mono_neutral_cong_left[OF _ ramified_face_polynomial_support_subset])
       (auto simp: polynomial_support_def)
  have expansion': "(\<Sum>n\<in>polynomial_support ?p.
      ramified_pbw_coeff l T (r-ramified_cut_exponent l rho sigma*int n) n * (of_nat (n choose j)*c^(n-j))) =
    (\<Sum>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
      ramified_pbw_coeff l T (r-ramified_cut_exponent l rho sigma*int n) n * (of_nat (n choose j)*c^(n-j)))"
    using expansion by (simp only: ramified_face_polynomial_coeff)
  show "coeff (ramified_face_polynomial l (ramified_cut_aut l rho sigma c T) r
      (ramified_cut_exponent l rho sigma)) j = coeff (pcompose ?p [:c,1:]) j"
    by (simp only: ramified_face_polynomial_coeff
      ramified_cut_aut_edge_coeff_finset[OF assms(1,2,3,4,5) upper]
      polynomial_translate_coeff_finset ramified_face_polynomial_coeff expansion')
qed
end
