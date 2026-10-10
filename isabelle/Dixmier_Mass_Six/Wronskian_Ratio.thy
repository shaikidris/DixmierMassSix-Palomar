theory Wronskian_Ratio
  imports "HOL-Computational_Algebra.Polynomial_Factorial"
begin

text \<open>Native generic-field formalization for WronskianRatio.lean,
commit 61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff. Explicit Bezout
coprimality matches Lean IsCoprime without coefficient gcd typeclasses.\<close>

definition polynomial_wronskian :: "'k::field poly \<Rightarrow> 'k poly \<Rightarrow> 'k poly" where
  "polynomial_wronskian f g = f * pderiv g - pderiv f * g"

definition polynomial_is_coprime :: "'k::field poly \<Rightarrow> 'k poly \<Rightarrow> bool" where
  "polynomial_is_coprime f g \<longleftrightarrow> (\<exists>a b. a*f+b*g=1)"

interpretation wronskian_poly: 
  normalization_euclidean_semiring where zero = "0 :: 'a :: field poly"
    and one = 1 and plus = plus and minus = minus
    and times = times
    and normalize = "\<lambda>p. smult (inverse (lead_coeff p)) p"
    and unit_factor = "\<lambda>p. [:lead_coeff p:]"
    and euclidean_size = "\<lambda>p. if p = 0 then 0 else 2 ^ degree p"
    and divide = divide and modulo = modulo
  rewrites "dvd.dvd (times :: 'a poly \<Rightarrow> _) = Rings.dvd"
    and "comm_monoid_mult.prod_mset times 1 = prod_mset"
    and "comm_semiring_1.irreducible times 1 0 = irreducible"
    and "comm_semiring_1.prime_elem times 1 0 = prime_elem"
proof -
  show "dvd.dvd (times :: 'a poly \<Rightarrow> _) = Rings.dvd"
    by (simp add: dvd_dict)
  show "comm_monoid_mult.prod_mset times 1 = prod_mset"
    by (simp add: prod_mset_dict)
  show "comm_semiring_1.irreducible times 1 0 = irreducible"
    by (simp add: irreducible_dict)
  show "comm_semiring_1.prime_elem times 1 0 = prime_elem"
    by (simp add: prime_elem_dict)
  show "class.normalization_euclidean_semiring divide plus minus (0 :: 'a poly) times 1
    modulo (\<lambda>p. if p = 0 then 0 else 2 ^ degree p)
    (\<lambda>p. [:lead_coeff p:]) (\<lambda>p. smult (inverse (lead_coeff p)) p)"
  proof (standard, fold dvd_dict)
    fix p :: "'a poly"
    show "[:lead_coeff p:] * smult (inverse (lead_coeff p)) p = p"
      by (cases "p = 0") simp_all
  next
    fix p :: "'a poly" assume "is_unit p"
    then show "[:lead_coeff p:] = p"
      by (elim is_unit_polyE) (auto simp: monom_0 one_poly_def field_simps)
  next
    fix p :: "'a poly" assume "p \<noteq> 0"
    then show "is_unit [:lead_coeff p:]"
      by (simp add: is_unit_pCons_iff)
  next
    fix a b :: "'a poly" assume "is_unit a"
    thus "[:lead_coeff (a * b):] = a * [:lead_coeff b:]"
      by (auto elim!: is_unit_polyE)
  qed (auto simp: lead_coeff_mult Rings.div_mult_mod_eq intro!: degree_mod_less' degree_mult_right_le)
qed

definition polynomial_gcd :: "'k::field poly \<Rightarrow> 'k poly \<Rightarrow> 'k poly" where
  "polynomial_gcd = Euclidean_Algorithm.normalization_euclidean_semiring.gcd
    0 modulo (\<lambda>p. smult (inverse (lead_coeff p)) p)"

lemma coprime_wronskian_zero_scalar_ratio:
  fixes f g :: "'k::field_char_0 poly"
  assumes g_nonzero: "g \<noteq> 0" and relatively_prime: "polynomial_is_coprime f g"
    and zero: "polynomial_wronskian f g = 0"
  shows "\<exists>c::'k. f = [:c:] * g"
proof -
  obtain a b where bezout: "a*f+b*g=1"
    using relatively_prime unfolding polynomial_is_coprime_def by blast
  have equation: "f * pderiv g = pderiv f * g"
    using zero unfolding polynomial_wronskian_def by simp
  have f_derivative_identity: "pderiv f = f*(a*pderiv f+b*pderiv g)"
  proof -
    have "pderiv f = pderiv f*(a*f+b*g)" by (simp only: bezout mult_1_right)
    also have "... = a*f*pderiv f + b*(pderiv f*g)" by (simp add: algebra_simps)
    also have "... = a*f*pderiv f + b*(f*pderiv g)" by (simp only: equation)
    also have "... = f*(a*pderiv f+b*pderiv g)" by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have g_derivative_identity: "pderiv g = g*(a*pderiv f+b*pderiv g)"
  proof -
    have "pderiv g = pderiv g*(a*f+b*g)" by (simp only: bezout mult_1_right)
    also have "... = a*(f*pderiv g) + b*g*pderiv g" by (simp add: algebra_simps)
    also have "... = a*(pderiv f*g) + b*g*pderiv g" by (simp only: equation)
    also have "... = g*(a*pderiv f+b*pderiv g)" by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have f_derivative: "f dvd pderiv f" using f_derivative_identity unfolding dvd_def by blast
  have g_derivative: "g dvd pderiv g" using g_derivative_identity unfolding dvd_def by blast
  have f_degree: "degree f = 0" using f_derivative by simp
  have g_degree: "degree g = 0" using g_derivative by simp
  obtain a where f_constant: "f = [:a:]" using degree_eq_zeroE[OF f_degree] by blast
  obtain b where g_constant: "g = [:b:]" using degree_eq_zeroE[OF g_degree] by blast
  have b_nonzero: "b \<noteq> 0" using g_nonzero g_constant by simp
  show ?thesis
    by (rule exI[of _ "a / b"]) (simp add: f_constant g_constant b_nonzero)
qed

lemma wronskian_common_mul:
  fixes d f g :: "'k::field poly"
  shows "polynomial_wronskian (d * f) (d * g) = d ^ 2 * polynomial_wronskian f g"
  by (simp add: polynomial_wronskian_def pderiv_mult power2_eq_square algebra_simps)

lemma field_poly_gcd_bezout:
  fixes f g :: "'k::field poly"
  shows "\<exists>a b. a*f+b*g = polynomial_gcd f g"
proof (induction f g rule: wronskian_poly.eucl_induct)
  case (zero f)
  show ?case
    by (rule exI[of _ "[:inverse (lead_coeff f):]"], rule exI[of _ 0])
      (simp add: polynomial_gcd_def wronskian_poly.gcd_0)
next
  case (mod f g)
  obtain a b where induction_identity: "a*g+b*(f mod g) = polynomial_gcd g (f mod g)"
    using mod.IH by blast
  have division: "f mod g = f-(f div g)*g"
    using div_mult_mod_eq[of f g] by (simp add: eq_diff_eq add.commute)
  have "b*f+(a-b*(f div g))*g = a*g+b*(f mod g)"
    by (simp add: division algebra_simps)
  also have "... = polynomial_gcd g (f mod g)" by (rule induction_identity)
  also have "... = polynomial_gcd f g" unfolding polynomial_gcd_def by (rule wronskian_poly.gcd_mod[OF mod.hyps])
  finally show ?case by blast
qed

lemma polynomial_gcd_divides:
  fixes f g :: "'k::field poly"
  shows "polynomial_gcd f g dvd f \<and> polynomial_gcd f g dvd g"
proof (induction f g rule: wronskian_poly.eucl_induct)
  case (zero f)
  have first: "smult (inverse (lead_coeff f)) f dvd f"
  proof (cases "f=0")
    case True then show ?thesis by simp
  next
    case False
    show ?thesis using False by (simp add: smult_dvd_iff)

  qed
  show ?case using first by (simp add: polynomial_gcd_def wronskian_poly.gcd_0)
next
  case (mod f g)
  have eq: "polynomial_gcd f g = polynomial_gcd g (f mod g)"
    unfolding polynomial_gcd_def using wronskian_poly.gcd_mod[OF mod.hyps] by simp
  show ?case using mod.IH by (auto simp add: eq dvd_mod_iff)
qed

lemma polynomial_wronskian_zero_scalar_ratio:
  fixes f g :: "'k::field_char_0 poly"
  assumes g_nonzero: "g \<noteq> 0" and zero: "polynomial_wronskian f g = 0"
  shows "\<exists>c::'k. f = [:c:] * g"
proof -
  let ?d = "polynomial_gcd f g"
  have divides_f: "?d dvd f" using polynomial_gcd_divides[of f g] by blast
  have divides_g: "?d dvd g" using polynomial_gcd_divides[of f g] by blast
  have d_nonzero: "?d \<noteq> 0" using divides_g g_nonzero by auto
  have f_factor: "?d * (f div ?d) = f" by (rule dvd_mult_div_cancel[OF divides_f])
  have g_factor: "?d * (g div ?d) = g" by (rule dvd_mult_div_cancel[OF divides_g])
  have quotient_nonzero: "g div ?d \<noteq> 0" using g_nonzero g_factor by auto
  obtain a b where bezout: "a*f+b*g=?d" using field_poly_gcd_bezout[of f g] by blast
  have quotient_coprime: "polynomial_is_coprime (f div ?d) (g div ?d)"
  proof -
    have factored: "?d*(a*(f div ?d)+b*(g div ?d)) = ?d*1"
    proof -
      have "?d*(a*(f div ?d)+b*(g div ?d)) = a*(?d*(f div ?d))+b*(?d*(g div ?d))"
        by (simp add: algebra_simps)
      also have "... = ?d*1" by (simp only: f_factor g_factor bezout mult_1_right)
      finally show ?thesis .
    qed
    have "a*(f div ?d)+b*(g div ?d)=1" using factored d_nonzero by simp
    then show ?thesis unfolding polynomial_is_coprime_def by blast
  qed
  have factored_zero: "?d ^ 2 * polynomial_wronskian (f div ?d) (g div ?d) = 0"
    using zero by (simp only: wronskian_common_mul[symmetric] f_factor g_factor)
  have quotient_zero: "polynomial_wronskian (f div ?d) (g div ?d) = 0"
    using factored_zero d_nonzero by simp
  obtain c where quotient_ratio: "f div ?d = [:c:] * (g div ?d)"
    using coprime_wronskian_zero_scalar_ratio[OF quotient_nonzero quotient_coprime quotient_zero] by blast
  have "f = ?d * (f div ?d)" using f_factor by simp
  also have "... = ?d * ([:c:] * (g div ?d))" by (simp only: quotient_ratio)
  also have "... = [:c:] * (?d * (g div ?d))" by (simp only: mult.assoc mult.left_commute)
  also have "... = [:c:] * g" by (simp only: g_factor)
  finally show ?thesis by blast
qed

end
