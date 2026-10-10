theory Multiplicity_Transport
  imports "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
    "Root_Multiplicity_Adapter"
    "Polynomial_Scaling"
    "Sparse_Root_Order"
begin

lemma dvd_of_forall_rootMultiplicity_le:
  fixes p q :: "complex poly"
  assumes hp: "p \<noteq> 0"
    and h: "\<And>a. rootMultiplicity a p \<le> rootMultiplicity a q"
  shows "p dvd q"
proof (cases "q=0")
  case True
  then show ?thesis by simp
next
  case False
  have roots: "proots p \<subseteq># proots q"
    using h by (simp add: subseteq_mset_def rootMultiplicity_eq_count_proots)
  have product: "(\<Prod>x\<in>#proots p. [:-x,1:]) dvd (\<Prod>x\<in>#proots q. [:-x,1:])"
    by (rule prod_mset_subset_imp_dvd, rule image_mset_subseteq_mono, rule roots)
  have "smult (lead_coeff p) (\<Prod>x\<in>#proots p. [:-x,1:]) dvd
    smult (lead_coeff q) (\<Prod>x\<in>#proots q. [:-x,1:])"
    using product hp False by (simp add: smult_dvd_iff dvd_smult_iff)
  then show ?thesis by (simp only: complex_poly_decompose_multiset)
qed

lemma rootMultiplicity_comp_C_mul_X:
  fixes p :: "complex poly"
  assumes hp: "p \<noteq> 0" and hc: "c \<noteq> 0"
  shows "rootMultiplicity b (pcompose p [:0,c:]) = rootMultiplicity (c*b) p"
proof -
  let ?q = "pcompose p [:0,c:]"
  have hq: "?q \<noteq> 0"
  proof
    assume q0: "?q=0"
    have "pcompose ?q [:0,inverse c:] = p"
      by (rule comp_C_mul_X_comp_C_inv_mul_X[OF hc])
    with q0 hp show False by simp
  qed
  show ?thesis
  proof (rule antisym)
    let ?m = "rootMultiplicity b ?q"
    have d: "[:-b,1:] ^ ?m dvd ?q"
      using hq by (simp add: Polynomial.order_divides rootMultiplicity_eq_order)
    have d': "[:- (b / inverse c),1:] ^ ?m dvd pcompose ?q [:0,inverse c:]"
      by (rule pow_dvd_comp_C_mul_X) (use hc d in auto)
    have dp: "[:- (c*b),1:] ^ ?m dvd p"
      using d' comp_C_mul_X_comp_C_inv_mul_X[OF hc, of p]
      by (simp add: divide_inverse mult.commute)
    show "rootMultiplicity b ?q \<le> rootMultiplicity (c*b) p"
      using dp hp by (simp add: Polynomial.order_divides rootMultiplicity_eq_order)
  next
    let ?m = "rootMultiplicity (c*b) p"
    have d: "[:- (c*b),1:] ^ ?m dvd p"
      using hp by (simp add: Polynomial.order_divides rootMultiplicity_eq_order)
    have d': "[:- ((c*b)/c),1:] ^ ?m dvd ?q"
      by (rule pow_dvd_comp_C_mul_X[OF hc d])
    have dq: "[:-b,1:] ^ ?m dvd ?q" using d' hc by simp
    show "rootMultiplicity (c*b) p \<le> rootMultiplicity b ?q"
      using dq hq by (simp add: Polynomial.order_divides rootMultiplicity_eq_order)
  qed
qed

lemma rootMultiplicity_le_two:
  fixes r :: "complex poly"
  assumes hr0: "poly r 0 \<noteq> 0" and ht: "termCount (r ^ 2) \<le> 6"
  shows "rootMultiplicity a r \<le> 2"
proof -
  have hr: "r \<noteq> 0" using hr0 by auto
  show ?thesis
  proof (cases "a=0")
    case True
    have "Polynomial.order 0 r = 0" by (rule Polynomial.order_0I[OF hr0])
    then show ?thesis using True hr by (simp add: rootMultiplicity_eq_order)
  next
    case False
    have hr2: "r ^ 2 \<noteq> 0" using hr by simp
    have bound: "Polynomial.order a (r ^ 2) < termCount (r ^ 2)"
      by (rule Sparse_Root_Order.rootMultiplicity_lt_termCount[OF hr2 False])
    have twice: "Polynomial.order a (r ^ 2) = 2 * rootMultiplicity a r"
      using hr by (simp add: power2_eq_square Polynomial.order_mult rootMultiplicity_eq_order; arith)
    show ?thesis using bound ht twice by arith
  qed
qed

end
