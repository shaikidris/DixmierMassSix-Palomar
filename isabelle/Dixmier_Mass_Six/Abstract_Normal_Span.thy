theory Abstract_Normal_Span
  imports Quotient_Scalar_Ring
begin

definition abstract_normal_monomial :: "nat \<Rightarrow> nat \<Rightarrow> 'k::field weyl_free set" where
  "abstract_normal_monomial i j = monoid.mult abstract_weyl_ring
    (pow abstract_weyl_ring abstract_X i) (pow abstract_weyl_ring abstract_Y j)"

inductive_set abstract_normal_span :: "'k::field weyl_free set set" where
  monomial: "abstract_normal_monomial i j \<in> abstract_normal_span"
| zero: "ring.zero abstract_weyl_ring \<in> abstract_normal_span"
| add: "z \<in> abstract_normal_span \<Longrightarrow> w \<in> abstract_normal_span \<Longrightarrow>
    ring.add abstract_weyl_ring z w \<in> abstract_normal_span"
| scalar: "z \<in> abstract_normal_span \<Longrightarrow>
    monoid.mult abstract_weyl_ring (abstract_scalar c) z \<in> abstract_normal_span"

text \<open>This context has only a static coefficient-type marker and no
mathematical assumptions. Its central-ring structure is proved from the actual
quotient. No evaluation, coefficient extraction or faithfulness is used below.\<close>

locale abstract_normal_arithmetic =
  fixes K :: "'k::field itself"
begin

sublocale W: central_scalar_ring "(abstract_weyl_ring :: 'k weyl_free set ring)" abstract_scalar
  by (rule abstract_central_scalar_ring)

abbreviation Q :: "'k weyl_free set ring" where "Q \<equiv> abstract_weyl_ring"
abbreviation qm where "qm \<equiv> monoid.mult Q"
abbreviation qa where "qa \<equiv> ring.add Q"
abbreviation q0 where "q0 \<equiv> ring.zero Q"
abbreviation q1 where "q1 \<equiv> monoid.one Q"
abbreviation qX :: "'k weyl_free set" where "qX \<equiv> abstract_X"
abbreviation qY :: "'k weyl_free set" where "qY \<equiv> abstract_Y"
abbreviation qpow where "qpow \<equiv> (pow Q :: 'k weyl_free set \<Rightarrow> nat \<Rightarrow> 'k weyl_free set)"

declare quotient_X_closed [simp] quotient_Y_closed [simp] quotient_scalar_closed [simp]

lemma x_power_closed [simp]: "qpow qX n \<in> carrier Q"
  by (rule W.scalar.S.nat_pow_closed[OF quotient_X_closed])
lemma y_power_closed [simp]: "qpow qY n \<in> carrier Q"
  by (rule W.scalar.S.nat_pow_closed[OF quotient_Y_closed])
lemma abstract_normal_monomial_closed [simp]: "abstract_normal_monomial i j \<in> carrier Q"
  unfolding abstract_normal_monomial_def by (rule W.scalar.S.m_closed[OF x_power_closed y_power_closed])
lemma abstract_span_closed:
  "z \<in> abstract_normal_span \<Longrightarrow> z \<in> carrier Q"
  by (induction rule: abstract_normal_span.induct)
     (blast intro: abstract_normal_monomial_closed W.scalar.S.zero_closed
       W.scalar.S.a_closed W.scalar.S.m_closed quotient_scalar_closed)+
lemma abstract_normal_monomial_zero:
  "(abstract_normal_monomial 0 0 :: 'k weyl_free set) = q1"
  by (simp add: abstract_normal_monomial_def)
lemma abstract_normal_monomial_X:
  "(abstract_normal_monomial 1 0 :: 'k weyl_free set) = qX"
  by (simp add: abstract_normal_monomial_def quotient_X_closed)
lemma abstract_normal_monomial_Y:
  "(abstract_normal_monomial 0 1 :: 'k weyl_free set) = qY"
  by (simp add: abstract_normal_monomial_def quotient_Y_closed)
lemma abstract_one_in_span: "q1 \<in> abstract_normal_span"
  by (subst abstract_normal_monomial_zero[symmetric]) (rule abstract_normal_span.monomial)
lemma abstract_X_in_span: "qX \<in> abstract_normal_span"
  by (subst abstract_normal_monomial_X[symmetric]) (rule abstract_normal_span.monomial)
lemma abstract_Y_in_span: "qY \<in> abstract_normal_span"
  by (subst abstract_normal_monomial_Y[symmetric]) (rule abstract_normal_span.monomial)

lemma abstract_y_power_succ_mul_x:
  "qm (qpow qY (Suc n)) qX =
    qa (qm qX (qpow qY (Suc n))) (qm (abstract_scalar (of_nat (Suc n))) (qpow qY n))"
proof (induction n)
  case 0
  show ?case by (simp add: abstract_relation abstract_scalar_one quotient_X_closed quotient_Y_closed)
next
  case (Suc n)
  have pn: "qm (qpow qY n) qY = qpow qY (Suc n)"
    by (simp only: W.scalar.S.nat_pow_Suc)
  have ps: "qm (qpow qY (Suc n)) qY = qpow qY (Suc (Suc n))"
    by (simp only: W.scalar.S.nat_pow_Suc)
  have cast_eq: "(of_nat (Suc (Suc n)) :: 'k) = of_nat (Suc n) + 1"
    by (simp add: of_nat_Suc add.commute)
  have scalar_step: "abstract_scalar (of_nat (Suc (Suc n))) = qa (abstract_scalar (of_nat (Suc n))) q1"
    by (simp only: cast_eq abstract_scalar_add abstract_scalar_one)
  have coeff: "qa (qm (abstract_scalar (of_nat (Suc n))) (qpow qY (Suc n))) (qpow qY (Suc n)) =
      qm (abstract_scalar (of_nat (Suc (Suc n)))) (qpow qY (Suc n))"
    by (simp only: scalar_step W.scalar.S.l_distr[OF quotient_scalar_closed W.scalar.S.one_closed y_power_closed]
      W.scalar.S.l_one[OF y_power_closed])
  have rearrange: "qa (qm (qa (qm qX (qpow qY (Suc n)))
        (qm (abstract_scalar (of_nat (Suc n))) (qpow qY n))) qY) (qpow qY (Suc n)) =
      qa (qm qX (qm (qpow qY (Suc n)) qY))
        (qa (qm (abstract_scalar (of_nat (Suc n))) (qm (qpow qY n) qY)) (qpow qY (Suc n)))"
    using quotient_X_closed[where 'k='k] quotient_Y_closed[where 'k='k]
      y_power_closed[of n] y_power_closed[of "Suc n"] quotient_scalar_closed[of "of_nat (Suc n) :: 'k"]
    by algebra
  have "qm (qpow qY (Suc (Suc n))) qX = qm (qpow qY (Suc n)) (qm qY qX)"
      by (simp only: ps[symmetric])
         (rule W.scalar.S.m_assoc[OF y_power_closed quotient_Y_closed quotient_X_closed])
  also have "... = qm (qpow qY (Suc n)) (qa (qm qX qY) q1)"
      by (simp only: abstract_relation)
  also have "... = qa (qm (qm (qpow qY (Suc n)) qX) qY) (qpow qY (Suc n))"
      by (simp only: W.scalar.S.r_distr[OF
          W.scalar.S.m_closed[OF quotient_X_closed quotient_Y_closed] W.scalar.S.one_closed y_power_closed]
        W.scalar.S.r_one[OF y_power_closed]
        W.scalar.S.m_assoc[OF y_power_closed quotient_X_closed quotient_Y_closed])
  also have "... = qa (qm (qa (qm qX (qpow qY (Suc n)))
          (qm (abstract_scalar (of_nat (Suc n))) (qpow qY n))) qY) (qpow qY (Suc n))"
      by (simp only: Suc.IH)
  also have "... = qa (qm qX (qpow qY (Suc (Suc n))))
          (qa (qm (abstract_scalar (of_nat (Suc n))) (qpow qY (Suc n))) (qpow qY (Suc n)))"
      by (simp only: rearrange pn ps)
  also have "... = qa (qm qX (qpow qY (Suc (Suc n))))
          (qm (abstract_scalar (of_nat (Suc (Suc n)))) (qpow qY (Suc n)))"
      by (simp only: coeff)
  finally show ?case .
qed

lemma abstract_normal_monomial_right_x_zero:
  "qm (abstract_normal_monomial i 0) qX = (abstract_normal_monomial (Suc i) 0 :: 'k weyl_free set)"
  by (simp add: abstract_normal_monomial_def quotient_X_closed)

lemma abstract_normal_monomial_right_x_succ:
  "qm (abstract_normal_monomial i (Suc j)) qX =
    qa (abstract_normal_monomial (Suc i) (Suc j))
      (qm (abstract_scalar (of_nat (Suc j))) (abstract_normal_monomial i j))"
proof -
  have coeff: "qm (qpow qX i) (abstract_scalar (of_nat (Suc j))) =
    qm (abstract_scalar (of_nat (Suc j))) (qpow qX i)"
    by (rule quotient_scalar_central[OF x_power_closed, symmetric])
  have px: "qm (qpow qX i) qX = qpow qX (Suc i)"
    by (simp only: W.scalar.S.nat_pow_Suc)
  have "qm (abstract_normal_monomial i (Suc j)) qX =
      qm (qpow qX i) (qm (qpow qY (Suc j)) qX)"
      unfolding abstract_normal_monomial_def
      by (rule W.scalar.S.m_assoc[OF x_power_closed y_power_closed quotient_X_closed])
  also have "... = qm (qpow qX i) (qa (qm qX (qpow qY (Suc j)))
        (qm (abstract_scalar (of_nat (Suc j))) (qpow qY j)))"
      by (simp only: abstract_y_power_succ_mul_x)
  also have "... = qa (qm (qm (qpow qX i) qX) (qpow qY (Suc j)))
        (qm (qm (qpow qX i) (abstract_scalar (of_nat (Suc j)))) (qpow qY j))"
      using x_power_closed[of i] y_power_closed[of j] y_power_closed[of "Suc j"]
        quotient_X_closed[where 'k='k] quotient_scalar_closed[of "of_nat (Suc j) :: 'k"]
      by algebra
  also have "... = qa (abstract_normal_monomial (Suc i) (Suc j))
        (qm (abstract_scalar (of_nat (Suc j))) (abstract_normal_monomial i j))"
      unfolding abstract_normal_monomial_def
      by (simp only: px coeff; rule arg_cong2[where f=qa, OF refl])
         (rule W.scalar.S.m_assoc[OF quotient_scalar_closed x_power_closed y_power_closed])
  finally show ?thesis .
qed

lemma abstract_normal_monomial_right_x_in_span:
  "qm (abstract_normal_monomial i j) qX \<in> abstract_normal_span"
proof (cases j)
  case 0
  then show ?thesis by (simp only: abstract_normal_monomial_right_x_zero abstract_normal_span.monomial)
next
  case (Suc n)
  then show ?thesis
    by (simp only: abstract_normal_monomial_right_x_succ)
       (intro abstract_normal_span.add abstract_normal_span.scalar abstract_normal_span.monomial)
qed

lemma abstract_normal_monomial_right_y:
  "qm (abstract_normal_monomial i j) qY = (abstract_normal_monomial i (Suc j) :: 'k weyl_free set)"
  unfolding abstract_normal_monomial_def
  by (simp only: W.scalar.S.nat_pow_Suc)
     (rule W.scalar.S.m_assoc[OF x_power_closed y_power_closed quotient_Y_closed])

lemma abstract_span_right_x:
  "z \<in> abstract_normal_span \<Longrightarrow> qm z qX \<in> abstract_normal_span"
proof (induction rule: abstract_normal_span.induct)
  case (monomial i j) show ?case by (rule abstract_normal_monomial_right_x_in_span)
next
  case zero show ?case
    by (simp only: W.scalar.S.l_null[OF quotient_X_closed] abstract_normal_span.zero)
next
  case (add z w)
  have eq: "qm (qa z w) qX = qa (qm z qX) (qm w qX)"
    by (rule W.scalar.S.l_distr[OF abstract_span_closed[OF add.hyps(1)]
      abstract_span_closed[OF add.hyps(2)] quotient_X_closed])
  show ?case unfolding eq by (rule abstract_normal_span.add[OF add.IH])
next
  case (scalar z c)
  have eq: "qm (qm (abstract_scalar c) z) qX = qm (abstract_scalar c) (qm z qX)"
    by (rule W.scalar.S.m_assoc[OF quotient_scalar_closed abstract_span_closed[OF scalar.hyps] quotient_X_closed])
  show ?case unfolding eq by (rule abstract_normal_span.scalar[OF scalar.IH])
qed

lemma abstract_span_right_y:
  "z \<in> abstract_normal_span \<Longrightarrow> qm z qY \<in> abstract_normal_span"
proof (induction rule: abstract_normal_span.induct)
  case (monomial i j) show ?case by (simp only: abstract_normal_monomial_right_y abstract_normal_span.monomial)
next
  case zero show ?case
    by (simp only: W.scalar.S.l_null[OF quotient_Y_closed] abstract_normal_span.zero)
next
  case (add z w)
  have eq: "qm (qa z w) qY = qa (qm z qY) (qm w qY)"
    by (rule W.scalar.S.l_distr[OF abstract_span_closed[OF add.hyps(1)]
      abstract_span_closed[OF add.hyps(2)] quotient_Y_closed])
  show ?case unfolding eq by (rule abstract_normal_span.add[OF add.IH])
next
  case (scalar z c)
  have eq: "qm (qm (abstract_scalar c) z) qY = qm (abstract_scalar c) (qm z qY)"
    by (rule W.scalar.S.m_assoc[OF quotient_scalar_closed abstract_span_closed[OF scalar.hyps] quotient_Y_closed])
  show ?case unfolding eq by (rule abstract_normal_span.scalar[OF scalar.IH])
qed

lemma abstract_word_in_span:
  "abstract_mk (Poly_Mapping.single (Word bs) 1) \<in> (abstract_normal_span :: 'k weyl_free set set)"
proof (induction bs rule: rev_induct)
  case Nil
  have "(Poly_Mapping.single (Word []) 1 :: 'k weyl_free) = 1"
    by (simp only: free_word_zero[symmetric] Poly_Mapping.single_one)
  then show ?case by (simp only: abstract_mk_one abstract_one_in_span)
next
  case (snoc b bs)
  have word: "(Poly_Mapping.single (Word (bs@[b])) 1 :: 'k weyl_free) =
    Poly_Mapping.single (Word bs) 1 * (if b then free_Y else free_X)"
    by (cases b) (simp_all add: free_X_def free_Y_def free_mult_single)
  show ?case unfolding word abstract_mk_mult
    using abstract_span_right_x[OF snoc.IH] abstract_span_right_y[OF snoc.IH]
    by (cases b) (simp_all only: if_True if_False abstract_X_def[symmetric] abstract_Y_def[symmetric])
qed

lemma abstract_single_in_span:
  "abstract_mk (Poly_Mapping.single w c) \<in> (abstract_normal_span :: 'k weyl_free set set)"
proof -
  obtain bs where w: "w = Word bs" by (cases w) auto
  have factor: "(Poly_Mapping.single w c :: 'k weyl_free) = free_scalar c * Poly_Mapping.single w 1"
    by (simp only: free_scalar_def Poly_Mapping.mult_single add.left_neutral mult.right_neutral)
  have mapped: "abstract_mk (Poly_Mapping.single w c) =
    qm (abstract_scalar c) (abstract_mk (Poly_Mapping.single w 1))"
    by (subst factor) (simp only: abstract_mk_mult abstract_scalar_def)
  have base: "abstract_mk (Poly_Mapping.single w 1) \<in> (abstract_normal_span :: 'k weyl_free set set)"
    unfolding w by (rule abstract_word_in_span)
  show ?thesis by (simp only: mapped) (rule abstract_normal_span.scalar[OF base])
qed

lemma abstract_free_image_in_span:
  "abstract_mk f \<in> (abstract_normal_span :: 'k weyl_free set set)"
proof (induction f rule: free_induct)
  case zero show ?case by (simp only: abstract_mk_zero abstract_normal_span.zero)
next
  case (add f g)
  show ?case unfolding abstract_mk_add by (rule abstract_normal_span.add[OF add.IH])
next
  case (single w c) show ?case by (rule abstract_single_in_span)
qed

lemma abstract_normal_span_eq_carrier:
  "(abstract_normal_span :: 'k weyl_free set set) = carrier Q"
proof (rule antisym)
  show "abstract_normal_span \<subseteq> carrier Q" by (rule subsetI) (erule abstract_span_closed)
  show "carrier Q \<subseteq> abstract_normal_span"
  proof
    fix z assume "z \<in> carrier Q"
    then obtain f where "z = abstract_mk f" using quotient_representative by blast
    then show "z \<in> abstract_normal_span" by (simp only: abstract_free_image_in_span)
  qed
qed

lemma abstract_normal_span_mult:
  assumes "z \<in> abstract_normal_span" "w \<in> abstract_normal_span"
  shows "qm z w \<in> abstract_normal_span"
  using W.scalar.S.m_closed[OF abstract_span_closed[OF assms(1)] abstract_span_closed[OF assms(2)]]
  by (simp only: abstract_normal_span_eq_carrier)

end
end
