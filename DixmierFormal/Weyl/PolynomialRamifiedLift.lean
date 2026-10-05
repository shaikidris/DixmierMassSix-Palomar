/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCutRootEndpoint
public import DixmierFormal.Weyl.Validation
public import DixmierFormal.Weyl.PositiveGradeNormalForms

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Finite PBW lift from the polynomial Weyl algebra

An element of `A₁(ℂ)` has a finite normal-ordered PBW expansion. We
reuse its exact coefficients and send `X^iY^j` to `T^(li)Y^j` in the
ramified operator algebra. The exact normal-ordering relation proves
that this finite lift is an injective algebra homomorphism. Its support
matches the scaled source PBW support; identifying the source cut
polynomial with the extracted ramified face remains a separate step.
-/
namespace Dixmier.Weyl

/-- A finite PBW coefficient sequence for a polynomial Weyl operator. -/
noncomputable def polynomialPBWData (P : A1 ℂ) : (ℕ × ℕ) →₀ ℂ :=
  Classical.choose (A1_exists_finiteNormalOrderedExpansion P)

theorem polynomialPBWData_eval (P : A1 ℂ) :
    (polynomialPBWData P).sum
      (fun p a => a • normalOrderedMonomial (K := ℂ) p.1 p.2) =
      (P : Module.End ℂ (Polynomial ℂ)) :=
  Classical.choose_spec (A1_exists_finiteNormalOrderedExpansion P)

theorem polynomialPBWData_coeff (P : A1 ℂ) (i j : ℕ) :
    polynomialPBWData P (i,j) =
      pbwCoeff (P : Module.End ℂ (Polynomial ℂ)) i j := by
  rw [← polynomialPBWData_eval P]
  exact (pbwCoeff_finsuppNormalOrderedSum (polynomialPBWData P) i j).symm

/-- The finite PBW lift into the algebra acting on Laurent polynomials
in `T=X^(1/l)`. The map is defined from the actual finite coefficients,
with no order or support cutoff. -/
noncomputable def polynomialRamifiedLift (l : ℕ)
    (P : A1 ℂ) : ramifiedOperatorAlgebra l :=
  (polynomialPBWData P).sum fun p a =>
    a • (ramifiedCoeffGen l
      (LaurentPolynomial.T ((l : ℤ) * (p.1 : ℤ))) *
      (ramifiedYGen l)^p.2)

theorem polynomialRamifiedLift_finite_sum (l : ℕ) (P : A1 ℂ) :
    polynomialRamifiedLift l P =
      ∑ p ∈ (polynomialPBWData P).support,
        polynomialPBWData P p •
          (ramifiedCoeffGen l
            (LaurentPolynomial.T ((l : ℤ) * (p.1 : ℤ))) *
            (ramifiedYGen l)^p.2) := by
  rfl

theorem ramifiedPBWCoeffs_polynomial_atom (l : ℕ) (hl : 0 < l)
    (i j : ℕ) :
    ramifiedPBWCoeffs l hl
      (ramifiedCoeffGen l
        (LaurentPolynomial.T ((l : ℤ) * (i : ℤ))) *
        (ramifiedYGen l)^j) =
      Finsupp.single j
        (LaurentPolynomial.T ((l : ℤ) * (i : ℤ))) := by
  apply ramifiedPBWCoeffs_eq_of_eval
  have hs := ramifiedNormalEvalLinear_single l j
    (LaurentPolynomial.T ((l : ℤ) * (i : ℤ)))
  change ramifiedNormalEval l
    (Finsupp.single j (LaurentPolynomial.T ((l : ℤ) * (i : ℤ)))) =
      ramifiedCoeffMul (LaurentPolynomial.T ((l : ℤ) * (i : ℤ))) *
        (ramifiedDerivative l)^j
  simpa only [ramifiedNormalEvalLinear_apply] using hs

theorem ramifiedPBWCoeffs_polynomial_finite_sum
    (l : ℕ) (hl : 0 < l) (s : Finset (ℕ × ℕ))
    (c : (ℕ × ℕ) → ℂ) :
    ramifiedPBWCoeffs l hl
      (∑ p ∈ s, c p •
        (ramifiedCoeffGen l
          (LaurentPolynomial.T ((l : ℤ) * (p.1 : ℤ))) *
          (ramifiedYGen l)^p.2)) =
      ∑ p ∈ s, Finsupp.single p.2
        (c p • LaurentPolynomial.T ((l : ℤ) * (p.1 : ℤ))) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      apply ramifiedPBWCoeffs_eq_of_eval
      simp [ramifiedNormalEval]
  | @insert p s hp ih =>
      simp only [Finset.sum_insert hp]
      rw [ramifiedPBWCoeffs_add, ramifiedPBWCoeffs_smul,
        ramifiedPBWCoeffs_polynomial_atom, Finsupp.smul_single, ih]

theorem polynomialRamifiedLift_pbwCoeffs (l : ℕ) (hl : 0 < l)
    (P : A1 ℂ) :
    ramifiedPBWCoeffs l hl (polynomialRamifiedLift l P) =
      ∑ p ∈ (polynomialPBWData P).support,
        Finsupp.single p.2
          (polynomialPBWData P p •
            LaurentPolynomial.T ((l : ℤ) * (p.1 : ℤ))) := by
  rw [polynomialRamifiedLift_finite_sum]
  exact ramifiedPBWCoeffs_polynomial_finite_sum l hl _ _

theorem polynomialRamifiedLift_pbwCoeff_finset (l : ℕ) (hl : 0 < l)
    (P : A1 ℂ) (k : ℤ) (j : ℕ) :
    ramifiedPBWCoeff l hl (polynomialRamifiedLift l P) k j =
      ∑ p ∈ (polynomialPBWData P).support,
        if p.2 = j ∧ (l : ℤ) * (p.1 : ℤ) = k then
          polynomialPBWData P p else 0 := by
  rw [ramifiedPBWCoeff, polynomialRamifiedLift_pbwCoeffs]
  simp only [Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_sum,
    Finsupp.single_apply]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpj : p.2 = j
  · simp [hpj, LaurentPolynomial.T_apply]
  · simp [hpj]

/-- The lifted coefficient at `T^(li)Y^j` is precisely the original
PBW coefficient of `X^iY^j`. -/
theorem polynomialRamifiedLift_pbwCoeff_scaled (l : ℕ) (hl : 0 < l)
    (P : A1 ℂ) (i j : ℕ) :
    ramifiedPBWCoeff l hl (polynomialRamifiedLift l P)
      ((l : ℤ) * (i : ℤ)) j =
      pbwCoeff (P : Module.End ℂ (Polynomial ℂ)) i j := by
  rw [polynomialRamifiedLift_pbwCoeff_finset]
  let c := polynomialPBWData P
  have huniq (p : ℕ × ℕ) (hpne : p ≠ (i,j)) :
      ¬ (p.2 = j ∧ (l : ℤ) * (p.1 : ℤ) = (l : ℤ) * (i : ℤ)) := by
    rintro ⟨hj,he⟩
    apply hpne
    have hlz : (l : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hl)
    have hi : p.1 = i := by
      have he' : (p.1 : ℤ) = (i : ℤ) :=
        (mul_left_cancel₀ hlz) he
      exact_mod_cast he'
    exact Prod.ext hi hj
  by_cases hmem : (i,j) ∈ c.support
  · rw [Finset.sum_eq_single (i,j)]
    · simp [polynomialPBWData_coeff P i j]
    · intro p hp hpne
      exact if_neg (huniq p hpne)
    · intro hnot
      exact (hnot hmem).elim
  · have hz : c (i,j) = 0 := Finsupp.notMem_support_iff.mp hmem
    have hsum :
        (∑ p ∈ c.support,
          if p.2 = j ∧ (l : ℤ) * (p.1 : ℤ) = (l : ℤ) * (i : ℤ)
          then c p else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have hpne : p ≠ (i,j) := by
        intro he
        subst p
        exact hmem hp
      exact if_neg (huniq p hpne)
    rw [hsum]
    rw [← polynomialPBWData_coeff P i j]
    exact hz.symm

/-- The polynomial lift has no fractional or negative Laurent exponents.
Every occupied exponent is of the form `li` for an original PBW
coefficient, with `i : ℕ`. -/
theorem polynomialRamifiedLift_pbwCoeff_zero_off_scaled (l : ℕ)
    (hl : 0 < l) (P : A1 ℂ) (k : ℤ) (j : ℕ)
    (hoff : ∀ i : ℕ, (l : ℤ) * (i : ℤ) ≠ k) :
    ramifiedPBWCoeff l hl (polynomialRamifiedLift l P) k j = 0 := by
  rw [polynomialRamifiedLift_pbwCoeff_finset]
  apply Finset.sum_eq_zero
  intro p hp
  have hne : ¬ (p.2 = j ∧ (l : ℤ) * (p.1 : ℤ) = k) := by
    rintro ⟨_,he⟩
    exact hoff p.1 he
  exact if_neg hne

theorem polynomialRamifiedLift_support_iff_scaled (l : ℕ)
    (hl : 0 < l) (P : A1 ℂ) (k : ℤ) (j : ℕ) :
    (k,j) ∈ ramifiedPBWSupport l hl (polynomialRamifiedLift l P) ↔
      ∃ i : ℕ, k = (l : ℤ) * (i : ℤ) ∧
        pbwCoeff (P : Module.End ℂ (Polynomial ℂ)) i j ≠ 0 := by
  constructor
  · intro hk
    by_contra hnone
    have hoff : ∀ i : ℕ, (l : ℤ) * (i : ℤ) ≠ k := by
      intro i he
      apply hnone
      refine ⟨i,he.symm,?_⟩
      have hc := (ramifiedPBWSupport_mem_iff l hl _ k j).mp hk
      rw [← he, polynomialRamifiedLift_pbwCoeff_scaled] at hc
      exact hc
    have hz := polynomialRamifiedLift_pbwCoeff_zero_off_scaled
      l hl P k j hoff
    exact (ramifiedPBWSupport_mem_iff l hl _ k j).mp hk hz
  · rintro ⟨i,rfl,hc⟩
    apply (ramifiedPBWSupport_mem_iff l hl _ _ j).mpr
    rw [polynomialRamifiedLift_pbwCoeff_scaled]
    exact hc

/-- The finite ramified support is exactly the scaled PBW symbol
support of the polynomial operator. -/
theorem polynomialRamifiedLift_support_iff_symbol (l : ℕ)
    (hl : 0 < l) (P : A1 ℂ) (k : ℤ) (j : ℕ) :
    (k,j) ∈ ramifiedPBWSupport l hl (polynomialRamifiedLift l P) ↔
      ∃ i : ℕ, k = (l : ℤ) * (i : ℤ) ∧
        expo i j ∈ (symbol (P : Module.End ℂ (Polynomial ℂ))).support := by
  rw [polynomialRamifiedLift_support_iff_scaled l hl P k j]
  simp_rw [MvPolynomial.mem_support_iff, symbol_coeff_pbwCoeff P]

theorem polynomialRamifiedLift_weight_scaled (l : ℕ)
    (ρ σ : ℤ) (i j : ℕ) :
    ramifiedWeight l ρ σ ((l : ℤ) * (i : ℤ),j) =
      (l : ℤ) * Finsupp.weight (wt ρ σ) (expo i j) := by
  rw [expo_weight]
  dsimp [ramifiedWeight]
  ring

/-- The finite ramified lift does not identify two distinct polynomial
Weyl operators. This is proved from exact PBW coefficient recovery. -/
theorem polynomialRamifiedLift_injective (l : ℕ) (hl : 0 < l) :
    Function.Injective (polynomialRamifiedLift l) := by
  intro P Q hPQ
  have hcoeff (i j : ℕ) :
      pbwCoeff (P : Module.End ℂ (Polynomial ℂ)) i j =
        pbwCoeff (Q : Module.End ℂ (Polynomial ℂ)) i j := by
    rw [← polynomialRamifiedLift_pbwCoeff_scaled l hl P i j,
      ← polynomialRamifiedLift_pbwCoeff_scaled l hl Q i j, hPQ]
  apply symbol_injective
  apply MvPolynomial.ext
  intro d
  obtain ⟨⟨i,j⟩,h⟩ := expo_surjective d
  rw [← h, symbol_coeff_pbwCoeff P, symbol_coeff_pbwCoeff Q]
  exact hcoeff i j

/-- Equality of all normal-ordered Laurent coefficients determines an
operator in the finite ramified algebra. -/
theorem ramifiedOperator_eq_of_pbwCoeff (l : ℕ) (hl : 0 < l)
    (T U : ramifiedOperatorAlgebra l)
    (h : ∀ k j, ramifiedPBWCoeff l hl T k j =
      ramifiedPBWCoeff l hl U k j) : T = U := by
  have hc : ramifiedPBWCoeffs l hl T = ramifiedPBWCoeffs l hl U := by
    ext j k
    exact h k j
  apply Subtype.ext
  have he := congrArg (ramifiedNormalEval l) hc
  simpa only [ramifiedPBWCoeffs_eval] using he

theorem polynomialRamifiedLift_add (l : ℕ) (hl : 0 < l)
    (P Q : A1 ℂ) :
    polynomialRamifiedLift l (P + Q) =
      polynomialRamifiedLift l P + polynomialRamifiedLift l Q := by
  apply ramifiedOperator_eq_of_pbwCoeff l hl
  intro k j
  by_cases hk : ∃ i : ℕ, k = (l : ℤ) * (i : ℤ)
  · obtain ⟨i,rfl⟩ := hk
    conv_rhs => rw [ramifiedPBWCoeff, ramifiedPBWCoeffs_add]
    simp only [Finsupp.add_apply, AddMonoidAlgebra.coeff_add]
    rw [← ramifiedPBWCoeff, ← ramifiedPBWCoeff]
    rw [polynomialRamifiedLift_pbwCoeff_scaled,
      polynomialRamifiedLift_pbwCoeff_scaled,
      polynomialRamifiedLift_pbwCoeff_scaled]
    exact pbwCoeff_add _ _ i j
  · have hoff : ∀ i : ℕ, (l : ℤ) * (i : ℤ) ≠ k := by
      intro i he
      exact hk ⟨i,he.symm⟩
    conv_rhs => rw [ramifiedPBWCoeff, ramifiedPBWCoeffs_add]
    simp only [Finsupp.add_apply, AddMonoidAlgebra.coeff_add]
    rw [← ramifiedPBWCoeff, ← ramifiedPBWCoeff]
    rw [polynomialRamifiedLift_pbwCoeff_zero_off_scaled l hl (P+Q) k j hoff,
      polynomialRamifiedLift_pbwCoeff_zero_off_scaled l hl P k j hoff,
      polynomialRamifiedLift_pbwCoeff_zero_off_scaled l hl Q k j hoff, add_zero]

theorem polynomialRamifiedLift_smul (l : ℕ) (hl : 0 < l)
    (c : ℂ) (P : A1 ℂ) :
    polynomialRamifiedLift l (c • P) =
      c • polynomialRamifiedLift l P := by
  apply ramifiedOperator_eq_of_pbwCoeff l hl
  intro k j
  by_cases hk : ∃ i : ℕ, k = (l : ℤ) * (i : ℤ)
  · obtain ⟨i,rfl⟩ := hk
    conv_rhs => rw [ramifiedPBWCoeff, ramifiedPBWCoeffs_smul]
    simp only [Finsupp.smul_apply, AddMonoidAlgebra.coeff_smul, smul_eq_mul]
    rw [← ramifiedPBWCoeff]
    rw [polynomialRamifiedLift_pbwCoeff_scaled,
      polynomialRamifiedLift_pbwCoeff_scaled]
    exact pbwCoeff_smul c _ i j
  · have hoff : ∀ i : ℕ, (l : ℤ) * (i : ℤ) ≠ k := by
      intro i he
      exact hk ⟨i,he.symm⟩
    conv_rhs => rw [ramifiedPBWCoeff, ramifiedPBWCoeffs_smul]
    simp only [Finsupp.smul_apply, AddMonoidAlgebra.coeff_smul, smul_eq_mul]
    rw [← ramifiedPBWCoeff]
    rw [polynomialRamifiedLift_pbwCoeff_zero_off_scaled l hl (c • P) k j hoff,
      polynomialRamifiedLift_pbwCoeff_zero_off_scaled l hl P k j hoff, mul_zero]

theorem polynomialRamifiedLift_zero (l : ℕ) (hl : 0 < l) :
    polynomialRamifiedLift l (0 : A1 ℂ) = 0 := by
  simpa using polynomialRamifiedLift_smul l hl (0 : ℂ) (0 : A1 ℂ)

noncomputable def polynomialRamifiedLiftLinear (l : ℕ) (hl : 0 < l) :
    A1 ℂ →ₗ[ℂ] ramifiedOperatorAlgebra l where
  toFun := polynomialRamifiedLift l
  map_add' := polynomialRamifiedLift_add l hl
  map_smul' := polynomialRamifiedLift_smul l hl

/-- The source PBW monomial, viewed inside the polynomial Weyl algebra. -/
noncomputable def polynomialNormalAtom (i j : ℕ) : A1 ℂ :=
  ⟨normalOrderedMonomial (K := ℂ) i j,
    normalOrderedSpan_le_A1
      (Submodule.subset_span ⟨(i,j), rfl⟩)⟩

theorem polynomialPBWData_atom (i j : ℕ) :
    polynomialPBWData (polynomialNormalAtom i j) =
      Finsupp.single (i,j) (1 : ℂ) := by
  ext p
  rw [polynomialPBWData_coeff]
  change pbwCoeff (normalOrderedMonomial (K := ℂ) i j) p.1 p.2 =
    Finsupp.single (i,j) (1 : ℂ) p
  rw [normalOrderedMonomial, pbwCoeff_normalOrdered_monomial]
  by_cases hp : p = (i,j)
  · subst p
    simp
  · have hpair : ¬ (p.1 = i ∧ p.2 = j) := by
      intro h
      exact hp (Prod.ext h.1 h.2)
    simp [hp, hpair]

theorem polynomialRamifiedLift_atom (l i j : ℕ) :
    polynomialRamifiedLift l (polynomialNormalAtom i j) =
      ramifiedCoeffGen l
        (LaurentPolynomial.T ((l : ℤ) * (i : ℤ))) *
          (ramifiedYGen l)^j := by
  simp [polynomialRamifiedLift, polynomialPBWData_atom]

theorem polynomialNormalAtom_sum (P : A1 ℂ) :
    (polynomialPBWData P).sum
      (fun p a => a • polynomialNormalAtom p.1 p.2) = P := by
  apply Subtype.ext
  simpa [Finsupp.sum, polynomialNormalAtom] using
    polynomialPBWData_eval P

theorem polynomialNormalAtom_X_mul (i j : ℕ) :
    polynomialNormalAtom 1 0 * polynomialNormalAtom i j =
      polynomialNormalAtom (i+1) j := by
  apply Subtype.ext
  change (xOp ℂ ^ 1 * yOp ℂ ^ 0) *
      (xOp ℂ ^ i * yOp ℂ ^ j) =
    xOp ℂ ^ (i+1) * yOp ℂ ^ j
  simp only [pow_one, pow_zero, mul_one]
  rw [← mul_assoc, ← pow_succ']

theorem polynomialRamifiedLift_X_mul_atom (l i j : ℕ) :
    polynomialRamifiedLift l
        (polynomialNormalAtom 1 0 * polynomialNormalAtom i j) =
      polynomialRamifiedLift l (polynomialNormalAtom 1 0) *
        polynomialRamifiedLift l (polynomialNormalAtom i j) := by
  rw [polynomialNormalAtom_X_mul,
    polynomialRamifiedLift_atom, polynomialRamifiedLift_atom,
    polynomialRamifiedLift_atom]
  simp only [Nat.cast_one, mul_one, pow_zero, mul_one]
  rw [← mul_assoc]
  congr 1
  apply Subtype.ext
  change ramifiedCoeffMul
      (LaurentPolynomial.T ((l : ℤ) * ((i+1 : ℕ) : ℤ))) =
    ramifiedCoeffMul (LaurentPolynomial.T (l : ℤ)) *
      ramifiedCoeffMul
        (LaurentPolynomial.T ((l : ℤ) * (i : ℤ)))
  rw [ramifiedCoeffMul_mul, ← LaurentPolynomial.T_add]
  congr 1
  push_cast
  ring

theorem polynomialNormalAtom_Y_mul_succ (i j : ℕ) :
    polynomialNormalAtom 0 1 * polynomialNormalAtom (i+1) j =
      polynomialNormalAtom (i+1) (j+1) +
        ((i+1 : ℂ) • polynomialNormalAtom i j) := by
  apply Subtype.ext
  change (xOp ℂ ^ 0 * yOp ℂ ^ 1) *
      (xOp ℂ ^ (i+1) * yOp ℂ ^ j) =
    xOp ℂ ^ (i+1) * yOp ℂ ^ (j+1) +
      ((i+1 : ℂ) • (xOp ℂ ^ i * yOp ℂ ^ j))
  simp only [pow_zero, one_mul, pow_one]
  rw [← mul_assoc, yOp_mul_xOp_pow_succ]
  rw [add_mul, smul_mul_assoc]
  rw [mul_assoc, ← pow_succ']

theorem polynomialRamifiedLift_X_mul (l : ℕ) (hl : 0 < l)
    (P : A1 ℂ) :
    polynomialRamifiedLift l (polynomialNormalAtom 1 0 * P) =
      polynomialRamifiedLift l (polynomialNormalAtom 1 0) *
        polynomialRamifiedLift l P := by
  classical
  let c := polynomialPBWData P
  have hP : c.sum (fun p a => a • polynomialNormalAtom p.1 p.2) = P :=
    polynomialNormalAtom_sum P
  have hL : polynomialRamifiedLift l P =
      ∑ p ∈ c.support, c p •
        polynomialRamifiedLift l (polynomialNormalAtom p.1 p.2) := by
    rw [← hP]
    change (polynomialRamifiedLiftLinear l hl)
      (∑ p ∈ c.support, c p • polynomialNormalAtom p.1 p.2) = _
    simp [polynomialRamifiedLiftLinear]
  calc
    polynomialRamifiedLift l (polynomialNormalAtom 1 0 * P) =
        polynomialRamifiedLift l
          (∑ p ∈ c.support, c p •
            (polynomialNormalAtom 1 0 * polynomialNormalAtom p.1 p.2)) := by
          rw [← hP]
          simp only [Finsupp.sum, Finset.mul_sum, mul_smul_comm]
    _ = ∑ p ∈ c.support, c p •
          polynomialRamifiedLift l
            (polynomialNormalAtom 1 0 * polynomialNormalAtom p.1 p.2) := by
          change (polynomialRamifiedLiftLinear l hl)
            (∑ p ∈ c.support, c p •
              (polynomialNormalAtom 1 0 * polynomialNormalAtom p.1 p.2)) = _
          simp [polynomialRamifiedLiftLinear]
    _ = polynomialRamifiedLift l (polynomialNormalAtom 1 0) *
          ∑ p ∈ c.support, c p •
            polynomialRamifiedLift l (polynomialNormalAtom p.1 p.2) := by
          simp only [polynomialRamifiedLift_X_mul_atom,
            Finset.mul_sum, mul_smul_comm]
    _ = _ := by
          rw [hL]

theorem ramifiedDerivative_T_scaled_succ (l : ℕ) (hl : 0 < l)
    (i : ℕ) :
    ramifiedDerivative l
      (LaurentPolynomial.T ((l : ℤ) * ((i+1 : ℕ) : ℤ))) =
        ((i+1 : ℂ) •
          LaurentPolynomial.T ((l : ℤ) * (i : ℤ))) := by
  have hpow : (LaurentPolynomial.T
      ((l : ℤ) * ((i+1 : ℕ) : ℤ)) : LaurentPolynomial ℂ) =
      (LaurentPolynomial.T (l : ℤ))^(i+1) := by
    rw [LaurentPolynomial.T_pow]
    congr 1
    push_cast
    ring
  rw [hpow, ramifiedDerivative_X_pow l hl]
  simp only [Nat.add_sub_cancel, LaurentPolynomial.T_pow]
  rw [mul_comm (i : ℤ) (l : ℤ)]
  simp

theorem ramifiedY_mul_scaled_X_succ (l : ℕ) (hl : 0 < l)
    (i : ℕ) :
    ramifiedYGen l *
      ramifiedCoeffGen l
        (LaurentPolynomial.T ((l : ℤ) * ((i+1 : ℕ) : ℤ))) =
    ramifiedCoeffGen l
        (LaurentPolynomial.T ((l : ℤ) * ((i+1 : ℕ) : ℤ))) *
      ramifiedYGen l +
      ((i+1 : ℂ) • ramifiedCoeffGen l
        (LaurentPolynomial.T ((l : ℤ) * (i : ℤ)))) := by
  apply Subtype.ext
  change ramifiedDerivative l *
      ramifiedCoeffMul
        (LaurentPolynomial.T ((l : ℤ) * ((i+1 : ℕ) : ℤ))) =
    ramifiedCoeffMul
        (LaurentPolynomial.T ((l : ℤ) * ((i+1 : ℕ) : ℤ))) *
      ramifiedDerivative l +
      ((i+1 : ℂ) • ramifiedCoeffMul
        (LaurentPolynomial.T ((l : ℤ) * (i : ℤ))))
  rw [ramified_normal_order, ramifiedDerivative_T_scaled_succ l hl i]
  congr 1
  apply LinearMap.ext
  intro f
  change ((i+1 : ℂ) •
      LaurentPolynomial.T ((l : ℤ) * (i : ℤ))) * f =
    (i+1 : ℂ) •
      (LaurentPolynomial.T ((l : ℤ) * (i : ℤ)) * f)
  rw [smul_mul_assoc]

theorem polynomialRamifiedLift_Y_mul_atom_succ
    (l : ℕ) (hl : 0 < l) (i j : ℕ) :
    polynomialRamifiedLift l
        (polynomialNormalAtom 0 1 * polynomialNormalAtom (i+1) j) =
      polynomialRamifiedLift l (polynomialNormalAtom 0 1) *
        polynomialRamifiedLift l (polynomialNormalAtom (i+1) j) := by
  rw [polynomialNormalAtom_Y_mul_succ,
    polynomialRamifiedLift_add l hl,
    polynomialRamifiedLift_smul l hl,
    polynomialRamifiedLift_atom, polynomialRamifiedLift_atom,
    polynomialRamifiedLift_atom]
  rw [polynomialRamifiedLift_atom l (i+1) j]
  have hone : ramifiedCoeffGen l (1 : LaurentPolynomial ℂ) = 1 := by
    apply Subtype.ext
    exact ramifiedCoeffMul_one
  simp [hone]
  have horder := ramifiedY_mul_scaled_X_succ l hl i
  simp only [Nat.cast_add, Nat.cast_one] at horder
  conv_rhs => rw [← mul_assoc, horder]
  rw [add_mul, smul_mul_assoc]
  simp only [mul_assoc, ← pow_succ']

theorem polynomialNormalAtom_Y_mul_zero (j : ℕ) :
    polynomialNormalAtom 0 1 * polynomialNormalAtom 0 j =
      polynomialNormalAtom 0 (j+1) := by
  apply Subtype.ext
  change (xOp ℂ ^ 0 * yOp ℂ ^ 1) *
      (xOp ℂ ^ 0 * yOp ℂ ^ j) =
    xOp ℂ ^ 0 * yOp ℂ ^ (j+1)
  simp only [pow_zero, one_mul, pow_one]
  exact (pow_succ' (yOp ℂ) j).symm

theorem polynomialRamifiedLift_Y_mul_atom_zero
    (l : ℕ) (j : ℕ) :
    polynomialRamifiedLift l
        (polynomialNormalAtom 0 1 * polynomialNormalAtom 0 j) =
      polynomialRamifiedLift l (polynomialNormalAtom 0 1) *
        polynomialRamifiedLift l (polynomialNormalAtom 0 j) := by
  rw [polynomialNormalAtom_Y_mul_zero,
    polynomialRamifiedLift_atom l 0 (j+1),
    polynomialRamifiedLift_atom l 0 1,
    polynomialRamifiedLift_atom l 0 j]
  have hone : ramifiedCoeffGen l (1 : LaurentPolynomial ℂ) = 1 := by
    apply Subtype.ext
    exact ramifiedCoeffMul_one
  simp only [Nat.cast_zero, mul_zero, LaurentPolynomial.T_zero, hone,
    one_mul]
  simpa using pow_succ' (ramifiedYGen l) j

set_option maxHeartbeats 1000000 in
theorem polynomialRamifiedLift_Y_mul (l : ℕ) (hl : 0 < l)
    (P : A1 ℂ) :
    polynomialRamifiedLift l (polynomialNormalAtom 0 1 * P) =
      polynomialRamifiedLift l (polynomialNormalAtom 0 1) *
        polynomialRamifiedLift l P := by
  classical
  let c := polynomialPBWData P
  have hP : c.sum (fun p a => a • polynomialNormalAtom p.1 p.2) = P :=
    polynomialNormalAtom_sum P
  have hL : polynomialRamifiedLift l P =
      ∑ p ∈ c.support, c p •
        polynomialRamifiedLift l (polynomialNormalAtom p.1 p.2) := by
    rw [← hP]
    change (polynomialRamifiedLiftLinear l hl)
      (∑ p ∈ c.support, c p • polynomialNormalAtom p.1 p.2) = _
    simp [polynomialRamifiedLiftLinear]
  calc
    polynomialRamifiedLift l (polynomialNormalAtom 0 1 * P) =
        polynomialRamifiedLift l
          (∑ p ∈ c.support, c p •
            (polynomialNormalAtom 0 1 * polynomialNormalAtom p.1 p.2)) := by
          rw [← hP]
          simp only [Finsupp.sum, Finset.mul_sum, mul_smul_comm]
    _ = ∑ p ∈ c.support, c p •
          polynomialRamifiedLift l
            (polynomialNormalAtom 0 1 * polynomialNormalAtom p.1 p.2) := by
          change (polynomialRamifiedLiftLinear l hl)
            (∑ p ∈ c.support, c p •
              (polynomialNormalAtom 0 1 * polynomialNormalAtom p.1 p.2)) = _
          simp [polynomialRamifiedLiftLinear]
    _ = polynomialRamifiedLift l (polynomialNormalAtom 0 1) *
          ∑ p ∈ c.support, c p •
            polynomialRamifiedLift l (polynomialNormalAtom p.1 p.2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          rw [mul_smul_comm]
          congr 1
          cases p.1 with
          | zero => exact polynomialRamifiedLift_Y_mul_atom_zero l p.2
          | succ i => exact polynomialRamifiedLift_Y_mul_atom_succ l hl i p.2
    _ = _ := by rw [hL]

theorem polynomialNormalAtom_X_eq :
    polynomialNormalAtom 1 0 =
      (⟨xOp ℂ, xOp_mem_A1⟩ : A1 ℂ) := by
  apply Subtype.ext
  simp [polynomialNormalAtom, normalOrderedMonomial]

theorem polynomialNormalAtom_Y_eq :
    polynomialNormalAtom 0 1 =
      (⟨yOp ℂ, yOp_mem_A1⟩ : A1 ℂ) := by
  apply Subtype.ext
  simp [polynomialNormalAtom, normalOrderedMonomial]

theorem polynomialNormalAtom_one :
    polynomialNormalAtom 0 0 = (1 : A1 ℂ) := by
  apply Subtype.ext
  simp [polynomialNormalAtom, normalOrderedMonomial]

theorem polynomialRamifiedLift_one (l : ℕ) :
    polynomialRamifiedLift l (1 : A1 ℂ) = 1 := by
  rw [← polynomialNormalAtom_one, polynomialRamifiedLift_atom]
  simp only [Nat.cast_zero, mul_zero, LaurentPolynomial.T_zero, pow_zero]
  have hone : ramifiedCoeffGen l (1 : LaurentPolynomial ℂ) = 1 := by
    apply Subtype.ext
    exact ramifiedCoeffMul_one
  rw [hone, one_mul]

theorem polynomialRamifiedLift_algebraMap (l : ℕ) (hl : 0 < l)
    (c : ℂ) :
    polynomialRamifiedLift l (algebraMap ℂ (A1 ℂ) c) =
      algebraMap ℂ (ramifiedOperatorAlgebra l) c := by
  calc
    polynomialRamifiedLift l (algebraMap ℂ (A1 ℂ) c) =
        polynomialRamifiedLift l (c • (1 : A1 ℂ)) := by
          simp [Algebra.smul_def]
    _ = c • polynomialRamifiedLift l (1 : A1 ℂ) :=
      polynomialRamifiedLift_smul l hl c 1
    _ = algebraMap ℂ (ramifiedOperatorAlgebra l) c := by
      rw [polynomialRamifiedLift_one]
      simp [Algebra.smul_def]

set_option maxHeartbeats 1000000 in
theorem polynomialRamifiedLift_mul (l : ℕ) (hl : 0 < l)
    (P Q : A1 ℂ) :
    polynomialRamifiedLift l (P * Q) =
      polynomialRamifiedLift l P * polynomialRamifiedLift l Q := by
  have key : ∀ x ∈ A1 ℂ,
      ∀ hx : x ∈ A1 ℂ, ∀ V : A1 ℂ,
      polynomialRamifiedLift l (⟨x,hx⟩ * V) =
        polynomialRamifiedLift l ⟨x,hx⟩ *
          polynomialRamifiedLift l V := by
    intro x hx
    refine Algebra.adjoin_induction
      (p := fun x _ => ∀ hx : x ∈ A1 ℂ, ∀ V : A1 ℂ,
        polynomialRamifiedLift l (⟨x,hx⟩ * V) =
          polynomialRamifiedLift l ⟨x,hx⟩ *
            polynomialRamifiedLift l V) ?_ ?_ ?_ ?_ hx
    · intro x hx hxA V
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · have heq : (⟨xOp ℂ,hxA⟩ : A1 ℂ) =
            polynomialNormalAtom 1 0 := by
          apply Subtype.ext
          simp [polynomialNormalAtom, normalOrderedMonomial]
        rw [heq]
        exact polynomialRamifiedLift_X_mul l hl V
      · have heq : (⟨yOp ℂ,hxA⟩ : A1 ℂ) =
            polynomialNormalAtom 0 1 := by
          apply Subtype.ext
          simp [polynomialNormalAtom, normalOrderedMonomial]
        rw [heq]
        exact polynomialRamifiedLift_Y_mul l hl V
    · intro c hxA V
      change polynomialRamifiedLift l
        ((algebraMap ℂ (A1 ℂ) c) * V) =
        polynomialRamifiedLift l
          (algebraMap ℂ (A1 ℂ) c) *
          polynomialRamifiedLift l V
      rw [← Algebra.smul_def, polynomialRamifiedLift_smul l hl,
        polynomialRamifiedLift_algebraMap l hl, Algebra.smul_def]
    · intro x y hx hy ihx ihy hxy V
      have hadd : (⟨x+y,hxy⟩ : A1 ℂ) =
          (⟨x,hx⟩ : A1 ℂ) + ⟨y,hy⟩ := Subtype.ext rfl
      rw [hadd]
      rw [add_mul, polynomialRamifiedLift_add l hl,
        polynomialRamifiedLift_add l hl, ihx hx V, ihy hy V, add_mul]
    · intro x y hx hy ihx ihy hxy V
      have hmul : (⟨x*y,hxy⟩ : A1 ℂ) =
          (⟨x,hx⟩ : A1 ℂ) * ⟨y,hy⟩ := Subtype.ext rfl
      rw [hmul, mul_assoc]
      rw [ihx hx (⟨y,hy⟩ * V), ihy hy V, ihx hx ⟨y,hy⟩,
        mul_assoc]
  exact key P.1 P.2 P.2 Q

/-- The finite PBW lift is an injective algebra homomorphism from the
polynomial Weyl algebra into each positive ramification algebra. -/
noncomputable def polynomialRamifiedLiftHom (l : ℕ) (hl : 0 < l) :
    A1 ℂ →ₐ[ℂ] ramifiedOperatorAlgebra l where
  toFun := polynomialRamifiedLift l
  map_one' := polynomialRamifiedLift_one l
  map_mul' := polynomialRamifiedLift_mul l hl
  map_zero' := polynomialRamifiedLift_zero l hl
  map_add' := polynomialRamifiedLift_add l hl
  commutes' := polynomialRamifiedLift_algebraMap l hl

theorem polynomialRamifiedLiftHom_injective (l : ℕ) (hl : 0 < l) :
    Function.Injective (polynomialRamifiedLiftHom l hl) :=
  polynomialRamifiedLift_injective l hl

theorem polynomialRamifiedLift_commutator (l : ℕ) (hl : 0 < l)
    (P Q : A1 ℂ) :
    polynomialRamifiedLift l (Q * P - P * Q) =
      polynomialRamifiedLift l Q * polynomialRamifiedLift l P -
        polynomialRamifiedLift l P * polynomialRamifiedLift l Q := by
  have hmap := map_sub (polynomialRamifiedLiftHom l hl) (Q * P) (P * Q)
  change polynomialRamifiedLift l (Q * P - P * Q) =
    polynomialRamifiedLift l (Q * P) -
      polynomialRamifiedLift l (P * Q) at hmap
  rw [polynomialRamifiedLift_mul l hl,
    polynomialRamifiedLift_mul l hl] at hmap
  exact hmap

theorem polynomialRamifiedLift_bracket_one (l : ℕ) (hl : 0 < l)
    (P Q : A1 ℂ) (h : Q * P - P * Q = 1) :
    polynomialRamifiedLift l Q * polynomialRamifiedLift l P -
        polynomialRamifiedLift l P * polynomialRamifiedLift l Q = 1 := by
  rw [← polynomialRamifiedLift_commutator l hl P Q, h,
    polynomialRamifiedLift_one]

end Dixmier.Weyl
