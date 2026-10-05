/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCutWeightSupport

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Coefficients on the ramified shear edge

The derivative term in the exact PBW recurrence cannot reach the
highest permitted Laurent exponent. The surviving recurrence is the
commutative binomial recurrence.
-/
namespace Dixmier.Weyl

theorem LaurentUpper_coeff_zero_above (f : LaurentPolynomial ℂ)
    (B i : ℤ) (hf : LaurentUpper f B) (hBi : B < i) :
    f.coeff i = 0 := by
  by_contra hnz
  have hi := hf i (Finsupp.mem_support_iff.mpr hnz)
  omega

theorem ramifiedCutShift_mul_coeff (l : ℕ) (ρ σ : ℤ)
    (c : ℂ) (f : LaurentPolynomial ℂ) (i : ℤ) :
    (ramifiedCutShift l ρ σ c * f).coeff i =
      c * f.coeff (i - ramifiedCutExponent l ρ σ) := by
  rw [ramifiedCutShift, LaurentPolynomial.smul_eq_C_mul,
    ← LaurentPolynomial.single_eq_C_mul_T]
  simpa [sub_eq_add_neg, add_comm] using
    (AddMonoidAlgebra.coeff_single_mul_apply f c
      (ramifiedCutExponent l ρ σ) i)

/-- The exact PBW coefficient at the proposed upper edge. -/
noncomputable def ramifiedCutEdgeCoeff (l : ℕ) (ρ σ : ℤ)
    (c : ℂ) (n j : ℕ) : ℂ :=
  let k := ramifiedCutExponent l ρ σ
  ((ramifiedShiftPBWPower l (ramifiedCutShift l ρ σ c) n) j).coeff
    (((n : ℤ) - (j : ℤ)) * k)

/-- The first contraction vanishes at the upper edge, leaving precisely
the Pascal recurrence for a commutative binomial expansion. -/
theorem ramifiedCutEdgeCoeff_succ (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (c : ℂ) (n j : ℕ) :
    ramifiedCutEdgeCoeff l ρ σ c (n+1) j =
      (if j = 0 then 0 else ramifiedCutEdgeCoeff l ρ σ c n (j-1)) +
        c * ramifiedCutEdgeCoeff l ρ σ c n j := by
  let k := ramifiedCutExponent l ρ σ
  let a := ramifiedShiftPBWPower l (ramifiedCutShift l ρ σ c) n
  let E : ℤ := (((n+1 : ℕ) : ℤ) - (j : ℤ)) * k
  have hk : -(l : ℤ) < k :=
    ramifiedCutExponent_gt_neg_index l hl ρ σ hρ hdiv hpos
  have hgt : ((n : ℤ) - (j : ℤ)) * k < E + (l : ℤ) := by
    dsimp [E]
    nlinarith
  have hderiv : (ramifiedDerivative l (a j)).coeff E = 0 := by
    rw [ramifiedDerivative_coeff]
    have hz : (a j).coeff (E + (l : ℤ)) = 0 :=
      LaurentUpper_coeff_zero_above _ _ _
        (ramifiedCutPower_upper l hl ρ σ hρ hdiv hpos c n j) hgt
    simp [hz]
  have hshift : (ramifiedCutShift l ρ σ c * a j).coeff E =
      c * ramifiedCutEdgeCoeff l ρ σ c n j := by
    rw [ramifiedCutShift_mul_coeff]
    have hidx : E - k = ((n : ℤ) - (j : ℤ)) * k := by
      dsimp [E]
      ring
    rw [hidx]
    rfl
  have hprev : (if j = 0 then 0 else a (j-1)).coeff E =
      (if j = 0 then 0 else ramifiedCutEdgeCoeff l ρ σ c n (j-1)) := by
    by_cases hj : j = 0
    · simp [hj]
    · simp only [hj, ↓reduceIte]
      have hidx : E = ((n : ℤ) - ((j-1 : ℕ) : ℤ)) * k := by
        have hjcast : ((j-1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
        dsimp [E]
        rw [hjcast]
        ring
      rw [hidx]
      rfl
  change (ramifiedShiftPBWStep l (ramifiedCutShift l ρ σ c) a j).coeff E =
    (if j = 0 then 0 else ramifiedCutEdgeCoeff l ρ σ c n (j-1)) +
      c * ramifiedCutEdgeCoeff l ρ σ c n j
  rw [ramifiedShiftPBWStep_apply]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  rw [hprev, hderiv, hshift]
  simp

/-- The upper-edge coefficients are exactly those of the commutative
binomial `(y+c t^k)^n`, with the usual zero convention for `j>n`. -/
theorem ramifiedCutEdgeCoeff_binomial (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (c : ℂ) (n j : ℕ) :
    ramifiedCutEdgeCoeff l ρ σ c n j =
      (Nat.choose n j : ℂ) * c^(n-j) := by
  induction n generalizing j with
  | zero =>
      by_cases hj : j = 0
      · subst j
        simp [ramifiedCutEdgeCoeff, ramifiedShiftPBWPower,
          ← LaurentPolynomial.T_zero]
      · have hz := ramifiedShiftPBWPower_zero_above l
          (ramifiedCutShift l ρ σ c) 0 j (by omega)
        simp [ramifiedCutEdgeCoeff, hz,
          Nat.choose_eq_zero_of_lt (by omega : 0 < j)]
  | succ n ih =>
      by_cases hj0 : j = 0
      · subst j
        rw [ramifiedCutEdgeCoeff_succ l hl ρ σ hρ hdiv hpos c n 0]
        simp only [ite_true, zero_add, ih]
        simpa [pow_succ] using (mul_comm c (c^n))
      · by_cases hjle : j ≤ n
        · obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
          rw [ramifiedCutEdgeCoeff_succ l hl ρ σ hρ hdiv hpos c n (m+1)]
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false,
            ↓reduceIte, Nat.add_one_sub_one]
          rw [ih m, ih (m+1), Nat.choose_succ_succ]
          have hm : m+1 ≤ n := hjle
          have hpow : n-m = (n-(m+1))+1 := by omega
          have hpowC : c^(n-m) = c^(n-(1+m)) * c := by
            rw [hpow, pow_succ]
            simp [Nat.add_comm]
          have hex : n+1-(m+1) = n-m := by omega
          simp only [Nat.succ_eq_add_one, hex]
          simp only [hpowC]
          push_cast
          ring_nf
        · by_cases hjeq : j = n+1
          · subst j
            rw [ramifiedCutEdgeCoeff_succ l hl ρ σ hρ hdiv hpos c n (n+1)]
            simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false,
              ↓reduceIte, Nat.add_one_sub_one]
            rw [ih n, ih (n+1)]
            simp
          · have hgt : n+1 < j := by omega
            have hz := ramifiedShiftPBWPower_zero_above l
              (ramifiedCutShift l ρ σ c) (n+1) j hgt
            simp [ramifiedCutEdgeCoeff, hz,
              Nat.choose_eq_zero_of_lt hgt]

/-- The exact canonical PBW coefficient on the upper Newton edge. -/
theorem ramifiedCutPower_edge_pbwCoeff (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (c : ℂ) (n j : ℕ) :
    ramifiedPBWCoeff l hl
      ((ramifiedShiftedYGen l (ramifiedCutShift l ρ σ c))^n)
      (((n : ℤ) - (j : ℤ)) * ramifiedCutExponent l ρ σ) j =
      (Nat.choose n j : ℂ) * c^(n-j) := by
  rw [ramifiedPBWCoeff, ramifiedShiftPBWPower_canonical]
  exact ramifiedCutEdgeCoeff_binomial l hl ρ σ hρ hdiv hpos c n j

end Dixmier.Weyl
