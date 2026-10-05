/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.HorizontalDescent
public import DixmierFormal.Weyl.PrimeTerminal

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Primitive horizontal base

The horizontal base is `x(1+αy)^2`. Its lowest `x`-degree is one, so
it cannot be a proper polynomial power. This is the boundary analogue
of the strict-crossing proper-power test.
-/

namespace Dixmier.Weyl

open MvPolynomial Polynomial
set_option maxHeartbeats 1000000

/-- The horizontal base begins in `x`-degree exactly one. -/
theorem horizontalBase_natTrailingDegree (α : ℂ) :
    (((MvPolynomial.finSuccEquiv ℂ 1)
      (MvPolynomial.X 0 *
        (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
          MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ))).natTrailingDegree) = 1 := by
  let E := MvPolynomial.finSuccEquiv ℂ 1
  let G : MvPolynomial (Fin 1) ℂ :=
    (1 + MvPolynomial.C α * MvPolynomial.X 0) ^ (2 : ℕ)
  have hG : G ≠ 0 := by
    intro hz
    have heval := congrArg (MvPolynomial.eval fun _ : Fin 1 => (0 : ℂ)) hz
    simp [G] at heval
  have hshape := horizontal_base_power_shape α 1
  simp only [pow_one, mul_one] at hshape
  have hx : E (MvPolynomial.X 0) = Polynomial.X := by
    simpa [E] using (MvPolynomial.finSuccEquiv_X_zero (R := ℂ) (n := 1))
  have hy : E (MvPolynomial.rename Fin.succ G) = Polynomial.C G := by
    simpa [E] using finSuccEquiv_rename_succ G
  have hE : E (MvPolynomial.X 0 *
      (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
        MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) =
      Polynomial.X * Polynomial.C G := by
    simp only [pow_one]
    rw [hshape, map_mul, hx, hy]
  change (E (MvPolynomial.X 0 *
    (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
      MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ))).natTrailingDegree = 1
  rw [hE]
  simpa only [pow_one] using
    (natTrailingDegree_X_pow_mul_of_coeff_zero_ne_zero
      (Polynomial.C G) 1 (by simpa using hG))

/-- A nonzero scalar multiple of the horizontal base is not a proper
polynomial power. The obstruction is its exact first `x`-order. -/
theorem horizontalBase_not_proper_power
    (α ν a : ℂ) (k : ℕ)
    (hν : ν ≠ 0) (ha : a ≠ 0) (hk : 2 ≤ k)
    (S : MvPolynomial (Fin 2) ℂ) (hS : S ≠ 0) :
    MvPolynomial.C ν *
      (MvPolynomial.X 0 *
        (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
          MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) ≠
      MvPolynomial.C a * S ^ k := by
  intro heq
  let E := MvPolynomial.finSuccEquiv ℂ 1
  have hES : E S ≠ 0 := by
    intro hz
    exact hS (E.injective (by simpa using hz))
  have hνC : (MvPolynomial.C ν : MvPolynomial (Fin 1) ℂ) ≠ 0 := by
    simpa using hν
  have haC : (MvPolynomial.C a : MvPolynomial (Fin 1) ℂ) ≠ 0 := by
    simpa using ha
  have hone : (E (MvPolynomial.X 0 *
      (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
        MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ))).natTrailingDegree = 1 := by
    exact horizontalBase_natTrailingDegree α
  have hR : E (MvPolynomial.X 0 *
      (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
        MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) ≠ 0 := by
    intro hz
    rw [hz] at hone
    simp at hone
  have hmap := congrArg E heq
  have hmap' : Polynomial.C (MvPolynomial.C ν) *
      E (MvPolynomial.X 0 *
        (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
          MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) =
      Polynomial.C (MvPolynomial.C a) * (E S) ^ k := by
    simpa [E, MvPolynomial.finSuccEquiv_apply] using hmap
  have horder := congrArg Polynomial.natTrailingDegree hmap'
  rw [Polynomial.natTrailingDegree_mul (Polynomial.C_ne_zero.mpr hνC) hR,
    Polynomial.natTrailingDegree_C,
    Polynomial.natTrailingDegree_mul (Polynomial.C_ne_zero.mpr haC)
      (pow_ne_zero k hES), Polynomial.natTrailingDegree_C,
    natTrailingDegree_pow_of_ne_zero (E S) hES] at horder
  rw [hone] at horder
  have hdiv : k ∣ 1 := ⟨(E S).natTrailingDegree,
    by simpa only [zero_add] using horder⟩
  have hkle : k ≤ 1 := Nat.le_of_dvd (by decide) hdiv
  omega

/-- The published proper-power input excludes a horizontal terminal mate
whose exponent is one. -/
theorem horizontal_mate_exponent_ne_one
    (H : GGVInputs) (P Q : A1 ℂ) (α ν : ℂ) (j : ℕ)
    (hν : ν ≠ 0) (hdir : IsDirection 1 0)
    (h : IsCounterexamplePair P Q)
    (hQface : leadingForm 1 0 Q.1 =
      MvPolynomial.C ν *
        (MvPolynomial.X 0 *
          (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
            MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) ^ j) :
    j ≠ 1 := by
  intro hj
  have hswap := isCounterexamplePair_swap_neg P Q h
  obtain ⟨a, k, S, F, m, ha, hk, hS, hShom, hFhom, hface, hpoisson⟩ :=
    GGVInputs.companion H Q (-P) hswap 1 0 hdir
  have heq : MvPolynomial.C ν *
      (MvPolynomial.X 0 *
        (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
          MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) =
      MvPolynomial.C a * S ^ k := by
    rw [hQface, hj, pow_one] at hface
    exact hface
  exact horizontalBase_not_proper_power α ν a k hν ha hk S hS heq

/-- Horizontal descent and the proper-power obstruction leave a genuine
terminal mate with coprime exponents `j,p`, unrestricted in degree. -/
theorem horizontal_prime_terminal
    (H : GGVInputs) (P Q : A1 ℂ) (μ α : ℂ) (p : ℕ)
    (hμ : μ ≠ 0) (hp : p.Prime)
    (hPface : leadingForm 1 0 P.1 =
      MvPolynomial.C μ *
        (MvPolynomial.X 0 *
          (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
            MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) ^ p)
    (h : IsCounterexamplePair P Q) :
    ∃ (Q' : A1 ℂ) (j : ℕ) (ν : ℂ),
      IsCounterexamplePair P Q' ∧ 1 < j ∧ Nat.Coprime j p ∧ ν ≠ 0 ∧
      vDeg 1 0 Q'.1 = j ∧
      leadingForm 1 0 Q'.1 =
        MvPolynomial.C ν *
          (MvPolynomial.X 0 *
            (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
              MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) ^ j := by
  have hPweight : vDeg 1 0 P.1 = (p : ℤ) := by
    simpa using crossingFace_weight_any_s P α μ 2 1 0 p hμ (by decide) hPface
  obtain ⟨Q', j, ν, hQ', hjpos, hnot, hν, hjweight, hQface⟩ :=
    horizontal_mate_descent_terminal H P Q μ α p hμ hp.two_le
      hPweight hPface h
  have hdir : IsDirection 1 0 := by
    simpa using (purePower_isDirection (q := 2) (s := 0) (ρ := 1)
      (by decide) (by decide))
  have hjne : j ≠ 1 :=
    horizontal_mate_exponent_ne_one H P Q' α ν j hν hdir hQ' hQface
  have hjgt : 1 < j := by omega
  exact ⟨Q', j, ν, hQ', hjgt, primeMateExponent_coprime hp hnot,
    hν, hjweight, hQface⟩

end Dixmier.Weyl
