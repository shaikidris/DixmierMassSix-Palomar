/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.DescentTermination

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The terminal mate exponent is not one

The primitive crossing base has lowest `x`-power exactly one. It cannot be a
proper polynomial power, even after multiplication by a nonzero scalar.
The published proper-power input applied to the exact mate therefore rules
out the `j = 1` endpoint of the mate descent.
-/

namespace Dixmier.Weyl

open MvPolynomial Polynomial

/-- A scalar multiple of the strict-crossing primitive base cannot be a
proper power up to a nonzero scalar. -/
theorem crossingBase_not_proper_power
    (α ν a : ℂ) (q ρ s k : ℕ)
    (hs : 0 < s) (hν : ν ≠ 0) (ha : a ≠ 0) (hk : 2 ≤ k)
    (S : MvPolynomial (Fin 2) ℂ) (hS : S ≠ 0) :
    MvPolynomial.C ν *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ≠
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
  have hone : (E (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q)).natTrailingDegree = 1 := by
    simpa [E] using (crossingBase_power_natTrailingDegree α q ρ s 1 hs)
  have hR : E (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ≠ 0 := by
    intro hz
    simp [hz] at hone
  have hmap := congrArg E heq
  have hmap' : Polynomial.C (MvPolynomial.C ν) *
      E (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) =
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

/-- The proper-power part of the published homogeneous-companion input
excludes exponent one for an actual strict-crossing mate face. -/
theorem crossingFace_mate_exponent_ne_one
    (H : GGVInputs) (P Q : A1 ℂ) (α ν : ℂ)
    (q ρ s j : ℕ) (hs : 0 < s) (hν : ν ≠ 0)
    (hdir : IsDirection ρ (-(s : ℤ)))
    (h : IsCounterexamplePair P Q)
    (hQface : leadingForm ρ (-(s : ℤ)) Q.1 =
      MvPolynomial.C ν *
        (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
          MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ j) :
    j ≠ 1 := by
  intro hj
  have hswap := isCounterexamplePair_swap_neg P Q h
  obtain ⟨a, k, S, F, m, ha, hk, hS, hShom, hFhom, hface, hpoisson⟩ :=
    GGVInputs.companion H Q (-P) hswap ρ (-(s : ℤ)) hdir
  have heq : MvPolynomial.C ν *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) =
      MvPolynomial.C a * S ^ k := by
    rw [hQface, hj, pow_one] at hface
    exact hface
  exact crossingBase_not_proper_power α ν a q ρ s k hs hν ha hk S hS heq

/-- The exact descent and proper-power obstruction yield a terminal mate whose
reduced weight ratio has denominator `p`. The face and unrestricted mate are
retained for the subsequent Newton cut. -/
theorem crossingFace_prime_terminal
    (H : GGVInputs) (P Q : A1 ℂ) (μ α : ℂ)
    (p q ρ s : ℕ) (hμ : μ ≠ 0) (hp : p.Prime)
    (hs : 0 < s) (hsρ : s < ρ)
    (hdir : IsDirection ρ (-(s : ℤ)))
    (hPweight : vDeg ρ (-(s : ℤ)) P.1 = (p : ℤ) * ρ)
    (hPface : leadingForm ρ (-(s : ℤ)) P.1 =
      MvPolynomial.C μ *
        (MvPolynomial.X 0 * (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
          MvPolynomial.X 1 ^ ρ) ^ q) ^ p)
    (h : IsCounterexamplePair P Q) :
    ∃ (Q' : A1 ℂ) (j : ℕ) (ν : ℂ),
      IsCounterexamplePair P Q' ∧ 1 < j ∧ Nat.Coprime j p ∧ ν ≠ 0 ∧
      vDeg ρ (-(s : ℤ)) Q'.1 = (ρ * j : ℕ) ∧
      leadingForm ρ (-(s : ℤ)) Q'.1 =
        MvPolynomial.C ν *
          (MvPolynomial.X 0 * (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
            MvPolynomial.X 1 ^ ρ) ^ q) ^ j := by
  obtain ⟨Q', j, ν, hQ', hjpos, hnot, hν, hjweight, hQface⟩ :=
    crossingFace_mate_descent_terminal H P Q μ α p q ρ s hμ hp.two_le
      hs hsρ hPweight hPface h
  have hjne : j ≠ 1 :=
    crossingFace_mate_exponent_ne_one H P Q' α ν q ρ s j hs hν hdir hQ' hQface
  have hjgt : 1 < j := by omega
  exact ⟨Q', j, ν, hQ', hjgt, primeMateExponent_coprime hp hnot,
    hν, hjweight, hQface⟩

/-- The coprime terminal exponent pair supplies the exact signed divisibility,
cross-multiplication, and rational-ratio clauses of the cut interface. -/
theorem primeMate_terminal_signed_ratio
    (P Q : A1 ℂ) (p j ρ s : ℕ)
    (hp : p.Prime) (hj : 1 < j) (hρ : 0 < ρ)
    (hcoprime : Nat.Coprime j p)
    (hPweight : vDeg ρ (-(s : ℤ)) P.1 = (p : ℤ) * ρ)
    (hQweight : vDeg ρ (-(s : ℤ)) Q.1 = (ρ * j : ℕ)) :
    ¬ (vDeg ρ (-(s : ℤ)) P.1 ∣ vDeg ρ (-(s : ℤ)) Q.1) ∧
    ¬ (vDeg ρ (-(s : ℤ)) Q.1 ∣ vDeg ρ (-(s : ℤ)) P.1) ∧
    vDeg ρ (-(s : ℤ)) Q.1 * p =
      vDeg ρ (-(s : ℤ)) P.1 * j ∧
    ((vDeg ρ (-(s : ℤ)) Q.1 : ℚ) /
      (vDeg ρ (-(s : ℤ)) P.1 : ℚ)) = (j : ℚ) / p := by
  have hnot : ¬ p ∣ j := hp.coprime_iff_not_dvd.mp hcoprime.symm
  obtain ⟨hforward, hbackward⟩ :=
    primeMateWeights_nonintegral_int hp hj hρ hnot
  have hforward' : ¬ (vDeg ρ (-(s : ℤ)) P.1 ∣
      vDeg ρ (-(s : ℤ)) Q.1) := by
    rw [hPweight, hQweight]
    simpa only [Nat.cast_mul, mul_comm] using hforward
  have hbackward' : ¬ (vDeg ρ (-(s : ℤ)) Q.1 ∣
      vDeg ρ (-(s : ℤ)) P.1) := by
    rw [hPweight, hQweight]
    simpa only [Nat.cast_mul, mul_comm] using hbackward
  have hcross : vDeg ρ (-(s : ℤ)) Q.1 * p =
      vDeg ρ (-(s : ℤ)) P.1 * j := by
    rw [hPweight, hQweight]
    push_cast
    ring
  have hratio : ((vDeg ρ (-(s : ℤ)) Q.1 : ℚ) /
      (vDeg ρ (-(s : ℤ)) P.1 : ℚ)) = (j : ℚ) / p := by
    rw [hPweight, hQweight]
    simpa only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast,
      mul_comm] using (primeMateWeight_ratio hp hρ :
        ((j * ρ : ℕ) : ℚ) / ((p * ρ : ℕ) : ℚ) = (j : ℚ) / p)
  exact ⟨hforward', hbackward', hcross, hratio⟩

end Dixmier.Weyl
