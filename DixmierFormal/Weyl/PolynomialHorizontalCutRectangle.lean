/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PolynomialHorizontalCutSupport
public import DixmierFormal.Weyl.GGVFourierRectangle

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Rectangle preservation by a polynomial horizontal cut

The finite derivative-order recurrence preserves the top PBW row. Combined
with the horizontal half-plane bound, this preserves an occupied rectangle
corner and total degree for the recovered polynomial operator.
-/
namespace Dixmier.Weyl

/-- A cut cannot raise a finite upper bound on derivative order. -/
theorem ramifiedCutAut_pbwCoeff_zero_above_bound
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (c : ℂ)
    (T : ramifiedOperatorAlgebra l) (b : ℕ)
    (hz : ∀ n : ℕ, b < n → ramifiedPBWCoeffs l hl T n = 0)
    (i : ℤ) (j : ℕ) (hj : b < j) :
    ramifiedPBWCoeff l hl (ramifiedCutAut l hl ρ σ c T) i j = 0 := by
  classical
  rw [ramifiedCutAut_pbwCoeff_finset]
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hbn : b < n
  · simp [hz n hbn]
  · rw [ramifiedShiftPBWPower_zero_above l _ n j (by omega)]
    simp

/-- The top PBW row is unchanged by a cut, without any bound on
Laurent exponents or on coefficients. -/
theorem ramifiedCutAut_pbwCoeff_top_row
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (c : ℂ)
    (T : ramifiedOperatorAlgebra l) (b : ℕ)
    (hz : ∀ n : ℕ, b < n → ramifiedPBWCoeffs l hl T n = 0)
    (i : ℤ) :
    ramifiedPBWCoeff l hl (ramifiedCutAut l hl ρ σ c T) i b =
      ramifiedPBWCoeff l hl T i b := by
  classical
  rw [ramifiedCutAut_pbwCoeff_finset]
  rw [Finset.sum_eq_single b]
  · rw [ramifiedShiftPBWPower_top, mul_one]
    rfl
  · intro n hn hnb
    by_cases hbn : b < n
    · simp [hz n hbn]
    · rw [ramifiedShiftPBWPower_zero_above l _ n b (by omega)]
      simp
  · intro hb
    have hzero : ramifiedPBWCoeffs l hl T b = 0 := Finsupp.notMem_support_iff.mp hb
    simp [hzero, ramifiedPBWCoeff]

private theorem polynomial_lift_zero_above_second_bound
    (P : A1 ℂ) (b : ℕ)
    (hb : ∀ e ∈ (symbol P.1).support, e 1 ≤ b) :
    ∀ n : ℕ, b < n → ramifiedPBWCoeffs 1 (by norm_num) (polynomialRamifiedLift 1 P) n = 0 := by
  intro n hn
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  change ((ramifiedPBWCoeffs 1 (by norm_num) (polynomialRamifiedLift 1 P)) n).coeff i = 0
  by_contra hne
  have hs : (i,n) ∈ ramifiedPBWSupport 1 (by norm_num) (polynomialRamifiedLift 1 P) :=
    (ramifiedPBWSupport_mem_iff 1 (by norm_num) _ i n).mpr (by simpa only [ramifiedPBWCoeff] using hne)
  obtain ⟨k, _, hk⟩ :=
    (polynomialRamifiedLift_support_iff_symbol 1 (by norm_num) P i n).mp hs
  have hle := hb (expo k n) hk
  simp [expo] at hle
  omega

/-- A recovered horizontal cut preserves the full occupied rectangle. -/
theorem polynomial_horizontal_cut_preserves_subrectangular
    (P R : A1 ℂ) (c : ℂ) (a b : ℕ)
    (hrect : IsSubrectangularAt P a b)
    (hrecover : polynomialRamifiedLift 1 R =
      ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 P)) :
    IsSubrectangularAt R a b := by
  have hz := polynomial_lift_zero_above_second_bound P b (fun e he => (hrect.2 e he).2)
  have htop := ramifiedCutAut_pbwCoeff_top_row 1 (by norm_num) 1 0 c
    (polynomialRamifiedLift 1 P) b hz (a : ℤ)
  rw [← hrecover] at htop
  have hcoeff : pbwCoeff R.1 a b = pbwCoeff P.1 a b := by
    simpa only [← polynomialRamifiedLift_pbwCoeff_scaled 1 (by norm_num),
      Int.natCast_one, one_mul] using htop
  refine ⟨?_, ?_⟩
  · rw [MvPolynomial.mem_support_iff, symbol_coeff_pbwCoeff, hcoeff]
    simpa only [symbol_coeff_pbwCoeff] using (MvPolynomial.mem_support_iff.mp hrect.1)
  · intro e he
    refine ⟨polynomial_horizontal_cut_first_coordinate_bound P R c a
      (fun d hd => (hrect.2 d hd).1) hrecover e he, ?_⟩
    by_contra hbad
    have hzero := ramifiedCutAut_pbwCoeff_zero_above_bound 1 (by norm_num) 1 0 c
      (polynomialRamifiedLift 1 P) b hz (e 0 : ℤ) (e 1) (by omega)
    rw [← hrecover] at hzero
    have hexpo : expo (e 0) (e 1) = e := by
      ext i
      fin_cases i <;> simp [expo]
    have hne : pbwCoeff R.1 (e 0) (e 1) ≠ 0 := by
      rw [← symbol_coeff_pbwCoeff]
      exact MvPolynomial.mem_support_iff.mp (hexpo.symm ▸ he)
    apply hne
    simpa only [← polynomialRamifiedLift_pbwCoeff_scaled 1 (by norm_num),
      Int.natCast_one, one_mul] using hzero

/-- Total degree is preserved for the occupied subrectangular source. -/
theorem polynomial_horizontal_cut_preserves_totalDeg
    (P R : A1 ℂ) (c : ℂ) (a b : ℕ)
    (hrect : IsSubrectangularAt P a b)
    (hrecover : polynomialRamifiedLift 1 R =
      ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 P)) :
    totalDeg R.1 = totalDeg P.1 := by
  rw [subrectangular_totalDeg_eq P a b hrect,
    subrectangular_totalDeg_eq R a b
      (polynomial_horizontal_cut_preserves_subrectangular P R c a b hrect hrecover)]

end Dixmier.Weyl
