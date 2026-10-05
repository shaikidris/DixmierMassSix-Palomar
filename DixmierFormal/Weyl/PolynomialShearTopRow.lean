/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PolynomialHorizontalCutRectangle
public import DixmierFormal.Weyl.PolynomialMonomialShearRecovery

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Preservation of the highest polynomial PBW row

Recovered finite cut shears preserve a differential-order bound and every
coefficient in its top row. In particular, the occupied top-row endpoints
survive an exact polynomial monomial shear.
-/
namespace Dixmier.Weyl

theorem polynomial_lift_zero_above_y_bound
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


/-- Every polynomial recovery of a cut preserves its differential-order
bound and every coefficient at that bound. -/
theorem polynomial_cut_preserves_y_bound_and_top_row
    (P R : A1 ℂ) (ρ σ : ℤ) (c : ℂ) (b : ℕ)
    (hb : ∀ e ∈ (symbol P.1).support, e 1 ≤ b)
    (hrecover : polynomialRamifiedLift 1 R =
      ramifiedCutAut 1 (by norm_num) ρ σ c (polynomialRamifiedLift 1 P)) :
    (∀ e ∈ (symbol R.1).support, e 1 ≤ b) ∧
      (∀ i : ℕ, pbwCoeff R.1 i b = pbwCoeff P.1 i b) := by
  have hz := polynomial_lift_zero_above_y_bound P b hb
  constructor
  · intro e he
    by_contra hbad
    have hzero := ramifiedCutAut_pbwCoeff_zero_above_bound 1 (by norm_num) ρ σ c
      (polynomialRamifiedLift 1 P) b hz (e 0 : ℤ) (e 1) (by omega)
    rw [← hrecover] at hzero
    have hcoeff : pbwCoeff R.1 (e 0) (e 1) = 0 := by
      simpa only [← polynomialRamifiedLift_pbwCoeff_scaled 1 (by norm_num),
        Int.natCast_one, one_mul] using hzero
    have hexpo : expo (e 0) (e 1) = e := by
      ext t
      fin_cases t <;> simp [expo]
    have hne := MvPolynomial.mem_support_iff.mp he
    rw [← hexpo, symbol_coeff_pbwCoeff, hcoeff] at hne
    exact hne rfl
  · intro i
    have ht := ramifiedCutAut_pbwCoeff_top_row 1 (by norm_num) ρ σ c
      (polynomialRamifiedLift 1 P) b hz (i : ℤ)
    rw [← hrecover] at ht
    simpa only [← polynomialRamifiedLift_pbwCoeff_scaled 1 (by norm_num),
      Int.natCast_one, one_mul] using ht

/-- An occupied top-row point remains occupied after polynomial recovery. -/
theorem polynomial_cut_preserves_top_row_point
    (P R : A1 ℂ) (ρ σ : ℤ) (c : ℂ) (a b : ℕ)
    (hb : ∀ e ∈ (symbol P.1).support, e 1 ≤ b)
    (hpoint : expo a b ∈ (symbol P.1).support)
    (hrecover : polynomialRamifiedLift 1 R =
      ramifiedCutAut 1 (by norm_num) ρ σ c (polynomialRamifiedLift 1 P)) :
    expo a b ∈ (symbol R.1).support := by
  have ht := (polynomial_cut_preserves_y_bound_and_top_row P R ρ σ c b hb hrecover).2 a
  rw [MvPolynomial.mem_support_iff, symbol_coeff_pbwCoeff, ht]
  simpa only [symbol_coeff_pbwCoeff] using MvPolynomial.mem_support_iff.mp hpoint

end Dixmier.Weyl
