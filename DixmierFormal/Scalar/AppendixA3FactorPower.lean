/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA3PositivePower

public import DixmierFormal.MvPolynomialCompat

@[expose] public section
namespace Dixmier
open Polynomial

/-- Multiplying two complex polynomials with positive real coefficients on their
full degree intervals preserves this property. -/
theorem positive_complex_coeff_mul {p q : ℂ[X]} {d e : ℕ}
    (hpd : p.natDegree ≤ d) (hqe : q.natDegree ≤ e)
    (hp : ∀ i ≤ d, ∃ x : ℝ, 0 < x ∧ p.coeff i = (x : ℂ))
    (hq : ∀ j ≤ e, ∃ x : ℝ, 0 < x ∧ q.coeff j = (x : ℂ)) :
    ∀ n ≤ d+e, ∃ x : ℝ, 0 < x ∧ (p*q).coeff n = (x : ℂ) := by
  let pr := realCoeffs p
  let qr := realCoeffs q
  have hpreal : ∀ n, (p.coeff n).im = 0 := by
    intro n
    by_cases hn : n ≤ d
    · obtain ⟨x,_,hx⟩ := hp n hn
      rw [hx]
      simp
    · have hz : p.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hz]
      simp
  have hqreal : ∀ n, (q.coeff n).im = 0 := by
    intro n
    by_cases hn : n ≤ e
    · obtain ⟨x,_,hx⟩ := hq n hn
      rw [hx]
      simp
    · have hz : q.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hz]
      simp
  have hpm : pr.map Complex.ofRealHom = p := realCoeffs_map hpreal
  have hqm : qr.map Complex.ofRealHom = q := realCoeffs_map hqreal
  have hinj : Function.Injective (Complex.ofRealHom : ℝ →+* ℂ) :=
    Complex.ofReal_injective
  have hprdeg : pr.natDegree ≤ d := by
    have heq : pr.natDegree = p.natDegree := by
      rw [← natDegree_map_eq_of_injective hinj, hpm]
    rw [heq]
    exact hpd
  have hqrdeg : qr.natDegree ≤ e := by
    have heq : qr.natDegree = q.natDegree := by
      rw [← natDegree_map_eq_of_injective hinj, hqm]
    rw [heq]
    exact hqe
  have hprpos : ∀ i ≤ d, 0 < pr.coeff i := by
    intro i hi
    obtain ⟨x,hx,hcoeff⟩ := hp i hi
    rw [realCoeffs_coeff, hcoeff]
    simpa using hx
  have hqrpos : ∀ j ≤ e, 0 < qr.coeff j := by
    intro j hj
    obtain ⟨x,hx,hcoeff⟩ := hq j hj
    rw [realCoeffs_coeff, hcoeff]
    simpa using hx
  intro n hn
  refine ⟨(pr*qr).coeff n, positive_coeff_mul hprdeg hqrdeg hprpos hqrpos n hn, ?_⟩
  have hmap : (pr*qr).map Complex.ofRealHom = p*q := by
    simpa only [Polynomial.map_mul, hpm, hqm]
  have heq := congrArg (fun R : ℂ[X] => R.coeff n) hmap
  rw [coeff_map] at heq
  exact heq.symm

end Dixmier

namespace Dixmier
open Polynomial

/-- The full-support conclusion for a quadratic factor times the square of a
cubic factor, conditional only on positive coefficients of both factors. -/
theorem positive_complex_quadratic_cubic_square_termCount {A B : ℂ[X]}
    (hAdeg : A.natDegree ≤ 2) (hBdeg : B.natDegree ≤ 3)
    (hApos : ∀ i ≤ 2, ∃ x : ℝ, 0 < x ∧ A.coeff i = (x : ℂ))
    (hBpos : ∀ j ≤ 3, ∃ x : ℝ, 0 < x ∧ B.coeff j = (x : ℂ))
    (k : ℕ) : termCount ((A*B^2)^k) = 8*k+1 := by
  have hB2deg : (B^2).natDegree ≤ 6 := by
    calc
      (B^2).natDegree ≤ 2*B.natDegree := natDegree_pow_le
      _ ≤ 2*3 := Nat.mul_le_mul_left 2 hBdeg
      _ = 6 := by norm_num
  have hB2pos : ∀ n ≤ 6, ∃ x : ℝ, 0 < x ∧ (B^2).coeff n = (x : ℂ) := by
    simpa only [pow_two] using (positive_complex_coeff_mul hBdeg hBdeg hBpos hBpos)
  have hRdeg : (A*B^2).natDegree ≤ 8 := by
    calc
      (A*B^2).natDegree ≤ A.natDegree+(B^2).natDegree := natDegree_mul_le
      _ ≤ 2+6 := Nat.add_le_add hAdeg hB2deg
      _ = 8 := by norm_num
  have hRpos : ∀ n ≤ 8, ∃ x : ℝ, 0 < x ∧ (A*B^2).coeff n = (x : ℂ) := by
    simpa only [show 2+6=8 by norm_num] using
      (positive_complex_coeff_mul hAdeg hB2deg hApos hB2pos)
  simpa only [Nat.mul_comm] using positive_complex_dense_power_termCount hRdeg hRpos k

end Dixmier
