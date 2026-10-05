/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CrossingMultiplicity
public import DixmierFormal.Weyl.CrossingTermCount
public import DixmierFormal.Scalar.SparseRoots

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Six-component numerical squeeze for strict crossings

This module proves the root-multiplicity term-count inequality and the
finite arithmetic conclusion of paper Lemma 5.1. The scalar hypothesis
is the full general crossing equation, not yet its classified special
case. The native face-to-mass transfer is already proved separately.
-/

namespace Dixmier.Weyl
open Polynomial

theorem crossing_power_multiplicity_lt_termCount
    (r : ℂ[X]) (k : ℕ) {α : ℂ}
    (hr0 : r.coeff 0 = 1) (hα : r.IsRoot α) :
    k * rootMultiplicity α r < Dixmier.termCount (r ^ k) := by
  have hrne : r ≠ 0 := by
    intro hz
    rw [hz] at hr0
    simp at hr0
  have hr0eval : r.eval 0 = 1 := by simpa only [coeff_zero_eq_eval_zero] using hr0
  have hαne : α ≠ 0 := by
    intro hz
    rw [IsRoot, hz, hr0eval] at hα
    exact one_ne_zero hα
  have hdiv : ((X - C α) ^ rootMultiplicity α r) ^ k ∣ r ^ k :=
    pow_dvd_pow_of_dvd (pow_rootMultiplicity_dvd r α) k
  have hmult : k * rootMultiplicity α r ≤ rootMultiplicity α (r ^ k) :=
    (le_rootMultiplicity_iff (pow_ne_zero k hrne)).mpr (by
      rw [mul_comm k (rootMultiplicity α r), pow_mul]
      exact hdiv)
  exact hmult.trans_lt (Dixmier.rootMultiplicity_lt_termCount (pow_ne_zero k hrne) hαne)

theorem crossing_six_parameter_arithmetic (k a b q t : ℕ)
    (hk : 2 ≤ k) (hab : b < a) (haq : a < q)
    (hqt : k * q < t) (ht : t ≤ 6) :
    k = 2 ∧ a = 1 ∧ b = 0 ∧ q = 2 := by
  have hq : 2 ≤ q := by omega
  have hkq : 2 * q ≤ k * q := Nat.mul_le_mul_right q hk
  have hqk : k * 2 ≤ k * q := Nat.mul_le_mul_left k hq
  omega

/-- Any general strict-crossing scalar configuration with at most six
terms has the unique outer/start/multiplicity parameters `(2,1,0,2)`. -/
theorem crossing_mass_six_parameters_of_scalar
    (ρ s a b k : ℕ) (r f : ℂ[X])
    (hs : 0 < s) (hsρ : s < ρ) (hab : b < a) (hk : 2 ≤ k)
    (hr0 : r.coeff 0 = 1) (hr : 0 < r.natDegree)
    (h : Polynomial.C ((ρ : ℂ) - s) * Polynomial.X * f * r.derivative -
      ((Polynomial.C ((a : ℂ) - b) * f +
          Polynomial.C ((ρ : ℂ) * a - (s : ℂ) * b) * Polynomial.X * f.derivative + 1) * r) = 0)
    (ht : Dixmier.termCount (r ^ k) ≤ 6) :
    k = 2 ∧ a = 1 ∧ b = 0 ∧
      ∃ α : ℂ, r.IsRoot α ∧ rootMultiplicity α r = 2 := by
  obtain ⟨α, hα, haq, _⟩ :=
    crossing_exists_rootMultiplicity_gt_a ρ s a b r f hs hsρ hab hr0 hr h
  have hqt := crossing_power_multiplicity_lt_termCount r k hr0 hα
  obtain ⟨hk2, ha1, hb0, hq2⟩ :=
    crossing_six_parameter_arithmetic k a b (rootMultiplicity α r)
      (Dixmier.termCount (r ^ k)) hk hab haq hqt ht
  exact ⟨hk2, ha1, hb0, α, hα, hq2⟩

end Dixmier.Weyl
