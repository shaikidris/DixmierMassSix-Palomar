/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CrossingTermCount

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Lattice support of the strict-crossing companion

In a primitive strict direction `(ρ,-s)`, every nonnegative lattice point
of weight `ρ-s` lies on the ray `(1+st,1+ρt)`. This is the support
calculation behind the paper's homogeneous companion `xy f(x^s y^ρ)`.
-/

namespace Dixmier.Weyl

/-- Nonnegative solutions of `ρ i - s j = ρ - s` lie on one primitive ray. -/
theorem companion_weight_lattice
    (ρ s i j : ℕ) (hs : 0 < s) (hsρ : s < ρ) (hc : Nat.Coprime ρ s)
    (hw : (ρ : ℤ) * i - s * j = ρ - s) :
    ∃ t : ℕ, i = 1 + s * t ∧ j = 1 + ρ * t := by
  have hi : 0 < i := by
    by_contra h
    have hi0 : i = 0 := by omega
    subst i
    have hsj : (0 : ℤ) ≤ (s : ℤ) * j := mul_nonneg (by omega) (by omega)
    omega
  have hj : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    subst j
    have hρi : (ρ : ℤ) ≤ (ρ : ℤ) * i := by
      have hρnonneg : (0 : ℤ) ≤ ρ := by omega
      have hi1 : (1 : ℤ) ≤ i := by omega
      nlinarith
    omega
  have hnat : ρ * (i - 1) = s * (j - 1) := by
    have hsubi : i - 1 + 1 = i := by omega
    have hsubj : j - 1 + 1 = j := by omega
    have hnat' : (ρ : ℤ) * ((i - 1 : ℕ) : ℤ) =
        (s : ℤ) * ((j - 1 : ℕ) : ℤ) := by
      nlinarith [hw]
    exact_mod_cast hnat'
  have hdiv : s ∣ i - 1 := by
    apply (Nat.Coprime.dvd_mul_left hc.symm).mp
    rw [hnat]
    exact dvd_mul_right s (j - 1)
  obtain ⟨t, ht⟩ := hdiv
  refine ⟨t, ?_, ?_⟩
  · omega
  · have hcancel : ρ * t = j - 1 := by
      have h := hnat
      rw [ht] at h
      nlinarith [hs]
    omega

/-- Every actual monomial of a weight-`ρ-s` companion lies on that ray. -/
theorem companion_support_lattice
    (F : MvPolynomial (Fin 2) ℂ) (ρ s : ℕ)
    (hs : 0 < s) (hsρ : s < ρ) (hc : Nat.Coprime ρ s)
    (hF : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) ((ρ : ℤ) - s)) :
    ∀ d ∈ F.support, ∃ t : ℕ, d = expo (1 + s * t) (1 + ρ * t) := by
  intro d hd
  have hw := hF (MvPolynomial.mem_support_iff.mp hd)
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
  rw [expo_weight] at hw
  have hw' : (ρ : ℤ) * i - s * j = ρ - s := by
    nlinarith [hw]
  obtain ⟨t, hi, hj⟩ := companion_weight_lattice ρ s i j hs hsρ hc hw'
  exact ⟨t, by rw [hi, hj]⟩

end Dixmier.Weyl
