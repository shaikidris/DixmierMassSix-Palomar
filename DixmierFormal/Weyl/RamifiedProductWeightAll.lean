/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedTopCommutator

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Arbitrary-output Newton weight bound for ramified PBW atom products

The previous contraction bound used an output index written as `r+m`.
Here the output index is arbitrary; a support witness supplies the
necessary index range and hence the exact contraction count.
-/

namespace Dixmier.Weyl

theorem ramifiedPBWCoeffs_atomProduct_support_order
    (l : ℕ) (hl : 0 < l)
    (f g : LaurentPolynomial ℂ) (n m j : ℕ)
    (hnz : ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
        (ramifiedCoeffGen l g * (ramifiedYGen l)^m)) j ≠ 0) :
    m ≤ j ∧ j ≤ n+m := by
  constructor
  · by_contra hbad
    have hj : j < m := by omega
    have hshape :
        (ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
            (ramifiedCoeffGen l g * (ramifiedYGen l)^m) =
          ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
            ramifiedCoeffGen l g) * (ramifiedYGen l)^m := by
      simp only [mul_assoc]
    rw [hshape] at hnz
    exact hnz (ramifiedPBWCoeffs_rightShift_zero_below l hl _ m j hj)
  · by_contra hbad
    have hj : n+m < j := by omega
    exact hnz (ramifiedPBWCoeffs_atomProduct_zero_above l hl f g n m j hj)

/-- A supported coefficient at any output derivative order `j` has
Newton weight at most the sum of input upper weights minus one step
for each of the `n+m-j` contractions. -/
theorem ramifiedPBWCoeffs_atomProduct_weight_upper_all
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (f g : LaurentPolynomial ℂ) (B C : ℤ)
    (hf : LaurentUpper f B) (hg : LaurentUpper g C)
    (n m j : ℕ) (v : ℤ)
    (hv : v ∈ (ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
        (ramifiedCoeffGen l g * (ramifiedYGen l)^m)) j).coeff.support) :
    ramifiedWeight l ρ σ (v,j) ≤
      ρ * (B+C) + (l : ℤ) * σ * ((n : ℤ)+(m : ℤ)) -
        (l : ℤ) * (ρ+σ) * (((n : ℤ)+(m : ℤ))-(j : ℤ)) := by
  have hnz : ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
        (ramifiedCoeffGen l g * (ramifiedYGen l)^m)) j ≠ 0 := by
    intro hz
    simp [hz] at hv
  have hmj := (ramifiedPBWCoeffs_atomProduct_support_order
    l hl f g n m j hnz).1
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hmj
  have hidx : m+r = r+m := by omega
  rw [hidx] at hv ⊢
  have h := ramifiedPBWCoeffs_atomProduct_weight_upper
    l hl ρ σ hρ f g B C hf hg n m r v hv
  convert h using 1 <;> push_cast <;> ring

/-- The same arbitrary-output weight bound holds for an atom
commutator: any surviving coefficient comes from at least one of its
two products, and the two bounds coincide. -/
theorem ramifiedPBWCoeffs_atomCommutator_weight_upper_all
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (f g : LaurentPolynomial ℂ) (B C : ℤ)
    (hf : LaurentUpper f B) (hg : LaurentUpper g C)
    (n m j : ℕ) (v : ℤ)
    (hv : v ∈ (ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
          (ramifiedCoeffGen l g * (ramifiedYGen l)^m) -
        (ramifiedCoeffGen l g * (ramifiedYGen l)^m) *
          (ramifiedCoeffGen l f * (ramifiedYGen l)^n)) j).coeff.support) :
    ramifiedWeight l ρ σ (v,j) ≤
      ρ * (B+C) + (l : ℤ) * σ * ((n : ℤ)+(m : ℤ)) -
        (l : ℤ) * (ρ+σ) * (((n : ℤ)+(m : ℤ))-(j : ℤ)) := by
  let U := ramifiedPBWCoeffs l hl
    ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
      (ramifiedCoeffGen l g * (ramifiedYGen l)^m)) j
  let V := ramifiedPBWCoeffs l hl
    ((ramifiedCoeffGen l g * (ramifiedYGen l)^m) *
      (ramifiedCoeffGen l f * (ramifiedYGen l)^n)) j
  have hsub : ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
          (ramifiedCoeffGen l g * (ramifiedYGen l)^m) -
        (ramifiedCoeffGen l g * (ramifiedYGen l)^m) *
          (ramifiedCoeffGen l f * (ramifiedYGen l)^n)) j = U-V := by
    simp [U, V, ramifiedPBWCoeffs_sub]
  by_cases hU : v ∈ U.coeff.support
  · exact ramifiedPBWCoeffs_atomProduct_weight_upper_all
      l hl ρ σ hρ f g B C hf hg n m j v hU
  · have hV : v ∈ V.coeff.support := by
      have hnz := Finsupp.mem_support_iff.mp hv
      rw [hsub, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply] at hnz
      have hUz : U.coeff v = 0 := Finsupp.notMem_support_iff.mp hU
      have hVnz : V.coeff v ≠ 0 := by
        intro hVz
        simp [hUz, hVz] at hnz
      exact Finsupp.mem_support_iff.mpr hVnz
    have h := ramifiedPBWCoeffs_atomProduct_weight_upper_all
      l hl ρ σ hρ g f C B hg hf m n j v hV
    convert h using 1 <;> ring

/-- At any output derivative order, a lower-weight input atom or a
second contraction misses the selected first-contraction weight.
This statement applies directly to an atom commutator, not only to
one multiplication order. -/
theorem ramifiedPBWCoeffs_atomCommutator_below_first_of_defect_all
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (f g : LaurentPolynomial ℂ) (B C A D : ℤ)
    (hf : LaurentUpper f B) (hg : LaurentUpper g C)
    (n m j : ℕ) (hc : j+1 ≤ n+m)
    (hP : ρ*B + (l : ℤ)*σ*(n : ℤ) ≤ A)
    (hQ : ρ*C + (l : ℤ)*σ*(m : ℤ) ≤ D)
    (hdefect : ρ*B + (l : ℤ)*σ*(n : ℤ) < A ∨
      ρ*C + (l : ℤ)*σ*(m : ℤ) < D ∨ j+2 ≤ n+m)
    (v : ℤ)
    (hv : v ∈ (ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l f * (ramifiedYGen l)^n) *
          (ramifiedCoeffGen l g * (ramifiedYGen l)^m) -
        (ramifiedCoeffGen l g * (ramifiedYGen l)^m) *
          (ramifiedCoeffGen l f * (ramifiedYGen l)^n)) j).coeff.support) :
    ramifiedWeight l ρ σ (v,j) < A+D-(l : ℤ)*(ρ+σ) := by
  have hw := ramifiedPBWCoeffs_atomCommutator_weight_upper_all
    l hl ρ σ hρ f g B C hf hg n m j v hv
  have hlz : (0 : ℤ) < (l : ℤ) := by exact_mod_cast hl
  have hstep : (0 : ℤ) < (l : ℤ)*(ρ+σ) := mul_pos hlz hsum
  have hgap : (1 : ℤ) ≤ (n : ℤ)+(m : ℤ)-(j : ℤ) := by omega
  rcases hdefect with hPstrict | hQstrict | hmore
  · nlinarith
  · nlinarith
  · have hgap2 : (2 : ℤ) ≤ (n : ℤ)+(m : ℤ)-(j : ℤ) := by omega
    nlinarith

end Dixmier.Weyl
