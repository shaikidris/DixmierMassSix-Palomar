/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVDiagonalCutFactorization
public import DixmierFormal.Weyl.HomogeneousCutReconstruction

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Complete diagonal face shapes

The scalar root budget and homogeneous reconstruction classify the actual
face, retaining the residual first-axis factor and all root multiplicities.
-/
namespace Dixmier.Weyl
open Polynomial

/-- The diagonal leading form has at most two distinct finite root factors;
the first-axis factor is explicitly retained. -/
theorem preliminary_diagonal_face_classification
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) :
    (∃ (lam : ℂ) (a : ℕ), lam ≠ 0 ∧ 1 ≤ a ∧
      leadingForm 1 1 P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ a) ∨
    (∃ (lam α : ℂ) (a k : ℕ), lam ≠ 0 ∧ 1 ≤ k ∧
      leadingForm 1 1 P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ a *
        (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^k) ∨
    (∃ (lam α β : ℂ) (a u v : ℕ), lam ≠ 0 ∧ α ≠ β ∧ 1 ≤ u ∧ 1 ≤ v ∧
      leadingForm 1 1 P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ a *
        (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^u *
        (MvPolynomial.X 1 - MvPolynomial.C β * MvPolynomial.X 0)^v) := by
  have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 1
    (by norm_num [IsDirection])
  let n := (vDeg 1 1 P.1).toNat
  have hn : vDeg 1 1 P.1 = (n : ℤ) := by
    dsimp [n]
    exact (Int.toNat_of_nonneg (le_of_lt hp)).symm
  have hbound := diagonal_cut_natDegree_le P n hn
  rcases preliminary_diagonal_cut_factorization hsource P Q hpair with
    ⟨lam, hlam, hc⟩ | ⟨lam, α, k, hlam, hk, hc⟩ |
    ⟨lam, α, β, u, v, hlam, hab, hu, hv, hc⟩
  · refine Or.inl ⟨lam, n, hlam, ?_, diagonal_face_eq_of_constant_cut P lam n hn hc⟩
    omega
  · have hkn : k ≤ n := by
      rw [hc, natDegree_C_mul hlam, natDegree_pow, natDegree_X_sub_C] at hbound
      simpa using hbound
    have hd : vDeg 1 1 P.1 = ((n-k + k + 0 : ℕ) : ℤ) := by
      rw [hn]
      congr 1
      omega
    have hf := diagonal_face_eq_of_factored_cut P lam α 0 (n-k) k 0 hd
      (by simpa using hc)
    exact Or.inr (Or.inl ⟨lam, α, n-k, k, hlam, hk, by simpa using hf⟩)
  · have huv : u + v ≤ n := by
      rw [hc, natDegree_mul
        (mul_ne_zero (C_ne_zero.mpr hlam) (pow_ne_zero u (X_sub_C_ne_zero α)))
        (pow_ne_zero v (X_sub_C_ne_zero β)), natDegree_C_mul hlam,
        natDegree_pow, natDegree_pow, natDegree_X_sub_C, natDegree_X_sub_C] at hbound
      simpa using hbound
    have hd : vDeg 1 1 P.1 = ((n-(u+v) + u + v : ℕ) : ℤ) := by
      rw [hn]
      congr 1
      omega
    exact Or.inr (Or.inr ⟨lam, α, β, n-(u+v), u, v, hlam, hab, hu, hv,
      diagonal_face_eq_of_factored_cut P lam α β (n-(u+v)) u v hd hc⟩)

end Dixmier.Weyl
