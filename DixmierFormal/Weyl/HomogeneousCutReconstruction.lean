/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CrossingCutRootCount
public import DixmierFormal.Weyl.FaceCutMass

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Reconstruction from a homogeneous cut

Specialization at the first variable equal to one is injective on each
fixed weighted homogeneous component when the first weight is positive.
-/
namespace Dixmier.Weyl
open Polynomial

/-- The cut retains every coefficient of a fixed weighted homogeneous face. -/
theorem homogeneous_eq_of_specialization_eq
    (F G : MvPolynomial (Fin 2) ℂ) (ρ σ degree : ℤ)
    (hρ : 0 < ρ)
    (hF : F.IsWeightedHomogeneous (wt ρ σ) degree)
    (hG : G.IsWeightedHomogeneous (wt ρ σ) degree)
    (heq : MvPolynomial.eval₂ Polynomial.C
      (fun t : Fin 2 => if t = 0 then 1 else Polynomial.X) F =
      MvPolynomial.eval₂ Polynomial.C
      (fun t : Fin 2 => if t = 0 then 1 else Polynomial.X) G) : F = G := by
  classical
  apply MvPolynomial.ext
  intro d
  obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective d
  by_cases hw : (i : ℤ) * ρ + (j : ℤ) * σ = degree
  · rw [← homogeneous_specialization_coeff_at_support F ρ σ degree hρ hF i j hw,
      ← homogeneous_specialization_coeff_at_support G ρ σ degree hρ hG i j hw,
      heq]
  · have hz : ∀ H : MvPolynomial (Fin 2) ℂ,
        H.IsWeightedHomogeneous (wt ρ σ) degree →
        MvPolynomial.coeff (expo i j) H = 0 := by
      intro H hH
      by_contra hc
      have hh := hH hc
      rw [expo_weight] at hh
      exact hw hh
    rw [hz F hF, hz G hG]

/-- A polynomial diagonal cut has degree at most its homogeneous weight. -/
theorem diagonal_cut_natDegree_le
    (P : A1 ℂ) (n : ℕ) (hdegree : vDeg 1 1 P.1 = (n : ℤ)) :
    (cutPoly 1 1 P.1).natDegree ≤ n := by
  classical
  by_cases hz : cutPoly 1 1 P.1 = 0
  · simp [hz]
  have hm := Polynomial.natDegree_mem_support_of_nonzero hz
  have hs := cutPolynomial_support_subset_y_exponents (leadingForm 1 1 P.1) hm
  obtain ⟨d, hd, he⟩ := Finset.mem_image.mp hs
  obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective d
  have hh := MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
    (φ := symbol P.1) (w := wt 1 1) (n := vDeg 1 1 P.1)
    (MvPolynomial.mem_support_iff.mp hd)
  rw [expo_weight, hdegree] at hh
  have hj : j = (cutPoly 1 1 P.1).natDegree := by simpa [expo] using he
  norm_num at hh
  omega

/-- Reconstruct the two linear factors, retaining the possible first-axis factor. -/
theorem diagonal_face_eq_of_factored_cut
    (P : A1 ℂ) (lam α β : ℂ) (a u v : ℕ)
    (hdegree : vDeg 1 1 P.1 = ((a + u + v : ℕ) : ℤ))
    (hcut : cutPoly 1 1 P.1 = Polynomial.C lam *
      (Polynomial.X - Polynomial.C α)^u * (Polynomial.X - Polynomial.C β)^v) :
    leadingForm 1 1 P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ a *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^u *
      (MvPolynomial.X 1 - MvPolynomial.C β * MvPolynomial.X 0)^v := by
  have hX : MvPolynomial.IsWeightedHomogeneous (wt 1 1)
      (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℂ) 1 := by
    simpa [wt] using MvPolynomial.isWeightedHomogeneous_X ℂ (wt 1 1) (1 : Fin 2)
  have hY : MvPolynomial.IsWeightedHomogeneous (wt 1 1)
      (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) 1 := by
    simpa [wt] using MvPolynomial.isWeightedHomogeneous_X ℂ (wt 1 1) (0 : Fin 2)
  apply homogeneous_eq_of_specialization_eq _ _ 1 1 (vDeg 1 1 P.1) (by norm_num)
  · exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt 1 1) (n := vDeg 1 1 P.1)
  · rw [hdegree]
    simpa [nsmul_eq_mul, mul_assoc] using
      (((hY.pow a).mul ((hX.sub (hY.C_mul α)).pow u)).mul
        ((hX.sub (hY.C_mul β)).pow v)).C_mul lam
  · change cutPoly 1 1 P.1 = _
    rw [hcut]
    let φ := MvPolynomial.eval₂Hom Polynomial.C
      (fun i : Fin 2 => if i = 0 then (1 : ℂ[X]) else Polynomial.X)
    change _ = φ _
    simp only [map_mul, map_pow, map_sub]
    dsimp [φ]
    simp only [MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
    norm_num

/-- A constant diagonal cut reconstructs the pure first-axis monomial. -/
theorem diagonal_face_eq_of_constant_cut
    (P : A1 ℂ) (lam : ℂ) (n : ℕ)
    (hdegree : vDeg 1 1 P.1 = (n : ℤ))
    (hcut : cutPoly 1 1 P.1 = Polynomial.C lam) :
    leadingForm 1 1 P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ n := by
  simpa using diagonal_face_eq_of_factored_cut P lam 0 0 n 0 0
    (by simpa using hdegree) (by simpa using hcut)

end Dixmier.Weyl
