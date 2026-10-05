/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CrossingBaseShape

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Grading restriction from strict crossing

The primitive crossing ray lowers the grade as its parameter increases.
Consequently, if the least-`x` monomial had `a ≤ b`, all grades of the
homogeneous base and every power would be nonpositive. A strict crossing
face has a positive grade, forcing `b < a`.
-/

namespace Dixmier.Weyl
open MvPolynomial Polynomial
set_option maxHeartbeats 1000000

theorem grade_add (d e : Fin 2 →₀ ℕ) : grade (d + e) = grade d + grade e := by
  simp [grade]
  omega

/-- Polynomials supported in nonpositive grades are closed under product. -/
theorem support_grade_nonpos_mul
    (P Q : MvPolynomial (Fin 2) ℂ)
    (hP : ∀ d ∈ P.support, grade d ≤ 0)
    (hQ : ∀ d ∈ Q.support, grade d ≤ 0) :
    ∀ d ∈ (P * Q).support, grade d ≤ 0 := by
  intro d hd
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  rw [grade_add]
  exact add_nonpos (hP u hu) (hQ v hv)

/-- Every power of a polynomial in nonpositive grades has the same property. -/
theorem support_grade_nonpos_pow
    (R : MvPolynomial (Fin 2) ℂ) (k : ℕ)
    (hR : ∀ d ∈ R.support, grade d ≤ 0) :
    ∀ d ∈ (R ^ k).support, grade d ≤ 0 := by
  induction k with
  | zero =>
      intro d hd
      simp at hd
      simp [hd, grade]
  | succ k ih =>
      rw [pow_succ]
      exact support_grade_nonpos_mul (R ^ k) R ih hR

theorem crossing_ray_nonpos_of_base_le
    (R : MvPolynomial (Fin 2) ℂ) (ρ s a b : ℕ)
    (hsρ : s < ρ) (hab : a ≤ b)
    (hray : ∀ d ∈ R.support, ∃ t : ℕ,
      d = expo (a + s * t) (b + ρ * t)) :
    ∀ d ∈ R.support, grade d ≤ 0 := by
  intro d hd
  obtain ⟨t, rfl⟩ := hray d hd
  have hst : (s : ℤ) * t ≤ (ρ : ℤ) * t :=
    mul_le_mul_of_nonneg_right (by omega) (by omega)
  simp [grade, expo]
  omega

/-- The initial monomial of a strict crossing base has positive grade. -/
theorem crossing_base_a_gt_b_of_strict_face
    (P : A1 ℂ) (R : MvPolynomial (Fin 2) ℂ)
    (μ : ℂ) (k ρ s a b : ℕ)
    (hμ : μ ≠ 0) (hsρ : s < ρ)
    (hray : ∀ d ∈ R.support, ∃ t : ℕ,
      d = expo (a + s * t) (b + ρ * t))
    (hface : leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ * R ^ k)
    (hcross : IsStrictCrossing ρ (-(s : ℤ)) P.1) :
    b < a := by
  by_contra h
  have hab : a ≤ b := by omega
  have hnonpos := crossing_ray_nonpos_of_base_le R ρ s a b hsρ hab hray
  obtain ⟨d, hd, hpos⟩ := hcross.2.1
  rw [hface, MvPolynomial.C_mul', MvPolynomial.support_smul_eq hμ] at hd
  exact not_le_of_gt hpos (support_grade_nonpos_pow R k hnonpos d hd)

/-- A nonzero scalar multiple of a powered monomial occupies one support point. -/
theorem monomial_power_face_support_one (μ : ℂ) (a b k : ℕ) (hμ : μ ≠ 0) :
    (MvPolynomial.C μ * ((MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b :
      MvPolynomial (Fin 2) ℂ) ^ k)).support.card = 1 := by
  rw [MvPolynomial.C_mul', MvPolynomial.support_smul_eq hμ]
  rw [mul_pow, ← pow_mul, ← pow_mul]
  simp [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
    MvPolynomial.support_monomial]

/-- The full normal-form portion of the paper's strict negative-crossing
reduction: the imported companion input, strict crossing, and primitive
direction produce a normalized nonconstant `r`, `b<a`, the face formula,
and equation (5.2), with no mass or mate-order restriction. This theorem
remains conditional on `GGVInputs`. -/
theorem strictCounterexample_crossing_scalar_of_GGV
    (H : GGVInputs) (P Q : A1 ℂ) (ρ s : ℕ)
    (hPQ : IsCounterexamplePair P Q)
    (hs : 0 < s) (hsρ : s < ρ) (hc : Nat.Coprime ρ s)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    (hcross : IsStrictCrossing ρ (-(s : ℤ)) P.1) :
    ∃ (μ : ℂ) (k a b : ℕ) (r f : ℂ[X]),
      μ ≠ 0 ∧ 2 ≤ k ∧ b < a ∧ r.coeff 0 = 1 ∧ 0 < r.natDegree ∧
      leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ *
        (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
          r.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) ^ k ∧
      (Polynomial.C ((ρ : ℂ) - s) * Polynomial.X * f * r.derivative -
        ((Polynomial.C ((a : ℂ) - b) * f +
            Polynomial.C ((ρ : ℂ) * a - (s : ℂ) * b) * Polynomial.X * f.derivative + 1) * r)) = 0 := by
  obtain ⟨μ₀, k, R, F, m, hμ₀, hk, hRne, hRhom, hFhom, hface, hbr⟩ :=
    H.companion P Q hPQ ρ (-(s : ℤ)) hdir
  obtain ⟨a, b, c, r, f, hcne, hr0, hray, hRshape, _hFshape, hscalar⟩ :=
    crossing_homogeneous_companion_scalar R F ρ s m hs hsρ hc hRne
      hRhom (by simpa only [sub_eq_add_neg] using hFhom) hbr
  have hab := crossing_base_a_gt_b_of_strict_face P R μ₀ k ρ s a b
    hμ₀ hsρ hray hface hcross
  have hrnon : r ≠ 1 := by
    intro hone
    have hcard : (leadingForm ρ (-(s : ℤ)) P.1).support.card = 1 := by
      rw [hface, hRshape, hone]
      simp only [Polynomial.eval₂_one, mul_one]
      convert monomial_power_face_support_one (μ₀ * c ^ k) a b k
        (mul_ne_zero hμ₀ (pow_ne_zero _ hcne)) using 1
      simp only [mul_pow, ← map_pow, map_mul]
      rw [mul_assoc]
    exact (Nat.ne_of_gt hcross.1) hcard
  have hrdeg : 0 < r.natDegree := by
    by_contra h
    have hz : r.natDegree ≤ 0 := by omega
    have hconst := Polynomial.eq_C_of_natDegree_le_zero hz
    simp only [hr0, map_one] at hconst
    exact hrnon hconst
  refine ⟨μ₀ * c ^ k, k, a, b, r, f, mul_ne_zero hμ₀ (pow_ne_zero _ hcne), hk,
    hab, hr0, hrdeg, ?_, hscalar⟩
  rw [hface, hRshape]
  simp only [mul_pow, ← map_pow, map_mul]
  ring

end Dixmier.Weyl
