/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCompanionFirstFace
public import DixmierFormal.Scalar.DiagonalLowestOrder

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Diagonal-start obstruction from an exact ramified companion

An exact finite fixed point of the first-contraction weight excludes a
diagonal minimum-order point on the actual leading face. The construction
of that fixed point from an arbitrary exact counterexample pair remains
the Joseph source obligation.
-/

namespace Dixmier.Weyl

theorem ramified_no_diagonal_start_of_bracket_coeffs
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P R : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hRne : R ≠ 0)
    (hbrcoeff : ∀ (j : ℕ) (v : ℤ),
      ramifiedWeight l ρ σ (v,j) = ramifiedWeightDeg l hl ρ σ P →
      ((ramifiedPBWCoeffs l hl (R * P - P * R)) j).coeff v =
        ((ramifiedPBWCoeffs l hl P) j).coeff v)
    (hRweight : ramifiedWeightDeg l hl ρ σ R =
      (l : ℤ) * (ρ + σ))
    (m : ℕ) (hm : 0 < m)
    (hpoint : ((l : ℤ) * (m : ℤ), m) ∈ ramifiedPBWSupport l hl P)
    (htop : ramifiedWeight l ρ σ ((l : ℤ) * (m : ℤ), m) =
      ramifiedWeightDeg l hl ρ σ P)
    (hmin : ∀ j ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support,
      m ≤ j) : False := by
  let g := ramifiedTopFacePolynomial l hl ρ σ P
  let f := ramifiedTopFacePolynomial l hl ρ σ R
  let D := ramifiedWeightDeg l hl ρ σ P
  let A := ramifiedWeightDeg l hl ρ σ R
  have hpointCoeff : ((ramifiedPBWCoeffs l hl P) m).coeff
      ((l : ℤ) * (m : ℤ)) ≠ 0 :=
    (ramifiedPBWSupport_mem_iff l hl P _ _).mp hpoint
  have hgm : g.coeff m ≠ 0 := by
    rw [← ramified_top_face_coeff_of_weight l hl ρ σ hρ P m
      ((l : ℤ) * (m : ℤ)) htop]
    exact hpointCoeff
  have hlow : ∀ j < m, g.coeff j = 0 := by
    intro j hj
    by_contra hc
    have hs : j ∈ g.support := Polynomial.mem_support_iff.mpr hc
    exact (not_le_of_gt hj) (hmin j hs)
  have hDA : D = A * (m : ℤ) := by
    dsimp [D, A]
    dsimp [ramifiedWeight] at htop
    nlinarith [hRweight]
  have hβ : ((A : ℂ) / ((l : ℂ) * (ρ : ℂ))) ≠ 0 := by
    have hA : A ≠ 0 := by
      dsimp [A]
      nlinarith [hRweight]
    have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hl
    have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
    exact div_ne_zero (by exact_mod_cast hA) (mul_ne_zero hlC hρC)
  have hdiag : (D : ℂ) / ((l : ℂ) * (ρ : ℂ)) =
      ((A : ℂ) / ((l : ℂ) * (ρ : ℂ))) * (m : ℂ) := by
    have hDAC : (D : ℂ) = (A : ℂ) * (m : ℂ) := by exact_mod_cast hDA
    rw [hDAC]
    ring
  have hneq := Dixmier.General.diagonal_lowest_order_bracket_ne
    f g ((D : ℂ) / ((l : ℂ) * (ρ : ℂ)))
      ((A : ℂ) / ((l : ℂ) * (ρ : ℂ))) m
      hm hβ hgm hlow hdiag
  apply hneq
  simpa only [f, g, A, D, mul_assoc] using
    (ramified_top_face_equation_of_bracket_coeffs
      l hl ρ σ hρ hsum P R hPne hRne hbrcoeff hRweight)

theorem ramified_fixed_point_no_diagonal_start
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P R : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hRne : R ≠ 0)
    (hfixed : R * P - P * R = P)
    (hRweight : ramifiedWeightDeg l hl ρ σ R =
      (l : ℤ) * (ρ + σ))
    (m : ℕ) (hm : 0 < m)
    (hpoint : ((l : ℤ) * (m : ℤ), m) ∈ ramifiedPBWSupport l hl P)
    (htop : ramifiedWeight l ρ σ ((l : ℤ) * (m : ℤ), m) =
      ramifiedWeightDeg l hl ρ σ P)
    (hmin : ∀ j ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support,
      m ≤ j) : False := by
  exact ramified_no_diagonal_start_of_bracket_coeffs
    l hl ρ σ hρ hsum P R hPne hRne
    (by intro j v _; rw [hfixed]) hRweight m hm hpoint htop hmin

/-- The exact non-diagonal-start assertion in the form consumed by the
maximum-root cut, conditional only on the required weighted fixed-point
operator. The mate has no order or support restriction. -/
theorem ramified_exact_pair_no_diagonal_start_of_bracket_coeffs
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P Q R : ramifiedOperatorAlgebra l)
    (hcomm : Q * P - P * Q = 1)
    (hPweight : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hRne : R ≠ 0)
    (hbrcoeff : ∀ (j : ℕ) (v : ℤ),
      ramifiedWeight l ρ σ (v,j) = ramifiedWeightDeg l hl ρ σ P →
      ((ramifiedPBWCoeffs l hl (R * P - P * R)) j).coeff v =
        ((ramifiedPBWCoeffs l hl P) j).coeff v)
    (hRweight : ramifiedWeightDeg l hl ρ σ R =
      (l : ℤ) * (ρ + σ)) :
    ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p = ramifiedWeightDeg l hl ρ σ P →
      (∀ q ∈ ramifiedPBWSupport l hl P,
        ramifiedWeight l ρ σ q = ramifiedWeightDeg l hl ρ σ P →
        p.2 ≤ q.2) →
      p.1 - (l : ℤ) * (p.2 : ℤ) ≠ 0 := by
  intro p hp htop hmin hdiag
  have hPne : P ≠ 0 := by
    intro hz
    rw [hz] at hcomm
    norm_num at hcomm
  have hi : p.1 = (l : ℤ) * (p.2 : ℤ) := sub_eq_zero.mp hdiag
  have hm : 0 < p.2 := by
    by_contra h
    have hzero : p.2 = 0 := by omega
    have hi0 : p.1 = 0 := by simpa [hzero] using hi
    simp [ramifiedWeight, hi0, hzero] at htop
    omega
  have hpoint : ((l : ℤ) * (p.2 : ℤ), p.2) ∈
      ramifiedPBWSupport l hl P := by
    simpa only [← hi] using hp
  have htop' : ramifiedWeight l ρ σ ((l : ℤ) * (p.2 : ℤ),p.2) =
      ramifiedWeightDeg l hl ρ σ P := by
    simpa only [← hi] using htop
  have hmin' : ∀ j ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support,
      p.2 ≤ j := by
    intro j hj
    obtain ⟨hjPBW,hjtop⟩ :=
      (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P j).mp hj
    let q : ℤ × ℕ := (ramifiedPBWTopLaurent l hl P j,j)
    have hq : q ∈ ramifiedPBWSupport l hl P :=
      ramifiedPBWTopLaurent_support l hl P j hjPBW
    exact hmin q hq hjtop
  exact ramified_no_diagonal_start_of_bracket_coeffs l hl ρ σ hρ hsum
    P R hPne hRne hbrcoeff hRweight p.2 hm hpoint htop' hmin'

/-- Source-facing scalar version: the homogeneous companion's actual
top-face equation suffices to exclude a diagonal start of an exact pair. -/
theorem ramified_exact_pair_no_diagonal_start_of_top_face_equation
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P Q F : ramifiedOperatorAlgebra l)
    (hcomm : Q * P - P * Q = 1)
    (hPweight : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hFne : F ≠ 0)
    (hFweight : ramifiedWeightDeg l hl ρ σ F =
      (l : ℤ) * (ρ + σ))
    (hscalar :
      Polynomial.C ((ramifiedWeightDeg l hl ρ σ P : ℂ) /
            ((l : ℂ) * (ρ : ℂ))) *
            ((ramifiedTopFacePolynomial l hl ρ σ F).derivative *
              ramifiedTopFacePolynomial l hl ρ σ P) -
        Polynomial.C ((ramifiedWeightDeg l hl ρ σ F : ℂ) /
            ((l : ℂ) * (ρ : ℂ))) *
            (ramifiedTopFacePolynomial l hl ρ σ F *
              (ramifiedTopFacePolynomial l hl ρ σ P).derivative) =
        ramifiedTopFacePolynomial l hl ρ σ P) :
    ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p = ramifiedWeightDeg l hl ρ σ P →
      (∀ q ∈ ramifiedPBWSupport l hl P,
        ramifiedWeight l ρ σ q = ramifiedWeightDeg l hl ρ σ P →
        p.2 ≤ q.2) →
      p.1 - (l : ℤ) * (p.2 : ℤ) ≠ 0 := by
  have hPne : P ≠ 0 := by
    intro hz
    rw [hz] at hcomm
    norm_num at hcomm
  exact ramified_exact_pair_no_diagonal_start_of_bracket_coeffs
    l hl ρ σ hρ hsum P Q F hcomm hPweight hFne
    (ramified_bracket_coeffs_of_top_face_equation
      l hl ρ σ hρ hsum P F hPne hFne hFweight hscalar)
    hFweight

theorem ramified_exact_pair_no_diagonal_start_of_fixed_point
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P Q R : ramifiedOperatorAlgebra l)
    (hcomm : Q * P - P * Q = 1)
    (hPweight : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hfixed : R * P - P * R = P)
    (hRweight : ramifiedWeightDeg l hl ρ σ R =
      (l : ℤ) * (ρ + σ)) :
    ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p = ramifiedWeightDeg l hl ρ σ P →
      (∀ q ∈ ramifiedPBWSupport l hl P,
        ramifiedWeight l ρ σ q = ramifiedWeightDeg l hl ρ σ P →
        p.2 ≤ q.2) →
      p.1 - (l : ℤ) * (p.2 : ℤ) ≠ 0 := by
  have hRne : R ≠ 0 := by
    intro hz
    rw [hz] at hfixed
    have hzero : P = 0 := by
      calc
        P = (0 : ramifiedOperatorAlgebra l) * P - P * 0 := hfixed.symm
        _ = 0 := by
          rw [zero_mul, mul_zero]
          exact sub_self (0 : ramifiedOperatorAlgebra l)
    rw [hzero] at hcomm
    norm_num at hcomm
  exact ramified_exact_pair_no_diagonal_start_of_bracket_coeffs
    l hl ρ σ hρ hsum P Q R hcomm hPweight hRne
    (by intro j v _; rw [hfixed]) hRweight

end Dixmier.Weyl
