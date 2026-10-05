/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedLeadingPoisson
public import DixmierFormal.Weyl.RamifiedCompanionSeed
public import DixmierFormal.Weyl.RamifiedCornerGradeBarrier

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

set_option maxHeartbeats 0

/-!
# The first face of a ramified companion

A leading-bracket coefficient identity yields the derivative-bracket
equation on the actual top face, provided the companion has the
first-contraction weight. An exact operator fixed point is one sufficient
special case. Existence of the source-facing homogeneous companion
remains the Joseph/GGV obligation.
-/

namespace Dixmier.Weyl

/-- At an output point on the actual maximum-weight line, its PBW
coefficient is exactly the corresponding coefficient of the canonical
top-face polynomial. This also covers absent derivative orders. -/
theorem ramified_top_face_coeff_of_weight
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (P : ramifiedOperatorAlgebra l) (j : ℕ) (v : ℤ)
    (hv : ramifiedWeight l ρ σ (v,j) =
      ramifiedWeightDeg l hl ρ σ P) :
    ((ramifiedPBWCoeffs l hl P) j).coeff v =
      (ramifiedTopFacePolynomial l hl ρ σ P).coeff j := by
  by_cases hc : ((ramifiedPBWCoeffs l hl P) j).coeff v = 0
  · have hp : (ramifiedTopFacePolynomial l hl ρ σ P).coeff j = 0 := by
      by_contra hpne
      have hj : j ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support :=
        Polynomial.mem_support_iff.mpr hpne
      obtain ⟨hjPBW,hjtop⟩ :=
        (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P j).mp hj
      have hvEq : v = ramifiedPBWTopLaurent l hl P j := by
        dsimp [ramifiedWeight] at hv
        nlinarith
      rw [hvEq] at hc
      apply hpne
      rw [ramifiedTopFacePolynomial_coeff_of_mem_support l hl ρ σ P j hj]
      exact hc
    rw [hc, hp]
  · have hmem : (v,j) ∈ ramifiedPBWSupport l hl P :=
      (ramifiedPBWSupport_mem_iff l hl P v j).mpr hc
    have hjPBW : j ∈ (ramifiedPBWCoeffs l hl P).support := by
      apply Finsupp.mem_support_iff.mpr
      intro hz
      simp [hz] at hc
    have hle := ramifiedPBWTopLaurent_upper l hl P j v
      (Finsupp.mem_support_iff.mpr hc)
    have htopmem := ramifiedPBWTopLaurent_support l hl P j hjPBW
    have htopweight := ramifiedWeight_le_weightDeg_of_mem
      l hl ρ σ P _ htopmem
    have hvEq : v = ramifiedPBWTopLaurent l hl P j := by
      dsimp [ramifiedWeight] at hv htopweight
      nlinarith
    have htop : ρ * ramifiedPBWTopLaurent l hl P j +
        (l : ℤ) * σ * (j : ℤ) = ramifiedWeightDeg l hl ρ σ P := by
      rw [← hvEq]
      exact hv
    rw [hvEq, ramifiedTopFacePolynomial_coeff, if_pos hjPBW, if_pos htop]

theorem ramified_first_face_coeff_of_bracket_coeffs
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P R : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hRne : R ≠ 0)
    (hbrcoeff : ∀ (j : ℕ) (v : ℤ),
      ramifiedWeight l ρ σ (v,j) = ramifiedWeightDeg l hl ρ σ P →
      ((ramifiedPBWCoeffs l hl (R * P - P * R)) j).coeff v =
        ((ramifiedPBWCoeffs l hl P) j).coeff v)
    (hRweight : ramifiedWeightDeg l hl ρ σ R = (l : ℤ) * (ρ + σ))
    (j : ℕ) (hj : j ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support) :
    (Polynomial.C ((ramifiedWeightDeg l hl ρ σ P : ℂ) /
          ((l : ℂ) * (ρ : ℂ))) *
          ((ramifiedTopFacePolynomial l hl ρ σ R).derivative *
            ramifiedTopFacePolynomial l hl ρ σ P) -
      Polynomial.C ((ramifiedWeightDeg l hl ρ σ R : ℂ) /
          ((l : ℂ) * (ρ : ℂ))) *
          (ramifiedTopFacePolynomial l hl ρ σ R *
            (ramifiedTopFacePolynomial l hl ρ σ P).derivative)).coeff j =
      (ramifiedTopFacePolynomial l hl ρ σ P).coeff j := by
  obtain ⟨hjPBW, hjtop⟩ :=
    (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P j).mp hj
  let v := ramifiedPBWTopLaurent l hl P j
  have hv : ramifiedWeight l ρ σ (v,j) =
      ramifiedWeightDeg l hl ρ σ R +
        ramifiedWeightDeg l hl ρ σ P - (l : ℤ) * (ρ + σ) := by
    dsimp [v, ramifiedWeight]
    rw [hRweight]
    omega
  have hbr := ramified_commutator_first_face_polynomial_bracket
    l hl ρ σ hρ hsum R P hRne hPne j v hv
  have hvP : ramifiedWeight l ρ σ (v,j) =
      ramifiedWeightDeg l hl ρ σ P := by
    rw [hv, hRweight]
    ring
  rw [hbrcoeff j v hvP] at hbr
  have hcoeff : ((ramifiedPBWCoeffs l hl P) j).coeff v =
      (ramifiedTopFacePolynomial l hl ρ σ P).coeff j := by
    rw [ramifiedTopFacePolynomial_coeff_of_mem_support l hl ρ σ P j hj]
  exact hbr.symm.trans hcoeff

/-- The source-facing bracket coefficient relation gives the entire leading-face
polynomial identity, including derivative orders absent from `P`'s
top support. The witness at the first-contraction weight is explicit. -/
theorem ramified_top_face_equation_of_bracket_coeffs
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P R : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hRne : R ≠ 0)
    (hbrcoeff : ∀ (j : ℕ) (v : ℤ),
      ramifiedWeight l ρ σ (v,j) = ramifiedWeightDeg l hl ρ σ P →
      ((ramifiedPBWCoeffs l hl (R * P - P * R)) j).coeff v =
        ((ramifiedPBWCoeffs l hl P) j).coeff v)
    (hRweight : ramifiedWeightDeg l hl ρ σ R = (l : ℤ) * (ρ + σ)) :
    Polynomial.C ((ramifiedWeightDeg l hl ρ σ P : ℂ) /
          ((l : ℂ) * (ρ : ℂ))) *
          ((ramifiedTopFacePolynomial l hl ρ σ R).derivative *
            ramifiedTopFacePolynomial l hl ρ σ P) -
      Polynomial.C ((ramifiedWeightDeg l hl ρ σ R : ℂ) /
          ((l : ℂ) * (ρ : ℂ))) *
          (ramifiedTopFacePolynomial l hl ρ σ R *
            (ramifiedTopFacePolynomial l hl ρ σ P).derivative) =
      ramifiedTopFacePolynomial l hl ρ σ P := by
  let f := ramifiedTopFacePolynomial l hl ρ σ R
  let g := ramifiedTopFacePolynomial l hl ρ σ P
  let A := ramifiedWeightDeg l hl ρ σ R
  let D := ramifiedWeightDeg l hl ρ σ P
  let H := Polynomial.C ((D : ℂ) / ((l : ℂ) * (ρ : ℂ))) *
      (f.derivative * g) -
    Polynomial.C ((A : ℂ) / ((l : ℂ) * (ρ : ℂ))) *
      (f * g.derivative)
  change H = g
  apply Polynomial.ext
  intro j
  by_cases hj : j ∈ g.support
  · exact ramified_first_face_coeff_of_bracket_coeffs
      l hl ρ σ hρ hsum P R hPne hRne hbrcoeff hRweight j hj
  · have hgzero : g.coeff j = 0 := by
      simpa using (Polynomial.mem_support_iff.not.mp hj)
    by_contra hne
    have hc : H.coeff j ≠ 0 := by
      intro hz
      exact hne (by simpa [hz, hgzero])
    have hsumne := hc
    change (Polynomial.C ((D : ℂ) / ((l : ℂ) * (ρ : ℂ))) *
      (f.derivative * g) -
      Polynomial.C ((A : ℂ) / ((l : ℂ) * (ρ : ℂ))) *
        (f * g.derivative)).coeff j ≠ 0 at hsumne
    rw [polynomial_derivative_bracket_coeff_support_pairs] at hsumne
    obtain ⟨n,hn,hnon⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
    obtain ⟨m,hm,hmnon⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnon
    have hfirst : n + m = j + 1 := by
      by_contra hbad
      simp [hbad] at hmnon
    have hRn := (ramifiedTopFacePolynomial_mem_support_iff
      l hl ρ σ R n).mp hn
    have hPm := (ramifiedTopFacePolynomial_mem_support_iff
      l hl ρ σ P m).mp hm
    let v : ℤ := ramifiedPBWTopLaurent l hl R n +
      ramifiedPBWTopLaurent l hl P m - (l : ℤ)
    have hfirstZ : (n : ℤ) + (m : ℤ) = (j : ℤ) + 1 := by
      exact_mod_cast hfirst
    have hfirstMul := congrArg
      (fun z : ℤ => (l : ℤ) * σ * z) hfirstZ
    have hv : ramifiedWeight l ρ σ (v,j) = D := by
      dsimp [v, ramifiedWeight, D]
      nlinarith [hRn.2, hPm.2, hfirstMul, hRweight]
    have hbr := ramified_commutator_first_face_polynomial_bracket
      l hl ρ σ hρ hsum R P hRne hPne j v (by
        rw [hv, hRweight]
        ring)
    rw [hbrcoeff j v hv] at hbr
    have htop := ramified_top_face_coeff_of_weight
      l hl ρ σ hρ P j v hv
    have hz : H.coeff j = 0 := by
      rw [← hbr, htop]
      exact hgzero
    exact hc hz

/-- The leading-face scalar identity determines every PBW coefficient
on the first-contraction weight line. This is the converse adapter
needed to import a homogeneous GGV bracket companion into the finite
ramified operator model. -/
theorem ramified_bracket_coeffs_of_top_face_equation
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P F : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hFne : F ≠ 0)
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
    ∀ (j : ℕ) (v : ℤ),
      ramifiedWeight l ρ σ (v,j) = ramifiedWeightDeg l hl ρ σ P →
      ((ramifiedPBWCoeffs l hl (F * P - P * F)) j).coeff v =
        ((ramifiedPBWCoeffs l hl P) j).coeff v := by
  intro j v hvP
  have hv : ramifiedWeight l ρ σ (v,j) =
      ramifiedWeightDeg l hl ρ σ F +
        ramifiedWeightDeg l hl ρ σ P - (l : ℤ) * (ρ + σ) := by
    rw [hvP, hFweight]
    ring
  rw [ramified_commutator_first_face_polynomial_bracket
    l hl ρ σ hρ hsum F P hFne hPne j v hv, hscalar]
  exact (ramified_top_face_coeff_of_weight l hl ρ σ hρ P j v hvP).symm

/-- An exact fixed point supplies the first-face coefficient relation. -/
theorem ramified_fixed_point_first_face_coeff
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P R : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hRne : R ≠ 0)
    (hfixed : R * P - P * R = P)
    (hRweight : ramifiedWeightDeg l hl ρ σ R = (l : ℤ) * (ρ + σ))
    (j : ℕ) (hj : j ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support) :
    (Polynomial.C ((ramifiedWeightDeg l hl ρ σ P : ℂ) /
          ((l : ℂ) * (ρ : ℂ))) *
          ((ramifiedTopFacePolynomial l hl ρ σ R).derivative *
            ramifiedTopFacePolynomial l hl ρ σ P) -
      Polynomial.C ((ramifiedWeightDeg l hl ρ σ R : ℂ) /
          ((l : ℂ) * (ρ : ℂ))) *
          (ramifiedTopFacePolynomial l hl ρ σ R *
            (ramifiedTopFacePolynomial l hl ρ σ P).derivative)).coeff j =
      (ramifiedTopFacePolynomial l hl ρ σ P).coeff j := by
  exact ramified_first_face_coeff_of_bracket_coeffs l hl ρ σ hρ hsum
    P R hPne hRne (by intro j v _; rw [hfixed]) hRweight j hj

/-- Exact operator fixed points are a special case of the source-facing
leading-bracket coefficient relation. -/
theorem ramified_fixed_point_top_face_equation
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P R : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hRne : R ≠ 0)
    (hfixed : R * P - P * R = P)
    (hRweight : ramifiedWeightDeg l hl ρ σ R = (l : ℤ) * (ρ + σ)) :
    Polynomial.C ((ramifiedWeightDeg l hl ρ σ P : ℂ) /
          ((l : ℂ) * (ρ : ℂ))) *
          ((ramifiedTopFacePolynomial l hl ρ σ R).derivative *
            ramifiedTopFacePolynomial l hl ρ σ P) -
      Polynomial.C ((ramifiedWeightDeg l hl ρ σ R : ℂ) /
          ((l : ℂ) * (ρ : ℂ))) *
          (ramifiedTopFacePolynomial l hl ρ σ R *
            (ramifiedTopFacePolynomial l hl ρ σ P).derivative) =
      ramifiedTopFacePolynomial l hl ρ σ P := by
  exact ramified_top_face_equation_of_bracket_coeffs l hl ρ σ hρ hsum
    P R hPne hRne (by intro j v _; rw [hfixed]) hRweight

end Dixmier.Weyl
