module

public import DixmierFormal.Weyl.RamifiedCompanionEndpointDichotomy
public import DixmierFormal.Weyl.CornerRootOrderRatio

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # A degree-one source companion forces a pure-power face

The actual companion root budget leaves at most one distinct complex root.
Its maximum multiplicity therefore consumes the entire face degree. No
direction/index divisibility is required for this conclusion.
-/

namespace Dixmier.Weyl
open Polynomial

theorem ramified_linear_source_companion_maxRoot_eq_degree
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P F : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hF : F ≠ 0)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P*F-F*P)=ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P*F-F*P)=
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F=(l:ℤ)*(ρ+σ))
    (hlinear : (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree=1) :
    maxRootMult (ramifiedTopFacePolynomial l hl ρ σ P)=
      (ramifiedTopFacePolynomial l hl ρ σ P).natDegree := by
  have hcount := ramified_source_companion_top_face_root_count
    l hl ρ σ hρ hsum P F hP hF hdegree hface hFweight
  rw [hlinear] at hcount
  have hlow := complex_polynomial_companion_root_budget _ 1 hcount
  simp only [one_mul] at hlow
  exact Nat.le_antisymm
    (maxRootMult_le_natDegree _
      (ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ P hP)) hlow

theorem ramified_linear_source_companion_face_eq_power
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P F : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hF : F ≠ 0)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P*F-F*P)=ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P*F-F*P)=
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F=(l:ℤ)*(ρ+σ))
    (hlinear : (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree=1)
    (hpositive : 0 < (ramifiedTopFacePolynomial l hl ρ σ P).natDegree) :
    ∃ c : ℂ, (ramifiedTopFacePolynomial l hl ρ σ P).IsRoot c ∧
      ramifiedTopFacePolynomial l hl ρ σ P=
        C (ramifiedTopFacePolynomial l hl ρ σ P).leadingCoeff *
          (X-C c)^(ramifiedTopFacePolynomial l hl ρ σ P).natDegree := by
  exact polynomial_eq_linear_power_of_maxRootMult_eq_natDegree _ hpositive
    (ramified_linear_source_companion_maxRoot_eq_degree
      l hl ρ σ hρ hsum P F hP hF hdegree hface hFweight hlinear)

end Dixmier.Weyl
