/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedLeadingPoisson

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Vanishing of the whole ramified top-face derivative bracket

At positive first-contraction weight, exact commutator one forces
the weighted derivative bracket of the actual top faces to vanish.
-/

set_option maxHeartbeats 0

namespace Dixmier.Weyl

/-- Above constant weight, the whole derivative bracket of the two
actual ramified top faces vanishes for an exact Weyl pair. -/
theorem ramified_exact_pair_top_face_bracket_eq_zero
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (hcomm : P*Q-Q*P = 1)
    (hthreshold : 0 < ramifiedWeightDeg l hl ρ σ P +
      ramifiedWeightDeg l hl ρ σ Q - (l : ℤ)*(ρ+σ)) :
    Polynomial.C ((ramifiedWeightDeg l hl ρ σ Q : ℂ) /
        ((l : ℂ)*(ρ : ℂ))) *
        ((ramifiedTopFacePolynomial l hl ρ σ P).derivative *
          ramifiedTopFacePolynomial l hl ρ σ Q) -
      Polynomial.C ((ramifiedWeightDeg l hl ρ σ P : ℂ) /
        ((l : ℂ)*(ρ : ℂ))) *
        (ramifiedTopFacePolynomial l hl ρ σ P *
          (ramifiedTopFacePolynomial l hl ρ σ Q).derivative) = 0 := by
  classical
  let f := ramifiedTopFacePolynomial l hl ρ σ P
  let g := ramifiedTopFacePolynomial l hl ρ σ Q
  let A := ramifiedWeightDeg l hl ρ σ P
  let D := ramifiedWeightDeg l hl ρ σ Q
  let H := Polynomial.C ((D : ℂ)/((l : ℂ)*(ρ : ℂ))) *
      (f.derivative*g) -
    Polynomial.C ((A : ℂ)/((l : ℂ)*(ρ : ℂ))) *
      (f*g.derivative)
  change H = 0
  apply Polynomial.ext
  intro j
  by_contra hc0
  have hc : H.coeff j ≠ 0 := by simpa using hc0
  have hsumne := hc
  change (Polynomial.C ((D : ℂ)/((l : ℂ)*(ρ : ℂ))) *
      (f.derivative*g) -
    Polynomial.C ((A : ℂ)/((l : ℂ)*(ρ : ℂ))) *
      (f*g.derivative)).coeff j ≠ 0 at hsumne
  rw [polynomial_derivative_bracket_coeff_support_pairs] at hsumne
  obtain ⟨n,hn,hnon⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
  obtain ⟨m,hm,hmnon⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnon
  have hfirst : n+m=j+1 := by
    by_contra hbad
    simp [hbad] at hmnon
  have hPn :=
    (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P n).mp hn
  have hQm :=
    (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ Q m).mp hm
  let v : ℤ := ramifiedPBWTopLaurent l hl P n +
    ramifiedPBWTopLaurent l hl Q m - (l : ℤ)
  have hfirstZ : (n : ℤ)+(m : ℤ)=(j : ℤ)+1 := by
    exact_mod_cast hfirst
  have hfirstMul := congrArg
    (fun z : ℤ => (l : ℤ)*σ*z) hfirstZ
  have hv : ramifiedWeight l ρ σ (v,j) =
      ramifiedWeightDeg l hl ρ σ P +
        ramifiedWeightDeg l hl ρ σ Q -
        (l : ℤ)*(ρ+σ) := by
    dsimp [v,ramifiedWeight]
    nlinarith [hPn.2,hQm.2,hfirstMul]
  have hpositive : 0 < ramifiedWeight l ρ σ (v,j) := by
    rw [hv]
    exact hthreshold
  have hz := ramified_exact_pair_first_face_polynomial_bracket_zero
    l hl ρ σ hρ hsum P Q hPne hQne hcomm j v hv hpositive
  exact hc (by simpa [H,f,g,A,D] using hz)

end Dixmier.Weyl
