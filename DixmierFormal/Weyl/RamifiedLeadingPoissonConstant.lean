/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedLeadingPoissonZero

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The constant-weight boundary of the ramified leading bracket

At the first-contraction threshold zero, the exact commutator gives
the constant polynomial one rather than bracket vanishing. This
separates the equality case from the positive-threshold theorem.
-/

set_option maxHeartbeats 0

namespace Dixmier.Weyl

/-- If the two actual ramified top weights add to the first-contraction
step, the top-face derivative bracket is exactly one. -/
theorem ramified_exact_pair_top_face_bracket_eq_one_of_threshold_zero
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (hcomm : P*Q-Q*P = 1)
    (hthreshold : ramifiedWeightDeg l hl ρ σ P +
      ramifiedWeightDeg l hl ρ σ Q - (l : ℤ)*(ρ+σ) = 0) :
    Polynomial.C ((ramifiedWeightDeg l hl ρ σ Q : ℂ) /
        ((l : ℂ)*(ρ : ℂ))) *
        ((ramifiedTopFacePolynomial l hl ρ σ P).derivative *
          ramifiedTopFacePolynomial l hl ρ σ Q) -
      Polynomial.C ((ramifiedWeightDeg l hl ρ σ P : ℂ) /
        ((l : ℂ)*(ρ : ℂ))) *
        (ramifiedTopFacePolynomial l hl ρ σ P *
          (ramifiedTopFacePolynomial l hl ρ σ Q).derivative) = 1 := by
  classical
  let f := ramifiedTopFacePolynomial l hl ρ σ P
  let g := ramifiedTopFacePolynomial l hl ρ σ Q
  let A := ramifiedWeightDeg l hl ρ σ P
  let D := ramifiedWeightDeg l hl ρ σ Q
  let H := Polynomial.C ((D : ℂ)/((l : ℂ)*(ρ : ℂ))) *
      (f.derivative*g) -
    Polynomial.C ((A : ℂ)/((l : ℂ)*(ρ : ℂ))) *
      (f*g.derivative)
  change H = 1
  apply Polynomial.ext
  intro j
  by_cases hj : j = 0
  · subst j
    have hv : ramifiedWeight l ρ σ ((0 : ℤ),0) = A+D-(l : ℤ)*(ρ+σ) := by
      simp [ramifiedWeight,hthreshold,A,D]
    have hcoeff := ramified_commutator_first_face_polynomial_bracket
      l hl ρ σ hρ hsum P Q hPne hQne 0 0 hv
    rw [hcomm,ramifiedPBWCoeffs_one_coeff_at_origin] at hcoeff
    simpa [H,f,g,A,D] using hcoeff.symm
  · by_contra hbad
    have hc : H.coeff j ≠ 0 := by
      have hone : (1 : Polynomial ℂ).coeff j = 0 := by
        change (Polynomial.C (1 : ℂ)).coeff j = 0
        rw [Polynomial.coeff_C]
        simp [hj]
      exact fun hz => hbad (by simpa [hz,hone])
    have hsumne := hc
    change (Polynomial.C ((D : ℂ)/((l : ℂ)*(ρ : ℂ))) *
        (f.derivative*g) -
      Polynomial.C ((A : ℂ)/((l : ℂ)*(ρ : ℂ))) *
        (f*g.derivative)).coeff j ≠ 0 at hsumne
    rw [polynomial_derivative_bracket_coeff_support_pairs] at hsumne
    obtain ⟨n,hn,hnon⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
    obtain ⟨m,hm,hmnon⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnon
    have hfirst : n+m=j+1 := by
      by_contra hbad'
      simp [hbad'] at hmnon
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
    have hv : ramifiedWeight l ρ σ (v,j) = A+D-(l : ℤ)*(ρ+σ) := by
      dsimp [v,ramifiedWeight]
      nlinarith [hPn.2,hQm.2,hfirstMul]
    have hcoeff := ramified_commutator_first_face_polynomial_bracket
      l hl ρ σ hρ hsum P Q hPne hQne j v hv
    have hnz : ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) j).coeff v ≠ 0 := by
      rw [hcoeff]
      simpa [H,f,g,A,D] using hc
    have horigin := (ramified_exact_pair_coeff_nonzero_iff_origin
      l hl P Q hcomm j v).mp hnz
    exact hj horigin.1

/-- At constant first-contraction weight, at least one actual top face
has a derivative-order-zero term. Thus an equality-case exclusion can be
obtained by proving both selected faces start above order zero. -/
theorem ramified_exact_pair_threshold_zero_has_top_order_zero
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (hcomm : P*Q-Q*P = 1)
    (hthreshold : ramifiedWeightDeg l hl ρ σ P +
      ramifiedWeightDeg l hl ρ σ Q - (l : ℤ)*(ρ+σ) = 0) :
    0 ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support ∨
      0 ∈ (ramifiedTopFacePolynomial l hl ρ σ Q).support := by
  let f := ramifiedTopFacePolynomial l hl ρ σ P
  let g := ramifiedTopFacePolynomial l hl ρ σ Q
  have hbr := ramified_exact_pair_top_face_bracket_eq_one_of_threshold_zero
    l hl ρ σ hρ hsum P Q hPne hQne hcomm hthreshold
  by_contra hnone
  push_neg at hnone
  have hf0 : f.eval 0 = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    by_contra hc
    exact hnone.1 (Polynomial.mem_support_iff.mpr hc)
  have hg0 : g.eval 0 = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    by_contra hc
    exact hnone.2 (Polynomial.mem_support_iff.mpr hc)
  have heval := congrArg (fun p : Polynomial ℂ => p.eval 0) hbr
  dsimp only [f,g] at hf0 hg0
  simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,
    hf0,hg0,mul_zero,zero_mul,sub_zero,Polynomial.eval_one] at heval
  exact one_ne_zero heval.symm

end Dixmier.Weyl
