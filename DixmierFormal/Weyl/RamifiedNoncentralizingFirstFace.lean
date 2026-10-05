module

public import DixmierFormal.Weyl.PolynomialCutDimensionWitness
public import DixmierFormal.Weyl.RamifiedLeadingPoisson

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Actual first-contraction coefficients of a noncentralizing face

Every occupied derivative-bracket coefficient lies on the ramified support
lattice: its Laurent exponent is the sum of the two input top exponents minus
the coefficient index. The canonical scalar noncentralizer therefore supplies
an occupied coefficient of the exact operator commutator.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 800000

theorem ramifiedFaceCentralization_support_lattice
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (P Q : ramifiedOperatorAlgebra l) (j : ℕ)
    (hj : (ramifiedFaceCentralization l hl ρ σ P Q).coeff j ≠ 0) :
    ∃ v : ℤ, ramifiedWeight l ρ σ (v,j) =
      ramifiedWeightDeg l hl ρ σ P + ramifiedWeightDeg l hl ρ σ Q -
        (l:ℤ)*(ρ+σ) := by
  classical
  let f := ramifiedTopFacePolynomial l hl ρ σ Q
  let g := ramifiedTopFacePolynomial l hl ρ σ P
  have he : ramifiedFaceCentralization l hl ρ σ P Q =
      C ((ramifiedWeightDeg l hl ρ σ P : ℂ) / ((l:ℂ)*(ρ:ℂ))) *
        (f.derivative*g) -
      C ((ramifiedWeightDeg l hl ρ σ Q : ℂ) / ((l:ℂ)*(ρ:ℂ))) *
        (f*g.derivative) := by
    dsimp [ramifiedFaceCentralization, f, g]
    ring
  rw [he, polynomial_derivative_bracket_coeff_support_pairs] at hj
  obtain ⟨n,hn,hns⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
  obtain ⟨m,hm,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hns
  have hfirst : n+m=j+1 := by
    by_contra hbad
    simp [hbad] at hterm
  have htopQ := ((ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ Q n).mp hn).2
  have htopP := ((ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P m).mp hm).2
  refine ⟨ramifiedPBWTopLaurent l hl Q n + ramifiedPBWTopLaurent l hl P m - (l:ℤ), ?_⟩
  have hfirstZ : (n:ℤ)+(m:ℤ)=(j:ℤ)+1 := by exact_mod_cast hfirst
  have hscaled := congrArg (fun z : ℤ => (l:ℤ)*σ*z) hfirstZ
  dsimp [ramifiedWeight]
  nlinarith

theorem ramifiedFaceCentralization_coeff_neg_commutator
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (j : ℕ) (v : ℤ)
    (hv : ramifiedWeight l ρ σ (v,j) =
      ramifiedWeightDeg l hl ρ σ P + ramifiedWeightDeg l hl ρ σ Q -
        (l:ℤ)*(ρ+σ)) :
    ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) j).coeff v =
      -(ramifiedFaceCentralization l hl ρ σ P Q).coeff j := by
  rw [ramified_commutator_first_face_polynomial_bracket l hl ρ σ hρ hsum P Q hP hQ j v hv]
  rw [← Polynomial.coeff_neg]
  congr 1
  unfold ramifiedFaceCentralization
  ring

theorem ramified_noncentralizing_first_face_exists
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hc : ramifiedFaceCentralization l hl ρ σ P Q ≠ 0) :
    ∃ p ∈ ramifiedPBWSupport l hl (P*Q-Q*P),
      ramifiedWeight l ρ σ p =
        ramifiedWeightDeg l hl ρ σ P + ramifiedWeightDeg l hl ρ σ Q -
          (l:ℤ)*(ρ+σ) := by
  have hex : ∃ j, (ramifiedFaceCentralization l hl ρ σ P Q).coeff j ≠ 0 := by
    by_contra hn
    apply hc
    ext j
    simpa using not_exists.mp hn j
  obtain ⟨j,hj⟩ := hex
  obtain ⟨v,hv⟩ := ramifiedFaceCentralization_support_lattice l hl ρ σ P Q j hj
  refine ⟨(v,j), (ramifiedPBWSupport_mem_iff l hl (P*Q-Q*P) v j).mpr ?_, hv⟩
  change ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) j).coeff v ≠ 0
  rw [ramifiedFaceCentralization_coeff_neg_commutator l hl ρ σ hρ hsum P Q hP hQ j v hv]
  exact neg_ne_zero.mpr hj

theorem ramified_first_weight_component_eq_neg_centralization
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ramifiedWeightComponent l hl ρ σ
      (ramifiedWeightDeg l hl ρ σ P + ramifiedWeightDeg l hl ρ σ Q -
        (l:ℤ)*(ρ+σ)) (P*Q-Q*P) =
      -ramifiedFaceCentralization l hl ρ σ P Q := by
  ext j
  rw [ramifiedWeightComponent_coeff, Polynomial.coeff_neg]
  split_ifs with hdiv
  · apply ramifiedFaceCentralization_coeff_neg_commutator l hl ρ σ hρ hsum P Q hP hQ
    have hc := Int.mul_ediv_cancel' hdiv
    dsimp [ramifiedWeight]
    omega
  · have hz : (ramifiedFaceCentralization l hl ρ σ P Q).coeff j = 0 := by
      by_contra hn
      obtain ⟨v,hv⟩ := ramifiedFaceCentralization_support_lattice l hl ρ σ P Q j hn
      apply hdiv
      refine ⟨v, ?_⟩
      dsimp [ramifiedWeight] at hv
      omega
    simp [hz]

end Dixmier.Weyl
