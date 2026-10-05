module

public import DixmierFormal.Weyl.RamifiedHomogeneousPolynomialRealization
public import DixmierFormal.Weyl.RamifiedTwoBracketScalarFixedPoint

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # A homogeneous Laurent companion for an actual polynomial-source cut

The polynomial quotient and its integral support lattice realize a finite
homogeneous operator. The exact first-contraction theorem identifies the
weight and canonical face of its full commutator with the cut operator.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 800000

theorem ramified_scalar_fixed_point_realizes_homogeneous_companion
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (q : ℂ[X])
    (hL : PolynomialWeightLattice ρ ((l:ℤ)*σ) ((l:ℤ)*(ρ+σ)) q)
    (hfixed : C (ramifiedWeightDeg l hl ρ σ P : ℂ)*
        ramifiedTopFacePolynomial l hl ρ σ P*q.derivative-
      C ((l:ℤ)*(ρ+σ):ℂ)*(ramifiedTopFacePolynomial l hl ρ σ P).derivative*q =
        -C ((l:ℂ)*(ρ:ℂ))*ramifiedTopFacePolynomial l hl ρ σ P) :
    ∃ F : ramifiedOperatorAlgebra l, F ≠ 0 ∧
      (∀ p ∈ ramifiedPBWSupport l hl F, ramifiedWeight l ρ σ p=(l:ℤ)*(ρ+σ)) ∧
      ramifiedWeightDeg l hl ρ σ F=(l:ℤ)*(ρ+σ) ∧
      ramifiedWeightDeg l hl ρ σ (P*F-F*P)=ramifiedWeightDeg l hl ρ σ P ∧
      ramifiedTopFacePolynomial l hl ρ σ (P*F-F*P)=ramifiedTopFacePolynomial l hl ρ σ P := by
  have hpface := ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ P hP
  have hden : (l:ℂ)*(ρ:ℂ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (ne_of_gt hl)) (by exact_mod_cast (ne_of_gt hρ))
  have hCden : (C ((l:ℂ)*(ρ:ℂ)) : ℂ[X]) ≠ 0 := by simpa using hden
  have hq : q ≠ 0 := by
    intro hz
    have he := hfixed
    simp only [hz,derivative_zero,mul_zero,sub_self] at he
    exact (neg_ne_zero.mpr (mul_ne_zero hCden hpface)) (by simpa using he.symm)
  let F := ramifiedPolynomialFace l ρ σ ((l:ℤ)*(ρ+σ)) q
  have hF : F ≠ 0 := ramifiedPolynomialFace_ne_zero l hl ρ σ _ q hq hL
  have hFw : ramifiedWeightDeg l hl ρ σ F=(l:ℤ)*(ρ+σ) :=
    ramifiedPolynomialFace_weight l hl ρ σ _ q hq hL
  have hFtop : ramifiedTopFacePolynomial l hl ρ σ F=q :=
    ramifiedPolynomialFace_top_face l hl ρ σ _ hρ q hq hL
  have hc : ramifiedFaceCentralization l hl ρ σ P F =
      -ramifiedTopFacePolynomial l hl ρ σ P := by
    apply mul_left_cancel₀ hCden
    rw [ramifiedFaceCentralization_clear_denominator l hl ρ σ hρ P F,hFw,hFtop]
    simpa only [Int.cast_mul,Int.cast_add,mul_neg,neg_mul] using hfixed
  have hcne : ramifiedFaceCentralization l hl ρ σ P F ≠ 0 := by
    rw [hc]
    exact neg_ne_zero.mpr hpface
  have hcommweight := ramified_noncentralizing_commutator_weight l hl ρ σ hρ hsum P F hP hF hcne
  rw [hFw] at hcommweight
  have hcommface := ramified_noncentralizing_commutator_top_face l hl ρ σ hρ hsum P F hP hF hcne
  rw [hc,neg_neg] at hcommface
  exact ⟨F,hF,fun p hp => ramifiedPolynomialFace_support_weight l hl ρ σ _ q hL p hp,
    hFw,by simpa using hcommweight,hcommface⟩

theorem ramified_two_bracket_homogeneous_companion_exists
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P R : ramifiedOperatorAlgebra l) (n : ℕ) (hP : P ≠ 0)
    (hm : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hwitness : RamifiedJosephTwoBracketAt l hl ρ σ P R n) :
    ∃ F : ramifiedOperatorAlgebra l, F ≠ 0 ∧
      (∀ p ∈ ramifiedPBWSupport l hl F, ramifiedWeight l ρ σ p=(l:ℤ)*(ρ+σ)) ∧
      ramifiedWeightDeg l hl ρ σ F=(l:ℤ)*(ρ+σ) ∧
      ramifiedWeightDeg l hl ρ σ (P*F-F*P)=ramifiedWeightDeg l hl ρ σ P ∧
      ramifiedTopFacePolynomial l hl ρ σ (P*F-F*P)=
        ramifiedTopFacePolynomial l hl ρ σ P := by
  obtain ⟨q,hL,_,hfixed⟩ := ramified_two_bracket_scalar_fixed_point_with_lattice
    l hl ρ σ hρ hsum P R n hP hm hwitness
  exact ramified_scalar_fixed_point_realizes_homogeneous_companion
    l hl ρ σ hρ hsum P hP q hL hfixed

theorem ramified_terminating_chain_homogeneous_companion_exists
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P R : ramifiedOperatorAlgebra l) (hP : P ≠ 0)
    (hm : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hfirst : ramifiedFaceCentralization l hl ρ σ P R ≠ 0)
    (hterminal : ∃ n, ramifiedJosephChain l P R n = 0) :
    ∃ F : ramifiedOperatorAlgebra l, F ≠ 0 ∧
      (∀ p ∈ ramifiedPBWSupport l hl F, ramifiedWeight l ρ σ p=(l:ℤ)*(ρ+σ)) ∧
      ramifiedWeightDeg l hl ρ σ F=(l:ℤ)*(ρ+σ) ∧
      ramifiedWeightDeg l hl ρ σ (P*F-F*P)=ramifiedWeightDeg l hl ρ σ P ∧
      ramifiedTopFacePolynomial l hl ρ σ (P*F-F*P)=
        ramifiedTopFacePolynomial l hl ρ σ P := by
  obtain ⟨n,hn⟩ := ramified_two_bracket_of_terminating_chain
    l hl ρ σ hρ hsum P R hP hfirst hterminal
  exact ramified_two_bracket_homogeneous_companion_exists
    l hl ρ σ hρ hsum P R n hP hm hn

theorem cut_generated_homogeneous_companion_exists
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (hdiv : ρ ∣ (l:ℤ)) (hσ : σ ≤ 0) (hsum : 0 < ρ+σ) (c : ℂ)
    (P Q : A1 ℂ) (hp : Q*P-P*Q=1)
    (ρ' σ' : ℤ) (hρ' : 0 < ρ') (hsum' : 0 < ρ'+σ')
    (hPcut : ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P) ≠ 0)
    (hm : 0 < ramifiedWeightDeg l hl ρ' σ'
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))) :
    ∃ F : ramifiedOperatorAlgebra l, F ≠ 0 ∧
      (∀ p ∈ ramifiedPBWSupport l hl F, ramifiedWeight l ρ' σ' p=(l:ℤ)*(ρ'+σ')) ∧
      ramifiedWeightDeg l hl ρ' σ' F=(l:ℤ)*(ρ'+σ') ∧
      ramifiedWeightDeg l hl ρ' σ'
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)*F-
          F*ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))=
        ramifiedWeightDeg l hl ρ' σ' (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) ∧
      ramifiedTopFacePolynomial l hl ρ' σ'
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)*F-
          F*ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))=
        ramifiedTopFacePolynomial l hl ρ' σ'
          (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) := by
  obtain ⟨R,_,n,hwitness⟩ := cut_generated_two_bracket_exists
    l hl ρ σ hρ hdiv hσ hsum c P Q hp ρ' σ' hρ' hsum' hPcut (ne_of_gt hm)
  exact ramified_two_bracket_homogeneous_companion_exists
    l hl ρ' σ' hρ' hsum'
    (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))
    (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l R)) n hPcut hm hwitness

end Dixmier.Weyl
