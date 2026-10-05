module

public import DixmierFormal.Weyl.PolynomialFiniteCutDimensionWitness
public import DixmierFormal.Weyl.RamifiedCutHomogeneousCompanion

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Homogeneous companions after finite admissible cut sequences

Word independence and the linear support interval supply the initial
noncentralizing face. Exact generated-chain termination then realizes a
finite homogeneous Laurent operator with the required commutator face.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

theorem finite_cut_generated_homogeneous_companion_exists
    (l : ℕ) (hl : 0 < l) (cuts : List (AdmissibleRamifiedCut l))
    (P Q : A1 ℂ) (hp : Q*P-P*Q=1)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (hU : ramifiedFiniteCutAut l hl cuts (polynomialRamifiedLift l P) ≠ 0)
    (hm : 0 < ramifiedWeightDeg l hl ρ σ
      (ramifiedFiniteCutAut l hl cuts (polynomialRamifiedLift l P))) :
    ∃ F : ramifiedOperatorAlgebra l, F ≠ 0 ∧
      (∀ p ∈ ramifiedPBWSupport l hl F, ramifiedWeight l ρ σ p=(l:ℤ)*(ρ+σ)) ∧
      ramifiedWeightDeg l hl ρ σ F=(l:ℤ)*(ρ+σ) ∧
      ramifiedWeightDeg l hl ρ σ
        (ramifiedFiniteCutAut l hl cuts (polynomialRamifiedLift l P)*F-
          F*ramifiedFiniteCutAut l hl cuts (polynomialRamifiedLift l P))=
        ramifiedWeightDeg l hl ρ σ
          (ramifiedFiniteCutAut l hl cuts (polynomialRamifiedLift l P)) ∧
      ramifiedTopFacePolynomial l hl ρ σ
        (ramifiedFiniteCutAut l hl cuts (polynomialRamifiedLift l P)*F-
          F*ramifiedFiniteCutAut l hl cuts (polynomialRamifiedLift l P))=
        ramifiedTopFacePolynomial l hl ρ σ
          (ramifiedFiniteCutAut l hl cuts (polynomialRamifiedLift l P)) := by
  obtain ⟨R,hR,hfirst⟩ := finite_cut_generated_noncentralizing_face_exists
    l hl cuts P Q hp ρ σ hρ
    (ramifiedFiniteCutAut l hl cuts (polynomialRamifiedLift l P)) hU (ne_of_gt hm)
  let φ := (ramifiedFiniteCutAut l hl cuts).toAlgHom.comp
    (polynomialRamifiedLiftHom l hl)
  have hterminal := ramified_generated_chain_terminates_of_map l φ P Q R hp hR
  exact ramified_terminating_chain_homogeneous_companion_exists
    l hl ρ σ hρ hsum
    (ramifiedFiniteCutAut l hl cuts (polynomialRamifiedLift l P))
    (ramifiedFiniteCutAut l hl cuts (polynomialRamifiedLift l R))
    hU hm hfirst hterminal

end Dixmier.Weyl
