module

public import DixmierFormal.Weyl.RamifiedCommutatorFirstWeight
public import DixmierFormal.Weyl.RamifiedJosephChainTransport

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Two-bracket witnesses for polynomial-source ramified cuts

The first vanishing canonical face bracket along a terminating exact chain
has a noncentralizing predecessor. Its exact successor is nonzero, has the
predicted first-contraction weight and face, and centralizes the fixed face.
The polynomial-source theorem supplies both the initial witness and chain
termination internally.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

def RamifiedJosephTwoBracketAt
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (P R : ramifiedOperatorAlgebra l) (n : ℕ) : Prop :=
  ramifiedFaceCentralization l hl ρ σ P (ramifiedJosephChain l P R n) ≠ 0 ∧
  ramifiedJosephChain l P R (n+1) ≠ 0 ∧
  ramifiedTopFacePolynomial l hl ρ σ (ramifiedJosephChain l P R (n+1)) =
    -ramifiedFaceCentralization l hl ρ σ P (ramifiedJosephChain l P R n) ∧
  ramifiedWeightDeg l hl ρ σ (ramifiedJosephChain l P R (n+1)) =
    ramifiedWeightDeg l hl ρ σ P +
      ramifiedWeightDeg l hl ρ σ (ramifiedJosephChain l P R n) -
        (l:ℤ)*(ρ+σ) ∧
  ramifiedFaceCentralization l hl ρ σ P (ramifiedJosephChain l P R (n+1)) = 0

theorem ramified_two_bracket_of_terminating_chain
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P R : ramifiedOperatorAlgebra l) (hP : P ≠ 0)
    (hfirst : ramifiedFaceCentralization l hl ρ σ P R ≠ 0)
    (hterminal : ∃ n, ramifiedJosephChain l P R n = 0) :
    ∃ n, RamifiedJosephTwoBracketAt l hl ρ σ P R n := by
  classical
  let B (n : ℕ) := ramifiedFaceCentralization l hl ρ σ P (ramifiedJosephChain l P R n)
  have hex : ∃ n, B n = 0 := by
    obtain ⟨n,hn⟩ := hterminal
    refine ⟨n, ?_⟩
    change ramifiedFaceCentralization l hl ρ σ P (ramifiedJosephChain l P R n) = 0
    rw [hn]
    exact ramifiedFaceCentralization_zero_right l hl ρ σ hρ P
  let N := Nat.find hex
  have hN : B N = 0 := Nat.find_spec hex
  have hNpos : 0 < N := by
    by_contra hn
    have hz : N = 0 := by omega
    rw [hz] at hN
    exact hfirst hN
  have hprev : B (N-1) ≠ 0 := Nat.find_min hex (by omega)
  have hprevne : ramifiedJosephChain l P R (N-1) ≠ 0 := by
    intro hz
    apply hprev
    change ramifiedFaceCentralization l hl ρ σ P (ramifiedJosephChain l P R (N-1)) = 0
    rw [hz]
    exact ramifiedFaceCentralization_zero_right l hl ρ σ hρ P
  have hi : (N-1)+1=N := by omega
  have hnext : ramifiedJosephChain l P R N =
      P*ramifiedJosephChain l P R (N-1) - ramifiedJosephChain l P R (N-1)*P := by
    conv_lhs => rw [← hi]
    rfl
  have hface := ramified_noncentralizing_commutator_top_face
    l hl ρ σ hρ hsum P (ramifiedJosephChain l P R (N-1)) hP hprevne hprev
  have hweight := ramified_noncentralizing_commutator_weight
    l hl ρ σ hρ hsum P (ramifiedJosephChain l P R (N-1)) hP hprevne hprev
  have hnextne : ramifiedJosephChain l P R N ≠ 0 := by
    intro hz
    rw [← hnext, hz, ramifiedTopFacePolynomial_zero_first_weight l hl ρ σ hρ] at hface
    exact hprev (neg_eq_zero.mp hface.symm)
  refine ⟨N-1, ?_⟩
  unfold RamifiedJosephTwoBracketAt
  rw [hi]
  refine ⟨hprev, hnextne, ?_, ?_, hN⟩
  · rw [hnext]
    exact hface
  · rw [hnext]
    exact hweight

theorem cut_generated_two_bracket_exists
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (hdiv : ρ ∣ (l:ℤ)) (hσ : σ ≤ 0) (hsum : 0 < ρ+σ) (c : ℂ)
    (P Q : A1 ℂ) (hp : Q*P-P*Q=1)
    (ρ' σ' : ℤ) (hρ' : 0 < ρ') (hsum' : 0 < ρ'+σ')
    (hPcut : ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P) ≠ 0)
    (hm : ramifiedWeightDeg l hl ρ' σ'
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) ≠ 0) :
    ∃ R : A1 ℂ, R ∈ Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ)) ∧
      ∃ n, RamifiedJosephTwoBracketAt l hl ρ' σ'
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l R)) n := by
  obtain ⟨R,hR,hfirst⟩ := cut_generated_noncentralizing_face_exists
    l hl ρ σ hρ hdiv hσ hsum c P Q hp ρ' σ' hρ'
    (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) hPcut hm
  have hterminal := ramifiedCut_generated_chain_terminates l hl ρ σ c P Q R hp hR
  obtain ⟨n,hn⟩ := ramified_two_bracket_of_terminating_chain l hl ρ' σ' hρ' hsum'
    (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))
    (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l R)) hPcut hfirst hterminal
  exact ⟨R,hR,n,hn⟩

end Dixmier.Weyl
