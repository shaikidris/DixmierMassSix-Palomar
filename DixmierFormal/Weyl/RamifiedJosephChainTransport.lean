module

public import DixmierFormal.Weyl.JosephLocalNilpotence
public import DixmierFormal.Weyl.PolynomialRamifiedLift
public import DixmierFormal.Weyl.RamifiedCutSetup

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Terminating Joseph chains for polynomial-source ramified cuts

The actual cut homomorphism transports every exact commutator chain.
Consequently each cut image of a generated polynomial operator has a
terminating chain. This supplies termination, but not the initial
noncentralizing leading form at the new Newton direction.
-/

namespace Dixmier.Weyl

noncomputable def ramifiedJosephChain (l : ℕ)
    (P R : ramifiedOperatorAlgebra l) : ℕ → ramifiedOperatorAlgebra l
  | 0 => R
  | n+1 => P * ramifiedJosephChain l P R n - ramifiedJosephChain l P R n * P

theorem ramifiedJosephChain_map (l : ℕ)
    (φ : A1 ℂ →ₐ[ℂ] ramifiedOperatorAlgebra l)
    (P R : A1 ℂ) (n : ℕ) :
    ramifiedJosephChain l (φ P) (φ R) n = φ (josephCommutatorChain P R n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ramifiedJosephChain, josephCommutatorChain, ih]
    exact (map_sub φ (P * josephCommutatorChain P R n)
      (josephCommutatorChain P R n * P)).trans
      (by rw [map_mul, map_mul]) |>.symm

theorem ramified_generated_chain_terminates_of_map
    (l : ℕ) (φ : A1 ℂ →ₐ[ℂ] ramifiedOperatorAlgebra l)
    (P Q R : A1 ℂ) (hpair : Q*P-P*Q=1)
    (hR : R ∈ Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ))) :
    ∃ n, ramifiedJosephChain l (φ P) (φ R) n = 0 := by
  obtain ⟨n,hn⟩ := joseph_chain_terminates_on_adjoin P Q R hpair hR
  refine ⟨n, ?_⟩
  rw [ramifiedJosephChain_map, hn, map_zero]

theorem ramifiedCut_generated_chain_terminates
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (c : ℂ)
    (P Q R : A1 ℂ) (hpair : Q*P-P*Q=1)
    (hR : R ∈ Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ))) :
    ∃ n, ramifiedJosephChain l
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l R)) n = 0 := by
  let φ := (ramifiedCutAut l hl ρ σ c).toAlgHom.comp
    (polynomialRamifiedLiftHom l hl)
  exact ramified_generated_chain_terminates_of_map l φ P Q R hpair hR

end Dixmier.Weyl
