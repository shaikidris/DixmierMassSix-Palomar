module

public import DixmierFormal.Weyl.GGVJosephSourceAdapter

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Extracting a two-bracket witness from an exact terminating chain

A nonzero first Poisson bracket and a terminating exact commutator chain
suffice to produce Joseph's two-bracket witness. Each operator stays in the
generated algebra and each nonzero symbol transition uses the PBW theorem.
Existence of the initial witness and termination are separate obligations.
-/
set_option maxHeartbeats 0

namespace Dixmier.Weyl
open MvPolynomial Polynomial

noncomputable def josephCommutatorChain (P R : A1 ℂ) : ℕ → A1 ℂ
  | 0 => R
  | n+1 => P * josephCommutatorChain P R n - josephCommutatorChain P R n * P

theorem josephCommutatorChain_mem (P Q R : A1 ℂ)
    (hR : R ∈ Algebra.adjoin ℂ {P,Q}) (n : ℕ) :
    josephCommutatorChain P R n ∈ Algebra.adjoin ℂ {P,Q} := by
  have hP : P ∈ Algebra.adjoin ℂ {P,Q} := Algebra.subset_adjoin (by simp)
  induction n with
  | zero => exact hR
  | succ n ih =>
    change P * josephCommutatorChain P R n - josephCommutatorChain P R n * P ∈ _
    exact Subalgebra.sub_mem (R := ℂ) (A := A1 ℂ) (Algebra.adjoin ℂ {P,Q})
      (Subalgebra.mul_mem _ hP ih) (Subalgebra.mul_mem _ ih hP)

/-- Extract the last nonzero symbol bracket before the first symbol cancellation. -/
theorem joseph_two_bracket_of_terminating_chain
    (P Q R : A1 ℂ) (ρ σ : ℤ) (hweight : 0 < ρ+σ)
    (hR : R ∈ Algebra.adjoin ℂ {P,Q})
    (hfirst : poisson (leadingForm ρ σ P.1) (leadingForm ρ σ R.1) ≠ 0)
    (hterminal : ∃ n, josephCommutatorChain P R n = 0) :
    ∃ T : A1 ℂ, T ∈ Algebra.adjoin ℂ {P,Q} ∧
      poisson (leadingForm ρ σ P.1) (leadingForm ρ σ T.1) ≠ 0 ∧
      poisson (leadingForm ρ σ P.1)
        (poisson (leadingForm ρ σ P.1) (leadingForm ρ σ T.1)) = 0 := by
  classical
  let B (n : ℕ) := poisson (leadingForm ρ σ P.1)
    (leadingForm ρ σ (josephCommutatorChain P R n).1)
  have hex : ∃ n, B n = 0 := by
    obtain ⟨n,hn⟩ := hterminal
    refine ⟨n,?_⟩
    have hz : symbol ((0 : A1 ℂ).1) = 0 := by
      have h := symbol_smul (0 : ℂ) (1 : A1 ℂ)
      simpa using h
    have hz' : symbol (0 : Module.End ℂ ℂ[X]) = 0 := hz
    simp [B,hn,leadingForm,hz',poisson]
  let N := Nat.find hex
  have hN : B N = 0 := Nat.find_spec hex
  have hNpos : 0 < N := by
    by_contra h
    have hz : N=0 := by omega
    rw [hz] at hN
    exact hfirst (by simpa [B,josephCommutatorChain] using hN)
  have hprev : B (N-1) ≠ 0 := Nat.find_min hex (by omega)
  let T := josephCommutatorChain P R (N-1)
  have hT : poisson (leadingForm ρ σ P.1) (leadingForm ρ σ T.1) ≠ 0 := hprev
  have hlead := (leadingForm_commutator T P ρ σ hweight hT).2
  have hnext : josephCommutatorChain P R N = P*T-T*P := by
    have hi : N=(N-1)+1 := by omega
    conv_lhs => rw [hi]
    rfl
  refine ⟨T,josephCommutatorChain_mem P Q R hR _,hT,?_⟩
  rw [← hlead]
  change poisson (leadingForm ρ σ P.1) (leadingForm ρ σ (P*T-T*P).1)=0
  rw [← hnext]
  exact hN

end Dixmier.Weyl
