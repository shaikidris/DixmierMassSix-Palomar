/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.AppendixA3FactorPower

public import DixmierFormal.MvPolynomialCompat

@[expose] public section
namespace Dixmier
open Polynomial

/-- Normalize the nonzero linear coefficient of the quadratic factor by a
nonzero scaling, preserving the companion equation and every power term count. -/
theorem appendix_A3_normalize_linear {ρ s : ℕ} {A B : ℂ[X]}
    (hu : A.coeff 1 ≠ 0)
    (hcomp : Comp ρ s (A*B^2) (A*B*(-1))) :
    ∃ An Bn : ℂ[X],
      Comp ρ s (An*Bn^2) (An*Bn*(-1)) ∧
      An.natDegree = A.natDegree ∧ Bn.natDegree = B.natDegree ∧
      An.eval 0 = A.eval 0 ∧ Bn.eval 0 = B.eval 0 ∧
      An.coeff 1 = 1 ∧
      (∀ k : ℕ, termCount ((An*Bn^2)^k) = termCount ((A*B^2)^k)) := by
  let c := (A.coeff 1)⁻¹
  let An := A.comp (C c*X)
  let Bn := B.comp (C c*X)
  have hc : c ≠ 0 := inv_ne_zero hu
  have hcomp' : Comp ρ s (An*Bn^2) (An*Bn*(-1)) := by
    have ht := hcomp.comp_C_mul_X c
    simpa only [An,Bn,mul_comp,pow_comp,neg_comp,one_comp] using ht
  refine ⟨An,Bn,hcomp',?_,?_,?_,?_,?_,?_⟩
  · exact natDegree_comp_C_mul_X hc
  · exact natDegree_comp_C_mul_X hc
  · exact eval_zero_comp_C_mul_X A c
  · exact eval_zero_comp_C_mul_X B c
  · dsimp [An,c]
    rw [coeff_comp_C_mul_X]
    simp [hu]
  · intro k
    have heq : An*Bn^2 = (A*B^2).comp (C c*X) := by
      simp only [An,Bn,mul_comp,pow_comp]
    rw [heq, ← pow_comp]
    exact termCount_comp_C_mul_X hc

end Dixmier
