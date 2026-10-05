/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Abstract

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

namespace Dixmier.Weyl

noncomputable section
variable (K L : Type*) [Field K] [Field L] [Algebra K L]

def freeBaseChange : WeylFreeAlgebra K →ₐ[K] A1 L :=
  FreeAlgebra.lift K (abstractGenerators L)

theorem freeBaseChange_relation : freeBaseChange K L (weylRelation K) = 0 := by
  simpa [freeBaseChange, weylRelation, evaluateWeylFree] using
    (evaluateWeylFree_relation L)

theorem freeBaseChange_zero_on_relationIdeal
    (a : WeylFreeAlgebra K) (ha : a ∈ weylRelationIdeal K) :
    freeBaseChange K L a = 0 := by
  unfold weylRelationIdeal at ha
  change a ∈ Submodule.span (WeylFreeAlgebra K) (weylRelationMultiples K) at ha
  refine Submodule.span_induction (R := WeylFreeAlgebra K) (s := weylRelationMultiples K)
    (p := fun x _ => freeBaseChange K L x = 0) ?_ ?_ ?_ ?_ ha
  · intro x hx
    rcases hx with ⟨⟨u,v⟩,rfl⟩
    simp only [map_mul]
    rw [freeBaseChange_relation]
    simp
  · simp
  · intro x y hx hy hxe hye
    simp [map_add, hxe, hye]
  · intro c x hx hxe
    change freeBaseChange K L (c*x) = 0
    rw [map_mul,hxe]
    simp

def abstractBaseChange : AbstractA1 K →ₐ[K] A1 L :=
  Ideal.Quotient.liftₐ (weylRelationIdeal K) (freeBaseChange K L)
    (freeBaseChange_zero_on_relationIdeal K L)

def concreteBaseChange [CharZero K] : A1 K →ₐ[K] A1 L :=
  (abstractBaseChange K L).comp (abstractToConcreteEquiv K).symm.toAlgHom

theorem abstractBaseChange_x : abstractBaseChange K L (abstractX K) = concreteX L := by
  change ((Ideal.Quotient.liftₐ (weylRelationIdeal K) (freeBaseChange K L)
    (freeBaseChange_zero_on_relationIdeal K L)).comp
      (Ideal.Quotient.mkₐ K (weylRelationIdeal K))) (FreeAlgebra.ι K 0) = concreteX L
  rw [Ideal.Quotient.liftₐ_comp]
  simp [freeBaseChange, abstractGenerators]

theorem abstractBaseChange_y : abstractBaseChange K L (abstractY K) = concreteY L := by
  change ((Ideal.Quotient.liftₐ (weylRelationIdeal K) (freeBaseChange K L)
    (freeBaseChange_zero_on_relationIdeal K L)).comp
      (Ideal.Quotient.mkₐ K (weylRelationIdeal K))) (FreeAlgebra.ι K 1) = concreteY L
  rw [Ideal.Quotient.liftₐ_comp]
  simp [freeBaseChange, abstractGenerators]

theorem concreteBaseChange_x [CharZero K] :
    concreteBaseChange K L (concreteX K) = concreteX L := by
  have h : (abstractToConcreteEquiv K).symm (concreteX K) = abstractX K := by
    apply (abstractToConcreteEquiv K).injective
    rw [AlgEquiv.apply_symm_apply]
    exact (abstractToConcrete_abstractX K).symm
  simpa [concreteBaseChange, h] using (abstractBaseChange_x K L)

theorem concreteBaseChange_y [CharZero K] :
    concreteBaseChange K L (concreteY K) = concreteY L := by
  have h : (abstractToConcreteEquiv K).symm (concreteY K) = abstractY K := by
    apply (abstractToConcreteEquiv K).injective
    rw [AlgEquiv.apply_symm_apply]
    exact (abstractToConcrete_abstractY K).symm
  simpa [concreteBaseChange, h] using (abstractBaseChange_y K L)

end
end Dixmier.Weyl
