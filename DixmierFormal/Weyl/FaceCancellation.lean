/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PurePowerArithmetic
public import Mathlib.Algebra.MvPolynomial.CommRing

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Strict weighted-degree drop after exact face cancellation

This is the algebraic termination measure used by mate descent. It makes no
claim that a suitable scalar or power exists; those are separate consequences
of the leading-face geometry and the published structural inputs.
-/

namespace Dixmier.Weyl

open Polynomial MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- If both polynomials have weight at most `m` and their `m`-components agree,
their difference has weight strictly below `m`. The zero difference is included
because `weightedTotalDegree' 0 = ⊥`. -/
theorem weightedDegree_sub_lt_of_top_eq (w : Fin 2 → ℤ)
    (p q : MvPolynomial (Fin 2) K) (m : ℤ)
    (hp : weightedTotalDegree' w p ≤ (m : WithBot ℤ))
    (hq : weightedTotalDegree' w q ≤ (m : WithBot ℤ))
    (htop : weightedHomogeneousComponent w m p = weightedHomogeneousComponent w m q) :
    weightedTotalDegree' w (p - q) < (m : WithBot ℤ) := by
  classical
  have hle : weightedTotalDegree' w (p - q) ≤ (m : WithBot ℤ) := by
    change (p - q).support.sup (fun d => (Finsupp.weight w d : WithBot ℤ)) ≤ m
    apply Finset.sup_le
    intro d hd
    rcases Finset.mem_union.mp (MvPolynomial.support_sub (Fin 2) p q hd) with hdp | hdq
    · have hle : (Finsupp.weight w d : WithBot ℤ) ≤ weightedTotalDegree' w p := by
        change (Finsupp.weight w d : WithBot ℤ) ≤
          p.support.sup (fun e => (Finsupp.weight w e : WithBot ℤ))
        exact Finset.le_sup (f := fun e => (Finsupp.weight w e : WithBot ℤ)) hdp
      exact le_trans hle hp
    · have hle : (Finsupp.weight w d : WithBot ℤ) ≤ weightedTotalDegree' w q := by
        change (Finsupp.weight w d : WithBot ℤ) ≤
          q.support.sup (fun e => (Finsupp.weight w e : WithBot ℤ))
        exact Finset.le_sup (f := fun e => (Finsupp.weight w e : WithBot ℤ)) hdq
      exact le_trans hle hq
  have hzero : weightedHomogeneousComponent w m (p - q) = 0 := by
    rw [map_sub, htop, sub_self]
  have hne : weightedTotalDegree' w (p - q) ≠ (m : WithBot ℤ) := by
    intro heq
    exact (weightedComponent_ne_zero_of_weightedTotalDegree_eq w (p - q) m heq) hzero
  exact lt_of_le_of_ne hle hne

/-- A positive integer mate weight strictly decreases when subtraction cancels
the entire top face and the removed term has no higher-weight monomial. -/
theorem mateSubtraction_weight_drop (P Q : A1 K) (c : K) (k : ℕ)
    (ρ σ m : ℤ) (hm : 0 < m)
    (hQ : weightedTotalDegree' (wt ρ σ)
      (symbol (Q : Module.End K K[X])) ≤ (m : WithBot ℤ))
    (hterm : weightedTotalDegree' (wt ρ σ)
      (symbol ((c • P ^ k : A1 K) : Module.End K K[X])) ≤ (m : WithBot ℤ))
    (hface : weightedHomogeneousComponent (wt ρ σ) m
      (symbol (Q : Module.End K K[X])) =
      weightedHomogeneousComponent (wt ρ σ) m
        (symbol ((c • P ^ k : A1 K) : Module.End K K[X]))) :
    vDeg ρ σ ((Q - c • P ^ k : A1 K) : Module.End K K[X]) < m := by
  have hsub := weightedDegree_sub_lt_of_top_eq (wt ρ σ)
    (symbol (Q : Module.End K K[X]))
    (symbol ((c • P ^ k : A1 K) : Module.End K K[X])) m hQ hterm hface
  rw [← symbol_sub Q (c • P ^ k)] at hsub
  change WithBot.unbotD 0
    (weightedTotalDegree' (wt ρ σ)
      (symbol ((Q - c • P ^ k : A1 K) : Module.End K K[X]))) < m
  exact (WithBot.unbotD_lt_iff (by intro _; exact hm)).mpr hsub

/-- A version of `mateSubtraction_weight_drop` stated using the paper's
leading-form language, with the two exact weighted degrees made explicit. -/
theorem mateSubtraction_weight_drop_of_leadingForm_eq (P Q : A1 K) (c : K) (k : ℕ)
    (ρ σ m : ℤ) (hm : 0 < m)
    (hQdeg : weightedTotalDegree' (wt ρ σ)
      (symbol (Q : Module.End K K[X])) = (m : WithBot ℤ))
    (htermdeg : weightedTotalDegree' (wt ρ σ)
      (symbol ((c • P ^ k : A1 K) : Module.End K K[X])) = (m : WithBot ℤ))
    (hform : leadingForm ρ σ (Q : Module.End K K[X]) =
      leadingForm ρ σ ((c • P ^ k : A1 K) : Module.End K K[X])) :
    vDeg ρ σ ((Q - c • P ^ k : A1 K) : Module.End K K[X]) < m := by
  have hvQ : vDeg ρ σ (Q : Module.End K K[X]) = m := by
    simp [vDeg, hQdeg]
  have hvTerm : vDeg ρ σ ((c • P ^ k : A1 K) : Module.End K K[X]) = m := by
    change WithBot.unbotD 0
      (weightedTotalDegree' (wt ρ σ)
        (symbol ((c • P ^ k : A1 K) : Module.End K K[X]))) = m
    rw [htermdeg]
    rfl
  have hface : weightedHomogeneousComponent (wt ρ σ) m
      (symbol (Q : Module.End K K[X])) =
      weightedHomogeneousComponent (wt ρ σ) m
        (symbol ((c • P ^ k : A1 K) : Module.End K K[X])) := by
    simpa only [leadingForm, hvQ, hvTerm] using hform
  exact mateSubtraction_weight_drop P Q c k ρ σ m hm
    (le_of_eq hQdeg) (le_of_eq htermdeg) hface

end Dixmier.Weyl
