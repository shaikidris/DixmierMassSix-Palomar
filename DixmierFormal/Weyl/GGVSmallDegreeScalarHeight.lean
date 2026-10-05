/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVSmallDegreeScalarReconstruction
public import DixmierFormal.Weyl.CrossingCutRootCount

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Scalar degree and full root multiplicity at the selected crossing height -/
namespace Dixmier.Weyl
open MvPolynomial
set_option maxHeartbeats 1000000

theorem smallDegreeCrossing_root_degreeOf_Y
    (P Q : A1 ℂ) (H : GGVSmallDegreeCrossingData P Q) :
    H.root.degreeOf 1 = H.v := by
  apply Nat.le_antisymm
  · rw [degreeOf_eq_sup]
    apply Finset.sup_le
    intro e he
    have hx := H.endMax e he
    have hw := H.rootHomogeneous (mem_support_iff.mp he)
    have hend := H.rootHomogeneous (mem_support_iff.mp H.endOccupied)
    obtain ⟨⟨a,b⟩,rfl⟩ := expo_surjective e
    rw [expo_weight] at hw hend
    simp [expo] at hx ⊢
    have hs : (0 : ℤ) < H.s := by exact_mod_cast H.sPos
    have hρ : (0 : ℤ) < H.rho := by exact_mod_cast H.rhoPos
    have hax : (a : ℤ) ≤ H.u := by exact_mod_cast hx
    have hb : (b : ℤ) ≤ H.v := by nlinarith
    exact_mod_cast hb
  · simpa [expo] using le_degreeOf_of_mem_support 1 H.endOccupied

theorem smallDegreeCrossing_scalar_degree_eq_height
    (P Q : A1 ℂ) (H : GGVSmallDegreeCrossingData P Q)
    (c : ℂ) (p : Polynomial ℂ) (hc : c ≠ 0) (hp0 : p.coeff 0=1)
    (hshape : H.root = C c * (X 0^H.r * X 1^H.t *
      p.eval₂ C (X 0^H.s * X 1^H.rho))) :
    p.natDegree=H.h := by
  have hp0eval : p.eval 0=1 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hp0
  have hcomp : p.comp (Polynomial.X^H.rho) ≠ 0 := by
    intro hz
    have he := congrArg (Polynomial.eval 0) hz
    simp [Polynomial.eval_comp,H.rhoPos.ne',hp0eval] at he
  have hspecial := homogeneous_specialization_natDegree_eq_degreeOf_Y
    H.root H.rho (-(H.s : ℤ)) H.weight
      (by exact_mod_cast H.rhoPos) H.rootHomogeneous
  rw [smallDegreeCrossing_root_degreeOf_Y P Q H] at hspecial
  have hspecialShape :
      MvPolynomial.eval₂ Polynomial.C
        (fun i : Fin 2 => if i=0 then 1 else Polynomial.X) H.root =
        Polynomial.C c * (Polynomial.X^H.t * p.comp (Polynomial.X^H.rho)) := by
    rw [hshape]
    simp only [MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,
      crossing_substitution_eval,MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X]
    simp
  rw [hspecialShape,Polynomial.natDegree_C_mul hc,
    Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) hcomp,
    Polynomial.natDegree_X_pow,Polynomial.natDegree_comp,
    Polynomial.natDegree_X_pow] at hspecial
  have hv := H.endHeight
  have hρ := H.rhoPos
  nlinarith

/-- The actual crossing reconstruction has a nonzero scalar root carrying
exactly the height used by the forbidden-corner coordinates. -/
theorem smallDegreeCrossing_scalar_root_at_height
    (P Q : A1 ℂ) (H : GGVSmallDegreeCrossingData P Q) :
    ∃ (c : ℂ) (p f : Polynomial ℂ) (α : ℂ),
      c ≠ 0 ∧ p.coeff 0=1 ∧
      H.root = C c * (X 0^H.r * X 1^H.t *
        p.eval₂ C (X 0^H.s * X 1^H.rho)) ∧
      H.companion = (X 0*X 1)*f.eval₂ C (X 0^H.s*X 1^H.rho) ∧
      p.natDegree=H.h ∧ α ≠ 0 ∧ p.IsRoot α ∧
      Polynomial.rootMultiplicity α p=H.h := by
  obtain ⟨c,p,f,hc,hp0,hR,hF,hf0,hfdeg,hg⟩ :=
    smallDegreeCrossing_exact_scalar_reconstruction P Q H
  have hpdeg := smallDegreeCrossing_scalar_degree_eq_height P Q H c p hc hp0 hR
  have hp0eval : p.eval 0=1 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hp0
  have hδ : 0 < H.rho-H.s := by have := H.direction.2; omega
  have hpPos : 0 < p.natDegree := by rw [hpdeg]; have := H.hProper; omega
  obtain ⟨α,hαne,hα,hmult⟩ := hg.exists_full_multiplicity_root hδ hp0eval hpPos hfdeg
  exact ⟨c,p,f,α,hc,hp0,hR,hF,hpdeg,hαne,hα,hmult.trans hpdeg⟩

end Dixmier.Weyl
