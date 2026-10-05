/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedShearCandidate

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Ramified coefficient shears are algebra automorphisms

For any Laurent coefficient `h`, substitution `Y ↦ Y+M_h` on the unique
finite PBW expansion preserves multiplication. The proof first establishes
intertwining for left multiplication by every coefficient and by `Y`, then
uses induction over the generated algebra. Shifting by `-h` is its inverse.

This is the abstract shear automorphism. The root-selected maximum cut,
the induced Newton polygon directions, endpoint formulas, and preservation
assertions of G13 Proposition 5.3 remain separate obligations.
-/
namespace Dixmier.Weyl

noncomputable def ramifiedCoeffLeftLinear (f : LaurentPolynomial ℂ) :
    (ℕ →₀ LaurentPolynomial ℂ) →ₗ[ℂ]
      (ℕ →₀ LaurentPolynomial ℂ) :=
  Finsupp.mapRange.linearMap (LinearMap.mulLeft ℂ f)

theorem ramifiedCoeffLeftLinear_single (f g : LaurentPolynomial ℂ)
    (j : ℕ) :
    ramifiedCoeffLeftLinear f (Finsupp.single j g) =
      Finsupp.single j (f*g) := by
  simp [ramifiedCoeffLeftLinear]

theorem ramifiedNormalEval_coeff_left (l : ℕ)
    (f : LaurentPolynomial ℂ) (a : ℕ →₀ LaurentPolynomial ℂ) :
    ramifiedNormalEval l (ramifiedCoeffLeftLinear f a) =
      ramifiedCoeffMul f * ramifiedNormalEval l a := by
  induction a using Finsupp.induction_linear with
  | zero =>
      simp [ramifiedCoeffLeftLinear, ramifiedNormalEval,
        ramifiedCoeffMul]
  | add a b ha hb =>
      rw [map_add, ← ramifiedNormalEvalLinear_apply, map_add,
        ramifiedNormalEvalLinear_apply,
        ramifiedNormalEvalLinear_apply, ha, hb]
      have hadd : ramifiedNormalEval l (a+b) =
          ramifiedNormalEval l a + ramifiedNormalEval l b := by
        rw [← ramifiedNormalEvalLinear_apply, map_add,
          ramifiedNormalEvalLinear_apply, ramifiedNormalEvalLinear_apply]
      rw [hadd, mul_add]
  | single j g =>
      rw [ramifiedCoeffLeftLinear_single]
      have h₁ := ramifiedNormalEvalLinear_single l j (f*g)
      have h₂ := ramifiedNormalEvalLinear_single l j g
      rw [ramifiedNormalEvalLinear_apply] at h₁ h₂
      rw [h₁, h₂, ← mul_assoc, ramifiedCoeffMul_mul]

theorem ramifiedShiftEval_coeff_left (l : ℕ)
    (h f : LaurentPolynomial ℂ) (a : ℕ →₀ LaurentPolynomial ℂ) :
    ramifiedShiftEval l h (ramifiedCoeffLeftLinear f a) =
      ramifiedCoeffMul f * ramifiedShiftEval l h a := by
  induction a using Finsupp.induction_linear with
  | zero =>
      simp [ramifiedCoeffLeftLinear, ramifiedShiftEval,
        ramifiedCoeffMul]
  | add a b ha hb =>
      rw [map_add, ← ramifiedShiftEvalLinear_apply, map_add,
        ramifiedShiftEvalLinear_apply,
        ramifiedShiftEvalLinear_apply, ha, hb]
      have hadd : ramifiedShiftEval l h (a+b) =
          ramifiedShiftEval l h a + ramifiedShiftEval l h b := by
        rw [← ramifiedShiftEvalLinear_apply, map_add,
          ramifiedShiftEvalLinear_apply, ramifiedShiftEvalLinear_apply]
      rw [hadd, mul_add]
  | single j g =>
      rw [ramifiedCoeffLeftLinear_single]
      rw [ramifiedShiftEval_single, ramifiedShiftEval_single,
        ← mul_assoc, ramifiedCoeffMul_mul]

theorem ramifiedPBWCoeffs_coeff_left (l : ℕ) (hl : 0 < l)
    (f : LaurentPolynomial ℂ) (T : ramifiedOperatorAlgebra l) :
    ramifiedPBWCoeffs l hl (ramifiedCoeffGen l f * T) =
      ramifiedCoeffLeftLinear f (ramifiedPBWCoeffs l hl T) := by
  apply ramifiedPBWCoeffs_eq_of_eval
  rw [ramifiedNormalEval_coeff_left, ramifiedPBWCoeffs_eval]
  rfl

theorem ramifiedShearCandidate_coeff_left (l : ℕ) (hl : 0 < l)
    (h f : LaurentPolynomial ℂ) (T : ramifiedOperatorAlgebra l) :
    ramifiedShearCandidate l hl h (ramifiedCoeffGen l f * T) =
      ramifiedCoeffGen l f * ramifiedShearCandidate l hl h T := by
  apply Subtype.ext
  change ramifiedShiftEval l h
    (ramifiedPBWCoeffs l hl (ramifiedCoeffGen l f * T)) =
      ramifiedCoeffMul f * ramifiedShiftEval l h
        (ramifiedPBWCoeffs l hl T)
  rw [ramifiedPBWCoeffs_coeff_left, ramifiedShiftEval_coeff_left]

noncomputable def ramifiedDerivativeLeftLinear (l : ℕ) :
    (ℕ →₀ LaurentPolynomial ℂ) →ₗ[ℂ]
      (ℕ →₀ LaurentPolynomial ℂ) :=
  (Finsupp.lsum ℂ) (fun j =>
    Finsupp.lsingle (j+1) +
      (Finsupp.lsingle j).comp (ramifiedDerivative l))

theorem ramifiedDerivativeLeftLinear_single (l j : ℕ)
    (f : LaurentPolynomial ℂ) :
    ramifiedDerivativeLeftLinear l (Finsupp.single j f) =
      Finsupp.single (j+1) f +
        Finsupp.single j (ramifiedDerivative l f) := by
  change (Finsupp.single j f).sum (fun i g =>
    Finsupp.single (i+1) g +
      Finsupp.single i (ramifiedDerivative l g)) = _
  rw [Finsupp.sum_single_index]
  simp

theorem ramifiedNormalEval_derivative_left (l : ℕ)
    (a : ℕ →₀ LaurentPolynomial ℂ) :
    ramifiedNormalEval l (ramifiedDerivativeLeftLinear l a) =
      ramifiedDerivative l * ramifiedNormalEval l a := by
  induction a using Finsupp.induction_linear with
  | zero =>
      simp [ramifiedDerivativeLeftLinear, ramifiedNormalEval]
  | add a b ha hb =>
      rw [map_add, ← ramifiedNormalEvalLinear_apply, map_add,
        ramifiedNormalEvalLinear_apply,
        ramifiedNormalEvalLinear_apply, ha, hb]
      have hadd : ramifiedNormalEval l (a+b) =
          ramifiedNormalEval l a + ramifiedNormalEval l b := by
        rw [← ramifiedNormalEvalLinear_apply, map_add,
          ramifiedNormalEvalLinear_apply, ramifiedNormalEvalLinear_apply]
      rw [hadd, mul_add]
  | single j f =>
      rw [ramifiedDerivativeLeftLinear_single]
      have h₁ := ramifiedNormalEvalLinear_single l (j+1) f
      have h₂ := ramifiedNormalEvalLinear_single l j
        (ramifiedDerivative l f)
      have h₃ := ramifiedNormalEvalLinear_single l j f
      simp only [ramifiedNormalEvalLinear_apply] at h₁ h₂ h₃
      rw [← ramifiedNormalEvalLinear_apply, map_add,
        ramifiedNormalEvalLinear_apply,
        ramifiedNormalEvalLinear_apply, h₁, h₂, h₃]
      rw [← mul_assoc, ramified_normal_order, add_mul]
      simp only [mul_assoc, ← pow_succ']

theorem ramifiedShiftEval_derivative_left (l : ℕ)
    (h : LaurentPolynomial ℂ) (a : ℕ →₀ LaurentPolynomial ℂ) :
    ramifiedShiftEval l h (ramifiedDerivativeLeftLinear l a) =
      ramifiedShiftedY l h * ramifiedShiftEval l h a := by
  induction a using Finsupp.induction_linear with
  | zero =>
      simp [ramifiedDerivativeLeftLinear, ramifiedShiftEval]
  | add a b ha hb =>
      rw [map_add, ← ramifiedShiftEvalLinear_apply, map_add,
        ramifiedShiftEvalLinear_apply,
        ramifiedShiftEvalLinear_apply, ha, hb]
      have hadd : ramifiedShiftEval l h (a+b) =
          ramifiedShiftEval l h a + ramifiedShiftEval l h b := by
        rw [← ramifiedShiftEvalLinear_apply, map_add,
          ramifiedShiftEvalLinear_apply, ramifiedShiftEvalLinear_apply]
      rw [hadd, mul_add]
  | single j f =>
      rw [ramifiedDerivativeLeftLinear_single]
      rw [← ramifiedShiftEvalLinear_apply, map_add,
        ramifiedShiftEvalLinear_apply,
        ramifiedShiftEvalLinear_apply,
        ramifiedShiftEval_single, ramifiedShiftEval_single,
        ramifiedShiftEval_single]
      rw [← mul_assoc, ramifiedShiftedY_normal_order, add_mul]
      simp only [mul_assoc, ← pow_succ']

theorem ramifiedPBWCoeffs_derivative_left (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) :
    ramifiedPBWCoeffs l hl (ramifiedYGen l * T) =
      ramifiedDerivativeLeftLinear l (ramifiedPBWCoeffs l hl T) := by
  apply ramifiedPBWCoeffs_eq_of_eval
  rw [ramifiedNormalEval_derivative_left, ramifiedPBWCoeffs_eval]
  rfl

theorem ramifiedShearCandidate_derivative_left (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) (T : ramifiedOperatorAlgebra l) :
    (ramifiedShearCandidate l hl h (ramifiedYGen l * T) :
      Module.End ℂ (LaurentPolynomial ℂ)) =
      ramifiedShiftedY l h *
        (ramifiedShearCandidate l hl h T :
          Module.End ℂ (LaurentPolynomial ℂ)) := by
  change ramifiedShiftEval l h
    (ramifiedPBWCoeffs l hl (ramifiedYGen l * T)) =
      ramifiedShiftedY l h * ramifiedShiftEval l h
        (ramifiedPBWCoeffs l hl T)
  rw [ramifiedPBWCoeffs_derivative_left, ramifiedShiftEval_derivative_left]

theorem ramifiedShearCandidate_one (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) :
    ramifiedShearCandidate l hl h 1 = 1 := by
  have hone : ramifiedCoeffGen l 1 = 1 := by
    apply Subtype.ext
    exact ramifiedCoeffMul_one
  rw [← hone, ramifiedShearCandidate_coeffGen, hone]

theorem ramifiedShearCandidate_algebraMap (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) (c : ℂ) :
    ramifiedShearCandidate l hl h
      (algebraMap ℂ (ramifiedOperatorAlgebra l) c) =
      algebraMap ℂ (ramifiedOperatorAlgebra l) c := by
  have hc : ramifiedCoeffGen l (LaurentPolynomial.C c) =
      algebraMap ℂ (ramifiedOperatorAlgebra l) c := by
    apply Subtype.ext
    exact ramifiedCoeffMul_C c
  rw [← hc, ramifiedShearCandidate_coeffGen, hc]

noncomputable def ramifiedShiftedYGen (l : ℕ)
    (h : LaurentPolynomial ℂ) : ramifiedOperatorAlgebra l :=
  ⟨ramifiedShiftedY l h, ramifiedShiftedY_mem l h⟩

theorem ramifiedShearCandidate_YGen_sub (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) :
    ramifiedShearCandidate l hl h (ramifiedYGen l) =
      ramifiedShiftedYGen l h := by
  apply Subtype.ext
  exact ramifiedShearCandidate_YGen l hl h

theorem ramifiedShearCandidate_derivative_left_sub (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) (T : ramifiedOperatorAlgebra l) :
    ramifiedShearCandidate l hl h (ramifiedYGen l * T) =
      ramifiedShiftedYGen l h * ramifiedShearCandidate l hl h T := by
  apply Subtype.ext
  exact ramifiedShearCandidate_derivative_left l hl h T

theorem ramifiedShearCandidate_mul (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) (T U : ramifiedOperatorAlgebra l) :
    ramifiedShearCandidate l hl h (T * U) =
      ramifiedShearCandidate l hl h T *
        ramifiedShearCandidate l hl h U := by
  have key : ∀ x ∈ ramifiedOperatorAlgebra l,
      ∀ hx : x ∈ ramifiedOperatorAlgebra l,
      ∀ V : ramifiedOperatorAlgebra l,
      ramifiedShearCandidate l hl h
        (⟨x, hx⟩ * V) =
        ramifiedShearCandidate l hl h ⟨x,hx⟩ *
          ramifiedShearCandidate l hl h V := by
    intro x hx
    refine Algebra.adjoin_induction
      (p := fun x _ => ∀ hx : x ∈ ramifiedOperatorAlgebra l,
        ∀ V : ramifiedOperatorAlgebra l,
        ramifiedShearCandidate l hl h (⟨x,hx⟩ * V) =
          ramifiedShearCandidate l hl h ⟨x,hx⟩ *
            ramifiedShearCandidate l hl h V) ?_ ?_ ?_ ?_ hx
    · intro x hx hxA V
      rcases hx with ⟨f,rfl⟩ | hx
      · change ramifiedShearCandidate l hl h (ramifiedCoeffGen l f * V) =
          ramifiedShearCandidate l hl h (ramifiedCoeffGen l f) *
            ramifiedShearCandidate l hl h V
        rw [ramifiedShearCandidate_coeff_left,
          ramifiedShearCandidate_coeffGen]
      · have heq : x = ramifiedDerivative l := Set.mem_singleton_iff.mp hx
        subst x
        change ramifiedShearCandidate l hl h (ramifiedYGen l * V) =
          ramifiedShearCandidate l hl h (ramifiedYGen l) *
            ramifiedShearCandidate l hl h V
        rw [ramifiedShearCandidate_derivative_left_sub,
          ramifiedShearCandidate_YGen_sub]
    · intro c hxA V
      change ramifiedShearCandidate l hl h
        ((algebraMap ℂ (ramifiedOperatorAlgebra l) c) * V) =
        ramifiedShearCandidate l hl h
          (algebraMap ℂ (ramifiedOperatorAlgebra l) c) *
          ramifiedShearCandidate l hl h V
      rw [← Algebra.smul_def, ramifiedShearCandidate_smul,
        ramifiedShearCandidate_algebraMap, Algebra.smul_def]
    · intro x y hx hy ihx ihy hxy V
      have hadd : (⟨x+y,hxy⟩ : ramifiedOperatorAlgebra l) =
          (⟨x,hx⟩ : ramifiedOperatorAlgebra l) + ⟨y,hy⟩ :=
        Subtype.ext rfl
      rw [hadd]
      rw [add_mul, ramifiedShearCandidate_add,
        ramifiedShearCandidate_add, ihx hx V, ihy hy V, add_mul]
    · intro x y hx hy ihx ihy hxy V
      have hmul : (⟨x*y,hxy⟩ : ramifiedOperatorAlgebra l) =
          (⟨x,hx⟩ : ramifiedOperatorAlgebra l) * ⟨y,hy⟩ :=
        Subtype.ext rfl
      rw [hmul, mul_assoc]
      rw [ihx hx (⟨y,hy⟩ * V), ihy hy V, ihx hx ⟨y,hy⟩,
        mul_assoc]
  exact key T.1 T.2 T.2 U

noncomputable def ramifiedShearHom (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) :
    ramifiedOperatorAlgebra l →ₐ[ℂ] ramifiedOperatorAlgebra l where
  toFun := ramifiedShearCandidate l hl h
  map_one' := ramifiedShearCandidate_one l hl h
  map_mul' := ramifiedShearCandidate_mul l hl h
  map_zero' := by
    have hz := ramifiedShearCandidate_smul l hl h 0 (0 : ramifiedOperatorAlgebra l)
    simpa using hz
  map_add' := ramifiedShearCandidate_add l hl h
  commutes' := ramifiedShearCandidate_algebraMap l hl h

theorem ramifiedAlgHom_ext (l : ℕ)
    (F G : ramifiedOperatorAlgebra l →ₐ[ℂ] ramifiedOperatorAlgebra l)
    (hcoeff : ∀ f : LaurentPolynomial ℂ,
      F (ramifiedCoeffGen l f) = G (ramifiedCoeffGen l f))
    (hY : F (ramifiedYGen l) = G (ramifiedYGen l)) : F = G := by
  apply AlgHom.ext
  intro T
  have key : ∀ x ∈ ramifiedOperatorAlgebra l,
      ∀ hx : x ∈ ramifiedOperatorAlgebra l,
      F ⟨x,hx⟩ = G ⟨x,hx⟩ := by
    intro x hx
    refine Algebra.adjoin_induction
      (p := fun x _ => ∀ hx : x ∈ ramifiedOperatorAlgebra l,
        F ⟨x,hx⟩ = G ⟨x,hx⟩) ?_ ?_ ?_ ?_ hx
    · intro x hx hxA
      rcases hx with ⟨f,rfl⟩ | hx
      · change F (ramifiedCoeffGen l f) = G (ramifiedCoeffGen l f)
        exact hcoeff f
      · have heq : x = ramifiedDerivative l := Set.mem_singleton_iff.mp hx
        subst x
        change F (ramifiedYGen l) = G (ramifiedYGen l)
        exact hY
    · intro c hxA
      change F (algebraMap ℂ (ramifiedOperatorAlgebra l) c) =
        G (algebraMap ℂ (ramifiedOperatorAlgebra l) c)
      simp
    · intro x y hx hy ihx ihy hxy
      have hadd : (⟨x+y,hxy⟩ : ramifiedOperatorAlgebra l) =
          (⟨x,hx⟩ : ramifiedOperatorAlgebra l) + ⟨y,hy⟩ := Subtype.ext rfl
      rw [hadd, map_add, map_add, ihx hx, ihy hy]
    · intro x y hx hy ihx ihy hxy
      have hmul : (⟨x*y,hxy⟩ : ramifiedOperatorAlgebra l) =
          (⟨x,hx⟩ : ramifiedOperatorAlgebra l) * ⟨y,hy⟩ := Subtype.ext rfl
      rw [hmul, map_mul, map_mul, ihx hx, ihy hy]
  exact key T.1 T.2 T.2

theorem ramifiedShiftedYGen_eq_add (l : ℕ) (h : LaurentPolynomial ℂ) :
    ramifiedShiftedYGen l h =
      ramifiedYGen l + ramifiedCoeffGen l h := by
  apply Subtype.ext
  rfl

theorem ramifiedCoeffGen_neg (l : ℕ) (h : LaurentPolynomial ℂ) :
    ramifiedCoeffGen l (-h) = -ramifiedCoeffGen l h := by
  apply Subtype.ext
  exact (ramifiedCoeffMulLinear.map_neg h)

theorem ramifiedShearHom_inverse_on_Y (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) :
    ramifiedShearHom l hl (-h)
      (ramifiedShearHom l hl h (ramifiedYGen l)) =
      ramifiedYGen l := by
  change ramifiedShearCandidate l hl (-h)
    (ramifiedShearCandidate l hl h (ramifiedYGen l)) = _
  rw [ramifiedShearCandidate_YGen_sub,
    ramifiedShiftedYGen_eq_add,
    ramifiedShearCandidate_add,
    ramifiedShearCandidate_YGen_sub,
    ramifiedShearCandidate_coeffGen,
    ramifiedShiftedYGen_eq_add,
    ramifiedCoeffGen_neg]
  abel

theorem ramifiedShearHom_inverse_left (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) :
    (ramifiedShearHom l hl (-h)).comp (ramifiedShearHom l hl h) =
      AlgHom.id ℂ (ramifiedOperatorAlgebra l) := by
  apply ramifiedAlgHom_ext l
  · intro f
    change ramifiedShearCandidate l hl (-h)
      (ramifiedShearCandidate l hl h (ramifiedCoeffGen l f)) = _
    rw [ramifiedShearCandidate_coeffGen,
      ramifiedShearCandidate_coeffGen]
    rfl
  · exact ramifiedShearHom_inverse_on_Y l hl h

theorem ramifiedShearHom_inverse_right (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) :
    (ramifiedShearHom l hl h).comp (ramifiedShearHom l hl (-h)) =
      AlgHom.id ℂ (ramifiedOperatorAlgebra l) := by
  simpa only [neg_neg] using ramifiedShearHom_inverse_left l hl (-h)

/-- The exact algebra automorphism `Y ↦ Y+M_h`, with inverse shift `-h`. -/
noncomputable def ramifiedShearAut (l : ℕ) (hl : 0 < l)
    (h : LaurentPolynomial ℂ) :
    ramifiedOperatorAlgebra l ≃ₐ[ℂ] ramifiedOperatorAlgebra l :=
  { ramifiedShearHom l hl h with
    invFun := ramifiedShearHom l hl (-h)
    left_inv := by
      intro T
      have heq := congrArg (fun F : ramifiedOperatorAlgebra l →ₐ[ℂ]
        ramifiedOperatorAlgebra l => F T)
        (ramifiedShearHom_inverse_left l hl h)
      exact heq
    right_inv := by
      intro T
      have heq := congrArg (fun F : ramifiedOperatorAlgebra l →ₐ[ℂ]
        ramifiedOperatorAlgebra l => F T)
        (ramifiedShearHom_inverse_right l hl h)
      exact heq }

end Dixmier.Weyl
