/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVHorizontalStandardCut

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!+# Polynomial recovery of the horizontal constant cut

The exact horizontal ramified shear preserves the faithful image of the
polynomial Weyl algebra. It therefore descends to a polynomial algebra
automorphism, with the negative constant shear as inverse. Generation is
preserved in polynomial A₁, rather than inferred from generation in the
larger Laurent differential-operator algebra.
-/

namespace Dixmier.Weyl

open Polynomial

set_option maxHeartbeats 800000

private theorem horizontal_cut_shift_scalar (c : ℂ) :
    ramifiedCoeffGen 1 (ramifiedCutShift 1 1 0 c) =
      algebraMap ℂ (ramifiedOperatorAlgebra 1) c := by
  simp only [ramifiedCutShift, ramifiedCutExponent, mul_zero, LaurentPolynomial.T_zero]
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  change (c • (1 : LaurentPolynomial ℂ)) * f = c • f
  simp

private theorem polynomial_lift_concreteX :
    polynomialRamifiedLift 1 (concreteX ℂ) =
      ramifiedCoeffGen 1 (LaurentPolynomial.T 1) := by
  change polynomialRamifiedLift 1 (⟨xOp ℂ, xOp_mem_A1⟩ : A1 ℂ) = _
  rw [← polynomialNormalAtom_X_eq, polynomialRamifiedLift_atom]
  simp

private theorem polynomial_lift_concreteY :
    polynomialRamifiedLift 1 (concreteY ℂ) = ramifiedYGen 1 := by
  change polynomialRamifiedLift 1 (⟨yOp ℂ, yOp_mem_A1⟩ : A1 ℂ) = _
  rw [← polynomialNormalAtom_Y_eq, polynomialRamifiedLift_atom]
  simp only [Nat.cast_zero, mul_zero, LaurentPolynomial.T_zero, pow_one]
  have hone : ramifiedCoeffGen 1 (1 : LaurentPolynomial ℂ) = 1 := by
    apply Subtype.ext
    exact ramifiedCoeffMul_one
  rw [hone, one_mul]

/-- Every horizontal constant cut of a polynomial source has a unique
polynomial preimage under the faithful lift. -/
theorem horizontal_cut_has_polynomial_preimage (c : ℂ) (P : A1 ℂ) :
    ∃ R : A1 ℂ, polynomialRamifiedLift 1 R =
      ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 P) := by
  let L := polynomialRamifiedLiftHom 1 (by norm_num)
  let S := ramifiedCutAut 1 (by norm_num) 1 0 c
  have hX : S (L (concreteX ℂ)) = L (concreteX ℂ) := by
    change ramifiedCutAut 1 (by norm_num) 1 0 c
      (polynomialRamifiedLift 1 (concreteX ℂ)) = _
    rw [polynomial_lift_concreteX, ramifiedCutAut_coeff]
    exact polynomial_lift_concreteX.symm
  have hY : S (L (concreteY ℂ)) = L (concreteY ℂ + algebraMap ℂ (A1 ℂ) c) := by
    change ramifiedCutAut 1 (by norm_num) 1 0 c
      (polynomialRamifiedLift 1 (concreteY ℂ)) = _
    rw [polynomial_lift_concreteY, ramifiedCutAut_Y, horizontal_cut_shift_scalar]
    change _ = L (concreteY ℂ + algebraMap ℂ (A1 ℂ) c)
    rw [map_add, AlgHom.commutes]
    change _ = polynomialRamifiedLift 1 (concreteY ℂ) + _
    rw [polynomial_lift_concreteY]
  have hall : ∀ (x : Module.End ℂ ℂ[X]) (hx : x ∈ A1 ℂ),
      ∃ R : A1 ℂ, L R = S (L (⟨x, hx⟩ : A1 ℂ)) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx
        · subst x
          exact ⟨concreteX ℂ, hX.symm⟩
        · subst x
          exact ⟨concreteY ℂ + algebraMap ℂ (A1 ℂ) c, hY.symm⟩
    | algebraMap z =>
        refine ⟨algebraMap ℂ (A1 ℂ) z, ?_⟩
        change L (algebraMap ℂ (A1 ℂ) z) = S (L (algebraMap ℂ (A1 ℂ) z))
        simp
    | add x y hx hy ihx ihy =>
        obtain ⟨R, hR⟩ := ihx
        obtain ⟨T, hT⟩ := ihy
        refine ⟨R+T, ?_⟩
        change L (R+T) = S (L ((⟨x,hx⟩ : A1 ℂ) + ⟨y,hy⟩))
        rw [map_add, map_add, map_add, hR, hT]
    | mul x y hx hy ihx ihy =>
        obtain ⟨R, hR⟩ := ihx
        obtain ⟨T, hT⟩ := ihy
        refine ⟨R*T, ?_⟩
        change L (R*T) = S (L ((⟨x,hx⟩ : A1 ℂ) * ⟨y,hy⟩))
        rw [map_mul, map_mul, map_mul, hR, hT]
  exact hall P.1 P.2

private theorem horizontal_cut_polynomial_hom (c : ℂ) :
    ∃ f : A1 ℂ →ₐ[ℂ] A1 ℂ, ∀ P,
      polynomialRamifiedLift 1 (f P) =
        ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 P) := by
  let L := polynomialRamifiedLiftHom 1 (by norm_num)
  let S := ramifiedCutAut 1 (by norm_num) 1 0 c
  let f : A1 ℂ → A1 ℂ := fun P => Classical.choose (horizontal_cut_has_polynomial_preimage c P)
  have hf : ∀ P, L (f P) = S (L P) :=
    fun P => Classical.choose_spec (horizontal_cut_has_polynomial_preimage c P)
  have hL : Function.Injective L := polynomialRamifiedLiftHom_injective 1 (by norm_num)
  let F : A1 ℂ →ₐ[ℂ] A1 ℂ :=
    { toFun := f
      map_one' := hL (by rw [hf]; simp)
      map_mul' := by
        intro P Q
        apply hL
        rw [hf, map_mul, map_mul, map_mul, hf, hf]
      map_zero' := hL (by rw [hf]; simp)
      map_add' := by
        intro P Q
        apply hL
        rw [hf, map_add, map_add, map_add, hf, hf]
      commutes' := by
        intro z
        apply hL
        rw [hf]
        simp }
  exact ⟨F, hf⟩

private theorem horizontal_cut_inverse_apply (c : ℂ) (T : ramifiedOperatorAlgebra 1) :
    ramifiedCutAut 1 (by norm_num) 1 0 (-c)
      (ramifiedCutAut 1 (by norm_num) 1 0 c T) = T := by
  have h := congrArg (fun F : ramifiedOperatorAlgebra 1 →ₐ[ℂ]
      ramifiedOperatorAlgebra 1 => F T)
    (ramifiedShearHom_inverse_left 1 (by norm_num) (ramifiedCutShift 1 1 0 c))
  simpa [ramifiedCutAut, ramifiedShearAut, ramifiedCutShift, neg_smul] using h

/-- The exact horizontal cut descends to an automorphism of polynomial
A₁. The commuting lift identity fixes it uniquely. -/
theorem horizontal_cut_has_polynomial_automorphism (c : ℂ) :
    ∃ E : A1 ℂ ≃ₐ[ℂ] A1 ℂ, ∀ P,
      polynomialRamifiedLift 1 (E P) =
        ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 P) := by
  obtain ⟨f, hf⟩ := horizontal_cut_polynomial_hom c
  obtain ⟨g, hg⟩ := horizontal_cut_polynomial_hom (-c)
  have hleft : Function.LeftInverse g f := by
    intro P
    apply polynomialRamifiedLift_injective 1 (by norm_num)
    rw [hg, hf, horizontal_cut_inverse_apply]
  have hright : Function.RightInverse g f := by
    intro P
    apply polynomialRamifiedLift_injective 1 (by norm_num)
    rw [hf, hg]
    simpa only [neg_neg] using horizontal_cut_inverse_apply (-c) (polynomialRamifiedLift 1 P)
  exact ⟨{ f with invFun := g, left_inv := hleft, right_inv := hright }, hf⟩

/-- Polynomial recovery of the exact horizontal cut preserves both
commutator one and nongeneration in polynomial A₁. -/
theorem horizontal_cut_recovers_polynomial_counterexample
    (c : ℂ) (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) :
    ∃ R S : A1 ℂ, IsCounterexamplePair R S ∧
      polynomialRamifiedLift 1 R =
        ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 P) ∧
      polynomialRamifiedLift 1 S =
        ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 Q) := by
  obtain ⟨E, hE⟩ := horizontal_cut_has_polynomial_automorphism c
  refine ⟨E P, E Q, ⟨?_, ?_⟩, hE P, hE Q⟩
  · have h := congrArg E.toAlgHom hpair.1
    have hsub := map_sub E.toAlgHom (Q * P) (P * Q)
    rw [hsub, map_mul, map_mul, map_one] at h
    exact h
  · intro hgen
    have hmap := congrArg (fun A : Subalgebra ℂ (A1 ℂ) => A.map E.symm.toAlgHom) hgen
    rw [AlgHom.map_adjoin, Algebra.map_top] at hmap
    have hrange : E.symm.toAlgHom.range = ⊤ :=
      (AlgHom.range_eq_top E.symm.toAlgHom).mpr E.symm.surjective
    apply hpair.2
    simpa [Set.image_insert_eq, Set.image_singleton, hrange] using hmap

end Dixmier.Weyl
