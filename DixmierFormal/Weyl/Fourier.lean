/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Abstract

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Fourier exchange on the first Weyl algebra

The exchange sends `X` to `Y` and `Y` to `-X`, using the finite PBW expansion on `A1 K`.
-/

namespace Dixmier.Weyl

open Polynomial Finset

variable {K : Type*} [Field K] [CharZero K]

noncomputable def fourierGenerators (K : Type*) [Field K] : Fin 2 → A1 K := fun i =>
  if i = 0 then concreteY K else -concreteX K

noncomputable def evaluateFourierFree (K : Type*) [Field K] : WeylFreeAlgebra K →ₐ[K] A1 K :=
  FreeAlgebra.lift K (fourierGenerators K)

private theorem evaluateFourierFree_relation (K : Type*) [Field K] :
    evaluateFourierFree K (weylRelation K) = 0 := by
  simp only [evaluateFourierFree, weylRelation, map_sub, map_mul, map_one,
    FreeAlgebra.lift_ι_apply]
  change (-concreteX K) * concreteY K - concreteY K * (-concreteX K) - 1 = 0
  apply Subtype.ext
  change (-xOp K) * yOp K - yOp K * (-xOp K) - 1 = 0
  apply LinearMap.ext
  intro p
  simp [Module.End.mul_apply, xOp, yOp, Polynomial.derivative_mul]

theorem evaluateFourierFree_zero_on_relationIdeal (K : Type*) [Field K]
    (a : WeylFreeAlgebra K) (ha : a ∈ weylRelationIdeal K) :
    evaluateFourierFree K a = 0 := by
  unfold weylRelationIdeal at ha
  change a ∈ Submodule.span (WeylFreeAlgebra K) (weylRelationMultiples K) at ha
  refine Submodule.span_induction (R := WeylFreeAlgebra K) (s := weylRelationMultiples K)
    (p := fun x _ => evaluateFourierFree K x = 0) ?_ ?_ ?_ ?_ ha
  · intro x hx
    rcases hx with ⟨⟨u, v⟩, rfl⟩
    simp only [map_mul]
    rw [evaluateFourierFree_relation]
    simp
  · simp
  · intro x y hx hy hxe hye
    simp [map_add, hxe, hye]
  · intro c x hx hxe
    change evaluateFourierFree K (c * x) = 0
    rw [map_mul, hxe]
    simp

noncomputable def fourierAbstractToConcrete (K : Type*) [Field K] : AbstractA1 K →ₐ[K] A1 K :=
  Ideal.Quotient.liftₐ (weylRelationIdeal K) (evaluateFourierFree K)
    (evaluateFourierFree_zero_on_relationIdeal K)

private theorem fourierAbstractToConcrete_mk (K : Type*) [Field K]
    (a : WeylFreeAlgebra K) :
    fourierAbstractToConcrete K (Ideal.Quotient.mkₐ K (weylRelationIdeal K) a) =
      evaluateFourierFree K a := by
  change ((Ideal.Quotient.liftₐ (weylRelationIdeal K) (evaluateFourierFree K)
    (evaluateFourierFree_zero_on_relationIdeal K)).comp
      (Ideal.Quotient.mkₐ K (weylRelationIdeal K))) a = evaluateFourierFree K a
  rw [Ideal.Quotient.liftₐ_comp]

private theorem fourierAbstractToConcrete_abstractX (K : Type*) [Field K] :
    fourierAbstractToConcrete K (abstractX K) = concreteY K := by
  rw [abstractX, fourierAbstractToConcrete_mk]
  simp [evaluateFourierFree, fourierGenerators]

private theorem fourierAbstractToConcrete_abstractY (K : Type*) [Field K] :
    fourierAbstractToConcrete K (abstractY K) = -concreteX K := by
  rw [abstractY, fourierAbstractToConcrete_mk]
  simp [evaluateFourierFree, fourierGenerators]

/-- The Fourier assignment extends to an algebra homomorphism on the concrete first Weyl
algebra. This homomorphism will be identified with the frozen PBW definition of `fourier`. -/
noncomputable def fourierAlgHom (K : Type*) [Field K] [CharZero K] : A1 K →ₐ[K] A1 K :=
  (fourierAbstractToConcrete K).comp (abstractToConcreteEquiv K).symm.toAlgHom

theorem fourierAlgHom_concreteX (K : Type*) [Field K] [CharZero K] :
    fourierAlgHom K (concreteX K) = concreteY K := by
  have hx : (abstractToConcreteEquiv K).symm (concreteX K) = abstractX K := by
    apply (abstractToConcreteEquiv K).injective
    rw [AlgEquiv.apply_symm_apply]
    change concreteX K = abstractToConcrete K (abstractX K)
    exact (abstractToConcrete_abstractX K).symm
  simp [fourierAlgHom, hx, fourierAbstractToConcrete_abstractX]

theorem fourierAlgHom_concreteY (K : Type*) [Field K] [CharZero K] :
    fourierAlgHom K (concreteY K) = -concreteX K := by
  have hy : (abstractToConcreteEquiv K).symm (concreteY K) = abstractY K := by
    apply (abstractToConcreteEquiv K).injective
    rw [AlgEquiv.apply_symm_apply]
    change concreteY K = abstractToConcrete K (abstractY K)
    exact (abstractToConcrete_abstractY K).symm
  simp [fourierAlgHom, hy, fourierAbstractToConcrete_abstractY]

private theorem fourier_neg_concreteX_pow (K : Type*) [Field K] (j : ℕ) :
    (-concreteX K) ^ j = (-1 : K) ^ j • (concreteX K) ^ j := by
  calc
    (-concreteX K) ^ j = ((-1 : K) • concreteX K) ^ j :=
      congrArg (fun z : A1 K => z ^ j) (neg_one_smul K (concreteX K)).symm
    _ = _ := smul_pow _ _ _

theorem fourierAlgHom_normalMonomial (K : Type*) [Field K] [CharZero K]
    (i j : ℕ) :
    fourierAlgHom K ((concreteX K) ^ i * (concreteY K) ^ j) =
      (-1 : K) ^ j • ((concreteY K) ^ i * (concreteX K) ^ j) := by
  rw [map_mul, map_pow, map_pow, fourierAlgHom_concreteX,
    fourierAlgHom_concreteY, fourier_neg_concreteX_pow]
  exact mul_smul_comm _ _ _

private theorem fourierAlgHom_map_neg (K : Type*) [Field K] [CharZero K]
    (T : A1 K) : fourierAlgHom K (-T) = -(fourierAlgHom K T) := by
  exact map_neg (fourierAlgHom K) T

omit [CharZero K] in
private theorem fourier_neg_neg (T : A1 K) : -(-T) = T := by
  apply Subtype.ext
  simp only [Subalgebra.coe_neg, neg_neg]

/-- The Fourier exchange of an element of the Weyl algebra remains in the Weyl algebra. -/
theorem fourier_mem_A1 (T : A1 K) : fourier (T : Module.End K K[X]) ∈ A1 K := by
  classical
  obtain ⟨c, hc⟩ := A1_exists_finiteNormalOrderedExpansion T
  have hcoeff : ∀ p : ℕ × ℕ,
      pbwCoeff (T : Module.End K K[X]) p.1 p.2 = c p := by
    intro p
    rw [← hc]
    exact pbwCoeff_finsuppNormalOrderedSum c p.1 p.2
  have hsub : Function.support (fun p : ℕ × ℕ =>
      pbwCoeff (T : Module.End K K[X]) p.1 p.2 •
        ((-1 : K) ^ p.2 • (yOp K ^ p.1 * xOp K ^ p.2))) ⊆ c.support := by
    intro p hp
    by_contra hnot
    have hz : c p = 0 := by simpa using hnot
    apply hp
    simp [hcoeff p, hz]
  unfold fourier
  rw [finsum_eq_sum_of_support_subset _ hsub]
  apply sum_mem
  intro p hp
  have hx : xOp K ∈ A1 K := xOp_mem_A1
  have hy : yOp K ∈ A1 K := yOp_mem_A1
  have hprod := mul_mem (pow_mem hy p.1) (pow_mem hx p.2)
  exact (A1 K).smul_mem ((A1 K).smul_mem hprod ((-1 : K) ^ p.2))
    (pbwCoeff (T : Module.End K K[X]) p.1 p.2)

/-- On any finite PBW expansion, the Fourier exchange is the finite sum obtained by sending
`X^i Y^j` to `(-1)^j Y^i X^j`. -/
theorem fourier_eq_finitePBWSum (T : A1 K) (c : (ℕ × ℕ) →₀ K)
    (hc : c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
      (T : Module.End K K[X])) :
    fourier (T : Module.End K K[X]) =
      c.sum (fun p a => a • ((-1 : K) ^ p.2 • (yOp K ^ p.1 * xOp K ^ p.2))) := by
  classical
  have hcoeff : ∀ p : ℕ × ℕ,
      pbwCoeff (T : Module.End K K[X]) p.1 p.2 = c p := by
    intro p
    rw [← hc]
    exact pbwCoeff_finsuppNormalOrderedSum c p.1 p.2
  have hsub : Function.support (fun p : ℕ × ℕ =>
      pbwCoeff (T : Module.End K K[X]) p.1 p.2 •
        ((-1 : K) ^ p.2 • (yOp K ^ p.1 * xOp K ^ p.2))) ⊆ c.support := by
    intro p hp
    by_contra hnot
    have hz : c p = 0 := by simpa using hnot
    apply hp
    simp [hcoeff p, hz]
  unfold fourier
  rw [finsum_eq_sum_of_support_subset _ hsub]
  rw [Finsupp.sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hcoeff p]

/-- The frozen PBW definition of Fourier is exactly the algebra homomorphism constructed
from the Weyl relation. -/
theorem fourier_eq_algHom (T : A1 K) :
    fourier (T : Module.End K K[X]) =
      ((fourierAlgHom K T : A1 K) : Module.End K K[X]) := by
  classical
  obtain ⟨c, hc⟩ := A1_exists_finiteNormalOrderedExpansion T
  have hcA : c.sum (fun p a => a • ((concreteX K) ^ p.1 * (concreteY K) ^ p.2)) = T := by
    apply Subtype.ext
    simpa [Finsupp.sum, concreteX, concreteY, normalOrderedMonomial] using hc
  have hmap : fourierAlgHom K T =
      c.sum (fun p a => a • ((-1 : K) ^ p.2 •
        ((concreteY K) ^ p.1 * (concreteX K) ^ p.2))) := by
    rw [← hcA]
    simp only [Finsupp.sum, map_sum, map_smul, fourierAlgHom_normalMonomial]
  calc
    fourier (T : Module.End K K[X]) =
        c.sum (fun p a => a • ((-1 : K) ^ p.2 •
          (yOp K ^ p.1 * xOp K ^ p.2))) := fourier_eq_finitePBWSum T c hc
    _ = ((c.sum (fun p a => a • ((-1 : K) ^ p.2 •
          ((concreteY K) ^ p.1 * (concreteX K) ^ p.2))) : A1 K) :
            Module.End K K[X]) := by
      simp [Finsupp.sum, concreteX, concreteY]
    _ = ((fourierAlgHom K T : A1 K) : Module.End K K[X]) :=
      congrArg Subtype.val hmap.symm

/-- Fourier preserves multiplication on the Weyl algebra, for the frozen operator definition. -/
theorem fourier_mul_A1 (P Q : A1 K) :
    fourier ((P : Module.End K K[X]) * (Q : Module.End K K[X])) =
      fourier (P : Module.End K K[X]) * fourier (Q : Module.End K K[X]) := by
  change fourier ((P*Q : A1 K) : Module.End K K[X]) = _
  rw [fourier_eq_algHom, fourier_eq_algHom P, fourier_eq_algHom Q]
  exact congrArg Subtype.val ((fourierAlgHom K).map_mul P Q)

/-- Applying the Fourier algebra homomorphism four times is the identity. -/
theorem fourierAlgHom_fourth (T : A1 K) :
    fourierAlgHom K (fourierAlgHom K (fourierAlgHom K (fourierAlgHom K T))) = T := by
  let F := fourierAlgHom K
  have hX : F (F (F (F (concreteX K)))) = concreteX K := by
    simp only [F, fourierAlgHom_concreteX, fourierAlgHom_concreteY,
      fourierAlgHom_map_neg, fourier_neg_neg]
  have hY : F (F (F (F (concreteY K)))) = concreteY K := by
    simp only [F, fourierAlgHom_concreteX, fourierAlgHom_concreteY,
      fourierAlgHom_map_neg, fourier_neg_neg]
  have hall : ∀ (x : Module.End K K[X]) (hx : x ∈ A1 K),
      F (F (F (F (⟨x, hx⟩ : A1 K)))) = (⟨x, hx⟩ : A1 K) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx
        · subst x
          exact hX
        · subst x
          exact hY
    | algebraMap c =>
        change F (F (F (F (algebraMap K (A1 K) c)))) = algebraMap K (A1 K) c
        simp [F]
    | add x y hx hy ihx ihy =>
        change F (F (F (F ((⟨x, hx⟩ : A1 K) + ⟨y, hy⟩)))) =
          (⟨x, hx⟩ : A1 K) + ⟨y, hy⟩
        simp only [map_add, ihx, ihy]
    | mul x y hx hy ihx ihy =>
        change F (F (F (F ((⟨x, hx⟩ : A1 K) * ⟨y, hy⟩)))) =
          (⟨x, hx⟩ : A1 K) * ⟨y, hy⟩
        simp only [map_mul, ihx, ihy]
  exact hall T.1 T.property

/-- The Fourier exchange is an algebra automorphism of the first Weyl algebra. -/
noncomputable def fourierAlgEquiv (K : Type*) [Field K] [CharZero K] : A1 K ≃ₐ[K] A1 K :=
  AlgEquiv.ofBijective (fourierAlgHom K) (by
    constructor
    · intro P Q h
      have h' := congrArg (fun T : A1 K =>
        fourierAlgHom K (fourierAlgHom K (fourierAlgHom K T))) h
      simpa only [fourierAlgHom_fourth] using h'
    · intro T
      exact ⟨fourierAlgHom K (fourierAlgHom K (fourierAlgHom K T)),
        fourierAlgHom_fourth T⟩)

/-- Fourier is additive on the Weyl algebra. -/
theorem fourier_add_A1 (P Q : A1 K) :
    fourier ((P : Module.End K K[X]) + (Q : Module.End K K[X])) =
      fourier (P : Module.End K K[X]) + fourier (Q : Module.End K K[X]) := by
  change fourier ((P+Q : A1 K) : Module.End K K[X]) = _
  rw [fourier_eq_algHom, fourier_eq_algHom P, fourier_eq_algHom Q]
  exact congrArg Subtype.val ((fourierAlgHom K).map_add P Q)

/-- The PBW symbol of a normal-ordered monomial is its single commutative monomial. -/
theorem symbol_concreteNormalMonomial (i j : ℕ) :
    symbol (((concreteX K) ^ i * (concreteY K) ^ j : A1 K) : Module.End K K[X]) =
      MvPolynomial.monomial (expo i j) (1 : K) := by
  apply MvPolynomial.ext
  intro e
  obtain ⟨⟨a,b⟩, rfl⟩ := expo_surjective e
  rw [symbol_coeff_pbwCoeff, MvPolynomial.coeff_monomial]
  have heq : expo a b = expo i j ↔ a = i ∧ b = j := by
    constructor
    · intro h
      have hp : (a,b) = (i,j) := expo_injective h
      exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
    · rintro ⟨rfl,rfl⟩
      rfl
  change pbwCoeff (xOp K ^ i * yOp K ^ j) a b = _
  rw [pbwCoeff_normalOrdered_monomial]
  by_cases hpair : a = i ∧ b = j
  · rcases hpair with ⟨rfl, rfl⟩
    simp
  · have hnot : expo i j ≠ expo a b := by
      intro h
      exact hpair (heq.mp h.symm)
    simp [hpair, hnot]

/-- The PBW symbol as a linear map on the finite Weyl operator algebra. -/
noncomputable def symbolLinearMap : A1 K →ₗ[K] MvPolynomial (Fin 2) K where
  toFun T := symbol (T : Module.End K K[X])
  map_add' P Q := symbol_add P Q
  map_smul' a P := symbol_smul a P

/-- Normal ordering an antinormal monomial gives only PBW monomials of the same grade. -/
theorem symbol_concreteAntiNormalMonomial (i j : ℕ) :
    symbol (((concreteY K) ^ i * (concreteX K) ^ j : A1 K) : Module.End K K[X]) =
      ∑ k ∈ Finset.range (min j i).succ,
        MvPolynomial.monomial (expo (j-k) (i-k))
          (i.choose k * j.descFactorial k : K) := by
  have hnormal : (concreteY K) ^ i * (concreteX K) ^ j =
      ∑ k ∈ Finset.range (min j i).succ,
        (i.choose k * j.descFactorial k : K) •
          ((concreteX K) ^ (j-k) * (concreteY K) ^ (i-k)) := by
    apply Subtype.ext
    simpa [concreteX, concreteY] using (yOp_pow_mul_xOp_pow (K := K) j i)
  have h := congrArg (symbolLinearMap (K := K)) hnormal
  change symbol (((concreteY K) ^ i * (concreteX K) ^ j : A1 K) :
      Module.End K K[X]) = _ at h
  rw [map_sum] at h
  simp only [map_smul] at h
  change symbol (((concreteY K) ^ i * (concreteX K) ^ j : A1 K) :
      Module.End K K[X]) =
    ∑ k ∈ Finset.range (min j i).succ,
      (i.choose k * j.descFactorial k : K) •
        symbol (((concreteX K) ^ (j-k) * (concreteY K) ^ (i-k) : A1 K) :
          Module.End K K[X]) at h
  simpa only [symbol_concreteNormalMonomial, MvPolynomial.smul_monomial,
    smul_eq_mul, mul_one] using h

/-- Every PBW term of `Y^i X^j` has grade `j-i`; normal ordering cannot change that grade. -/
theorem grade_symbol_concreteAntiNormalMonomial (i j : ℕ)
    (e : Fin 2 →₀ ℕ)
    (he : e ∈ (symbol (((concreteY K) ^ i * (concreteX K) ^ j : A1 K) :
      Module.End K K[X])).support) :
    grade e = (j : ℤ) - (i : ℤ) := by
  classical
  rw [symbol_concreteAntiNormalMonomial] at he
  have he' := MvPolynomial.support_sum he
  simp only [Finset.mem_biUnion] at he'
  rcases he' with ⟨k, hk, hmono⟩
  have hcoeff := MvPolynomial.mem_support_iff.mp hmono
  have hexp : e = expo (j-k) (i-k) := by
    by_contra hne
    rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)] at hcoeff
    exact hcoeff rfl
  subst e
  have hkmin : k ≤ min j i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hkj : k ≤ j := hkmin.trans (min_le_left _ _)
  have hki : k ≤ i := hkmin.trans (min_le_right _ _)
  simp only [grade, expo, Finsupp.add_apply, Finsupp.single_apply]
  simp [Nat.cast_sub hkj, Nat.cast_sub hki]

/-- The finite PBW symbol expansion of the Fourier image. -/
theorem symbol_fourierAlgHom_eq_sum (T : A1 K) (c : (ℕ × ℕ) →₀ K)
    (hc : c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
      (T : Module.End K K[X])) :
    symbol ((fourierAlgHom K T : A1 K) : Module.End K K[X]) =
      ∑ p ∈ c.support, c p • ((-1 : K) ^ p.2 •
        symbol (((concreteY K) ^ p.1 * (concreteX K) ^ p.2 : A1 K) :
          Module.End K K[X])) := by
  classical
  have hcA : c.sum (fun p a => a • ((concreteX K) ^ p.1 * (concreteY K) ^ p.2)) = T := by
    apply Subtype.ext
    simpa [Finsupp.sum, concreteX, concreteY, normalOrderedMonomial] using hc
  calc
    symbol ((fourierAlgHom K T : A1 K) : Module.End K K[X]) =
        symbol ((fourierAlgHom K
          (c.sum (fun p a => a • ((concreteX K) ^ p.1 * (concreteY K) ^ p.2))) : A1 K) :
            Module.End K K[X]) := by rw [hcA]
    _ = ∑ p ∈ c.support, c p • ((-1 : K) ^ p.2 •
        symbol (((concreteY K) ^ p.1 * (concreteX K) ^ p.2 : A1 K) :
          Module.End K K[X])) := by
      change symbolLinearMap (fourierAlgHom K
        (c.sum (fun p a => a • ((concreteX K) ^ p.1 * (concreteY K) ^ p.2)))) = _
      rw [Finsupp.sum, map_sum]
      simp only [map_smul, fourierAlgHom_normalMonomial]
      rw [map_sum]
      simp only [map_smul]
      rfl

/-- Fourier reverses every occupied PBW grade; this inclusion does not yet assert that
different contributions within one grade cannot cancel. -/
theorem fourier_gradeSupport_subset (T : A1 K) :
    (symbol ((fourierAlgHom K T : A1 K) : Module.End K K[X])).support.image grade ⊆
      ((symbol (T : Module.End K K[X])).support.image grade).image (fun z : ℤ => -z) := by
  classical
  obtain ⟨c, hc, hsupport⟩ := symbol_support_eq_pbwCoefficientImage T
  intro g hg
  rcases Finset.mem_image.mp hg with ⟨e, he, rfl⟩
  rw [symbol_fourierAlgHom_eq_sum T c hc] at he
  have he' := MvPolynomial.support_sum he
  simp only [Finset.mem_biUnion] at he'
  rcases he' with ⟨p, hp, hterm⟩
  have hanti : e ∈ (symbol (((concreteY K) ^ p.1 * (concreteX K) ^ p.2 : A1 K) :
      Module.End K K[X])).support := by
    have hcoeff := MvPolynomial.mem_support_iff.mp hterm
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_smul] at hcoeff
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    rw [hz] at hcoeff
    simp at hcoeff
  have hgrade := grade_symbol_concreteAntiNormalMonomial p.1 p.2 e hanti
  have horig : expo p.1 p.2 ∈ (symbol (T : Module.End K K[X])).support := by
    rw [hsupport]
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hnegg : grade e = -grade (expo p.1 p.2) := by
    rw [hgrade]
    simp [grade, expo]
  apply Finset.mem_image.mpr
  refine ⟨grade (expo p.1 p.2), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨expo p.1 p.2, horig, rfl⟩
  · exact hnegg.symm

private theorem mass_fourierAlgHom_le (T : A1 K) :
    mass ((fourierAlgHom K T : A1 K) : Module.End K K[X]) ≤
      mass (T : Module.End K K[X]) := by
  unfold mass
  calc
    ((symbol ((fourierAlgHom K T : A1 K) : Module.End K K[X])).support.image grade).card ≤
        (((symbol (T : Module.End K K[X])).support.image grade).image
          (fun z : ℤ => -z)).card :=
      Finset.card_le_card (fourier_gradeSupport_subset T)
    _ ≤ ((symbol (T : Module.End K K[X])).support.image grade).card :=
      Finset.card_image_le

/-- The Fourier algebra automorphism preserves the paper's mass invariant exactly. -/
theorem mass_fourierAlgHom (T : A1 K) :
    mass ((fourierAlgHom K T : A1 K) : Module.End K K[X]) =
      mass (T : Module.End K K[X]) := by
  let F := fourierAlgHom K
  have h1 := mass_fourierAlgHom_le T
  have h2 := mass_fourierAlgHom_le (F T)
  have h3 := mass_fourierAlgHom_le (F (F T))
  have h4 := mass_fourierAlgHom_le (F (F (F T)))
  have h4eq : mass ((F (F (F (F T))) : A1 K) : Module.End K K[X]) =
      mass (T : Module.End K K[X]) := by
    rw [fourierAlgHom_fourth]
  apply le_antisymm h1
  calc
    mass (T : Module.End K K[X]) =
        mass ((F (F (F (F T))) : A1 K) : Module.End K K[X]) := h4eq.symm
    _ ≤ mass ((F (F (F T)) : A1 K) : Module.End K K[X]) := h4
    _ ≤ mass ((F (F T) : A1 K) : Module.End K K[X]) := h3
    _ ≤ mass ((F T : A1 K) : Module.End K K[X]) := h2

/-- The frozen operator-level Fourier map preserves mass on `A1 K`. -/
theorem mass_fourier_A1 (T : A1 K) :
    mass (fourier (T : Module.End K K[X])) = mass (T : Module.End K K[X]) := by
  rw [fourier_eq_algHom]
  exact mass_fourierAlgHom T

omit [CharZero K] in
private theorem adjoin_pair_eq_top_of_algEquiv
    (E : A1 K ≃ₐ[K] A1 K) (P Q : A1 K)
    (h : Algebra.adjoin K ({P,Q} : Set (A1 K)) = ⊤) :
    Algebra.adjoin K ({E P,E Q} : Set (A1 K)) = ⊤ := by
  have hmap := congrArg
    (fun S : Subalgebra K (A1 K) => S.map E.toAlgHom) h
  rw [AlgHom.map_adjoin, Algebra.map_top] at hmap
  have hrange : E.toAlgHom.range = ⊤ :=
    (AlgHom.range_eq_top E.toAlgHom).mpr E.surjective
  simpa [Set.image_insert_eq, Set.image_singleton, hrange] using hmap

/-- Generation by a pair is invariant under the Fourier automorphism. -/
theorem adjoin_fourier_eq_top_iff (P Q : A1 K) :
    Algebra.adjoin K ({fourierAlgHom K P, fourierAlgHom K Q} : Set (A1 K)) = ⊤ ↔
      Algebra.adjoin K ({P,Q} : Set (A1 K)) = ⊤ := by
  let E := fourierAlgEquiv K
  constructor
  · intro h
    have h' := adjoin_pair_eq_top_of_algEquiv E.symm (E P) (E Q) h
    simpa [E] using h'
  · intro h
    exact adjoin_pair_eq_top_of_algEquiv E P Q h

/-- Fourier carries a counterexample pair to another counterexample pair, preserving the exact
commutator and nongeneration conditions. -/
theorem isCounterexamplePair_fourier (P Q : A1 ℂ)
    (h : IsCounterexamplePair P Q) :
    IsCounterexamplePair (fourierAlgHom ℂ P) (fourierAlgHom ℂ Q) := by
  rcases h with ⟨hcomm, hnonGen⟩
  constructor
  · have hmap := congrArg (fourierAlgHom ℂ) hcomm
    have hsub := map_sub (fourierAlgHom ℂ) (Q*P) (P*Q)
    rw [hsub, map_mul, map_mul] at hmap
    rw [map_one] at hmap
    exact hmap
  · intro hgen
    exact hnonGen ((adjoin_fourier_eq_top_iff P Q).mp hgen)

/-- The directional range used for a strict crossing in the GGV case split satisfies the
positive-weight-sum hypothesis of the symbol calculus. -/
theorem positive_weight_sum_of_crossing_range {ρ σ : ℤ}
    (hσ : -ρ < σ) : 0 < ρ + σ := by
  omega

end Dixmier.Weyl
