/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.FieldBaseChange
public import Mathlib.Algebra.CharP.Algebra

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

namespace Dixmier.Weyl
open Polynomial
noncomputable section
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [CharZero K]

theorem concreteBaseChange_normalMonomial (i j : ℕ) :
    concreteBaseChange K L (concreteX K ^ i * concreteY K ^ j) =
      concreteX L ^ i * concreteY L ^ j := by
  rw [map_mul, map_pow, map_pow, concreteBaseChange_x, concreteBaseChange_y]

theorem concreteBaseChange_finsuppSum (c : (ℕ × ℕ) →₀ K) :
    concreteBaseChange K L
      (c.sum (fun p a => a • (concreteX K ^ p.1 * concreteY K ^ p.2))) =
    c.sum (fun p a => a • (concreteX L ^ p.1 * concreteY L ^ p.2)) := by
  classical
  simp only [Finsupp.sum]
  rw [map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [concreteBaseChange_normalMonomial]

theorem concreteNormalSum_val (c : (ℕ × ℕ) →₀ K) :
    ((c.sum (fun p a => a • (concreteX K ^ p.1 * concreteY K ^ p.2)) : A1 K) :
      Module.End K K[X]) =
      c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) := by
  classical
  simp only [Finsupp.sum]
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only [SetLike.val_smul]
  apply Finset.sum_congr rfl
  intro p hp
  rfl

noncomputable def extendPBWCoeffs (c : (ℕ × ℕ) →₀ K) : (ℕ × ℕ) →₀ L :=
  Finsupp.mapRange (algebraMap K L) (map_zero _) c

theorem extendPBWCoeffs_support (c : (ℕ × ℕ) →₀ K) :
    (extendPBWCoeffs K L c).support = c.support := by
  exact Finsupp.support_mapRange_of_injective (map_zero (algebraMap K L)) c
    (algebraMap K L).injective

theorem extendPBWCoeffs_sum (c : (ℕ × ℕ) →₀ K) :
    (extendPBWCoeffs K L c).sum
      (fun p a => a • (concreteX L ^ p.1 * concreteY L ^ p.2)) =
    c.sum (fun p a => a • (concreteX L ^ p.1 * concreteY L ^ p.2)) := by
  classical
  simp only [Finsupp.sum, extendPBWCoeffs_support]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [extendPBWCoeffs, Finsupp.mapRange_apply]
  rw [Algebra.smul_def, Algebra.smul_def]
  rw [← IsScalarTower.algebraMap_apply K L (A1 L) (c p)]

theorem mass_eq_of_normalExpansion (T : A1 K) (c : (ℕ × ℕ) →₀ K)
    (hc : c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
      (T : Module.End K K[X])) :
    mass (T : Module.End K K[X]) =
      (c.support.image (fun p => (p.1 : ℤ) - (p.2 : ℤ))).card := by
  obtain ⟨d, hd, hm⟩ := mass_eq_pbwExpansionGradeSupport T
  have hdc : d = c := A1_finiteNormalOrderedExpansion_unique T d c hd hc
  simpa [hdc] using hm

theorem concreteBaseChange_mass (T : A1 K) :
    mass ((concreteBaseChange K L T : A1 L) : Module.End L L[X]) =
      mass (T : Module.End K K[X]) := by
  letI : CharZero L := charZero_of_injective_algebraMap
    (algebraMap K L).injective
  obtain ⟨c, hc⟩ := A1_exists_finiteNormalOrderedExpansion T
  let d := extendPBWCoeffs K L c
  have hT : T = c.sum (fun p a => a • (concreteX K ^ p.1 * concreteY K ^ p.2)) := by
    apply Subtype.ext
    rw [concreteNormalSum_val]
    exact hc.symm
  have hmapT : concreteBaseChange K L T =
      d.sum (fun p a => a • (concreteX L ^ p.1 * concreteY L ^ p.2)) := by
    rw [hT, concreteBaseChange_finsuppSum]
    exact (extendPBWCoeffs_sum K L c).symm
  have hvalL : d.sum (fun p a => a • normalOrderedMonomial (K := L) p.1 p.2) =
      ((concreteBaseChange K L T : A1 L) : Module.End L L[X]) := by
    rw [hmapT]
    exact (concreteNormalSum_val L d).symm
  rw [mass_eq_of_normalExpansion L _ d hvalL,
      mass_eq_of_normalExpansion K T c hc]
  rw [extendPBWCoeffs_support]

theorem concreteBaseChange_zero_imp_zero (T : A1 K)
    (hT : concreteBaseChange K L T = 0) : T = 0 := by
  letI : CharZero L := charZero_of_injective_algebraMap
    (algebraMap K L).injective
  obtain ⟨c, hc⟩ := A1_exists_finiteNormalOrderedExpansion T
  let d := extendPBWCoeffs K L c
  have hexp : T = c.sum (fun p a => a • (concreteX K ^ p.1 * concreteY K ^ p.2)) := by
    apply Subtype.ext
    rw [concreteNormalSum_val]
    exact hc.symm
  have hsum : d.sum (fun p a => a • (concreteX L ^ p.1 * concreteY L ^ p.2)) = 0 := by
    rw [extendPBWCoeffs_sum, ← concreteBaseChange_finsuppSum, ← hexp]
    exact hT
  have hd0 : d = 0 := by
    apply A1_finiteNormalOrderedExpansion_unique (0 : A1 L) d 0
    · rw [← concreteNormalSum_val]
      exact congrArg Subtype.val hsum
    · simp
  have hc0 : c = 0 := by
    ext p
    have hd := congrArg (fun z : (ℕ × ℕ) →₀ L => z p) hd0
    simpa [d, extendPBWCoeffs] using
      (algebraMap K L).injective (by simpa [d, extendPBWCoeffs] using hd)
  rw [hexp, hc0]
  simp

theorem concreteBaseChange_injective : Function.Injective (concreteBaseChange K L) := by
  intro P Q h
  apply sub_eq_zero.mp
  apply concreteBaseChange_zero_imp_zero K L
  simpa only [map_sub] using (sub_eq_zero.mpr h)

/-- Each PBW coefficient of a Weyl operator is carried to the corresponding coefficient
under extension of its coefficient field. -/
theorem pbwCoeff_concreteBaseChange (T : A1 K) (i j : ℕ) :
    pbwCoeff ((concreteBaseChange K L T : A1 L) : Module.End L L[X]) i j =
      algebraMap K L (pbwCoeff (T : Module.End K K[X]) i j) := by
  letI : CharZero L := charZero_of_injective_algebraMap
    (algebraMap K L).injective
  obtain ⟨c, hc⟩ := A1_exists_finiteNormalOrderedExpansion T
  have hT : T = c.sum (fun p a => a • (concreteX K ^ p.1 * concreteY K ^ p.2)) := by
    apply Subtype.ext
    rw [concreteNormalSum_val]
    exact hc.symm
  have hLT : ((concreteBaseChange K L T : A1 L) : Module.End L L[X]) =
      (extendPBWCoeffs K L c).sum
        (fun p a => a • normalOrderedMonomial (K := L) p.1 p.2) := by
    rw [hT, concreteBaseChange_finsuppSum]
    rw [← extendPBWCoeffs_sum]
    exact concreteNormalSum_val L (extendPBWCoeffs K L c)
  rw [hLT, pbwCoeff_finsuppNormalOrderedSum, ← hc,
    pbwCoeff_finsuppNormalOrderedSum]
  rfl

end
end Dixmier.Weyl
