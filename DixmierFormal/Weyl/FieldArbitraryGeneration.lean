/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.FieldCountability
public import DixmierFormal.Weyl.FieldBaseChangePBW
public import DixmierFormal.Weyl.FieldGenerationDescent
public import DixmierFormal.Weyl.ComplexGeneration

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

namespace Dixmier.Weyl
open Polynomial
noncomputable section

/-!
# Arbitrary characteristic-zero coefficient fields

The paper's complex generation theorem transfers to every characteristic-zero
field by first restricting a pair to a countable rational coefficient field,
embedding that field into `ℂ`, and descending generation back. The theorem at
the end is conditional only on the explicit `GGVInputs` interface used by the
complex theorem.
-/

section PBW
variable (K : Type*) [Field K]

def pbwOperator (c : (ℕ × ℕ) →₀ K) : A1 K :=
  c.sum (fun p a => a • (concreteX K ^ p.1 * concreteY K ^ p.2))

private theorem pbwOperator_normalExpansion [CharZero K] (c : (ℕ × ℕ) →₀ K) :
    ((pbwOperator K c : A1 K) : Module.End K K[X]) =
      c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) := by
  exact concreteNormalSum_val K c

end PBW

variable {K L : Type*} [Field K] [Field L]

variable [CharZero K]

def subfieldCoeffs (E : Subfield K) (c : (ℕ × ℕ) →₀ K)
    (hc : ∀ p ∈ c.support, c p ∈ E) : (ℕ × ℕ) →₀ E :=
  Finsupp.onFinset c.support
    (fun p => if hp : p ∈ c.support then ⟨c p, hc p hp⟩ else 0)
    (by
      intro p hp
      by_contra h
      simp [h] at hp)

omit [CharZero K] in
private theorem extend_subfieldCoeffs {E : Subfield K} (c : (ℕ × ℕ) →₀ K)
    (hc : ∀ p ∈ c.support, c p ∈ E) :
    extendPBWCoeffs E K (subfieldCoeffs E c hc) = c := by
  classical
  ext p
  by_cases hp : p ∈ c.support
  · have hcp : c p ≠ 0 := Finsupp.mem_support_iff.mp hp
    simp only [extendPBWCoeffs, Finsupp.mapRange_apply, subfieldCoeffs,
      Finsupp.onFinset_apply, dif_pos hp]
    rfl
  · have hc0 : c p = 0 := by
      by_contra hne
      exact hp (Finsupp.mem_support_iff.mpr hne)
    simp [extendPBWCoeffs, subfieldCoeffs, Finsupp.mapRange_apply, hc0]

private theorem pbwOperator_baseChange [Algebra K L]
    (c : (ℕ × ℕ) →₀ K) :
    concreteBaseChange K L (pbwOperator K c) = pbwOperator L (extendPBWCoeffs K L c) := by
  change concreteBaseChange K L
    (c.sum (fun p a => a • (concreteX K ^ p.1 * concreteY K ^ p.2))) =
      (extendPBWCoeffs K L c).sum
        (fun p a => a • (concreteX L ^ p.1 * concreteY L ^ p.2))
  rw [concreteBaseChange_finsuppSum]
  exact (extendPBWCoeffs_sum K L c).symm

private theorem exists_pair_subfield_realization {K : Type*} [Field K] [CharZero K]
    (P Q : A1 K) :
    ∃ (E : Subfield K) (PE QE : A1 E),
      Countable E ∧
      ((concreteBaseChange E K PE : A1 K) = P) ∧
      ((concreteBaseChange E K QE : A1 K) = Q) := by
  obtain ⟨E, c, d, hcount, hc, hd, hce, hde⟩ :=
    exists_countable_ratSubfield_for_pair P Q
  let cE := subfieldCoeffs E c hce
  let dE := subfieldCoeffs E d hde
  let PE : A1 E := pbwOperator E cE
  let QE : A1 E := pbwOperator E dE
  have hpK : pbwOperator K c = P := by
    apply Subtype.ext
    rw [pbwOperator_normalExpansion]
    exact hc
  have hqK : pbwOperator K d = Q := by
    apply Subtype.ext
    rw [pbwOperator_normalExpansion]
    exact hd
  refine ⟨E, PE, QE, hcount, ?_, ?_⟩
  · change concreteBaseChange E K (pbwOperator E cE) = P
    rw [pbwOperator_baseChange, extend_subfieldCoeffs, hpK]
  · change concreteBaseChange E K (pbwOperator E dE) = Q
    rw [pbwOperator_baseChange, extend_subfieldCoeffs, hqK]

private theorem pair_generation_ascends {E K : Type*} [Field E] [Field K] [CharZero E]
    [Algebra E K] (PE QE : A1 E) (P Q : A1 K)
    (hPE : concreteBaseChange E K PE = P)
    (hQE : concreteBaseChange E K QE = Q)
    (hgen : Algebra.adjoin E {PE, QE} = ⊤) :
    Algebra.adjoin K {P, Q} = ⊤ := by
  let f := concreteBaseChange E K
  let B := Algebra.adjoin K {P, Q}
  have map_mem : ∀ z : A1 E, z ∈ Algebra.adjoin E {PE, QE} → f z ∈ B := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
        rcases hz with rfl | rfl
        · rw [hPE]
          exact Algebra.subset_adjoin (Set.mem_insert _ _)
        · rw [hQE]
          exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)
    | algebraMap r =>
        have hscalar : f (algebraMap E (A1 E) r) =
            algebraMap K (A1 K) (algebraMap E K r) := by
          calc
            f (algebraMap E (A1 E) r) = algebraMap E (A1 K) r := by simp [f]
            _ = algebraMap K (A1 K) (algebraMap E K r) := by
              rw [← IsScalarTower.algebraMap_apply E K (A1 K) r]
        rw [hscalar]
        exact B.algebraMap_mem _
    | add x y hx hy ihx ihy => simpa only [map_add] using B.add_mem ihx ihy
    | mul x y hx hy ihx ihy => simpa only [map_mul] using B.mul_mem ihx ihy
  have hXE : concreteX E ∈ Algebra.adjoin E {PE, QE} := by
    rw [hgen]
    trivial
  have hYE : concreteY E ∈ Algebra.adjoin E {PE, QE} := by
    rw [hgen]
    trivial
  have hXK : concreteX K ∈ B := by
    rw [← concreteBaseChange_x E K]
    exact map_mem (concreteX E) hXE
  have hYK : concreteY K ∈ B := by
    rw [← concreteBaseChange_y E K]
    exact map_mem (concreteY E) hYE
  rw [eq_top_iff]
  intro T _
  have key : ∀ S ∈ A1 K, ∀ hS : S ∈ A1 K, (⟨S, hS⟩ : A1 K) ∈ B := by
    intro S hS
    refine Algebra.adjoin_induction (p := fun S _ => ∀ hS : S ∈ A1 K,
      (⟨S, hS⟩ : A1 K) ∈ B) ?_ ?_ ?_ ?_ hS
    · intro x hx hxA
      rcases hx with rfl | rfl
      · change concreteX K ∈ B
        exact hXK
      · change concreteY K ∈ B
        exact hYK
    · intro r hr
      exact B.algebraMap_mem r
    · intro x y hx hy ihx ihy hxy
      exact B.add_mem (ihx hx) (ihy hy)
    · intro x y hx hy ihx ihy hxy
      exact B.mul_mem (ihx hx) (ihy hy)
  exact key T.1 T.2 T.2

theorem massSixGeneration_of_GGV (H : GGVInputs) : Statement.MassSixGeneration := by
  intro K _ _ P Q hcomm hmass
  obtain ⟨E, PE, QE, hcount, hPE, hQE⟩ :=
    exists_pair_subfield_realization P Q
  have hcommOp :
      (Q.1 * P.1 - P.1 * Q.1 : Module.End K K[X]) = 1 := by
    simpa using congrArg (fun T : A1 K => (T : Module.End K K[X])) hcomm
  have hcommPlus : Q * P = 1 + P * Q := by
    apply Subtype.ext
    change (Q : Module.End K K[X]) * (P : Module.End K K[X]) =
      1 + (P : Module.End K K[X]) * (Q : Module.End K K[X])
    calc
      (Q : Module.End K K[X]) * (P : Module.End K K[X]) =
          ((Q : Module.End K K[X]) * (P : Module.End K K[X]) -
            (P : Module.End K K[X]) * (Q : Module.End K K[X])) +
              (P : Module.End K K[X]) * (Q : Module.End K K[X]) :=
        (sub_add_cancel _ _).symm
      _ = 1 + (P : Module.End K K[X]) * (Q : Module.End K K[X]) := by rw [hcommOp]
  have hcommPlusE : QE * PE = 1 + PE * QE := by
    apply (concreteBaseChange_injective E K)
    calc
      concreteBaseChange E K (QE * PE) = Q * P := by rw [map_mul, hQE, hPE]
      _ = 1 + P * Q := hcommPlus
      _ = concreteBaseChange E K (1 + PE * QE) := by rw [map_add, map_one, map_mul, hPE, hQE]
  have hcommEOp :
      (QE.1 * PE.1 - PE.1 * QE.1 : Module.End E E[X]) = 1 := by
    have hplus : (QE.1 * PE.1 : Module.End E E[X]) =
        1 + PE.1 * QE.1 := by
      simpa using congrArg (fun T : A1 E => (T : Module.End E E[X])) hcommPlusE
    calc
      QE.1 * PE.1 - PE.1 * QE.1 = (1 + PE.1 * QE.1) - PE.1 * QE.1 := by rw [hplus]
      _ = 1 := add_sub_cancel_right 1 (PE.1 * QE.1)
  have hcommE : QE * PE - PE * QE = 1 := by
    apply Subtype.ext
    change (QE : Module.End E E[X]) * (PE : Module.End E E[X]) -
      (PE : Module.End E E[X]) * (QE : Module.End E E[X]) = 1
    exact hcommEOp
  have hmassE : mass PE.1 ≤ 6 := by
    rw [← concreteBaseChange_mass E K PE, hPE]
    exact hmass
  obtain ⟨φ⟩ :=
    @exists_algHom_to_complex_of_countable E inferInstance inferInstance hcount
  letI : Algebra E ℂ := φ.toRingHom.toAlgebra
  let PC : A1 ℂ := concreteBaseChange E ℂ PE
  let QC : A1 ℂ := concreteBaseChange E ℂ QE
  have hcommPlusC : QC * PC = 1 + PC * QC := by
    have hh := congrArg (concreteBaseChange E ℂ) hcommPlusE
    simpa only [map_mul, map_add, map_one, PC, QC] using hh
  have hcommCOp :
      (QC.1 * PC.1 - PC.1 * QC.1 : Module.End ℂ ℂ[X]) = 1 := by
    have hplus : (QC.1 * PC.1 : Module.End ℂ ℂ[X]) = 1 + PC.1 * QC.1 := by
      simpa using congrArg (fun T : A1 ℂ => (T : Module.End ℂ ℂ[X])) hcommPlusC
    calc
      QC.1 * PC.1 - PC.1 * QC.1 = (1 + PC.1 * QC.1) - PC.1 * QC.1 := by rw [hplus]
      _ = 1 := add_sub_cancel_right 1 (PC.1 * QC.1)
  have hcommC : QC * PC - PC * QC = 1 := by
    apply Subtype.ext
    change (QC : Module.End ℂ ℂ[X]) * (PC : Module.End ℂ ℂ[X]) -
      (PC : Module.End ℂ ℂ[X]) * (QC : Module.End ℂ ℂ[X]) = 1
    exact hcommCOp
  have hmassC : mass PC.1 ≤ 6 := by
    change mass ((concreteBaseChange E ℂ PE : A1 ℂ) : Module.End ℂ ℂ[X]) ≤ 6
    rw [concreteBaseChange_mass E ℂ PE]
    exact hmassE
  have hgenC : Algebra.adjoin ℂ {PC, QC} = ⊤ :=
    massSixGeneration_complex_of_GGV H PC QC hcommC hmassC
  have hgenE : Algebra.adjoin E {PE, QE} = ⊤ := by
    apply pair_generation_descends E ℂ PE QE
    simpa only [PC, QC] using hgenC
  exact pair_generation_ascends PE QE P Q hPE hQE hgenE

end
end Dixmier.Weyl
