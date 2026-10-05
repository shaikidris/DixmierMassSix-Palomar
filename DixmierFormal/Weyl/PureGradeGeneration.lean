/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GeneratorCentralizer
public import DixmierFormal.Weyl.OppositeGradeSlice

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

set_option maxHeartbeats 1000000

/-!
# Generation by an exact pair with a pure negative-grade member

The exact opposite-grade slice supplies a nonzero multiple of `X`; the remaining
mate lies in the centralizer of `Y`, already proved to be `ℂ[Y]`.
-/

namespace Dixmier.Weyl

open Polynomial

theorem adjoin_eq_top_of_xy_mem {K : Type*} [Field K]
    (S : Subalgebra K (A1 K))
    (hx : (⟨xOp K, xOp_mem_A1⟩ : A1 K) ∈ S)
    (hy : (⟨yOp K, yOp_mem_A1⟩ : A1 K) ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro T _
  have key : ∀ U ∈ A1 K, ∀ hU : U ∈ A1 K, (⟨U, hU⟩ : A1 K) ∈ S := by
    intro U hU
    refine Algebra.adjoin_induction (p := fun U _ => ∀ hU : U ∈ A1 K,
      (⟨U, hU⟩ : A1 K) ∈ S) ?_ ?_ ?_ ?_ hU
    · intro x hx' hxA
      rcases hx' with rfl | rfl
      · exact hx
      · exact hy
    · intro r hr
      exact S.algebraMap_mem r
    · intro x y hx' hy' ihx ihy hxy
      exact S.add_mem (ihx hx') (ihy hy')
    · intro x y hx' hy' ihx ihy hxy
      exact S.mul_mem (ihx hx') (ihy hy')
  exact key T.1 T.2 T.2

/-- A full exact mate of a pure negative-grade Weyl operator generates the
first Weyl algebra; there is no grade or degree bound on the mate. -/
theorem pure_negative_grade_exact_pair_generates
    (P Q : A1 ℂ) (k : ℕ) (hk : 0 < k)
    (hPgrade : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support,
      grade d = -(k : ℤ))
    (hcomm : Q * P - P * Q = 1) :
    Algebra.adjoin ℂ ({P, Q} : Set (A1 ℂ)) = ⊤ := by
  obtain ⟨Qtop, a, b, hP, hQtop, htopcomm, _, ha, hRY⟩ :=
    opposite_grade_generator_slice P Q k hk hPgrade hcomm
  let xA : A1 ℂ := ⟨xOp ℂ, xOp_mem_A1⟩
  let yA : A1 ℂ := ⟨yOp ℂ, yOp_mem_A1⟩
  let R : A1 ℂ := Q - Qtop
  let S := Algebra.adjoin ℂ ({P, Q} : Set (A1 ℂ))
  have hb : b ≠ 0 := by
    intro hz
    have hzero : Qtop = 0 := by simpa [xA, hz] using hQtop
    norm_num [hzero] at htopcomm
  have hyS : yA ∈ S := by
    have hPmem : P ∈ S := Algebra.subset_adjoin (by simp)
    have hscaled : a⁻¹ • P ∈ S := S.smul_mem hPmem a⁻¹
    simpa [hP, smul_smul, ha, yA] using hscaled
  have hRcomm : yOp ℂ * (R : Module.End ℂ ℂ[X]) -
      (R : Module.End ℂ ℂ[X]) * yOp ℂ = 0 := by
    have hOp := congrArg (fun z : A1 ℂ => (z : Module.End ℂ ℂ[X])) hRY
    have heq : (R : Module.End ℂ ℂ[X]) * yOp ℂ =
        yOp ℂ * (R : Module.End ℂ ℂ[X]) := by
      apply sub_eq_zero.mp
      simpa [R, yA] using hOp
    exact sub_eq_zero.mpr heq.symm
  have hRsmall : R ∈ Algebra.adjoin ℂ ({yA} : Set (A1 ℂ)) :=
    mem_adjoin_y_of_commutes_y R hRcomm
  have hRS : R ∈ S := by
    have hle : Algebra.adjoin ℂ ({yA} : Set (A1 ℂ)) ≤ S := by
      apply Algebra.adjoin_le
      intro z hz
      simpa only [Set.mem_singleton_iff] using hz ▸ hyS
    exact hle hRsmall
  have hQtopS : Qtop ∈ S := by
    have hQmem : Q ∈ S := Algebra.subset_adjoin (by simp)
    have hneg : (-R : A1 ℂ) ∈ S :=
      Subalgebra.neg_mem (R := ℂ) (A := A1 ℂ) S hRS
    have hsum : Q + -R ∈ S := S.add_mem hQmem hneg
    have heq : Q + -R = Qtop := by dsimp [R]; abel
    exact heq ▸ hsum
  have hxS : xA ∈ S := by
    have hscaled : b⁻¹ • Qtop ∈ S := S.smul_mem hQtopS b⁻¹
    simpa [hQtop, smul_smul, hb, xA] using hscaled
  exact adjoin_eq_top_of_xy_mem S hxS hyS

end Dixmier.Weyl
