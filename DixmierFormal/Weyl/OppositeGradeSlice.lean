/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PBWGradeSlices
public import DixmierFormal.Weyl.OppositeGradeCommutator

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

set_option maxHeartbeats 1000000

/-!
# Extracting the opposite-grade slice of an exact Weyl mate

If one member of an exact Weyl pair is supported in one grade, only the
opposite-grade slice of its mate can contribute to grade zero in the
commutator. This file proves that the slice itself remains an exact mate.
-/

namespace Dixmier.Weyl

open Polynomial

private theorem pbwCoeff_sub_slice
    (T S : A1 ℂ) (i j : ℕ) :
    pbwCoeff ((T - S : A1 ℂ) : Module.End ℂ ℂ[X]) i j =
      pbwCoeff (T : Module.End ℂ ℂ[X]) i j -
        pbwCoeff (S : Module.End ℂ ℂ[X]) i j := by
  simp [pbwCoeff, coeffPoly, Polynomial.coeff_sub,
    Finset.sum_sub_distrib, mul_sub]

private theorem pbwCoeff_zero_of_grade_avoided
    (T : A1 ℂ) (i j : ℕ) (g : ℤ)
    (havoid : ∀ d ∈ (symbol (T : Module.End ℂ ℂ[X])).support, grade d ≠ g)
    (hij : (i : ℤ) - j = g) :
    pbwCoeff (T : Module.End ℂ ℂ[X]) i j = 0 := by
  by_contra hne
  have hs : expo i j ∈ (symbol (T : Module.End ℂ ℂ[X])).support := by
    rw [MvPolynomial.mem_support_iff, symbol_coeff_pbwCoeff]
    exact hne
  have hgrade := havoid (expo i j) hs
  have hcoord : grade (expo i j) = (i : ℤ) - j := by simp [grade, expo]
  rw [hcoord, hij] at hgrade
  exact hgrade rfl

private theorem symbol_support_grade_avoided_of_products
    (L R : A1 ℂ) (k : ℕ)
    (hL : ∀ d ∈ (symbol (L : Module.End ℂ ℂ[X])).support,
      grade d ≠ (k : ℤ))
    (hR : ∀ d ∈ (symbol (R : Module.End ℂ ℂ[X])).support,
      grade d = -(k : ℤ)) :
    ∀ d ∈ (symbol ((L * R : A1 ℂ) : Module.End ℂ ℂ[X])).support,
      grade d ≠ 0 := by
  intro d hd hzero
  obtain ⟨e, he, f, hf, hsum⟩ := symbol_mul_grade_decomposition L R d hd
  have hegrade : grade e ≠ (k : ℤ) := hL e he
  have hfgrade : grade f = -(k : ℤ) := hR f hf
  rw [hsum, hfgrade] at hzero
  exact hegrade (by omega)

private theorem symbol_support_grade_avoided_of_products_right
    (L R : A1 ℂ) (k : ℕ)
    (hL : ∀ d ∈ (symbol (L : Module.End ℂ ℂ[X])).support,
      grade d = -(k : ℤ))
    (hR : ∀ d ∈ (symbol (R : Module.End ℂ ℂ[X])).support,
      grade d ≠ (k : ℤ)) :
    ∀ d ∈ (symbol ((L * R : A1 ℂ) : Module.End ℂ ℂ[X])).support,
      grade d ≠ 0 := by
  intro d hd hzero
  obtain ⟨e, he, f, hf, hsum⟩ := symbol_mul_grade_decomposition L R d hd
  have hegrade : grade e = -(k : ℤ) := hL e he
  have hfgrade : grade f ≠ (k : ℤ) := hR f hf
  rw [hsum, hegrade] at hzero
  exact hfgrade (by omega)

private theorem symbol_sub_support_grade_avoided
    (L R : A1 ℂ) (g : ℤ)
    (hL : ∀ d ∈ (symbol (L : Module.End ℂ ℂ[X])).support, grade d ≠ g)
    (hR : ∀ d ∈ (symbol (R : Module.End ℂ ℂ[X])).support, grade d ≠ g) :
    ∀ d ∈ (symbol ((L - R : A1 ℂ) : Module.End ℂ ℂ[X])).support,
      grade d ≠ g := by
  intro d hd hgd
  have hcoeff := MvPolynomial.mem_support_iff.mp hd
  rw [symbol_sub, MvPolynomial.coeff_sub] at hcoeff
  have hzeroL : MvPolynomial.coeff d (symbol (L : Module.End ℂ ℂ[X])) = 0 := by
    by_contra hne
    have hs : d ∈ (symbol (L : Module.End ℂ ℂ[X])).support :=
      MvPolynomial.mem_support_iff.mpr hne
    exact hL d hs hgd
  have hzeroR : MvPolynomial.coeff d (symbol (R : Module.End ℂ ℂ[X])) = 0 := by
    by_contra hne
    have hs : d ∈ (symbol (R : Module.End ℂ ℂ[X])).support :=
      MvPolynomial.mem_support_iff.mpr hne
    exact hR d hs hgd
  rw [hzeroL, hzeroR] at hcoeff
  simp at hcoeff

/-- For a pure grade `-k` operator `P`, the exact grade `+k` projection of any
exact Weyl mate `Q` is itself a Weyl mate. No one-sided bound on the remaining
grades of `Q` is required. -/
theorem opposite_grade_projection_is_exact_mate
    (P Q : A1 ℂ) (k : ℕ)
    (hPgrade : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support,
      grade d = -(k : ℤ))
    (hcomm : Q * P - P * Q = 1) :
    ∃ Qtop : A1 ℂ,
      (∀ d ∈ (symbol (Qtop : Module.End ℂ ℂ[X])).support,
        grade d = (k : ℤ)) ∧
      (∀ i j, pbwCoeff (Qtop : Module.End ℂ ℂ[X]) i j =
        if (i : ℤ) - j = (k : ℤ) then
          pbwCoeff (Q : Module.End ℂ ℂ[X]) i j else 0) ∧
      Qtop * P - P * Qtop = 1 ∧
      (Q - Qtop) * P - P * (Q - Qtop) = 0 := by
  obtain ⟨Qtop, hQtopgrade, hQtopcoeff⟩ := exists_exact_grade_projection Q k
  let Qlo : A1 ℂ := Q - Qtop
  have hQsplit : Qtop + Qlo = Q := by
    dsimp [Qlo]
    abel
  have hQloavoid : ∀ d ∈ (symbol (Qlo : Module.End ℂ ℂ[X])).support,
      grade d ≠ (k : ℤ) := by
    intro d hd hgd
    obtain ⟨⟨i, j⟩, he⟩ := expo_surjective d
    change expo i j = d at he
    have hcoeff : pbwCoeff (Qlo : Module.End ℂ ℂ[X]) i j ≠ 0 := by
      have h := MvPolynomial.mem_support_iff.mp hd
      rw [← he, symbol_coeff_pbwCoeff] at h
      exact h
    have hcoord : (i : ℤ) - j = (k : ℤ) := by
      have hgrade : grade (expo i j) = (i : ℤ) - j := by simp [grade, expo]
      calc
        (i : ℤ) - j = grade (expo i j) := hgrade.symm
        _ = grade d := by rw [he]
        _ = (k : ℤ) := hgd
    have hcoeff' : pbwCoeff (Qlo : Module.End ℂ ℂ[X]) i j = 0 := by
      change pbwCoeff ((Q - Qtop : A1 ℂ) : Module.End ℂ ℂ[X]) i j = 0
      rw [pbwCoeff_sub_slice, hQtopcoeff, if_pos hcoord]
      ring
    exact hcoeff hcoeff'
  have hQPavoid := symbol_support_grade_avoided_of_products Qlo P k
    hQloavoid hPgrade
  have hPQavoid := symbol_support_grade_avoided_of_products_right P Qlo k
    hPgrade hQloavoid
  let Ctail : A1 ℂ := Qlo * P - P * Qlo
  have hCtailavoid : ∀ d ∈ (symbol (Ctail : Module.End ℂ ℂ[X])).support,
      grade d ≠ 0 := by
    dsimp [Ctail]
    exact symbol_sub_support_grade_avoided (Qlo * P) (P * Qlo) 0 hQPavoid hPQavoid
  let Ctop : A1 ℂ := Qtop * P - P * Qtop
  have hCtopgrade : ∀ d ∈ (symbol (Ctop : Module.End ℂ ℂ[X])).support,
      grade d = 0 := by
    have hQP0 : ∀ d ∈ (symbol ((Qtop * P : A1 ℂ) : Module.End ℂ ℂ[X])).support,
        grade d = 0 := by
      intro d hd
      have h := symbol_mul_grade_eq Qtop P (k : ℤ) (-(k : ℤ))
        hQtopgrade hPgrade d hd
      omega
    have hPQ0 : ∀ d ∈ (symbol ((P * Qtop : A1 ℂ) : Module.End ℂ ℂ[X])).support,
        grade d = 0 := by
      intro d hd
      have h := symbol_mul_grade_eq P Qtop (-(k : ℤ)) (k : ℤ)
        hPgrade hQtopgrade d hd
      omega
    have hQP := hQP0
    have hPQ := hPQ0
    simpa only [Ctop] using
      (symbol_sub_grade_eq (Qtop * P) (P * Qtop) 0 hQP hPQ)
  have hExpand : Q * P - P * Q = Ctop + Ctail := by
    dsimp [Ctop, Ctail]
    rw [← hQsplit]
    simp only [add_mul, mul_add]
    abel
  have hsumone : Ctop + Ctail = 1 := by rw [← hExpand]; exact hcomm
  have hOneCoeff (i j : ℕ) :
      pbwCoeff ((1 : A1 ℂ) : Module.End ℂ ℂ[X]) i j =
        if i = 0 ∧ j = 0 then 1 else 0 := by
    simpa [normalOrderedMonomial] using
      (pbwCoeff_normalOrdered_monomial (K := ℂ) 0 0 i j)
  have hcoeff (i j : ℕ) :
      pbwCoeff (Ctop : Module.End ℂ ℂ[X]) i j =
        pbwCoeff ((1 : A1 ℂ) : Module.End ℂ ℂ[X]) i j := by
    by_cases hij : (i : ℤ) - j = 0
    · have htail : pbwCoeff (Ctail : Module.End ℂ ℂ[X]) i j = 0 :=
        pbwCoeff_zero_of_grade_avoided Ctail i j 0 hCtailavoid hij
      have hsumcoeff := congrArg (fun T : A1 ℂ =>
        pbwCoeff (T : Module.End ℂ ℂ[X]) i j) hsumone
      rw [Subalgebra.coe_add, pbwCoeff_add] at hsumcoeff
      rw [htail, add_zero] at hsumcoeff
      exact hsumcoeff
    · have htop : pbwCoeff (Ctop : Module.End ℂ ℂ[X]) i j = 0 := by
        by_contra hne
        have hd : expo i j ∈ (symbol (Ctop : Module.End ℂ ℂ[X])).support := by
          rw [MvPolynomial.mem_support_iff, symbol_coeff_pbwCoeff]
          exact hne
        have hg := hCtopgrade (expo i j) hd
        have hcoord : grade (expo i j) = (i : ℤ) - j := by simp [grade, expo]
        exact hij (hcoord.symm.trans hg)
      have hone : pbwCoeff ((1 : A1 ℂ) : Module.End ℂ ℂ[X]) i j = 0 := by
        rw [hOneCoeff]
        have hnot : ¬(i = 0 ∧ j = 0) := by
          rintro ⟨rfl, rfl⟩
          exact hij (by norm_num)
        simp [hnot]
      exact htop.trans hone.symm
  have hCtop : Ctop = 1 := by
    apply symbol_injective
    apply MvPolynomial.ext
    intro d
    obtain ⟨⟨i, j⟩, hd⟩ := expo_surjective d
    rw [← hd, symbol_coeff_pbwCoeff, symbol_coeff_pbwCoeff]
    exact hcoeff i j
  have hCtail : Ctail = 0 := by
    have h := hsumone
    rw [hCtop] at h
    have h' : (1 : A1 ℂ) + Ctail = (1 : A1 ℂ) + 0 := by simpa using h
    have h'' := congrArg (fun z : A1 ℂ => z - 1) h'
    calc
      Ctail = (1 + Ctail) - 1 := by abel
      _ = (1 + 0) - 1 := h''
      _ = 0 := by simpa only [add_zero] using (sub_self (1 : A1 ℂ))
  refine ⟨Qtop, hQtopgrade, hQtopcoeff, ?_, ?_⟩
  · exact hCtop
  · simpa [Ctail, Qlo] using hCtail

/-- A full exact Weyl pair with a pure negative-grade member reduces to the source's
homogeneous-pair configuration: its opposite-grade slice is a generator mate, the grade size
is one, and the discarded remainder centralizes the original member. -/
theorem opposite_grade_homogeneous_pair_reduction
    (P Q : A1 ℂ) (k : ℕ) (hk : 0 < k)
    (hPgrade : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support,
      grade d = -(k : ℤ))
    (hcomm : Q * P - P * Q = 1) :
    ∃ (Qtop : A1 ℂ) (f g : ℂ[X]),
      (P : Module.End ℂ ℂ[X]) = aeval (yOp ℂ * xOp ℂ) f * yOp ℂ ^ k ∧
      (Qtop : Module.End ℂ ℂ[X]) = aeval (yOp ℂ * xOp ℂ) g * xOp ℂ ^ k ∧
      k = 1 ∧ f.natDegree = 0 ∧ g.natDegree = 0 ∧
      (Q - Qtop) * P - P * (Q - Qtop) = 0 := by
  obtain ⟨Qtop, hQtopgrade, _, htopcomm, htailcomm⟩ :=
    opposite_grade_projection_is_exact_mate P Q k hPgrade hcomm
  obtain ⟨f, g, hf, hg, hkone, hfdeg, hgdeg⟩ :=
    opposite_grade_exact_pair_forces_generator_forms P Qtop k hk
      hPgrade hQtopgrade htopcomm
  exact ⟨Qtop, f, g, hf, hg, hkone, hfdeg, hgdeg, htailcomm⟩

/-- The homogeneous-pair reduction in the concrete Weyl generators.  The only
remaining freedom in the full mate is an operator commuting with `P`. -/
theorem opposite_grade_generator_slice
    (P Q : A1 ℂ) (k : ℕ) (hk : 0 < k)
    (hPgrade : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support,
      grade d = -(k : ℤ))
    (hcomm : Q * P - P * Q = 1) :
    ∃ (Qtop : A1 ℂ) (a b : ℂ),
      P = a • (⟨yOp ℂ, yOp_mem_A1⟩ : A1 ℂ) ∧
      Qtop = b • (⟨xOp ℂ, xOp_mem_A1⟩ : A1 ℂ) ∧
      Qtop * P - P * Qtop = 1 ∧ k = 1 ∧ a ≠ 0 ∧
      (Q - Qtop) * (⟨yOp ℂ, yOp_mem_A1⟩ : A1 ℂ) -
        (⟨yOp ℂ, yOp_mem_A1⟩ : A1 ℂ) * (Q - Qtop) = 0 := by
  obtain ⟨Qtop, hQtopgrade, _, htopcomm, htail⟩ :=
    opposite_grade_projection_is_exact_mate P Q k hPgrade hcomm
  obtain ⟨f, g, hf, hg, hkone, hfdeg, hgdeg⟩ :=
    opposite_grade_exact_pair_forces_generator_forms P Qtop k hk
      hPgrade hQtopgrade htopcomm
  let yA : A1 ℂ := ⟨yOp ℂ, yOp_mem_A1⟩
  let xA : A1 ℂ := ⟨xOp ℂ, xOp_mem_A1⟩
  have hP : P = (f.coeff 0) • yA := by
    apply Subtype.ext
    rw [hf, Polynomial.eq_C_of_natDegree_eq_zero hfdeg, hkone]
    simp [yA, Algebra.algebraMap_eq_smul_one]
  have hQtop : Qtop = (g.coeff 0) • xA := by
    apply Subtype.ext
    rw [hg, Polynomial.eq_C_of_natDegree_eq_zero hgdeg, hkone]
    simp [xA, Algebra.algebraMap_eq_smul_one]
  have ha : f.coeff 0 ≠ 0 := by
    intro hz
    have hPzero : P = 0 := by simpa [hz] using hP
    norm_num [hPzero] at hcomm
  have hY : (Q - Qtop) * yA - yA * (Q - Qtop) = 0 := by
    rw [hP] at htail
    have htailOp := congrArg (fun z : A1 ℂ => (z : Module.End ℂ ℂ[X])) htail
    have heq : ((Q - Qtop : A1 ℂ) : Module.End ℂ ℂ[X]) *
        ((f.coeff 0) • (yOp ℂ)) =
        ((f.coeff 0) • (yOp ℂ)) *
          ((Q - Qtop : A1 ℂ) : Module.End ℂ ℂ[X]) := by
      apply sub_eq_zero.mp
      simpa [yA] using htailOp
    rw [mul_smul_comm, smul_mul_assoc] at heq
    have heq' := congrArg
      (fun z : Module.End ℂ ℂ[X] => (f.coeff 0)⁻¹ • z) heq
    have heqY : ((Q - Qtop : A1 ℂ) : Module.End ℂ ℂ[X]) * yOp ℂ =
        yOp ℂ * ((Q - Qtop : A1 ℂ) : Module.End ℂ ℂ[X]) := by
      simpa [smul_smul, ha] using heq'
    apply Subtype.ext
    change ((Q - Qtop : A1 ℂ) : Module.End ℂ ℂ[X]) * yOp ℂ -
      yOp ℂ * ((Q - Qtop : A1 ℂ) : Module.End ℂ ℂ[X]) = 0
    exact sub_eq_zero.mpr heqY
  exact ⟨Qtop, f.coeff 0, g.coeff 0, hP, hQtop, htopcomm, hkone, ha, hY⟩

end Dixmier.Weyl
