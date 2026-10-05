/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.OneSidedFaceDispatch
public import DixmierFormal.Weyl.PureGradeGeneration
public import DixmierFormal.Weyl.GGVGradesAdapter

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Scalar normalization of one-sided exact Weyl pairs

Subtracting the PBW constant coefficient preserves every nonzero exponent,
the exact commutator, and the generated algebra. This connects the scalar-free
crossing exclusion to the unrestricted one-sided source theorem.
-/

namespace Dixmier.Weyl

open Polynomial MvPolynomial
set_option maxHeartbeats 1000000

noncomputable def pbwConstant (T : A1 ℂ) : ℂ :=
  MvPolynomial.coeff 0 (symbol (T : Module.End ℂ ℂ[X]))

noncomputable def removePBWConstant (T : A1 ℂ) : A1 ℂ :=
  T - pbwConstant T • (1 : A1 ℂ)

theorem symbol_removePBWConstant (T : A1 ℂ) :
    symbol ((removePBWConstant T : A1 ℂ) : Module.End ℂ ℂ[X]) =
      symbol (T : Module.End ℂ ℂ[X]) -
        pbwConstant T • (1 : MvPolynomial (Fin 2) ℂ) := by
  simp only [removePBWConstant, symbol_sub, symbol_smul, symbol_one_A1]

theorem removePBWConstant_scalar_free (T : A1 ℂ) :
    (0 : Fin 2 →₀ ℕ) ∉
      (symbol ((removePBWConstant T : A1 ℂ) : Module.End ℂ ℂ[X])).support := by
  rw [MvPolynomial.mem_support_iff, symbol_removePBWConstant]
  simp [pbwConstant]

theorem removePBWConstant_coeff_of_ne_zero (T : A1 ℂ)
    (d : Fin 2 →₀ ℕ) (hd : d ≠ 0) :
    MvPolynomial.coeff d
      (symbol ((removePBWConstant T : A1 ℂ) : Module.End ℂ ℂ[X])) =
      MvPolynomial.coeff d (symbol (T : Module.End ℂ ℂ[X])) := by
  rw [symbol_removePBWConstant]
  simp [MvPolynomial.coeff_one, Ne.symm hd]

theorem removePBWConstant_support_iff (T : A1 ℂ)
    (d : Fin 2 →₀ ℕ) (hd : d ≠ 0) :
    d ∈ (symbol ((removePBWConstant T : A1 ℂ) : Module.End ℂ ℂ[X])).support ↔
      d ∈ (symbol (T : Module.End ℂ ℂ[X])).support := by
  simp only [MvPolynomial.mem_support_iff]
  rw [removePBWConstant_coeff_of_ne_zero T d hd]

theorem removePBWConstant_preserves_nonpositive_grades (T : A1 ℂ)
    (hT : ∀ d ∈ (symbol (T : Module.End ℂ ℂ[X])).support, grade d ≤ 0) :
    ∀ d ∈ (symbol ((removePBWConstant T : A1 ℂ) : Module.End ℂ ℂ[X])).support,
      grade d ≤ 0 := by
  intro d hd
  have hne : d ≠ 0 := by
    intro hz
    exact removePBWConstant_scalar_free T (hz ▸ hd)
  exact hT d ((removePBWConstant_support_iff T d hne).mp hd)

theorem removePBWConstant_exact_pair (P Q : A1 ℂ)
    (hpair : Q * P - P * Q = 1) :
    removePBWConstant Q * removePBWConstant P -
      removePBWConstant P * removePBWConstant Q = 1 := by
  simp only [removePBWConstant]
  have hcomm (T : A1 ℂ) (c : ℂ) :
      (c • (1 : A1 ℂ)) * T = T * (c • (1 : A1 ℂ)) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using (Algebra.commutes c T)
  let a : A1 ℂ := pbwConstant P • (1 : A1 ℂ)
  let b : A1 ℂ := pbwConstant Q • (1 : A1 ℂ)
  change (Q - b) * (P - a) - (P - a) * (Q - b) = 1
  have hmain : (Q - b) * (P - a) - (P - a) * (Q - b) = Q * P - P * Q := by
    apply Subtype.ext
    change ((Q : Module.End ℂ ℂ[X]) - b) * ((P : Module.End ℂ ℂ[X]) - a) -
      ((P : Module.End ℂ ℂ[X]) - a) * ((Q : Module.End ℂ ℂ[X]) - b) =
        (Q : Module.End ℂ ℂ[X]) * P - (P : Module.End ℂ ℂ[X]) * Q
    have haQ := congrArg Subtype.val (hcomm Q (pbwConstant P))
    have hbP := congrArg Subtype.val (hcomm P (pbwConstant Q))
    have hba := congrArg Subtype.val (hcomm a (pbwConstant Q))
    simp only [Subalgebra.coe_mul] at haQ hbP hba
    simp only [sub_mul, mul_sub]
    rw [haQ, hbP, hba]
    abel
  exact hmain.trans hpair

/-- Generation by the normalized pair implies generation by the original
pair, since the removed constants already lie in every unital algebra. -/
theorem generation_of_removePBWConstant_generation (P Q : A1 ℂ)
    (hgen : Algebra.adjoin ℂ
      ({removePBWConstant P, removePBWConstant Q} : Set (A1 ℂ)) = ⊤) :
    Algebra.adjoin ℂ ({P, Q} : Set (A1 ℂ)) = ⊤ := by
  let S := Algebra.adjoin ℂ ({P, Q} : Set (A1 ℂ))
  have hP : P ∈ S := Algebra.subset_adjoin (by simp)
  have hQ : Q ∈ S := Algebra.subset_adjoin (by simp)
  have hnormP : removePBWConstant P ∈ S := by
    have hc : (-pbwConstant P) • (1 : A1 ℂ) ∈ S := by
      simpa only [Algebra.algebraMap_eq_smul_one] using (S.algebraMap_mem (-pbwConstant P))
    have heq : removePBWConstant P = P + (-pbwConstant P) • (1 : A1 ℂ) := by
      apply Subtype.ext
      change (P : Module.End ℂ ℂ[X]) - pbwConstant P • (1 : Module.End ℂ ℂ[X]) =
        (P : Module.End ℂ ℂ[X]) + (-pbwConstant P) • (1 : Module.End ℂ ℂ[X])
      have hneg : (-pbwConstant P) • (1 : Module.End ℂ ℂ[X]) =
          -(pbwConstant P • (1 : Module.End ℂ ℂ[X])) := by
        ext f
        simp
      rw [hneg]
      abel
    rw [heq]
    exact S.add_mem hP hc
  have hnormQ : removePBWConstant Q ∈ S := by
    have hc : (-pbwConstant Q) • (1 : A1 ℂ) ∈ S := by
      simpa only [Algebra.algebraMap_eq_smul_one] using (S.algebraMap_mem (-pbwConstant Q))
    have heq : removePBWConstant Q = Q + (-pbwConstant Q) • (1 : A1 ℂ) := by
      apply Subtype.ext
      change (Q : Module.End ℂ ℂ[X]) - pbwConstant Q • (1 : Module.End ℂ ℂ[X]) =
        (Q : Module.End ℂ ℂ[X]) + (-pbwConstant Q) • (1 : Module.End ℂ ℂ[X])
      have hneg : (-pbwConstant Q) • (1 : Module.End ℂ ℂ[X]) =
          -(pbwConstant Q • (1 : Module.End ℂ ℂ[X])) := by
        ext f
        simp
      rw [hneg]
      abel
    rw [heq]
    exact S.add_mem hQ hc
  have hle : Algebra.adjoin ℂ
      ({removePBWConstant P, removePBWConstant Q} : Set (A1 ℂ)) ≤ S := by
    apply Algebra.adjoin_le
    intro T hT
    rcases Set.mem_insert_iff.mp hT with hT | hT
    · exact hT ▸ hnormP
    · have hT' : T = removePBWConstant Q := by simpa using hT
      exact hT' ▸ hnormQ
  rw [hgen] at hle
  exact top_le_iff.mp hle

private theorem symbol_zero_A1 :
    symbol ((0 : A1 ℂ) : Module.End ℂ ℂ[X]) = 0 := by
  have h := symbol_smul (0 : ℂ) (1 : A1 ℂ)
  simpa using h

/-- A scalar-free member of an exact pair has an occupied nonconstant PBW
exponent; otherwise symbol injectivity would make that member zero. -/
theorem scalar_free_exact_pair_left_nonconstant (P Q : A1 ℂ)
    (hpair : Q * P - P * Q = 1)
    (hscalar : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (P : Module.End ℂ ℂ[X])).support) :
    ∃ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, d ≠ 0 := by
  by_contra hn
  have hsupport : (symbol (P : Module.End ℂ ℂ[X])).support = ∅ := by
    ext d
    constructor
    · intro hd
      have : False := by
        by_cases hz : d = 0
        · exact hscalar (hz ▸ hd)
        · exact hn ⟨d, hd, hz⟩
      exact this.elim
    · simp
  have hsymbol : symbol (P : Module.End ℂ ℂ[X]) = 0 := by
    exact MvPolynomial.support_eq_empty.mp hsupport
  have hpzero : P = 0 := symbol_injective (by rw [hsymbol, symbol_zero_A1])
  rw [hpzero] at hpair
  have hpairOp := congrArg Subtype.val hpair
  simp at hpairOp

theorem scalar_free_exact_pair_right_nonconstant (P Q : A1 ℂ)
    (hpair : Q * P - P * Q = 1)
    (hscalar : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (Q : Module.End ℂ ℂ[X])).support) :
    ∃ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, d ≠ 0 := by
  by_contra hn
  have hsupport : (symbol (Q : Module.End ℂ ℂ[X])).support = ∅ := by
    ext d
    constructor
    · intro hd
      have : False := by
        by_cases hz : d = 0
        · exact hscalar (hz ▸ hd)
        · exact hn ⟨d, hd, hz⟩
      exact this.elim
    · simp
  have hsymbol : symbol (Q : Module.End ℂ ℂ[X]) = 0 := by
    exact MvPolynomial.support_eq_empty.mp hsupport
  have hqzero : Q = 0 := symbol_injective (by rw [hsymbol, symbol_zero_A1])
  rw [hqzero] at hpair
  have hpairOp := congrArg Subtype.val hpair
  simp at hpairOp

/-- Han--Tan's nonpositive-grade one-member theorem in the exact-pair
orientation of this project. The mate has no mass, grade, or order bound. -/
theorem oneSided_nonpositive_exact_pair_generates (P Q : A1 ℂ)
    (hpair : Q * P - P * Q = 1)
    (hPside : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d ≤ 0) :
    Algebra.adjoin ℂ ({P, Q} : Set (A1 ℂ)) = ⊤ := by
  let P₀ := removePBWConstant P
  let Q₀ := removePBWConstant Q
  have hpair₀ : Q₀ * P₀ - P₀ * Q₀ = 1 :=
    removePBWConstant_exact_pair P Q hpair
  have hPside₀ : ∀ d ∈ (symbol (P₀ : Module.End ℂ ℂ[X])).support,
      grade d ≤ 0 := removePBWConstant_preserves_nonpositive_grades P hPside
  have hPscalar : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (P₀ : Module.End ℂ ℂ[X])).support :=
    removePBWConstant_scalar_free P
  have hQscalar : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (Q₀ : Module.End ℂ ℂ[X])).support :=
    removePBWConstant_scalar_free Q
  have hPnonconst := scalar_free_exact_pair_left_nonconstant P₀ Q₀ hpair₀ hPscalar
  have hQnonconst := scalar_free_exact_pair_right_nonconstant P₀ Q₀ hpair₀ hQscalar
  have hPonly : ∀ d ∈ (symbol (P₀ : Module.End ℂ ℂ[X])).support,
      d = expo 0 1 := by
    intro d hd
    by_contra hne
    exact oneSided_exact_pair_nonmonomial_impossible P₀ Q₀ hpair₀ hPside₀
      hPnonconst hQnonconst hPscalar hQscalar ⟨d, hd, hne⟩
  have hPgrade : ∀ d ∈ (symbol (P₀ : Module.End ℂ ℂ[X])).support,
      grade d = -(1 : ℤ) := by
    intro d hd
    rw [hPonly d hd]
    simp [grade, expo]
  have hgen₀ : Algebra.adjoin ℂ ({P₀, Q₀} : Set (A1 ℂ)) = ⊤ :=
    pure_negative_grade_exact_pair_generates P₀ Q₀ 1 (by omega) hPgrade hpair₀
  exact generation_of_removePBWConstant_generation P Q hgen₀

/-- Fourier exchange reduces the nonnegative-grade member to the proved
nonpositive-grade case. -/
theorem oneSided_nonnegative_exact_pair_generates (P Q : A1 ℂ)
    (hpair : Q * P - P * Q = 1)
    (hPside : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, 0 ≤ grade d) :
    Algebra.adjoin ℂ ({P, Q} : Set (A1 ℂ)) = ⊤ := by
  have hpair' : fourierAlgHom ℂ Q * fourierAlgHom ℂ P -
      fourierAlgHom ℂ P * fourierAlgHom ℂ Q = (1 : A1 ℂ) := by
    have hmap := congrArg (fourierAlgHom ℂ) hpair
    rw [map_sub (fourierAlgHom ℂ), map_mul (fourierAlgHom ℂ),
      map_mul (fourierAlgHom ℂ), map_one (fourierAlgHom ℂ)] at hmap
    exact hmap
  have hPside' : ∀ d ∈
      (symbol ((fourierAlgHom ℂ P : A1 ℂ) : Module.End ℂ ℂ[X])).support,
      grade d ≤ 0 := by
    intro d hd
    have hgrade : grade d ∈
        (symbol ((fourierAlgHom ℂ P : A1 ℂ) : Module.End ℂ ℂ[X])).support.image grade :=
      Finset.mem_image.mpr ⟨d, hd, rfl⟩
    have hsubset := fourier_gradeSupport_subset P hgrade
    rcases Finset.mem_image.mp hsubset with ⟨g, hg, hgd⟩
    rcases Finset.mem_image.mp hg with ⟨e, he, heg⟩
    have hde : grade d = -grade e := by simpa [heg] using hgd.symm
    rw [hde]
    exact neg_nonpos.mpr (hPside e he)
  have hgen' := oneSided_nonpositive_exact_pair_generates
    (fourierAlgHom ℂ P) (fourierAlgHom ℂ Q) hpair' hPside'
  exact (adjoin_fourier_eq_top_iff P Q).mp hgen'

/-- The full Han--Tan one-member interface is proved rather than retained
as an imported hypothesis. -/
theorem hanTanOneSidedGrades_proved : HanTanOneSidedGrades := by
  intro P Q hpair hside
  rcases hside with hnonneg | hnonpos
  · exact oneSided_nonnegative_exact_pair_generates P Q hpair hnonneg
  · exact oneSided_nonpositive_exact_pair_generates P Q hpair hnonpos

/-- The first of the six mandatory GGV fields, now an unconditional theorem
for counterexample pairs. -/
theorem ggv_grades_opposite_proved :
    ∀ P Q : A1 ℂ, IsCounterexamplePair P Q →
      (∃ d ∈ (symbol P.1).support, 0 < grade d) ∧
      (∃ d ∈ (symbol P.1).support, grade d < 0) :=
  grades_opposite_of_HanTan hanTanOneSidedGrades_proved

end Dixmier.Weyl
