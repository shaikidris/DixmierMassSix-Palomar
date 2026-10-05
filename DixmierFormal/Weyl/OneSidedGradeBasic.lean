/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Fourier

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

open MvPolynomial Polynomial
namespace Dixmier.Weyl

/-- Taking a weighted leading form can remove support terms, but cannot introduce a new
exponent. This is the support-level fact needed when passing from an operator to its Newton
roof faces. -/
theorem leadingForm_support_subset_symbol_support {K : Type*} [Field K]
    (T : Module.End K K[X]) (ρ σ : ℤ) :
    (leadingForm ρ σ T).support ⊆ (symbol T).support := by
  classical
  rw [leadingForm, support_weightedHomogeneousComponent]
  intro d hd
  have hd' : d ∈ (symbol T).support ∧
      (Finsupp.weight (wt ρ σ)) d = vDeg ρ σ T := by
    simpa only [Finset.mem_filter] using hd
  exact hd'.1

/-- Every exponent on a weighted leading face inherits any grade bound that holds on the
whole PBW symbol. In particular, an operator supported in nonpositive grades has all of its
Newton-roof faces in the same half-plane. -/
theorem leadingForm_support_grade_bound {K : Type*} [Field K]
    (T : Module.End K K[X]) (ρ σ bound : ℤ)
    (hT : ∀ d ∈ (symbol T).support, grade d ≤ bound) :
    ∀ d ∈ (leadingForm ρ σ T).support, grade d ≤ bound := by
  intro d hd
  exact hT d (leadingForm_support_subset_symbol_support T ρ σ hd)

lemma pbwCoeff_orderZero_eq_coeff_applyOne (T : Module.End ℂ ℂ[X]) (i : ℕ) :
    pbwCoeff T i 0 = (T 1).coeff i := by
  simp [pbwCoeff, coeffPoly]

lemma nonpositive_grades_applyOne_is_constant (T : A1 ℂ)
    (hT : ∀ d ∈ (symbol (T : Module.End ℂ ℂ[X])).support, grade d ≤ 0) :
    ∃ c : ℂ, (T : Module.End ℂ ℂ[X]) 1 = Polynomial.C c := by
  have hcoeff : ∀ i : ℕ, 0 < i → ((T : Module.End ℂ ℂ[X]) 1).coeff i = 0 := by
    intro i hi
    have hnot : expo i 0 ∉ (symbol (T : Module.End ℂ ℂ[X])).support := by
      intro hmem
      have hle := hT (expo i 0) hmem
      have hpos : 0 < grade (expo i 0) := by simp [grade, expo]; omega
      omega
    have hz : MvPolynomial.coeff (expo i 0)
        (symbol (T : Module.End ℂ ℂ[X])) = 0 := by
      by_contra hne
      exact hnot (MvPolynomial.mem_support_iff.mpr hne)
    have hz' : pbwCoeff (T : Module.End ℂ ℂ[X]) i 0 = 0 := by
      rw [← symbol_coeff_pbwCoeff]
      exact hz
    simpa [pbwCoeff, coeffPoly] using hz'
  refine ⟨((T : Module.End ℂ ℂ[X]) 1).coeff 0, ?_⟩
  ext i
  by_cases hi : i = 0
  · subst i
    simp
  · have hpos : 0 < i := Nat.pos_of_ne_zero hi
    rw [Polynomial.coeff_C_of_ne_zero (Nat.ne_of_gt hpos)]
    exact hcoeff i hpos

end Dixmier.Weyl

namespace Dixmier.Weyl
theorem no_exact_pair_both_nonpositive (P Q : A1 ℂ)
    (hP : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d ≤ 0)
    (hQ : ∀ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, grade d ≤ 0) :
    Q * P - P * Q ≠ (1 : A1 ℂ) := by
  intro hpq
  obtain ⟨a, ha⟩ := nonpositive_grades_applyOne_is_constant P hP
  obtain ⟨b, hb⟩ := nonpositive_grades_applyOne_is_constant Q hQ
  have hPa : ∀ c : ℂ, (P : Module.End ℂ ℂ[X]) (Polynomial.C c) = Polynomial.C (c*a) := by
    intro c
    calc
      (P : Module.End ℂ ℂ[X]) (Polynomial.C c) =
          (P : Module.End ℂ ℂ[X]) (c • (1 : ℂ[X])) := by
            rw [Polynomial.C_eq_algebraMap, Algebra.algebraMap_eq_smul_one]
      _ = c • ((P : Module.End ℂ ℂ[X]) 1) := map_smul _ _ _
      _ = c • Polynomial.C a := by rw [ha]
      _ = Polynomial.C (c*a) := by
            rw [Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hQb : ∀ c : ℂ, (Q : Module.End ℂ ℂ[X]) (Polynomial.C c) = Polynomial.C (c*b) := by
    intro c
    calc
      (Q : Module.End ℂ ℂ[X]) (Polynomial.C c) =
          (Q : Module.End ℂ ℂ[X]) (c • (1 : ℂ[X])) := by
            rw [Polynomial.C_eq_algebraMap, Algebra.algebraMap_eq_smul_one]
      _ = c • ((Q : Module.End ℂ ℂ[X]) 1) := map_smul _ _ _
      _ = c • Polynomial.C b := by rw [hb]
      _ = Polynomial.C (c*b) := by
            rw [Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hzero : (((Q : Module.End ℂ ℂ[X]) * P - (P : Module.End ℂ ℂ[X]) * Q) 1) = 0 := by
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
    rw [hQb, hPa]
    rw [mul_comm a b]
    simp
  have hone : (((Q : Module.End ℂ ℂ[X]) * P - (P : Module.End ℂ ℂ[X]) * Q) 1) = 1 := by
    have hval : (Q : Module.End ℂ ℂ[X]) * P - (P : Module.End ℂ ℂ[X]) * Q = (1 : Module.End ℂ ℂ[X]) := by
      exact congrArg Subtype.val hpq
    rw [hval]
    simp
  rw [hzero] at hone
  exact zero_ne_one hone

end Dixmier.Weyl

namespace Dixmier.Weyl

/-- The Fourier exchange reverses grades, so a pair both supported in nonnegative grades also
cannot satisfy the Weyl relation. -/
theorem no_exact_pair_both_nonnegative (P Q : A1 ℂ)
    (hP : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, 0 ≤ grade d)
    (hQ : ∀ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, 0 ≤ grade d) :
    Q * P - P * Q ≠ (1 : A1 ℂ) := by
  intro hpq
  have hcomm : fourierAlgHom ℂ Q * fourierAlgHom ℂ P -
      fourierAlgHom ℂ P * fourierAlgHom ℂ Q = (1 : A1 ℂ) := by
    have hmap := congrArg (fourierAlgHom ℂ) hpq
    rw [map_sub (fourierAlgHom ℂ), map_mul (fourierAlgHom ℂ),
      map_mul (fourierAlgHom ℂ), map_one (fourierAlgHom ℂ)] at hmap
    exact hmap
  have hP' : ∀ d ∈ (symbol ((fourierAlgHom ℂ P : A1 ℂ) : Module.End ℂ ℂ[X])).support,
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
    exact neg_nonpos.mpr (hP e he)
  have hQ' : ∀ d ∈ (symbol ((fourierAlgHom ℂ Q : A1 ℂ) : Module.End ℂ ℂ[X])).support,
      grade d ≤ 0 := by
    intro d hd
    have hgrade : grade d ∈
        (symbol ((fourierAlgHom ℂ Q : A1 ℂ) : Module.End ℂ ℂ[X])).support.image grade :=
      Finset.mem_image.mpr ⟨d, hd, rfl⟩
    have hsubset := fourier_gradeSupport_subset Q hgrade
    rcases Finset.mem_image.mp hsubset with ⟨g, hg, hgd⟩
    rcases Finset.mem_image.mp hg with ⟨e, he, heg⟩
    have hde : grade d = -grade e := by simpa [heg] using hgd.symm
    rw [hde]
    exact neg_nonpos.mpr (hQ e he)
  exact no_exact_pair_both_nonpositive (fourierAlgHom ℂ P) (fourierAlgHom ℂ Q) hP' hQ' hcomm

end Dixmier.Weyl
