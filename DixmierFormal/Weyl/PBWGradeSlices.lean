module

public import DixmierFormal.Weyl.PositiveGradeNormalForms
public import DixmierFormal.Weyl.PureGradeCommutator
public import DixmierFormal.Weyl.OneSidedGradeBasic
public import Mathlib.Algebra.MvPolynomial.CommRing

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

namespace Dixmier.Weyl

open Polynomial

private theorem pbwCoeff_sub
    (T S : A1 ℂ) (i j : ℕ) :
    pbwCoeff ((T - S : A1 ℂ) : Module.End ℂ ℂ[X]) i j =
      pbwCoeff (T : Module.End ℂ ℂ[X]) i j - pbwCoeff (S : Module.End ℂ ℂ[X]) i j := by
  simp [pbwCoeff, coeffPoly, Polynomial.coeff_sub,
    Finset.sum_sub_distrib, mul_sub]

/-- Products of operators supported in single grades remain in the sum grade. This follows
coefficient-by-coefficient from the exact PBW product decomposition. -/
theorem symbol_mul_grade_eq
    (P Q : A1 ℂ) (g h : ℤ)
    (hP : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d = g)
    (hQ : ∀ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, grade d = h) :
    ∀ d ∈ (symbol ((P * Q : A1 ℂ) : Module.End ℂ ℂ[X])).support,
      grade d = g + h := by
  intro d hd
  obtain ⟨e, he, f, hf, hgrade⟩ := symbol_mul_grade_decomposition P Q d hd
  rw [hgrade, hP e he, hQ f hf]

/-- The difference of two operators supported in a common exact grade is supported in that
same grade. -/
theorem symbol_sub_grade_eq
    (P Q : A1 ℂ) (g : ℤ)
    (hP : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d = g)
    (hQ : ∀ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, grade d = g) :
    ∀ d ∈ (symbol ((P - Q : A1 ℂ) : Module.End ℂ ℂ[X])).support,
      grade d = g := by
  intro d hd
  obtain ⟨p, hdp⟩ := expo_surjective d
  obtain ⟨i, j⟩ := p
  have hpbw : pbwCoeff ((P - Q : A1 ℂ) : Module.End ℂ ℂ[X]) i j ≠ 0 := by
    have hcoeff := MvPolynomial.mem_support_iff.mp hd
    rw [← hdp, symbol_coeff_pbwCoeff] at hcoeff
    exact hcoeff
  have hcoord : grade (expo i j) = (i : ℤ) - j := by simp [grade, expo]
  have hgd : grade (expo i j) = grade d := congrArg grade hdp
  by_contra hnot
  have hPzero : pbwCoeff (P : Module.End ℂ ℂ[X]) i j = 0 := by
    by_contra hne
    have hs : expo i j ∈ (symbol (P : Module.End ℂ ℂ[X])).support := by
      rw [MvPolynomial.mem_support_iff, symbol_coeff_pbwCoeff]
      exact hne
    have h := hP (expo i j) hs
    exact hnot (hgd.symm.trans h)
  have hQzero : pbwCoeff (Q : Module.End ℂ ℂ[X]) i j = 0 := by
    by_contra hne
    have hs : expo i j ∈ (symbol (Q : Module.End ℂ ℂ[X])).support := by
      rw [MvPolynomial.mem_support_iff, symbol_coeff_pbwCoeff]
      exact hne
    have h := hQ (expo i j) hs
    exact hnot (hgd.symm.trans h)
  rw [pbwCoeff_sub, hPzero, hQzero] at hpbw
  norm_num at hpbw

noncomputable def gradeFilteredCoeffs (c : (ℕ × ℕ) →₀ ℂ) (g : ℤ) :
    (ℕ × ℕ) →₀ ℂ :=
  c.filter (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = g)

noncomputable def gradeFilteredSum (c : (ℕ × ℕ) →₀ ℂ) (g : ℤ) :
    Module.End ℂ ℂ[X] :=
  (gradeFilteredCoeffs c g).sum
    (fun p a => a • normalOrderedMonomial (K := ℂ) p.1 p.2)

theorem gradeFilteredSum_mem (c : (ℕ × ℕ) →₀ ℂ) (g : ℤ) :
    gradeFilteredSum c g ∈ A1 ℂ := by
  change gradeFilteredSum c g ∈ (A1 ℂ).toSubmodule
  apply normalOrderedSpan_le_A1
  classical
  change (gradeFilteredCoeffs c g).sum
    (fun p a => a • normalOrderedMonomial (K := ℂ) p.1 p.2) ∈
      normalOrderedSpan (K := ℂ)
  rw [Finsupp.sum]
  apply Submodule.sum_mem
  intro p hp
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨p, rfl⟩

noncomputable def gradeFilteredElement
    (c : (ℕ × ℕ) →₀ ℂ) (g : ℤ) : A1 ℂ :=
  ⟨gradeFilteredSum c g, gradeFilteredSum_mem c g⟩

private theorem gradeFilteredElement_pbwCoeff
    (c : (ℕ × ℕ) →₀ ℂ) (g : ℤ) (i j : ℕ) :
    pbwCoeff (gradeFilteredElement c g : Module.End ℂ ℂ[X]) i j =
      if (i : ℤ) - j = g then c (i,j) else 0 := by
  change pbwCoeff (gradeFilteredSum c g) i j = _
  rw [gradeFilteredSum]
  rw [pbwCoeff_finsuppNormalOrderedSum]
  simp [gradeFilteredCoeffs, Finsupp.filter_apply]

private theorem gradeFilteredElement_has_grade
    (c : (ℕ × ℕ) →₀ ℂ) (g : ℤ) :
    ∀ d ∈ (symbol (gradeFilteredElement c g : Module.End ℂ ℂ[X])).support,
      grade d = g := by
  intro d hd
  obtain ⟨⟨i,j⟩, he⟩ := expo_surjective d
  change expo i j = d at he
  have hcoeff : MvPolynomial.coeff d
      (symbol (gradeFilteredElement c g : Module.End ℂ ℂ[X])) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  rw [← he, symbol_coeff_pbwCoeff] at hcoeff
  rw [gradeFilteredElement_pbwCoeff] at hcoeff
  by_cases h : (i : ℤ) - j = g
  · have hegrade : grade d = (i : ℤ) - j := by
      rw [← he]
      simp [grade, expo]
    exact hegrade.trans h
  · simp [h] at hcoeff

/-- Every operator has a source-grade slice in `A1`: it retains exactly the PBW coefficients of
one grade, and its symbol support lies entirely in that grade. -/
theorem exists_exact_grade_projection
    (T : A1 ℂ) (g : ℤ) :
    ∃ S : A1 ℂ,
      (∀ d ∈ (symbol (S : Module.End ℂ ℂ[X])).support, grade d = g) ∧
      (∀ i j, pbwCoeff (S : Module.End ℂ ℂ[X]) i j =
        if (i : ℤ) - j = g then pbwCoeff (T : Module.End ℂ ℂ[X]) i j else 0) := by
  classical
  obtain ⟨c, hc⟩ := A1_exists_finiteNormalOrderedExpansion T
  refine ⟨gradeFilteredElement c g, gradeFilteredElement_has_grade c g, ?_⟩
  intro i j
  rw [gradeFilteredElement_pbwCoeff]
  have hcoeff : pbwCoeff (T : Module.End ℂ ℂ[X]) i j = c (i,j) := by
    rw [← hc]
    exact pbwCoeff_finsuppNormalOrderedSum c i j
  by_cases h : (i : ℤ) - j = g
  · simp [h, hcoeff]
  · simp [h]

/-- Removing the exact grade-`g` projection from an operator whose grades are at most `g`
leaves only grades at most `g-1`. -/
theorem grade_projection_remainder_le
    (T S : A1 ℂ) (g : ℤ)
    (hT : ∀ d ∈ (symbol (T : Module.End ℂ ℂ[X])).support, grade d ≤ g)
    (hScoeff : ∀ i j, pbwCoeff (S : Module.End ℂ ℂ[X]) i j =
      if (i : ℤ) - j = g then pbwCoeff (T : Module.End ℂ ℂ[X]) i j else 0) :
    ∀ d ∈ (symbol ((T - S : A1 ℂ) : Module.End ℂ ℂ[X])).support,
      grade d ≤ g - 1 := by
  intro d hd
  obtain ⟨p, hdp⟩ := expo_surjective d
  obtain ⟨i, j⟩ := p
  have hpbw : pbwCoeff ((T - S : A1 ℂ) : Module.End ℂ ℂ[X]) i j ≠ 0 := by
    have hcoeff := MvPolynomial.mem_support_iff.mp hd
    rw [← hdp, symbol_coeff_pbwCoeff] at hcoeff
    exact hcoeff
  have hcoord : grade (expo i j) = (i : ℤ) - j := by simp [grade, expo]
  have hgd : grade (expo i j) = grade d := congrArg grade hdp
  have hneq : grade d ≠ g := by
    intro hEq
    have hEq' : (i : ℤ) - j = g := by rw [← hcoord, hgd, hEq]
    rw [pbwCoeff_sub, hScoeff, if_pos hEq'] at hpbw
    simp at hpbw
  have hSzero : pbwCoeff (S : Module.End ℂ ℂ[X]) i j = 0 := by
    rw [hScoeff, if_neg (by
      intro hEq
      apply hneq
      rw [← hgd, hcoord, hEq])]
  have hTnonzero : pbwCoeff (T : Module.End ℂ ℂ[X]) i j ≠ 0 := by
    intro hzero
    rw [pbwCoeff_sub, hzero, hSzero] at hpbw
    norm_num at hpbw
  have hTsupport : expo i j ∈ (symbol (T : Module.End ℂ ℂ[X])).support := by
    rw [MvPolynomial.mem_support_iff, symbol_coeff_pbwCoeff]
    exact hTnonzero
  have hupper := hT (expo i j) hTsupport
  rw [hgd] at hupper
  omega

private theorem pbwCoeff_zero_of_grade_upper
    (T : A1 ℂ) (b : ℤ) (i j : ℕ)
    (hT : ∀ d ∈ (symbol (T : Module.End ℂ ℂ[X])).support, grade d ≤ b)
    (hgrade : b < (i : ℤ) - j) :
    pbwCoeff (T : Module.End ℂ ℂ[X]) i j = 0 := by
  by_contra hne
  have hs : expo i j ∈ (symbol (T : Module.End ℂ ℂ[X])).support := by
    rw [MvPolynomial.mem_support_iff, symbol_coeff_pbwCoeff]
    exact hne
  have hupper := hT (expo i j) hs
  have hcoord : grade (expo i j) = (i : ℤ) - j := by simp [grade, expo]
  rw [hcoord] at hupper
  omega

/-- At the sum of the maximal grades, the PBW coefficient of the full commutator is exactly
the coefficient of the commutator of the two exact top-grade slices. All cross terms have
strictly lower grade by `grade_projection_remainder_le` and `symbol_mul_grade_le`. -/
theorem top_grade_commutator_coeff_eq
    (P Q Ptop Qtop : A1 ℂ) (m n : ℤ) (i j : ℕ)
    (hP : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d ≤ m)
    (hQ : ∀ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, grade d ≤ n)
    (hPtop : ∀ d ∈ (symbol (Ptop : Module.End ℂ ℂ[X])).support, grade d = m)
    (hQtop : ∀ d ∈ (symbol (Qtop : Module.End ℂ ℂ[X])).support, grade d = n)
    (hPcoeff : ∀ i j, pbwCoeff (Ptop : Module.End ℂ ℂ[X]) i j =
      if (i : ℤ) - j = m then pbwCoeff (P : Module.End ℂ ℂ[X]) i j else 0)
    (hQcoeff : ∀ i j, pbwCoeff (Qtop : Module.End ℂ ℂ[X]) i j =
      if (i : ℤ) - j = n then pbwCoeff (Q : Module.End ℂ ℂ[X]) i j else 0)
    (hij : (i : ℤ) - j = m + n) :
    pbwCoeff ((Q * P - P * Q : A1 ℂ) : Module.End ℂ ℂ[X]) i j =
      pbwCoeff ((Qtop * Ptop - Ptop * Qtop : A1 ℂ) : Module.End ℂ ℂ[X]) i j := by
  let Plo : A1 ℂ := P - Ptop
  let Qlo : A1 ℂ := Q - Qtop
  have hPlo : ∀ d ∈ (symbol (Plo : Module.End ℂ ℂ[X])).support, grade d ≤ m - 1 := by
    exact grade_projection_remainder_le P Ptop m hP hPcoeff
  have hQlo : ∀ d ∈ (symbol (Qlo : Module.End ℂ ℂ[X])).support, grade d ≤ n - 1 := by
    exact grade_projection_remainder_le Q Qtop n hQ hQcoeff
  have hQPlo : ∀ d ∈ (symbol ((Qlo * P : A1 ℂ) : Module.End ℂ ℂ[X])).support,
      grade d ≤ m + n - 1 := by
    intro d hd
    have h := symbol_mul_grade_le Qlo P (n - 1) m hQlo hP d hd
    omega
  have hQtopPlo : ∀ d ∈ (symbol ((Qtop * Plo : A1 ℂ) : Module.End ℂ ℂ[X])).support,
      grade d ≤ m + n - 1 := by
    intro d hd
    have hQtop' : ∀ e ∈ (symbol (Qtop : Module.End ℂ ℂ[X])).support, grade e ≤ n :=
      fun e he => le_of_eq (hQtop e he)
    have h := symbol_mul_grade_le Qtop Plo n (m - 1) hQtop' hPlo d hd
    omega
  have hPloQ : ∀ d ∈ (symbol ((Plo * Q : A1 ℂ) : Module.End ℂ ℂ[X])).support,
      grade d ≤ m + n - 1 := by
    intro d hd
    have h := symbol_mul_grade_le Plo Q (m - 1) n hPlo hQ d hd
    omega
  have hPtopQlo : ∀ d ∈ (symbol ((Ptop * Qlo : A1 ℂ) : Module.End ℂ ℂ[X])).support,
      grade d ≤ m + n - 1 := by
    intro d hd
    have hPtop' : ∀ e ∈ (symbol (Ptop : Module.End ℂ ℂ[X])).support, grade e ≤ m :=
      fun e he => le_of_eq (hPtop e he)
    have h := symbol_mul_grade_le Ptop Qlo m (n - 1) hPtop' hQlo d hd
    omega
  have hzeroQPlo : pbwCoeff ((Qlo * P : A1 ℂ) : Module.End ℂ ℂ[X]) i j = 0 :=
    pbwCoeff_zero_of_grade_upper (Qlo * P) (m + n - 1) i j hQPlo (by omega)
  have hzeroQtopPlo : pbwCoeff ((Qtop * Plo : A1 ℂ) : Module.End ℂ ℂ[X]) i j = 0 :=
    pbwCoeff_zero_of_grade_upper (Qtop * Plo) (m + n - 1) i j hQtopPlo (by omega)
  have hzeroPloQ : pbwCoeff ((Plo * Q : A1 ℂ) : Module.End ℂ ℂ[X]) i j = 0 :=
    pbwCoeff_zero_of_grade_upper (Plo * Q) (m + n - 1) i j hPloQ (by omega)
  have hzeroPtopQlo : pbwCoeff ((Ptop * Qlo : A1 ℂ) : Module.End ℂ ℂ[X]) i j = 0 :=
    pbwCoeff_zero_of_grade_upper (Ptop * Qlo) (m + n - 1) i j hPtopQlo (by omega)
  have hPsplit : Ptop + Plo = P := by
    dsimp [Plo]
    abel
  have hQsplit : Qtop + Qlo = Q := by
    dsimp [Qlo]
    abel
  have hExpand : Q * P - P * Q =
      (Qtop * Ptop - Ptop * Qtop) +
        (Qlo * P + Qtop * Plo - Plo * Q - Ptop * Qlo) := by
    rw [← hQsplit, ← hPsplit]
    simp only [mul_add, add_mul]
    abel
  have hcross : pbwCoeff
      ((Qlo * P + Qtop * Plo - Plo * Q - Ptop * Qlo : A1 ℂ) : Module.End ℂ ℂ[X]) i j = 0 := by
    rw [pbwCoeff_sub, pbwCoeff_sub, Subalgebra.coe_add, pbwCoeff_add,
      hzeroQPlo, hzeroQtopPlo, hzeroPloQ, hzeroPtopQlo]
    ring
  calc
    pbwCoeff ((Q * P - P * Q : A1 ℂ) : Module.End ℂ ℂ[X]) i j =
        pbwCoeff (((Qtop * Ptop - Ptop * Qtop) +
          (Qlo * P + Qtop * Plo - Plo * Q - Ptop * Qlo) : A1 ℂ) : Module.End ℂ ℂ[X]) i j := by
      rw [hExpand]
    _ = pbwCoeff ((Qtop * Ptop - Ptop * Qtop : A1 ℂ) : Module.End ℂ ℂ[X]) i j +
        pbwCoeff ((Qlo * P + Qtop * Plo - Plo * Q - Ptop * Qlo : A1 ℂ) : Module.End ℂ ℂ[X]) i j :=
      pbwCoeff_add _ _ _ _
    _ = pbwCoeff ((Qtop * Ptop - Ptop * Qtop : A1 ℂ) : Module.End ℂ ℂ[X]) i j := by
      rw [hcross, add_zero]

/-- If the highest grades of an exact source-order pair are `-1` and `+1`, then the
commutator of those two exact grade slices is itself exactly one. The full commutator's
grade-zero coefficients agree with the slice commutator by the top-grade coefficient
comparison; the slice commutator has no other grades. -/
theorem adjacent_top_grade_commutator_eq_one
    (P Q Ptop Qtop : A1 ℂ)
    (hpair : P * Q - Q * P = 1)
    (hP : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d ≤ -1)
    (hQ : ∀ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, grade d ≤ 1)
    (hPtop : ∀ d ∈ (symbol (Ptop : Module.End ℂ ℂ[X])).support, grade d = -1)
    (hQtop : ∀ d ∈ (symbol (Qtop : Module.End ℂ ℂ[X])).support, grade d = 1)
    (hPcoeff : ∀ i j, pbwCoeff (Ptop : Module.End ℂ ℂ[X]) i j =
      if (i : ℤ) - j = -1 then pbwCoeff (P : Module.End ℂ ℂ[X]) i j else 0)
    (hQcoeff : ∀ i j, pbwCoeff (Qtop : Module.End ℂ ℂ[X]) i j =
      if (i : ℤ) - j = 1 then pbwCoeff (Q : Module.End ℂ ℂ[X]) i j else 0) :
    Ptop * Qtop - Qtop * Ptop = 1 := by
  let Ctop : A1 ℂ := Ptop * Qtop - Qtop * Ptop
  have hCgrade : ∀ d ∈ (symbol (Ctop : Module.End ℂ ℂ[X])).support, grade d = 0 := by
    apply symbol_sub_grade_eq
    · exact symbol_mul_grade_eq Ptop Qtop (-1) 1 hPtop hQtop
    · exact symbol_mul_grade_eq Qtop Ptop 1 (-1) hQtop hPtop
  have hOneCoeff (i j : ℕ) :
      pbwCoeff ((1 : A1 ℂ) : Module.End ℂ ℂ[X]) i j =
        if i = 0 ∧ j = 0 then 1 else 0 := by
    simpa [normalOrderedMonomial] using
      (pbwCoeff_normalOrdered_monomial (K := ℂ) 0 0 i j)
  have hcoeff (i j : ℕ) :
      pbwCoeff (Ctop : Module.End ℂ ℂ[X]) i j =
        pbwCoeff ((1 : A1 ℂ) : Module.End ℂ ℂ[X]) i j := by
    by_cases hgrade : (i : ℤ) - j = 0
    · have htop := top_grade_commutator_coeff_eq Q P Qtop Ptop 1 (-1) i j
        hQ hP hQtop hPtop hQcoeff hPcoeff (by omega)
      change pbwCoeff ((P * Q - Q * P : A1 ℂ) : Module.End ℂ ℂ[X]) i j = _ at htop
      rw [hpair] at htop
      exact htop.symm
    · have hslice : pbwCoeff (Ctop : Module.End ℂ ℂ[X]) i j = 0 := by
        by_contra hne
        have hd : expo i j ∈ (symbol (Ctop : Module.End ℂ ℂ[X])).support := by
          rw [MvPolynomial.mem_support_iff, symbol_coeff_pbwCoeff]
          exact hne
        have hc := hCgrade (expo i j) hd
        have hcoord : grade (expo i j) = (i : ℤ) - j := by simp [grade, expo]
        exact hgrade (hcoord.symm.trans hc)
      have hone : pbwCoeff ((1 : A1 ℂ) : Module.End ℂ ℂ[X]) i j = 0 := by
        rw [hOneCoeff]
        have hnot : ¬(i = 0 ∧ j = 0) := by
          rintro ⟨rfl, rfl⟩
          exact hgrade (by norm_num)
        simp [hnot]
      rw [hslice, hone]
  apply symbol_injective
  apply MvPolynomial.ext
  intro d
  obtain ⟨⟨i, j⟩, hd⟩ := expo_surjective d
  rw [← hd, symbol_coeff_pbwCoeff, symbol_coeff_pbwCoeff]
  exact hcoeff i j

private theorem symbol_neg_A1 (T : A1 ℂ) :
    symbol ((-T : A1 ℂ) : Module.End ℂ ℂ[X]) =
      -symbol (T : Module.End ℂ ℂ[X]) := by
  have h : (-T : A1 ℂ) = (-1 : ℂ) • T := (neg_one_smul ℂ T).symm
  rw [h, symbol_smul]
  simp

private theorem pbwCoeff_neg_A1 (T : A1 ℂ) (i j : ℕ) :
    pbwCoeff ((-T : A1 ℂ) : Module.End ℂ ℂ[X]) i j =
      -pbwCoeff (T : Module.End ℂ ℂ[X]) i j := by
  change pbwCoeff (-(T : Module.End ℂ ℂ[X])) i j = _
  rw [show -(T : Module.End ℂ ℂ[X]) =
      (-1 : ℂ) • (T : Module.End ℂ ℂ[X]) by exact (neg_one_smul ℂ _).symm,
    pbwCoeff_smul]
  simp

/-- An exact Weyl pair cannot have highest grades `-1` and `j>1` when the projected top-grade
components are nonzero. The top-grade coefficient comparison reduces the full relation to the
nonzero commutator of those two components, while the scalar identity has only grade zero. -/
theorem exact_pair_excludes_top_grade_minusOne_positive
    (P Q Ptop Qtop : A1 ℂ) (j : ℕ) (hj : 1 < j)
    (hpair : Q * P - P * Q = 1)
    (hP : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d ≤ -1)
    (hQ : ∀ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, grade d ≤ (j : ℤ))
    (hPtop : ∀ d ∈ (symbol (Ptop : Module.End ℂ ℂ[X])).support, grade d = -1)
    (hQtop : ∀ d ∈ (symbol (Qtop : Module.End ℂ ℂ[X])).support, grade d = (j : ℤ))
    (hPtop_ne : Ptop ≠ 0) (hQtop_ne : Qtop ≠ 0)
    (hPcoeff : ∀ a b, pbwCoeff (Ptop : Module.End ℂ ℂ[X]) a b =
      if (a : ℤ) - b = -1 then pbwCoeff (P : Module.End ℂ ℂ[X]) a b else 0)
    (hQcoeff : ∀ a b, pbwCoeff (Qtop : Module.End ℂ ℂ[X]) a b =
      if (a : ℤ) - b = (j : ℤ) then pbwCoeff (Q : Module.End ℂ ℂ[X]) a b else 0) :
    False := by
  let Ctop : A1 ℂ := Qtop * Ptop - Ptop * Qtop
  have hCtop_ne : Ctop ≠ 0 := by
    exact pureGrade_minusOne_positive_commutator_ne_zero Ptop Qtop j (by omega)
      hPtop_ne hQtop_ne hPtop hQtop
  have hCtop_grade : ∀ d ∈ (symbol (Ctop : Module.End ℂ ℂ[X])).support,
      grade d = -1 + (j : ℤ) := by
    apply symbol_sub_grade_eq
    · intro d hd
      have h := symbol_mul_grade_eq Qtop Ptop (j : ℤ) (-1) hQtop hPtop d hd
      omega
    · intro d hd
      have h := symbol_mul_grade_eq Ptop Qtop (-1) (j : ℤ) hPtop hQtop d hd
      omega
  have hsymbol0 : symbol ((0 : A1 ℂ) : Module.End ℂ ℂ[X]) = 0 := by
    simp [symbol, pbwCoeff, coeffPoly]
  have hCtop_symbol_ne : symbol (Ctop : Module.End ℂ ℂ[X]) ≠ 0 := by
    intro hz
    apply hCtop_ne
    apply symbol_injective
    calc
      symbol (Ctop : Module.End ℂ ℂ[X]) = 0 := hz
      _ = symbol ((0 : A1 ℂ) : Module.End ℂ ℂ[X]) := hsymbol0.symm
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hCtop_symbol_ne
  obtain ⟨p, hdp⟩ := expo_surjective d
  obtain ⟨i, k⟩ := p
  have hcoeffTop : pbwCoeff (Ctop : Module.End ℂ ℂ[X]) i k ≠ 0 := by
    have hcoeff := MvPolynomial.mem_support_iff.mp hd
    rw [← hdp, symbol_coeff_pbwCoeff] at hcoeff
    exact hcoeff
  have hgradeCoord : (i : ℤ) - k = -1 + (j : ℤ) := by
    have hcoord : grade (expo i k) = (i : ℤ) - k := by simp [grade, expo]
    have hgd : grade (expo i k) = grade d := congrArg grade hdp
    calc
      (i : ℤ) - k = grade (expo i k) := hcoord.symm
      _ = grade d := hgd
      _ = -1 + (j : ℤ) := hCtop_grade d hd
  have htopCoeff := top_grade_commutator_coeff_eq P Q Ptop Qtop (-1) (j : ℤ) i k
    hP hQ hPtop hQtop hPcoeff hQcoeff (by omega)
  have hfull : pbwCoeff ((Q * P - P * Q : A1 ℂ) : Module.End ℂ ℂ[X]) i k =
      pbwCoeff (Ctop : Module.End ℂ ℂ[X]) i k := htopCoeff
  rw [hpair] at hfull
  have hone : pbwCoeff ((1 : A1 ℂ) : Module.End ℂ ℂ[X]) i k = 0 := by
    have hnotzero : ¬(i = 0 ∧ k = 0) := by
      intro h
      rcases h with ⟨rfl, rfl⟩
      simp at hgradeCoord
      omega
    have honeCoeff : pbwCoeff ((1 : A1 ℂ) : Module.End ℂ ℂ[X]) i k =
        if i = 0 ∧ k = 0 then 1 else 0 := by
      simpa [normalOrderedMonomial] using
        (pbwCoeff_normalOrdered_monomial (K := ℂ) 0 0 i k)
    rw [honeCoeff]
    simp [hnotzero]
  rw [hone] at hfull
  exact hcoeffTop hfull.symm

/-- The PBW symbol of the exact grade projection is the corresponding weighted homogeneous
component for the grade weight `(1,-1)`. -/
theorem symbol_exact_grade_projection
    (T : A1 ℂ) (g : ℤ) :
    ∃ S : A1 ℂ,
      (∀ d ∈ (symbol (S : Module.End ℂ ℂ[X])).support, grade d = g) ∧
      symbol (S : Module.End ℂ ℂ[X]) =
        MvPolynomial.weightedHomogeneousComponent (wt 1 (-1)) g
          (symbol (T : Module.End ℂ ℂ[X])) := by
  obtain ⟨S, hSgrade, hScoeff⟩ := exists_exact_grade_projection T g
  refine ⟨S, hSgrade, ?_⟩
  apply MvPolynomial.ext
  intro d
  obtain ⟨p, hd⟩ := expo_surjective d
  obtain ⟨i, j⟩ := p
  rw [← hd, symbol_coeff_pbwCoeff, hScoeff,
    MvPolynomial.coeff_weightedHomogeneousComponent, symbol_coeff_pbwCoeff]
  have hweight : Finsupp.weight (wt 1 (-1)) (expo i j) = (i : ℤ) - j := by
    rw [expo_weight]
    simp
    ring
  rw [← hweight]


/-- A nonempty grade of `T` gives a nonzero exact component in the projection above. -/
theorem exists_nonzero_exact_grade_projection
    (T : A1 ℂ) (g : ℤ)
    (hgrade : ∃ d ∈ (symbol (T : Module.End ℂ ℂ[X])).support, grade d = g) :
    ∃ S : A1 ℂ,
      S ≠ 0 ∧
      (∀ d ∈ (symbol (S : Module.End ℂ ℂ[X])).support, grade d = g) ∧
      (∀ i j, pbwCoeff (S : Module.End ℂ ℂ[X]) i j =
        if (i : ℤ) - j = g then pbwCoeff (T : Module.End ℂ ℂ[X]) i j else 0) := by
  obtain ⟨S, hSgrade, hScoeff⟩ := exists_exact_grade_projection T g
  refine ⟨S, ?_, hSgrade, hScoeff⟩
  intro hzero
  obtain ⟨d, hd, hgd⟩ := hgrade
  obtain ⟨⟨i,j⟩, he⟩ := expo_surjective d
  change expo i j = d at he
  have hij : (i : ℤ) - j = g := by
    have h := hgd
    rw [← he] at h
    simpa [grade, expo] using h
  have hcoeffT : pbwCoeff (T : Module.End ℂ ℂ[X]) i j ≠ 0 := by
    have hcoeff := MvPolynomial.mem_support_iff.mp hd
    rw [← he, symbol_coeff_pbwCoeff] at hcoeff
    exact hcoeff
  have hcoeffS : pbwCoeff (S : Module.End ℂ ℂ[X]) i j ≠ 0 := by
    rw [hScoeff i j]
    simp [hij, hcoeffT]
  have hcoeff0 : pbwCoeff (S : Module.End ℂ ℂ[X]) i j = 0 := by
    have hval : (S : Module.End ℂ ℂ[X]) = 0 := congrArg Subtype.val hzero
    rw [hval]
    simp [pbwCoeff, coeffPoly]
  exact hcoeffS hcoeff0

/-- The top-grade branch of Han--Tan's case `(a.2)` is impossible when the grade `-1`
component is nonmonomial. For `j=1`, the top slices satisfy the exact adjacent-grade relation,
so I128 forces singleton support. For `j>1`, I137 and the pure-grade commutator obstruction
exclude the pair. The remaining source adapter must identify its leading components with these
exact PBW projections. -/
theorem top_grade_source_case_nonmonomial_impossible
    (P Q Ptop Qtop : A1 ℂ) (j : ℕ) (hj : 0 < j)
    (hpair : P * Q - Q * P = 1)
    (hP : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d ≤ -1)
    (hQ : ∀ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, grade d ≤ (j : ℤ))
    (hPtop : ∀ d ∈ (symbol (Ptop : Module.End ℂ ℂ[X])).support, grade d = -1)
    (hQtop : ∀ d ∈ (symbol (Qtop : Module.End ℂ ℂ[X])).support, grade d = (j : ℤ))
    (hPtop_ne : Ptop ≠ 0) (hQtop_ne : Qtop ≠ 0)
    (hPcoeff : ∀ a b, pbwCoeff (Ptop : Module.End ℂ ℂ[X]) a b =
      if (a : ℤ) - b = -1 then pbwCoeff (P : Module.End ℂ ℂ[X]) a b else 0)
    (hQcoeff : ∀ a b, pbwCoeff (Qtop : Module.End ℂ ℂ[X]) a b =
      if (a : ℤ) - b = (j : ℤ) then pbwCoeff (Q : Module.End ℂ ℂ[X]) a b else 0)
    (hPtop_nonmonomial : 1 < (symbol (Ptop : Module.End ℂ ℂ[X])).support.card) :
    False := by
  by_cases hj1 : j = 1
  · subst j
    have htop := adjacent_top_grade_commutator_eq_one P Q Ptop Qtop hpair hP hQ
      hPtop hQtop hPcoeff (by simpa using hQcoeff)
    have htopEnd :
        (Ptop : Module.End ℂ ℂ[X]) * (Qtop : Module.End ℂ ℂ[X]) -
          (Qtop : Module.End ℂ ℂ[X]) * (Ptop : Module.End ℂ ℂ[X]) = 1 := by
      simpa using congrArg (fun R : A1 ℂ => (R : Module.End ℂ ℂ[X])) htop
    exact adjacent_grade_exact_pair_nonmonomial_impossible Ptop Qtop hPtop hQtop
      htopEnd hPtop_nonmonomial
  · have hj' : 1 < j := by omega
    have hPneg : ∀ d ∈ (symbol ((-P : A1 ℂ) : Module.End ℂ ℂ[X])).support,
        grade d ≤ -1 := by
      intro d hd
      have hneg := symbol_neg_A1 P
      have hsupport : (symbol ((-P : A1 ℂ) : Module.End ℂ ℂ[X])).support =
          (symbol (P : Module.End ℂ ℂ[X])).support := by
        rw [hneg, MvPolynomial.support_neg]
      have hd' : d ∈ (symbol (P : Module.End ℂ ℂ[X])).support := by
        rw [← hsupport]
        exact hd
      exact hP d hd'
    have hPtopneg : ∀ d ∈ (symbol ((-Ptop : A1 ℂ) : Module.End ℂ ℂ[X])).support,
        grade d = -1 := by
      intro d hd
      have hneg := symbol_neg_A1 Ptop
      have hsupport : (symbol ((-Ptop : A1 ℂ) : Module.End ℂ ℂ[X])).support =
          (symbol (Ptop : Module.End ℂ ℂ[X])).support := by
        rw [hneg, MvPolynomial.support_neg]
      have hd' : d ∈ (symbol (Ptop : Module.End ℂ ℂ[X])).support := by
        rw [← hsupport]
        exact hd
      exact hPtop d hd'
    have hPtopneg_ne : -Ptop ≠ 0 := by
      intro hz
      have hPzero : Ptop = 0 := by
        apply Subtype.ext
        have hzval := congrArg (fun R : A1 ℂ => (R : Module.End ℂ ℂ[X])) hz
        change -(Ptop : Module.End ℂ ℂ[X]) = 0 at hzval
        exact neg_eq_zero.mp hzval
      exact hPtop_ne hPzero
    have hPcoeffneg : ∀ a b, pbwCoeff ((-Ptop : A1 ℂ) : Module.End ℂ ℂ[X]) a b =
        if (a : ℤ) - b = -1 then
          pbwCoeff ((-P : A1 ℂ) : Module.End ℂ ℂ[X]) a b else 0 := by
      intro a b
      rw [pbwCoeff_neg_A1, hPcoeff, pbwCoeff_neg_A1]
      split_ifs <;> simp
    have hpairnegEnd :
        (Q : Module.End ℂ ℂ[X]) * (-(P : Module.End ℂ ℂ[X])) -
          (-(P : Module.End ℂ ℂ[X])) * (Q : Module.End ℂ ℂ[X]) = 1 := by
      have hnegP : -(P : Module.End ℂ ℂ[X]) =
          (-1 : ℂ) • (P : Module.End ℂ ℂ[X]) := (neg_one_smul ℂ _).symm
      have hnegQP : (-1 : ℂ) •
          ((Q : Module.End ℂ ℂ[X]) * (P : Module.End ℂ ℂ[X])) =
          -((Q : Module.End ℂ ℂ[X]) * (P : Module.End ℂ ℂ[X])) :=
        neg_one_smul ℂ ((Q : Module.End ℂ ℂ[X]) * (P : Module.End ℂ ℂ[X]))
      have hnegPQ : (-1 : ℂ) •
          ((P : Module.End ℂ ℂ[X]) * (Q : Module.End ℂ ℂ[X])) =
          -((P : Module.End ℂ ℂ[X]) * (Q : Module.End ℂ ℂ[X])) :=
        neg_one_smul ℂ ((P : Module.End ℂ ℂ[X]) * (Q : Module.End ℂ ℂ[X]))
      have hpairEnd := congrArg (fun R : A1 ℂ => (R : Module.End ℂ ℂ[X])) hpair
      calc
        _ = (-1 : ℂ) • ((Q : Module.End ℂ ℂ[X]) * (P : Module.End ℂ ℂ[X])) -
            (-1 : ℂ) • ((P : Module.End ℂ ℂ[X]) * (Q : Module.End ℂ ℂ[X])) := by
              rw [hnegP, mul_smul_comm, smul_mul_assoc]
        _ = (P : Module.End ℂ ℂ[X]) * (Q : Module.End ℂ ℂ[X]) -
            (Q : Module.End ℂ ℂ[X]) * (P : Module.End ℂ ℂ[X]) := by
              rw [hnegQP, hnegPQ]
              abel
        _ = 1 := hpairEnd
    have hpairneg : Q * (-P) - (-P) * Q = 1 := by
      apply Subtype.ext
      simpa only [Subalgebra.coe_neg, Subalgebra.coe_mul,
        Subalgebra.coe_sub, Subalgebra.coe_one] using hpairnegEnd
    exact exact_pair_excludes_top_grade_minusOne_positive (-P) Q (-Ptop) Qtop j hj'
      hpairneg hPneg hQ hPtopneg hQtop hPtopneg_ne hQtop_ne hPcoeffneg hQcoeff

/-- A top-grade contradiction stated directly in terms of the weighted leading component.
This wrapper constructs the exact PBW slices, so a source adapter only needs to provide the
grade bounds, a nonmonomial grade `-1` component, and a nonzero top grade `j>0` for the mate. -/
theorem weighted_top_grade_nonmonomial_pair_impossible
    (P Q : A1 ℂ) (j : ℕ) (hj : 0 < j)
    (hpair : P * Q - Q * P = 1)
    (hP : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d ≤ -1)
    (hQ : ∀ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, grade d ≤ (j : ℤ))
    (hPface : 1 < (MvPolynomial.weightedHomogeneousComponent (wt 1 (-1)) (-1)
      (symbol (P : Module.End ℂ ℂ[X]))).support.card)
    (hQgrade : ∃ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, grade d = (j : ℤ)) :
    False := by
  obtain ⟨Ptop, hPtop, hPsymbol⟩ := symbol_exact_grade_projection P (-1)
  obtain ⟨Qtop, hQtop_ne, hQtop, hQcoeff⟩ := exists_nonzero_exact_grade_projection Q j hQgrade
  have hPcoeff : ∀ i k, pbwCoeff (Ptop : Module.End ℂ ℂ[X]) i k =
      if (i : ℤ) - k = -1 then pbwCoeff (P : Module.End ℂ ℂ[X]) i k else 0 := by
    intro i k
    have h := congrArg (MvPolynomial.coeff (expo i k)) hPsymbol
    have hweight : Finsupp.weight (wt 1 (-1)) (expo i k) = (i : ℤ) - k := by
      rw [expo_weight]
      simp
      ring
    rw [symbol_coeff_pbwCoeff,
      MvPolynomial.coeff_weightedHomogeneousComponent,
      symbol_coeff_pbwCoeff, hweight] at h
    exact h
  have hPtop_nonmonomial : 1 < (symbol (Ptop : Module.End ℂ ℂ[X])).support.card := by
    rw [hPsymbol]
    exact hPface
  have hPtop_ne : Ptop ≠ 0 := by
    intro hz
    have hzero : symbol (Ptop : Module.End ℂ ℂ[X]) = 0 := by
      rw [hz]
      simp [symbol, pbwCoeff, coeffPoly]
    rw [hzero] at hPtop_nonmonomial
    simp at hPtop_nonmonomial
  exact top_grade_source_case_nonmonomial_impossible P Q Ptop Qtop j hj
    hpair hP hQ hPtop hQtop hPtop_ne hQtop_ne hPcoeff hQcoeff hPtop_nonmonomial

private theorem grade_eq_weight_one_neg_one (d : Fin 2 →₀ ℕ) :
    grade d = Finsupp.weight (wt 1 (-1)) d := by
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
  rw [expo_weight]
  simp [grade, expo]
  ring

private theorem symbol_weight_le_vDeg (T : A1 ℂ) (ρ σ : ℤ)
    (d : Fin 2 →₀ ℕ) (hd : d ∈ (symbol (T : Module.End ℂ ℂ[X])).support) :
    Finsupp.weight (wt ρ σ) d ≤ vDeg ρ σ (T : Module.End ℂ ℂ[X]) := by
  have hbound : (Finsupp.weight (wt ρ σ) d : WithBot ℤ) ≤
      MvPolynomial.weightedTotalDegree' (wt ρ σ)
        (symbol (T : Module.End ℂ ℂ[X])) := by
    change (Finsupp.weight (wt ρ σ) d : WithBot ℤ) ≤
      ((symbol (T : Module.End ℂ ℂ[X])).support.sup
        fun e => (Finsupp.weight (wt ρ σ) e : WithBot ℤ))
    exact Finset.le_sup
      (f := fun e : Fin 2 →₀ ℕ => (Finsupp.weight (wt ρ σ) e : WithBot ℤ)) hd
  exact WithBot.le_unbotD (a := 0) hbound

/-- The exact interface needed for Han--Tan case `(a.2)` in the project's PBW coordinates.
The source's face direction `(-1,1)` uses `(p,q)`, while the operator symbol here uses
`(q,p)`; after this coordinate swap it is the grade weight `(1,-1)`. If that leading face
contains the generator term `p` and is nonmonomial, its grade is exactly `-1`; all grades of
the first operator are therefore at most `-1`. The exact commutator then forces a positive
grade in the mate, and its finite support has a positive maximal grade. The weighted top-grade
contradiction closes the case without separately assuming these grade bounds or the mate's top
component. The only source facts left for the outer adapter are the leading-face identification,
the generator-term membership, and nonmonomiality. -/
theorem hanTan_case_a2_face_impossible
    (P Q : A1 ℂ)
    (hpair : P * Q - Q * P = 1)
    (hgen : expo 0 1 ∈
      (leadingForm 1 (-1) (P : Module.End ℂ ℂ[X])).support)
    (hnonmonomial : 1 <
      (leadingForm 1 (-1) (P : Module.End ℂ ℂ[X])).support.card) : False := by
  have hgenFilter : expo 0 1 ∈ (symbol (P : Module.End ℂ ℂ[X])).support ∧
      Finsupp.weight (wt 1 (-1)) (expo 0 1) =
        vDeg 1 (-1) (P : Module.End ℂ ℂ[X]) := by
    change expo 0 1 ∈ (MvPolynomial.weightedHomogeneousComponent (wt 1 (-1))
      (vDeg 1 (-1) (P : Module.End ℂ ℂ[X]))
      (symbol (P : Module.End ℂ ℂ[X]))).support at hgen
    rw [MvPolynomial.support_weightedHomogeneousComponent] at hgen
    exact Finset.mem_filter.mp hgen
  have hgenWeight : Finsupp.weight (wt 1 (-1)) (expo 0 1) = -1 := by
    rw [expo_weight]
    norm_num
  have hPmax : vDeg 1 (-1) (P : Module.End ℂ ℂ[X]) = -1 := by
    exact hgenFilter.2.symm.trans hgenWeight
  have hPgrade : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d ≤ -1 := by
    intro d hd
    have hbound := symbol_weight_le_vDeg P 1 (-1) d hd
    rw [hPmax] at hbound
    simpa [grade_eq_weight_one_neg_one] using hbound
  have hQpositive : ∃ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, 0 < grade d := by
    by_contra hn
    have hQnonpos : ∀ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, grade d ≤ 0 := by
      intro d hd
      have hnot : ¬ 0 < grade d := by
        intro hpos
        exact hn ⟨d, hd, hpos⟩
      omega
    have hPnonpos : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d ≤ 0 := by
      intro d hd
      exact le_trans (hPgrade d hd) (by norm_num)
    exact (no_exact_pair_both_nonpositive Q P hQnonpos hPnonpos) hpair
  have hQsupport : (symbol (Q : Module.End ℂ ℂ[X])).support.Nonempty := by
    rcases hQpositive with ⟨d, hd, _⟩
    exact ⟨d, hd⟩
  let jmax : ℤ := (symbol (Q : Module.End ℂ ℂ[X])).support.sup' hQsupport grade
  have hjmax : 0 < jmax := by
    rcases hQpositive with ⟨d, hd, hpos⟩
    dsimp [jmax]
    exact lt_of_lt_of_le hpos (Finset.le_sup' grade hd)
  obtain ⟨dmax, hdmax, hmax⟩ :=
    (symbol (Q : Module.End ℂ ℂ[X])).support.exists_mem_eq_sup' hQsupport grade
  let j : ℕ := jmax.toNat
  have hjcast : (j : ℤ) = jmax := by
    dsimp [j]
    exact Int.toNat_of_nonneg (le_of_lt hjmax)
  have hj : 0 < j := by omega
  have hQgradeBound :
      ∀ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, grade d ≤ (j : ℤ) := by
    intro d hd
    have hle : grade d ≤ jmax := by
      dsimp [jmax]
      exact Finset.le_sup' grade hd
    rw [hjcast]
    exact hle
  have hQgrade : ∃ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support,
      grade d = (j : ℤ) := by
    refine ⟨dmax, hdmax, ?_⟩
    have hmax' : jmax = grade dmax := by
      simpa [jmax] using hmax
    calc
      grade dmax = jmax := hmax'.symm
      _ = (j : ℤ) := hjcast.symm
  have hnonmonomial' : 1 <
      (MvPolynomial.weightedHomogeneousComponent (wt 1 (-1)) (-1)
        (symbol (P : Module.End ℂ ℂ[X]))).support.card := by
    simpa [leadingForm, hPmax] using hnonmonomial
  exact weighted_top_grade_nonmonomial_pair_impossible P Q j hj hpair
    hPgrade hQgradeBound hnonmonomial' hQgrade

def hanTanCoordinateSwap : Fin 2 → Fin 2 := Equiv.swap 0 1

private theorem hanTanCoordinateSwap_injective :
    Function.Injective hanTanCoordinateSwap := by
  exact Equiv.injective (Equiv.swap 0 1)

private theorem hanTanCoordinateSwap_expo (i j : ℕ) :
    Finsupp.mapDomain hanTanCoordinateSwap (expo i j) = expo j i := by
  ext k
  fin_cases k <;> simp [hanTanCoordinateSwap, expo]

private theorem hanTanCoordinateSwap_weight (d : Fin 2 →₀ ℕ) :
    Finsupp.weight (wt (-1) 1) (Finsupp.mapDomain hanTanCoordinateSwap d) =
      Finsupp.weight (wt 1 (-1)) d := by
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
  rw [hanTanCoordinateSwap_expo, expo_weight, expo_weight]
  ring

noncomputable def hanTanSourceSymbol (T : A1 ℂ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.rename hanTanCoordinateSwap (symbol (T : Module.End ℂ ℂ[X]))

noncomputable def hanTanSourceVDeg (T : A1 ℂ) : ℤ :=
  WithBot.unbotD 0
    (MvPolynomial.weightedTotalDegree' (wt (-1) 1) (hanTanSourceSymbol T))

private theorem hanTanSourceVDeg_eq (T : A1 ℂ) :
    hanTanSourceVDeg T = vDeg 1 (-1) (T : Module.End ℂ ℂ[X]) := by
  have hdegree :
      MvPolynomial.weightedTotalDegree' (wt (-1) 1) (hanTanSourceSymbol T) =
        MvPolynomial.weightedTotalDegree' (wt 1 (-1))
          (symbol (T : Module.End ℂ ℂ[X])) := by
    unfold hanTanSourceSymbol
    rw [MvPolynomial.weightedTotalDegree',
      MvPolynomial.support_rename_of_injective hanTanCoordinateSwap_injective,
      MvPolynomial.weightedTotalDegree']
    apply le_antisymm
    · rw [Finset.sup_le_iff]
      intro d hd
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
      simpa [hanTanCoordinateSwap_weight] using
        (Finset.le_sup (f := fun e : Fin 2 →₀ ℕ =>
          (Finsupp.weight (wt 1 (-1)) e : WithBot ℤ)) he)
    · rw [Finset.sup_le_iff]
      intro e he
      have hle :
          (Finsupp.weight (wt (-1) 1)
            (Finsupp.mapDomain hanTanCoordinateSwap e) : WithBot ℤ) ≤
            (Finset.image (Finsupp.mapDomain hanTanCoordinateSwap)
              ((symbol (T : Module.End ℂ ℂ[X])).support)).sup
                (fun d => (Finsupp.weight (wt (-1) 1) d : WithBot ℤ)) :=
        Finset.le_sup
          (f := fun d : Fin 2 →₀ ℕ =>
            (Finsupp.weight (wt (-1) 1) d : WithBot ℤ))
          (Finset.mem_image.mpr ⟨e, he, rfl⟩)
      simpa [hanTanCoordinateSwap_weight] using hle
  change WithBot.unbotD 0
      (MvPolynomial.weightedTotalDegree' (wt (-1) 1) (hanTanSourceSymbol T)) =
    WithBot.unbotD 0
      (MvPolynomial.weightedTotalDegree' (wt 1 (-1))
        (symbol (T : Module.End ℂ ℂ[X])))
  rw [hdegree]

noncomputable def hanTanSourceLeadingForm (T : A1 ℂ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.weightedHomogeneousComponent (wt (-1) 1) (hanTanSourceVDeg T)
    (hanTanSourceSymbol T)

noncomputable def hanTanSourceFace (T : A1 ℂ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.weightedHomogeneousComponent (wt (-1) 1) (-1) (hanTanSourceSymbol T)

/-- Swapping from the project's `(q,p)` PBW-symbol coordinates to Han--Tan's `(p,q)`
coordinates transports the `(-1,1)` face to the project's grade `-1` component. -/
private theorem hanTanSourceFace_support_eq (T : A1 ℂ) :
    (hanTanSourceFace T).support =
      Finset.image (Finsupp.mapDomain hanTanCoordinateSwap)
        (MvPolynomial.weightedHomogeneousComponent (wt 1 (-1)) (-1)
          (symbol (T : Module.End ℂ ℂ[X]))).support := by
  classical
  rw [hanTanSourceFace, MvPolynomial.support_weightedHomogeneousComponent]
  unfold hanTanSourceSymbol
  rw [MvPolynomial.support_rename_of_injective hanTanCoordinateSwap_injective,
    MvPolynomial.support_weightedHomogeneousComponent]
  ext d
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨e, he, rfl⟩, hweight⟩
    refine ⟨e, ?_, rfl⟩
    exact ⟨he, (hanTanCoordinateSwap_weight e).symm.trans hweight⟩
  · rintro ⟨e, he, hde⟩
    refine ⟨⟨e, he.1, hde⟩, ?_⟩
    rw [← hde, hanTanCoordinateSwap_weight]
    exact he.2

/-- Han--Tan's source-coordinate version of case `(a.2)` feeds directly into the exact PBW
terminal argument. The source variables are `(p,q)`; `hanTanSourceSymbol` swaps them from the
operator model's `(q,p)` coordinates. The generator term `p` and nonmonomiality therefore
become the grade `-1` face hypotheses proved impossible above. -/
theorem hanTan_case_a2_source_coordinates_impossible
    (P Q : A1 ℂ)
    (hpair : P * Q - Q * P = 1)
    (hgen : expo 1 0 ∈
      (hanTanSourceLeadingForm P).support)
    (hnonmonomial : 1 <
      (hanTanSourceLeadingForm P).support.card) : False := by
  have hgenFilter : expo 1 0 ∈ (hanTanSourceSymbol P).support ∧
      Finsupp.weight (wt (-1) 1) (expo 1 0) =
        hanTanSourceVDeg P := by
    change expo 1 0 ∈ (MvPolynomial.weightedHomogeneousComponent (wt (-1) 1)
      (hanTanSourceVDeg P) (hanTanSourceSymbol P)).support at hgen
    rw [MvPolynomial.support_weightedHomogeneousComponent] at hgen
    exact Finset.mem_filter.mp hgen
  have hgenWeight : Finsupp.weight (wt (-1) 1) (expo 1 0) = -1 := by
    rw [expo_weight]
    norm_num
  have hsourceMax : hanTanSourceVDeg P = -1 :=
    hgenFilter.2.symm.trans hgenWeight
  have hPmax : vDeg 1 (-1) (P : Module.End ℂ ℂ[X]) = -1 := by
    rw [← hanTanSourceVDeg_eq P]
    exact hsourceMax
  change expo 1 0 ∈ (MvPolynomial.weightedHomogeneousComponent (wt (-1) 1)
    (hanTanSourceVDeg P) (hanTanSourceSymbol P)).support at hgen
  rw [hsourceMax] at hgen
  have hsourceFaceGen : expo 1 0 ∈ (hanTanSourceFace P).support := by
    exact hgen
  change 1 < (MvPolynomial.weightedHomogeneousComponent (wt (-1) 1)
    (hanTanSourceVDeg P) (hanTanSourceSymbol P)).support.card at hnonmonomial
  rw [hsourceMax] at hnonmonomial
  have hsourceFaceNonmonomial : 1 < (hanTanSourceFace P).support.card := by
    exact hnonmonomial
  have hfaceSupport := hanTanSourceFace_support_eq P
  rw [hfaceSupport] at hsourceFaceGen
  obtain ⟨e, he, hmap⟩ := Finset.mem_image.mp hsourceFaceGen
  have hmapEq : Finsupp.mapDomain hanTanCoordinateSwap e =
      Finsupp.mapDomain hanTanCoordinateSwap (expo 0 1) := by
    calc
      Finsupp.mapDomain hanTanCoordinateSwap e = expo 1 0 := hmap
      _ = Finsupp.mapDomain hanTanCoordinateSwap (expo 0 1) :=
        (hanTanCoordinateSwap_expo 0 1).symm
  have heq : e = expo 0 1 :=
    Finsupp.mapDomain_injective hanTanCoordinateSwap_injective hmapEq
  subst e
  have hfaceGen : expo 0 1 ∈
      (MvPolynomial.weightedHomogeneousComponent (wt 1 (-1)) (-1)
        (symbol (P : Module.End ℂ ℂ[X]))).support := he
  have hfaceNonmonomial : 1 <
      (MvPolynomial.weightedHomogeneousComponent (wt 1 (-1)) (-1)
        (symbol (P : Module.End ℂ ℂ[X]))).support.card := by
    have hcard :
        (Finset.image (Finsupp.mapDomain hanTanCoordinateSwap)
          (MvPolynomial.weightedHomogeneousComponent (wt 1 (-1)) (-1)
            (symbol (P : Module.End ℂ ℂ[X]))).support).card =
          (MvPolynomial.weightedHomogeneousComponent (wt 1 (-1)) (-1)
            (symbol (P : Module.End ℂ ℂ[X]))).support.card :=
      Finset.card_image_of_injective _
        (Finsupp.mapDomain_injective hanTanCoordinateSwap_injective)
    have himage : 1 <
        (Finset.image (Finsupp.mapDomain hanTanCoordinateSwap)
          (MvPolynomial.weightedHomogeneousComponent (wt 1 (-1)) (-1)
            (symbol (P : Module.End ℂ ℂ[X]))).support).card := by
      simpa only [hfaceSupport] using hsourceFaceNonmonomial
    rw [hcard] at himage
    exact himage
  have hgenCurrent : expo 0 1 ∈
      (leadingForm 1 (-1) (P : Module.End ℂ ℂ[X])).support := by
    simpa [leadingForm, hPmax] using hfaceGen
  have hnonmonomialCurrent : 1 <
      (leadingForm 1 (-1) (P : Module.End ℂ ℂ[X])).support.card := by
    simpa [leadingForm, hPmax] using hfaceNonmonomial
  exact hanTan_case_a2_face_impossible P Q hpair hgenCurrent hnonmonomialCurrent

end Dixmier.Weyl
