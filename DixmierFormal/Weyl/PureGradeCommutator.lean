module

public import DixmierFormal.Weyl.PoissonEndpoints

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

namespace Dixmier.Weyl
open Polynomial

variable {K : Type*} [Field K]

private theorem exponent_eq_of_grade_totalWeight
    (d e : Fin 2 →₀ ℕ)
    (hgrade : grade d = grade e)
    (hweight : Finsupp.weight (wt 1 1) d = Finsupp.weight (wt 1 1) e) : d = e := by
  have hsum : (d 0 : ℤ) + d 1 = (e 0 : ℤ) + e 1 := by
    rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum] at hweight
    simpa [wt] using hweight
  have hdiff : (d 0 : ℤ) - d 1 = (e 0 : ℤ) - e 1 := by
    simpa [grade] using hgrade
  have h0 : (d 0 : ℤ) = e 0 := by omega
  have h1 : (d 1 : ℤ) = e 1 := by omega
  apply Finsupp.ext
  intro i
  fin_cases i
  · exact_mod_cast h0
  · exact_mod_cast h1

private theorem totalLeadingForm_ne_zero [CharZero K]
    (T : A1 K) (hT : T ≠ 0) : leadingForm 1 1 (T : Module.End K K[X]) ≠ 0 := by
  have hsymbol0 : symbol ((0 : A1 K) : Module.End K K[X]) = 0 := by
    classical
    simp [symbol, pbwCoeff, coeffPoly]
  have hsymbol : symbol (T : Module.End K K[X]) ≠ 0 := by
    intro hz
    have hzero : T = 0 := symbol_injective (P := T) (Q := 0) (by
      rw [hsymbol0]
      exact hz)
    exact hT hzero
  have hnotbot : MvPolynomial.weightedTotalDegree' (wt 1 1)
      (symbol (T : Module.End K K[X])) ≠ ⊥ := by
    intro hb
    exact hsymbol ((MvPolynomial.weightedTotalDegree'_eq_bot_iff _ _).mp hb)
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hnotbot
  have hdeg : MvPolynomial.weightedTotalDegree' (wt 1 1)
      (symbol (T : Module.End K K[X])) = (vDeg 1 1 (T : Module.End K K[X]) : WithBot ℤ) := by
    unfold vDeg
    rw [← hm, WithBot.unbotD_coe]
  exact weightedComponent_ne_zero_of_weightedTotalDegree_eq (wt 1 1)
    (symbol (T : Module.End K K[X])) (vDeg 1 1 (T : Module.End K K[X])) hdeg

private theorem totalLeadingForm_monomial [CharZero K]
    (T : A1 K) (hT : T ≠ 0) (j : ℤ)
    (hgrade : ∀ d ∈ (symbol (T : Module.End K K[X])).support, grade d = j) :
    ∃ d a, leadingForm 1 1 (T : Module.End K K[X]) = MvPolynomial.monomial d a ∧
      a ≠ 0 ∧ grade d = j := by
  classical
  let F := leadingForm 1 1 (T : Module.End K K[X])
  have hF : F ≠ 0 := totalLeadingForm_ne_zero T hT
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hF
  have hd' : d ∈ (symbol (T : Module.End K K[X])).support ∧
      Finsupp.weight (wt 1 1) d = vDeg 1 1 (T : Module.End K K[X]) := by
    change d ∈ (MvPolynomial.weightedHomogeneousComponent (wt 1 1)
      (vDeg 1 1 (T : Module.End K K[X])) (symbol (T : Module.End K K[X]))).support at hd
    rw [MvPolynomial.support_weightedHomogeneousComponent] at hd
    exact Finset.mem_filter.mp hd
  have hgd : grade d = j := hgrade d hd'.1
  have hsub : ∀ e ∈ F.support, e = d := by
    intro e he
    have he' : e ∈ (symbol (T : Module.End K K[X])).support ∧
        Finsupp.weight (wt 1 1) e = vDeg 1 1 (T : Module.End K K[X]) := by
      change e ∈ (MvPolynomial.weightedHomogeneousComponent (wt 1 1)
        (vDeg 1 1 (T : Module.End K K[X])) (symbol (T : Module.End K K[X]))).support at he
      rw [MvPolynomial.support_weightedHomogeneousComponent] at he
      exact Finset.mem_filter.mp he
    have hge : grade e = grade d := (hgrade e he'.1).trans hgd.symm
    have hweight : Finsupp.weight (wt 1 1) e = Finsupp.weight (wt 1 1) d :=
      he'.2.trans hd'.2.symm
    have hde : e = d := exponent_eq_of_grade_totalWeight e d hge hweight
    simp [hde]
  have hmono : F = MvPolynomial.monomial d (MvPolynomial.coeff d F) :=
    MvPolynomial.eq_monomial_of_support_subset_singleton hsub
  refine ⟨d, MvPolynomial.coeff d F, ?_, ?_, hgd⟩
  · simpa [F] using hmono
  · exact MvPolynomial.mem_support_iff.mp hd

private theorem monomial_poisson_ne_zero
    (d e : Fin 2 →₀ ℕ) (a b : ℂ) (hdet : (d 1 : ℂ) * (e 0 : ℂ) -
        (d 0 : ℂ) * (e 1 : ℂ) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    poisson (MvPolynomial.monomial d a) (MvPolynomial.monomial e b) ≠ 0 := by
  rw [poisson_monomial_general, MvPolynomial.smul_monomial]
  exact mt MvPolynomial.monomial_eq_zero.mp (mul_ne_zero hdet (mul_ne_zero ha hb))

/-- Nonzero operators supported in grades `-1` and `j>0` cannot commute.
The proof compares their total-degree leading monomials and applies the exact Weyl leading-commutator law. -/
theorem pureGrade_minusOne_positive_commutator_ne_zero
    (P Q : A1 ℂ) (j : ℕ) (hj : 0 < j)
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hPgrade : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d = -1)
    (hQgrade : ∀ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, grade d = (j : ℤ)) :
    Q * P - P * Q ≠ 0 := by
  obtain ⟨d, a, hQform, ha, hdgrade⟩ := totalLeadingForm_monomial Q hQ (j : ℤ) hQgrade
  obtain ⟨e, b, hPform, hb, hegrade⟩ := totalLeadingForm_monomial P hP (-1) hPgrade
  have hdcoord : d 0 = d 1 + j := by
    have h := hdgrade
    simp [grade] at h
    omega
  have hecoord : e 1 = e 0 + 1 := by
    have h := hegrade
    simp [grade] at h
    omega
  have hdet : (d 1 : ℂ) * (e 0 : ℂ) - (d 0 : ℂ) * (e 1 : ℂ) ≠ 0 := by
    have hmul : 0 < j * (e 0 + 1) := Nat.mul_pos hj (Nat.succ_pos _)
    have hpos : 0 < d 1 + j * (e 0 + 1) := by omega
    have hcast : ((d 1 + j * (e 0 + 1) : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hpos)
    have hformula : (d 1 : ℂ) * (e 0 : ℂ) - (d 0 : ℂ) * (e 1 : ℂ) =
        -((d 1 + j * (e 0 + 1) : ℕ) : ℂ) := by
      rw [hdcoord, hecoord]
      push_cast
      ring
    rw [hformula]
    exact neg_ne_zero.mpr hcast
  have hbr : poisson (leadingForm 1 1 (Q : Module.End ℂ ℂ[X]))
      (leadingForm 1 1 (P : Module.End ℂ ℂ[X])) ≠ 0 := by
    rw [hQform, hPform]
    exact monomial_poisson_ne_zero d e a b hdet ha hb
  intro hcomm
  have htop := leadingForm_commutator P Q 1 1 (by norm_num) hbr
  have htopzero : leadingForm 1 1 ((Q * P - P * Q : A1 ℂ) : Module.End ℂ ℂ[X]) = 0 := by
    rw [hcomm]
    simp [leadingForm, vDeg, symbol, pbwCoeff, coeffPoly]
  rw [htopzero] at htop
  exact hbr htop.2.symm

end Dixmier.Weyl
