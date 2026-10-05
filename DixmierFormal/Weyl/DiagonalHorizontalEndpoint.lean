/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.FourierDiagonalEndpoints
public import DixmierFormal.Weyl.HorizontalLastZeroExclusion

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Identification of the diagonal and horizontal endpoints

The preliminary companion's global X-bound identifies a rightmost
diagonal point with the highest point of the horizontal face. The exact
endpoint has nonzero grade; its negative sign gives the crossing case.
-/
namespace Dixmier.Weyl

/-- A rightmost positive-X diagonal point is the maximum-Y horizontal endpoint. -/
theorem preliminary_diagonal_first_point_horizontal_endpoint
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b : ℕ) (ha : 0<a)
    (hmem : expo a b ∈ (leadingForm 1 1 P.1).support)
    (hfirst : ∀ d ∈ (leadingForm 1 1 P.1).support, d 0 ≤ a) :
    expo a b ∈ (leadingForm 1 0 P.1).support ∧
      ∀ d ∈ (leadingForm 1 0 P.1).support, d 1 ≤ b := by
  have hx := preliminary_diagonal_first_point_x_bound hsource P Q hpair a b ha hmem hfirst
  have hsourcePoint := (leadingForm_mem_iff_rational_slope P 1 1 (by norm_num)
    (expo a b)).mp hmem |>.1
  have hh : expo a b ∈ (leadingForm 1 0 P.1).support := by
    apply (leadingForm_mem_iff_rational_slope P 1 0 (by norm_num) (expo a b)).mpr
    refine ⟨hsourcePoint,?_⟩
    intro d hd
    have hle := hx d hd
    norm_num [rationalNewtonWeight,expo]
    exact_mod_cast hle
  refine ⟨hh,?_⟩
  intro d hd
  have hdata := (leadingForm_mem_iff_rational_slope P 1 0 (by norm_num) d).mp hd
  have hrev := hdata.2 (expo a b) hsourcePoint
  norm_num [rationalNewtonWeight,expo] at hrev
  have hlow : a ≤ d 0 := by exact_mod_cast hrev
  have hupper := hx d hdata.1
  have hcoord : d 0=a := by omega
  have ht := diagonal_face_point_total_degree P (expo a b) hmem
  simp only [expo, Finsupp.single_apply, Fin.isValue] at ht
  have hbnd := MvPolynomial.le_totalDegree hdata.1
  rw [Finsupp.sum_fintype d (fun _ n => n) (by simp)] at hbnd
  have hsum : d 0+d 1 ≤ totalDeg P.1 := by
    simpa [totalDeg,Fin.sum_univ_two] using hbnd
  have htotal : a+b=totalDeg P.1 := by simpa [expo] using diagonal_face_point_total_degree P (expo a b) hmem
  omega

/-- The identified endpoint cannot lie on the grade-zero diagonal. -/
theorem preliminary_diagonal_first_point_grade_ne_zero
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b : ℕ) (ha : 0<a)
    (hmem : expo a b ∈ (leadingForm 1 1 P.1).support)
    (hfirst : ∀ d ∈ (leadingForm 1 1 P.1).support, d 0 ≤ a) :
    grade (expo a b) ≠ 0 := by
  obtain ⟨hh,hmax⟩ := preliminary_diagonal_first_point_horizontal_endpoint
    hsource P Q hpair a b ha hmem hfirst
  exact preliminary_horizontal_max_y_grade_ne_zero hsource P Q hpair (expo a b) hh
    (by simpa [expo] using hmax)

/-- A negative rightmost diagonal endpoint yields the native crossing alternative. -/
theorem preliminary_diagonal_negative_first_point_caseAlternative
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b : ℕ) (ha : 0<a) (hab : a<b)
    (hmem : expo a b ∈ (leadingForm 1 1 P.1).support)
    (hfirst : ∀ d ∈ (leadingForm 1 1 P.1).support, d 0 ≤ a) :
    CaseAlternative P := by
  obtain ⟨hh,_⟩ := preliminary_diagonal_first_point_horizontal_endpoint
    hsource P Q hpair a b ha hmem hfirst
  apply preliminary_horizontal_negative_point_caseAlternative hsource P Q hpair
  refine ⟨expo a b,hh,?_⟩
  simp only [grade,expo]
  norm_num
  omega

end Dixmier.Weyl
