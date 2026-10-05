/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.NewtonEndpointCones
public import DixmierFormal.Weyl.NewtonRealDirection
public import DixmierFormal.Weyl.OneSidedGradeBasic
public import DixmierFormal.Weyl.LeadingMate

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The all-zero leading-bracket branch of one-sided generation

This module combines the roof-cone comparison with exact support geometry. A positive-grade
support exponent is exposed by a positive-sum integer direction after a sufficiently small
perturbation of the grade functional. Hence equal roof cones transfer one-sided support bounds.
-/

namespace Dixmier.Weyl

open MvPolynomial

def exponentTotal (d : Fin 2 →₀ ℕ) : ℕ := d 0 + d 1

/-- Any positive-grade exponent in a finite PBW support yields a positive-grade point on its
integer positive Newton roof. The exposing direction is `(N+1,1-N)`, with `N` larger than every
total degree in the support, so the grade maximum dominates all lower-grade terms. -/
theorem exists_positive_grade_exponent_in_integerPositiveNewtonRoof
    (T : Module.End ℂ (Polynomial ℂ))
    (hpositive : ∃ d ∈ (symbol T).support, 0 < grade d) :
    ∃ d ∈ (symbol T).support, 0 < grade d ∧
      exponentPoint d ∈ integerPositiveNewtonRoof T := by
  classical
  let S := (symbol T).support
  obtain ⟨dpos, hdpos, hpos⟩ := hpositive
  have hS : S.Nonempty := ⟨dpos, hdpos⟩
  let gradeValues := S.image grade
  have hgradeValues : gradeValues.Nonempty := Finset.image_nonempty.mpr hS
  let g : ℤ := gradeValues.max' hgradeValues
  have hgmem : g ∈ gradeValues := by
    exact Finset.max'_mem gradeValues hgradeValues
  have hgmax (d : Fin 2 →₀ ℕ) (hd : d ∈ S) : grade d ≤ g := by
    have hmem : grade d ∈ gradeValues := Finset.mem_image.mpr ⟨d, hd, rfl⟩
    exact Finset.le_max' gradeValues (grade d) hmem
  have hgpos : 0 < g := lt_of_lt_of_le hpos (hgmax dpos hdpos)
  obtain ⟨dgrade, hdgrade, hdgradeEq⟩ := Finset.mem_image.mp hgmem
  have hdgradeS : dgrade ∈ S := hdgrade
  have hgradeEq : grade dgrade = g := hdgradeEq
  let Sgrade := S.filter fun d => grade d = g
  have hSgrade : Sgrade.Nonempty := by
    refine ⟨dgrade, Finset.mem_filter.mpr ⟨hdgradeS, hgradeEq⟩⟩
  let totals := Sgrade.image exponentTotal
  have htotals : totals.Nonempty := Finset.image_nonempty.mpr hSgrade
  let dtotalMax := totals.max' htotals
  have hdtotalMax : dtotalMax ∈ totals := Finset.max'_mem totals htotals
  obtain ⟨d, hdSgrade, hdtotalEq⟩ := Finset.mem_image.mp hdtotalMax
  have hdS : d ∈ S := (Finset.mem_filter.mp hdSgrade).1
  have hdgrade : grade d = g := (Finset.mem_filter.mp hdSgrade).2
  have htotalMax (e : Fin 2 →₀ ℕ) (he : e ∈ Sgrade) :
      exponentTotal e ≤ exponentTotal d := by
    have hemem : exponentTotal e ∈ totals := Finset.mem_image.mpr ⟨e, he, rfl⟩
    have hle := Finset.le_max' totals (exponentTotal e) hemem
    have hle' : exponentTotal e ≤ dtotalMax := by simpa [dtotalMax] using hle
    exact hle'.trans (le_of_eq hdtotalEq.symm)
  let totalValues := S.image exponentTotal
  have htotalValues : totalValues.Nonempty := Finset.image_nonempty.mpr hS
  let M : ℕ := totalValues.max' htotalValues
  have hM (e : Fin 2 →₀ ℕ) (he : e ∈ S) : exponentTotal e ≤ M := by
    have hemem : exponentTotal e ∈ totalValues := Finset.mem_image.mpr ⟨e, he, rfl⟩
    exact Finset.le_max' totalValues (exponentTotal e) hemem
  let N : ℤ := (M : ℤ) + 1
  let ρ : ℤ := N + 1
  let σ : ℤ := 1 - N
  have hsum : 0 < ρ + σ := by dsimp [ρ, σ]; omega
  have hNnonneg : 0 ≤ N := by dsimp [N]; omega
  have hNgtM : (M : ℤ) < N := by dsimp [N]; omega
  have hweight (e : Fin 2 →₀ ℕ) :
      Finsupp.weight (wt ρ σ) e = N * grade e + (exponentTotal e : ℤ) := by
    simp [wt, ρ, σ, N, Finsupp.weight_eq_sum, grade, exponentTotal]
    ring
  have hmaxweight (e : Fin 2 →₀ ℕ) (he : e ∈ S) :
      Finsupp.weight (wt ρ σ) e ≤ Finsupp.weight (wt ρ σ) d := by
    by_cases hgrade : grade e = g
    · have hetotal := htotalMax e (Finset.mem_filter.mpr ⟨he, hgrade⟩)
      have hetotalInt : (exponentTotal e : ℤ) ≤ (exponentTotal d : ℤ) := by
        exact_mod_cast hetotal
      rw [hweight e, hweight d, hgrade, hdgrade]
      nlinarith
    · have hge := hgmax e he
      have hgradelt : grade e ≤ g - 1 := by omega
      have hmul : N * grade e ≤ N * (g - 1) :=
        mul_le_mul_of_nonneg_left hgradelt hNnonneg
      have hetotal := hM e he
      have hetotalInt : (exponentTotal e : ℤ) ≤ M := by exact_mod_cast hetotal
      have htargetTotal : 0 ≤ (exponentTotal d : ℤ) := by exact_mod_cast Nat.zero_le _
      have hstrict : N * (g - 1) + (M : ℤ) < N * g := by nlinarith
      rw [hweight e, hweight d]
      have hless : N * grade e + (exponentTotal e : ℤ) < N * g := by nlinarith
      rw [hdgrade]
      linarith
  have hface : d ∈ realExposedFace (ρ : ℝ) (σ : ℝ)
      ((symbol T).support : Set (Fin 2 →₀ ℕ)) := by
    refine ⟨hdS, ?_⟩
    intro e he
    have hle := hmaxweight e he
    have hcast : ((Finsupp.weight (wt ρ σ) e : ℤ) : ℝ) ≤
        ((Finsupp.weight (wt ρ σ) d : ℤ) : ℝ) := by exact_mod_cast hle
    have hrealweight (e : Fin 2 →₀ ℕ) :
        realNewtonWeight (ρ : ℝ) (σ : ℝ) e =
          ((Finsupp.weight (wt ρ σ) e : ℤ) : ℝ) := by
      simp [realNewtonWeight, wt, Finsupp.weight_eq_sum]
      ring
    rw [hrealweight e, hrealweight d]
    exact hcast
  have hface' : d ∈ (leadingForm ρ σ T).support :=
    (leadingForm_mem_iff_realExposedFace ρ σ T d).mpr hface
  have hpoint : exponentPoint d ∈ convexHull ℝ
      (exponentPoint '' ((leadingForm ρ σ T).support : Set (Fin 2 →₀ ℕ))) :=
    subset_convexHull ℝ _ ⟨d, hface', rfl⟩
  refine ⟨d, hdS, ?_, ?_⟩
  · simpa [hdgrade] using hgpos
  · exact ⟨ρ, σ, hsum, hpoint⟩

/-- If one member of an exact Weyl pair is supported in nonpositive grades and every positive-sum
integer leading bracket vanishes, then no such pair exists. The zero-bracket roof theorem forces
the other member's support onto the same side, contradicting the exact relation. -/
theorem no_exact_pair_all_positive_integer_leading_brackets_zero
    (P Q : A1 ℂ)
    (hPnonconstant : ∃ d ∈ (symbol (P : Module.End ℂ (Polynomial ℂ))).support, d ≠ 0)
    (hQnonconstant : ∃ d ∈ (symbol (Q : Module.End ℂ (Polynomial ℂ))).support, d ≠ 0)
    (hPscalarFree : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (P : Module.End ℂ (Polynomial ℂ))).support)
    (hQscalarFree : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (Q : Module.End ℂ (Polynomial ℂ))).support)
    (hPside : ∀ d ∈ (symbol (P : Module.End ℂ (Polynomial ℂ))).support, grade d ≤ 0)
    (hexact : Q * P - P * Q = 1)
    (hbr : ∀ ρ σ : ℤ, 0 < ρ + σ →
      poisson (leadingForm ρ σ (Q : Module.End ℂ (Polynomial ℂ)))
        (leadingForm ρ σ (P : Module.End ℂ (Polynomial ℂ))) = 0) :
    False := by
  have hbr' : ∀ ρ σ : ℤ, 0 < ρ + σ →
      poisson (leadingForm ρ σ (P : Module.End ℂ (Polynomial ℂ)))
        (leadingForm ρ σ (Q : Module.End ℂ (Polynomial ℂ))) = 0 := by
    intro ρ σ hsum
    have hanti : poisson (leadingForm ρ σ (P : Module.End ℂ (Polynomial ℂ)))
        (leadingForm ρ σ (Q : Module.End ℂ (Polynomial ℂ))) =
        - poisson (leadingForm ρ σ (Q : Module.End ℂ (Polynomial ℂ)))
          (leadingForm ρ σ (P : Module.End ℂ (Polynomial ℂ))) := by
      unfold poisson
      ring
    rw [hanti, hbr ρ σ hsum]
    simp
  have hroof := integerPositiveNewtonRoof_cones_equal_of_zeroBracket_and_scalarFree
    P Q hPnonconstant hQnonconstant hPscalarFree hQscalarFree hbr'
  have hPcone := positiveScalarCone_subset_nonpositive_halfspace _
    (integerPositiveNewtonRoof_grade_nonpositive P hPside)
  have hQside : ∀ d ∈ (symbol (Q : Module.End ℂ (Polynomial ℂ))).support,
      grade d ≤ 0 := by
    intro d hd
    by_contra hnot
    have hpositive : 0 < grade d := by omega
    obtain ⟨e, he, hepositive, hroofQ⟩ :=
      exists_positive_grade_exponent_in_integerPositiveNewtonRoof
        (Q : Module.End ℂ (Polynomial ℂ)) ⟨d, hd, hpositive⟩
    have hQroofCone : exponentPoint e ∈
        positiveScalarCone (integerPositiveNewtonRoof (Q : Module.End ℂ (Polynomial ℂ))) :=
      ⟨1, by norm_num, exponentPoint e, hroofQ, by simp⟩
    rw [← hroof] at hQroofCone
    have hhalf := hPcone hQroofCone
    have hstrict : (exponentPoint e).2 < (exponentPoint e).1 := by
      change ((e 1 : ℕ) : ℝ) < ((e 0 : ℕ) : ℝ)
      have hnat : e 1 < e 0 := by
        have hz : (e 0 : ℤ) - (e 1 : ℤ) > 0 := by simpa [grade] using hepositive
        omega
      exact_mod_cast hnat
    change (exponentPoint e).1 ≤ (exponentPoint e).2 at hhalf
    exact not_lt_of_ge hhalf hstrict
  exact no_exact_pair_both_nonpositive P Q hPside hQside hexact

/-- For an exact pair with one member supported in nonpositive grades, at least one positive-sum
integer direction has leading Poisson bracket one. The alternative that all such brackets vanish
is excluded by the roof-cone argument above. -/
theorem exists_integer_positive_direction_leading_bracket_one
    (P Q : A1 ℂ)
    (hPnonconstant : ∃ d ∈ (symbol (P : Module.End ℂ (Polynomial ℂ))).support, d ≠ 0)
    (hQnonconstant : ∃ d ∈ (symbol (Q : Module.End ℂ (Polynomial ℂ))).support, d ≠ 0)
    (hPscalarFree : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (P : Module.End ℂ (Polynomial ℂ))).support)
    (hQscalarFree : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (Q : Module.End ℂ (Polynomial ℂ))).support)
    (hPside : ∀ d ∈ (symbol (P : Module.End ℂ (Polynomial ℂ))).support, grade d ≤ 0)
    (hexact : Q * P - P * Q = 1) :
    ∃ ρ σ : ℤ, 0 < ρ + σ ∧
      poisson (leadingForm ρ σ (Q : Module.End ℂ (Polynomial ℂ)))
        (leadingForm ρ σ (P : Module.End ℂ (Polynomial ℂ))) = 1 := by
  by_contra hnone
  apply no_exact_pair_all_positive_integer_leading_brackets_zero P Q
    hPnonconstant hQnonconstant hPscalarFree hQscalarFree hPside hexact
  intro ρ σ hsum
  rcases exactPair_leadingPoisson_zero_or_one P Q ρ σ hsum hexact with hzero | hone
  · exact hzero
  · exact False.elim (hnone ⟨ρ, σ, hsum, hone⟩)

/-- A zero Poisson bracket between homogeneous faces forces their positive support cones to
coincide. Thus a face whose support lies in the nonpositive-grade half-plane cannot Poisson
commute with a face containing a positive-grade exponent. This is the support-separation step
used in Han--Tan's crossing-face case. -/
theorem poisson_ne_zero_of_homogeneous_faces_grade_separated
    (w : Fin 2 → ℤ) (degreeP degreeQ : ℤ)
    (p q : MvPolynomial (Fin 2) ℂ)
    (hwnz : w 0 ≠ 0 ∨ w 1 ≠ 0)
    (hpdeg : ∀ d ∈ p.support, Finsupp.weight w d = degreeP)
    (hqdeg : ∀ e ∈ q.support, Finsupp.weight w e = degreeQ)
    (hpnonconst : ∃ d ∈ p.support, d ≠ 0)
    (hqnonconst : ∃ e ∈ q.support, e ≠ 0)
    (hpne : p ≠ 0) (hqne : q ≠ 0)
    (hpSide : ∀ d ∈ p.support, grade d ≤ 0)
    (hqPositive : ∃ e ∈ q.support, 0 < grade e) :
    poisson p q ≠ 0 := by
  intro hzero
  let Sp := convexHull ℝ (exponentPoint '' (p.support : Set (Fin 2 →₀ ℕ)))
  let Sq := convexHull ℝ (exponentPoint '' (q.support : Set (Fin 2 →₀ ℕ)))
  have hcones : positiveScalarCone Sp = positiveScalarCone Sq :=
    poisson_homogeneous_support_cones_equal w degreeP degreeQ p q hwnz
      hpdeg hqdeg hpnonconst hqnonconst hpne hqne hzero
  obtain ⟨e, he, hePositive⟩ := hqPositive
  have hqmem : exponentPoint e ∈ positiveScalarCone Sq := by
    refine ⟨1, by norm_num, exponentPoint e, ?_, by simp⟩
    exact subset_convexHull ℝ _ ⟨e, he, rfl⟩
  have hpmem : exponentPoint e ∈ positiveScalarCone Sp := by
    rw [hcones]
    exact hqmem
  have himage : exponentPoint '' (p.support : Set (Fin 2 →₀ ℕ)) ⊆
      {z : ℝ × ℝ | z.1 - z.2 ≤ 0} := by
    rintro z ⟨d, hd, rfl⟩
    have hgrade : (d 0 : ℤ) - (d 1 : ℤ) ≤ 0 := by
      simpa [grade] using hpSide d hd
    change ((d 0 : ℕ) : ℝ) - ((d 1 : ℕ) : ℝ) ≤ 0
    exact_mod_cast hgrade
  have hconvex : Convex ℝ {z : ℝ × ℝ | z.1 - z.2 ≤ 0} :=
    convex_halfSpace_le IsLinearMap.isLinearMap_sub 0
  have hPconvex : Sp ⊆ {z : ℝ × ℝ | z.1 - z.2 ≤ 0} := by
    intro z hz
    exact convexHull_min himage hconvex hz
  have hPcone : positiveScalarCone Sp ⊆ {z : ℝ × ℝ | z.1 ≤ z.2} := by
    apply positiveScalarCone_subset_nonpositive_halfspace
    intro z hz
    have hz' := hPconvex hz
    dsimp at hz' ⊢
    linarith
  have hpoint := hPcone hpmem
  have hgradeInt : (e 1 : ℤ) < (e 0 : ℤ) := by
    have h := hePositive
    dsimp [grade] at h
    omega
  have hstrict : (exponentPoint e).2 < (exponentPoint e).1 := by
    change ((e 1 : ℕ) : ℝ) < ((e 0 : ℕ) : ℝ)
    exact_mod_cast hgradeInt
  change (exponentPoint e).1 ≤ (exponentPoint e).2 at hpoint
  exact (not_lt_of_ge hpoint) hstrict

end Dixmier.Weyl
