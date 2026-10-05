/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PoissonEndpoints
public import Mathlib.Algebra.MvPolynomial.CommRing

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Diagonal top grade is incompatible with an exact Poisson companion

This is the symbol-level core of G13 Theorem 4.1(3). A top-grade
diagonal monomial cannot survive the equation `{R,F}=R` when the
top-grade terms are unique. Weighted-homogeneous positive-sum faces
provide that uniqueness; connecting the universal ramified operator
case remains separate.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- A positive-sum Newton weight and the diagonal grade determine a bivariate
exponent uniquely. This converts weighted homogeneity into unique grade
maximizers without a support-size assumption. -/
theorem exponent_eq_of_grade_and_weight
    (ρ σ : ℤ) (hsum : ρ + σ ≠ 0) (d e : Fin 2 →₀ ℕ)
    (hg : grade d = grade e)
    (hw : Finsupp.weight (wt ρ σ) d = Finsupp.weight (wt ρ σ) e) :
    d = e := by
  have hdiff : (d 0 : ℤ) - d 1 = (e 0 : ℤ) - e 1 := by
    simpa [grade] using hg
  have hweighted : (d 0 : ℤ) * ρ + (d 1 : ℤ) * σ =
      (e 0 : ℤ) * ρ + (e 1 : ℤ) * σ := by
    rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum] at hw
    simpa [wt] using hw
  have hscaled := congrArg (fun z : ℤ => z * σ) hdiff
  have hprod : ((d 0 : ℤ) - e 0) * (ρ + σ) = 0 := by
    nlinarith [hweighted, hscaled]
  have h0 : (d 0 : ℤ) = e 0 := sub_eq_zero.mp
    ((mul_eq_zero.mp hprod).resolve_right hsum)
  have h1 : (d 1 : ℤ) = e 1 := by omega
  apply Finsupp.ext
  intro i
  fin_cases i
  · exact_mod_cast h0
  · exact_mod_cast h1

private theorem diagonal_weight_eq_grade (d : Fin 2 →₀ ℕ) :
    Finsupp.weight (wt 1 (-1)) d = grade d := by
  obtain ⟨⟨i,j⟩, rfl⟩ := expo_surjective d
  rw [expo_weight]
  simp [grade, expo]
  ring

theorem poisson_support_weight_le
    (w : Fin 2 → ℤ) (R F : MvPolynomial (Fin 2) ℂ)
    (m n : ℤ)
    (hR : ∀ e ∈ R.support, Finsupp.weight w e ≤ m)
    (hF : ∀ e ∈ F.support, Finsupp.weight w e ≤ n)
    (e : Fin 2 →₀ ℕ) (he : e ∈ (poisson R F).support) :
    Finsupp.weight w e ≤ m + n - (w 0 + w 1) := by
  have hRy := pderiv_support_weight_le w R m hR 1
  have hRx := pderiv_support_weight_le w R m hR 0
  have hFy := pderiv_support_weight_le w F n hF 1
  have hFx := pderiv_support_weight_le w F n hF 0
  unfold poisson at he
  have hs := MvPolynomial.support_sub (Fin 2)
    (pderiv 1 R * pderiv 0 F)
    (pderiv 0 R * pderiv 1 F) he
  rcases Finset.mem_union.mp hs with hs | hs
  · have hmul := MvPolynomial.support_mul (pderiv 1 R) (pderiv 0 F) hs
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.mem_add.mp hmul
    have ha' := hRy a ha
    have hb' := hFx b hb
    rw [← hab, map_add]
    omega
  · have hmul := MvPolynomial.support_mul (pderiv 0 R) (pderiv 1 F) hs
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.mem_add.mp hmul
    have ha' := hRx a ha
    have hb' := hFy b hb
    rw [← hab, map_add]
    omega

/-- An exact Poisson companion cannot have a strictly negative maximal
diagonal grade: its bracket would have lower grade than the top term of `R`. -/
theorem poisson_companion_top_grade_nonnegative
    (R F : MvPolynomial (Fin 2) ℂ) {d e : Fin 2 →₀ ℕ}
    (hcomp : poisson R F = R)
    (hd : d ∈ R.support)
    (hdmax : ∀ x ∈ R.support,
      Finsupp.weight (wt 1 (-1)) x ≤ Finsupp.weight (wt 1 (-1)) d)
    (hemax : ∀ x ∈ F.support,
      Finsupp.weight (wt 1 (-1)) x ≤ Finsupp.weight (wt 1 (-1)) e) :
    0 ≤ Finsupp.weight (wt 1 (-1)) e := by
  have hdbr : d ∈ (poisson R F).support := by simpa [hcomp] using hd
  have hbound := poisson_support_weight_le (wt 1 (-1)) R F
    (Finsupp.weight (wt 1 (-1)) d) (Finsupp.weight (wt 1 (-1)) e)
    hdmax hemax d hdbr
  have hzero : wt 1 (-1) 0 + wt 1 (-1) 1 = 0 := by decide
  omega

/-- A pair of collinear unique top terms cannot support a nonzero top
component of an exact Poisson companion equation. -/
theorem poisson_companion_unique_top_not_collinear
    (v : Fin 2 → ℤ) (R F : MvPolynomial (Fin 2) ℂ)
    {d e : Fin 2 →₀ ℕ}
    (hcomp : poisson R F = R)
    (hd : d ∈ R.support) (_he : e ∈ F.support)
    (hdmax : ∀ x ∈ R.support, Finsupp.weight v x ≤ Finsupp.weight v d)
    (hemax : ∀ x ∈ F.support, Finsupp.weight v x ≤ Finsupp.weight v e)
    (hduniq : ∀ x ∈ R.support, Finsupp.weight v x = Finsupp.weight v d → x = d)
    (heuniq : ∀ x ∈ F.support, Finsupp.weight v x = Finsupp.weight v e → x = e)
    (hgrade : Finsupp.weight v e = v 0 + v 1) :
    (d 1 : ℂ) * (e 0 : ℂ) - (d 0 : ℂ) * (e 1 : ℂ) ≠ 0 := by
  intro hparallel
  let m := Finsupp.weight v d
  let n := Finsupp.weight v e
  have hRtop : weightedHomogeneousComponent v m R =
      monomial d (MvPolynomial.coeff d R) := by
    calc
      _ = monomial d (MvPolynomial.coeff d (weightedHomogeneousComponent v m R)) :=
        eq_monomial_of_support_subset_singleton (by
          intro x hx
          simp only [support_weightedHomogeneousComponent, Finset.mem_filter] at hx
          exact hduniq x hx.1 hx.2)
      _ = monomial d (MvPolynomial.coeff d R) := by
        congr 1
        simp [coeff_weightedHomogeneousComponent, m]
  have hFtop : weightedHomogeneousComponent v n F =
      monomial e (MvPolynomial.coeff e F) := by
    calc
      _ = monomial e (MvPolynomial.coeff e (weightedHomogeneousComponent v n F)) :=
        eq_monomial_of_support_subset_singleton (by
          intro x hx
          simp only [support_weightedHomogeneousComponent, Finset.mem_filter] at hx
          exact heuniq x hx.1 hx.2)
      _ = monomial e (MvPolynomial.coeff e F) := by
        congr 1
        simp [coeff_weightedHomogeneousComponent, n]
  have htop := poisson_weightedComponent_of_bounds v R F m n hdmax hemax
  have htop' : weightedHomogeneousComponent v m R = 0 := by
    have hw : m + n - (v 0 + v 1) = m := by simp [n, hgrade]
    rw [hw, hcomp, hRtop, hFtop, poisson_monomial_general,
      hparallel, zero_smul] at htop
    exact hRtop.trans htop
  have hcoeff : MvPolynomial.coeff d R ≠ 0 := mem_support_iff.mp hd
  rw [hRtop] at htop'
  exact hcoeff (monomial_eq_zero.mp htop')

/-- The zero-grade/zero-grade case of the diagonal-start obstruction. Both
unique top exponents lie on the diagonal, so their top Poisson bracket is zero,
incompatible with `{R,F}=R`. -/
theorem poisson_companion_no_two_diagonal_tops
    (R F : MvPolynomial (Fin 2) ℂ) {d e : Fin 2 →₀ ℕ}
    (hcomp : poisson R F = R)
    (hd : d ∈ R.support) (he : e ∈ F.support)
    (hdmax : ∀ x ∈ R.support,
      Finsupp.weight (wt 1 (-1)) x ≤ Finsupp.weight (wt 1 (-1)) d)
    (hemax : ∀ x ∈ F.support,
      Finsupp.weight (wt 1 (-1)) x ≤ Finsupp.weight (wt 1 (-1)) e)
    (hduniq : ∀ x ∈ R.support,
      Finsupp.weight (wt 1 (-1)) x = Finsupp.weight (wt 1 (-1)) d → x = d)
    (heuniq : ∀ x ∈ F.support,
      Finsupp.weight (wt 1 (-1)) x = Finsupp.weight (wt 1 (-1)) e → x = e)
    (hdiagR : d 0 = d 1) (hdiagF : e 0 = e 1) : False := by
  have hparallel : (d 1 : ℂ) * (e 0 : ℂ) - (d 0 : ℂ) * (e 1 : ℂ) = 0 := by
    rw [hdiagR, hdiagF]
    ring
  have hweight : Finsupp.weight (wt 1 (-1)) e =
      wt 1 (-1) 0 + wt 1 (-1) 1 := by
    obtain ⟨⟨i,j⟩, rfl⟩ := expo_surjective e
    have hij : i = j := by simpa [expo] using hdiagF
    rw [expo_weight]
    simp [wt, hij]
  exact (poisson_companion_unique_top_not_collinear (wt 1 (-1)) R F
    hcomp hd he hdmax hemax hduniq heuniq hweight) hparallel

/-- Full diagonal-start exclusion when each polynomial has a unique maximal
term for the diagonal grading. The distinguished term of `R` is nonconstant. -/
theorem poisson_companion_no_diagonal_unique_top
    (R F : MvPolynomial (Fin 2) ℂ) {d e : Fin 2 →₀ ℕ}
    (hcomp : poisson R F = R)
    (hd : d ∈ R.support) (he : e ∈ F.support)
    (hdmax : ∀ x ∈ R.support,
      Finsupp.weight (wt 1 (-1)) x ≤ Finsupp.weight (wt 1 (-1)) d)
    (hemax : ∀ x ∈ F.support,
      Finsupp.weight (wt 1 (-1)) x ≤ Finsupp.weight (wt 1 (-1)) e)
    (hduniq : ∀ x ∈ R.support,
      Finsupp.weight (wt 1 (-1)) x = Finsupp.weight (wt 1 (-1)) d → x = d)
    (heuniq : ∀ x ∈ F.support,
      Finsupp.weight (wt 1 (-1)) x = Finsupp.weight (wt 1 (-1)) e → x = e)
    (hdiagR : d 0 = d 1) (hdpos : 0 < d 0) : False := by
  let v := wt 1 (-1)
  let n := Finsupp.weight v e
  have hm : Finsupp.weight v d = 0 := by
    obtain ⟨⟨i,j⟩, rfl⟩ := expo_surjective d
    have hij : i = j := by simpa [expo] using hdiagR
    rw [expo_weight]
    simp [hij]
  have hn : 0 ≤ n := poisson_companion_top_grade_nonnegative R F
    hcomp hd hdmax hemax
  by_cases hnzero : n = 0
  · have hediag : e 0 = e 1 := by
      obtain ⟨⟨i,j⟩, rfl⟩ := expo_surjective e
      have hij : i = j := by
        dsimp [n, v] at hnzero
        rw [expo_weight] at hnzero
        simp at hnzero
        omega
      simp [expo, hij]
    exact poisson_companion_no_two_diagonal_tops R F hcomp hd he
      hdmax hemax hduniq heuniq hdiagR hediag
  · have hnpos : 0 < n := lt_of_le_of_ne hn (Ne.symm hnzero)
    have htopR : weightedHomogeneousComponent v n R = 0 := by
      apply support_eq_empty.mp
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      rw [support_weightedHomogeneousComponent] at hx
      obtain ⟨hxR, hxw⟩ := Finset.mem_filter.mp hx
      have hle := hdmax x hxR
      dsimp [v] at *
      omega
    have htop : weightedHomogeneousComponent v
        (Finsupp.weight v d + Finsupp.weight v e - (v 0 + v 1))
        (poisson R F) = 0 := by
      have hv : v 0 + v 1 = 0 := by decide
      have hindex : Finsupp.weight v d + Finsupp.weight v e -
          (v 0 + v 1) = n := by omega
      rw [hindex, hcomp]
      exact htopR
    have hcoll := poisson_unique_maximizers_collinear_of_top_zero v R F
      htop hd he hdmax hemax hduniq heuniq
    have hdc : (d 1 : ℂ) ≠ 0 := by
      rw [← hdiagR]
      exact_mod_cast (Nat.ne_of_gt hdpos)
    have heqC : (e 0 : ℂ) = (e 1 : ℂ) := by
      rw [hdiagR] at hcoll
      have hprod : (d 1 : ℂ) * ((e 0 : ℂ) - (e 1 : ℂ)) = 0 := by
        linear_combination hcoll
      exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hdc)
    have hediag : e 0 = e 1 := Nat.cast_injective heqC
    obtain ⟨⟨i,j⟩, rfl⟩ := expo_surjective e
    have hij : i = j := by simpa [expo] using hediag
    dsimp [n, v] at hnpos
    rw [expo_weight] at hnpos
    simp [hij] at hnpos

/-- Source-facing polynomial version: weighted homogeneity at a Newton
direction of nonzero coordinate sum supplies the uniqueness required by the
diagonal-start obstruction. This remains a polynomial Poisson statement;
transport to the exact ramified Weyl pair is separate. -/
theorem poisson_companion_no_diagonal_homogeneous_top
    (ρ σ m n : ℤ) (hsum : ρ + σ ≠ 0)
    (R F : MvPolynomial (Fin 2) ℂ) {d e : Fin 2 →₀ ℕ}
    (hRhom : R.IsWeightedHomogeneous (wt ρ σ) m)
    (hFhom : F.IsWeightedHomogeneous (wt ρ σ) n)
    (hcomp : poisson R F = R)
    (hd : d ∈ R.support) (he : e ∈ F.support)
    (hdmax : ∀ x ∈ R.support,
      Finsupp.weight (wt 1 (-1)) x ≤ Finsupp.weight (wt 1 (-1)) d)
    (hemax : ∀ x ∈ F.support,
      Finsupp.weight (wt 1 (-1)) x ≤ Finsupp.weight (wt 1 (-1)) e)
    (hdiagR : d 0 = d 1) (hdpos : 0 < d 0) : False := by
  have hduniq : ∀ x ∈ R.support,
      Finsupp.weight (wt 1 (-1)) x = Finsupp.weight (wt 1 (-1)) d → x = d := by
    intro x hx hgrade
    apply exponent_eq_of_grade_and_weight ρ σ hsum x d
    · simpa only [diagonal_weight_eq_grade] using hgrade
    · exact (hRhom (mem_support_iff.mp hx)).trans
        (hRhom (mem_support_iff.mp hd)).symm
  have heuniq : ∀ x ∈ F.support,
      Finsupp.weight (wt 1 (-1)) x = Finsupp.weight (wt 1 (-1)) e → x = e := by
    intro x hx hgrade
    apply exponent_eq_of_grade_and_weight ρ σ hsum x e
    · simpa only [diagonal_weight_eq_grade] using hgrade
    · exact (hFhom (mem_support_iff.mp hx)).trans
        (hFhom (mem_support_iff.mp he)).symm
  exact poisson_companion_no_diagonal_unique_top R F hcomp hd he
    hdmax hemax hduniq heuniq hdiagR hdpos

/-- The companion's maximal diagonal-grade exponent is selected from its
finite support, rather than supplied as a separate hypothesis. -/
theorem poisson_companion_no_diagonal_homogeneous_max
    (ρ σ m n : ℤ) (hsum : ρ + σ ≠ 0)
    (R F : MvPolynomial (Fin 2) ℂ) {d : Fin 2 →₀ ℕ}
    (hRhom : R.IsWeightedHomogeneous (wt ρ σ) m)
    (hFhom : F.IsWeightedHomogeneous (wt ρ σ) n)
    (hcomp : poisson R F = R)
    (hd : d ∈ R.support)
    (hdmax : ∀ x ∈ R.support,
      Finsupp.weight (wt 1 (-1)) x ≤ Finsupp.weight (wt 1 (-1)) d)
    (hdiagR : d 0 = d 1) (hdpos : 0 < d 0) : False := by
  classical
  have hRne : R ≠ 0 := by
    intro hz
    simp [hz] at hd
  have hFne : F ≠ 0 := by
    intro hz
    subst F
    simp [poisson] at hcomp
    exact hRne hcomp.symm
  obtain ⟨e, he, hemax⟩ := Finset.exists_max_image F.support
    (Finsupp.weight (wt 1 (-1))) (support_nonempty.mpr hFne)
  exact poisson_companion_no_diagonal_homogeneous_top ρ σ m n hsum
    R F hRhom hFhom hcomp hd he hdmax hemax hdiagR hdpos

end Dixmier.Weyl
