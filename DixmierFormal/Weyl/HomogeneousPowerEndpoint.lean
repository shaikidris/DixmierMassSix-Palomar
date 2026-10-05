/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PoissonEndpoints
public import DixmierFormal.Weyl.MatePower
public import DixmierFormal.Weyl.GGVDegreeFiniteCheck
public import DixmierFormal.Weyl.PrimitiveDirectionArithmetic
public import DixmierFormal.Weyl.GGVDegreeNormalization
public import DixmierFormal.Weyl.FaceMass
public import DixmierFormal.Weyl.CompanionNonmonomial
public import DixmierFormal.Weyl.CompanionBase
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Endpoint scaling for a homogeneous power

On a negative-slope homogeneous face, the maximal `x` exponent determines
the corresponding `y` exponent. Its endpoint scales with a polynomial power.
This is the elementary support implication used in G13 Proposition 7.3.
-/

namespace Dixmier.Weyl

open MvPolynomial

theorem homogeneous_power_max_x_endpoint
    (R : MvPolynomial (Fin 2) ℂ) (ρ s m u v : ℕ) (degree : ℤ)
    (hRne : R ≠ 0) (hs : 0 < s)
    (hhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degree)
    (hpoint : expo u v ∈ R.support)
    (hmax : ∀ d ∈ R.support, d 0 ≤ u) :
    expo (m * u) (m * v) ∈ (R ^ m).support := by
  classical
  have hdegR : R.degreeOf 0 = u := by
    apply Nat.le_antisymm
    · rw [MvPolynomial.degreeOf_eq_sup]
      exact Finset.sup_le fun d hd => hmax d hd
    · simpa [expo] using MvPolynomial.le_degreeOf_of_mem_support 0 hpoint
  have hpowne : R ^ m ≠ 0 := pow_ne_zero _ hRne
  have hsupport : (R ^ m).support.Nonempty :=
    MvPolynomial.support_nonempty.mpr hpowne
  obtain ⟨d, hd, hdmax⟩ :=
    Finset.exists_max_image (R ^ m).support (fun e => e 0) hsupport
  have hd0 : d 0 = m * u := by
    have hmaxdeg : (R ^ m).degreeOf 0 = d 0 := by
      apply Nat.le_antisymm
      · rw [MvPolynomial.degreeOf_eq_sup]
        exact Finset.sup_le fun e he => hdmax e he
      · exact MvPolynomial.le_degreeOf_of_mem_support 0 hd
    rw [MvPolynomial.degreeOf_pow_eq 0 R m hRne, hdegR] at hmaxdeg
    omega
  have hdegreePoint : Finsupp.weight (wt ρ (-(s : ℤ))) (expo u v) = degree :=
    hhom (MvPolynomial.mem_support_iff.mp hpoint)
  have hdegreePow : Finsupp.weight (wt ρ (-(s : ℤ))) d = degree * m := by
    simpa [nsmul_eq_mul, mul_comm] using
      (hhom.pow m) (MvPolynomial.mem_support_iff.mp hd)
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
  have hi : i = m * u := by simpa [expo] using hd0
  have hj : j = m * v := by
    rw [expo_weight] at hdegreePoint hdegreePow
    rw [hi] at hdegreePow
    have hsne : (s : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
    have hmul : (s : ℤ) * ((j : ℤ) - ((m * v : ℕ) : ℤ)) = 0 := by
      push_cast at hdegreePow ⊢
      nlinarith [hdegreePoint, hdegreePow]
    have hz := (mul_eq_zero.mp hmul).resolve_left hsne
    exact_mod_cast (sub_eq_zero.mp hz)
  subst i
  subst j
  simpa only [expo] using hd

/-- The corresponding minimal-`x` endpoint also scales under powers.
The proof reads the first coordinate as a trailing polynomial degree. -/
theorem homogeneous_power_min_x_endpoint
    (R : MvPolynomial (Fin 2) ℂ) (ρ s m u v : ℕ) (degree : ℤ)
    (hRne : R ≠ 0) (hs : 0 < s)
    (hhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degree)
    (hpoint : expo u v ∈ R.support)
    (hmin : ∀ d ∈ R.support, u ≤ d 0) :
    expo (m * u) (m * v) ∈ (R ^ m).support := by
  classical
  let E := MvPolynomial.finSuccEquiv ℂ 1
  have hERne : E R ≠ 0 := (E.map_ne_zero_iff).mpr hRne
  have huE : u ∈ (E R).support := by
    rw [MvPolynomial.support_finSuccEquiv]
    exact Finset.mem_image.mpr ⟨expo u v, hpoint, by simp [expo]⟩
  have htrailR : (E R).natTrailingDegree = u := by
    apply Nat.le_antisymm
    · exact Polynomial.natTrailingDegree_le_of_mem_supp u huE
    · have htrailMem := Polynomial.natTrailingDegree_mem_support_of_nonzero hERne
      rw [MvPolynomial.support_finSuccEquiv] at htrailMem
      obtain ⟨d, hd, hd0⟩ := Finset.mem_image.mp htrailMem
      exact le_trans (hmin d hd) (le_of_eq hd0)
  have hpowne : E (R ^ m) ≠ 0 := by
    exact (E.map_ne_zero_iff).mpr (pow_ne_zero _ hRne)
  have hmapPow : E (R ^ m) = (E R) ^ m := map_pow E R m
  have htrailPow : (E (R ^ m)).natTrailingDegree = m * u := by
    rw [hmapPow, natTrailingDegree_pow_of_ne_zero (E R) hERne m, htrailR]
  have hminMem := Polynomial.natTrailingDegree_mem_support_of_nonzero hpowne
  rw [MvPolynomial.support_finSuccEquiv] at hminMem
  obtain ⟨d, hd, hd0⟩ := Finset.mem_image.mp hminMem
  have hd0' : d 0 = m * u := by
    rw [htrailPow] at hd0
    exact hd0
  have hdegreePoint : Finsupp.weight (wt ρ (-(s : ℤ))) (expo u v) = degree :=
    hhom (MvPolynomial.mem_support_iff.mp hpoint)
  have hdegreePow : Finsupp.weight (wt ρ (-(s : ℤ))) d = degree * m := by
    simpa [nsmul_eq_mul, mul_comm] using
      (hhom.pow m) (MvPolynomial.mem_support_iff.mp hd)
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
  have hi : i = m * u := by simpa [expo] using hd0'
  have hj : j = m * v := by
    rw [expo_weight] at hdegreePoint hdegreePow
    rw [hi] at hdegreePow
    have hsne : (s : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
    have hmul : (s : ℤ) * ((j : ℤ) - ((m * v : ℕ) : ℤ)) = 0 := by
      push_cast at hdegreePow ⊢
      nlinarith [hdegreePoint, hdegreePow]
    have hz := (mul_eq_zero.mp hmul).resolve_left hsne
    exact_mod_cast (sub_eq_zero.mp hz)
  subst i
  subst j
  simpa only [expo] using hd

/-- The scaled maximal endpoint remains maximal in the powered support. -/
theorem homogeneous_power_max_x_bound
    (R : MvPolynomial (Fin 2) ℂ) (m u : ℕ)
    (hRne : R ≠ 0)
    (hmax : ∀ d ∈ R.support, d 0 ≤ u) :
    ∀ d ∈ (R ^ m).support, d 0 ≤ m * u := by
  classical
  have hdegree : R.degreeOf 0 ≤ u := by
    rw [MvPolynomial.degreeOf_eq_sup]
    exact Finset.sup_le fun d hd => hmax d hd
  intro d hd
  have hle := MvPolynomial.le_degreeOf_of_mem_support 0 hd
  rw [MvPolynomial.degreeOf_pow_eq 0 R m hRne] at hle
  exact le_trans hle (Nat.mul_le_mul_left m hdegree)

/-- The scaled minimal endpoint remains minimal in the powered support. -/
theorem homogeneous_power_min_x_bound
    (R : MvPolynomial (Fin 2) ℂ) (m u : ℕ)
    (hRne : R ≠ 0)
    (hmin : ∀ d ∈ R.support, u ≤ d 0) :
    ∀ d ∈ (R ^ m).support, m * u ≤ d 0 := by
  classical
  let E := MvPolynomial.finSuccEquiv ℂ 1
  have hERne : E R ≠ 0 := (E.map_ne_zero_iff).mpr hRne
  have htrail : u ≤ (E R).natTrailingDegree := by
    have htrailMem := Polynomial.natTrailingDegree_mem_support_of_nonzero hERne
    rw [MvPolynomial.support_finSuccEquiv] at htrailMem
    obtain ⟨d, hd, hd0⟩ := Finset.mem_image.mp htrailMem
    exact le_trans (hmin d hd) (le_of_eq hd0)
  intro d hd
  have hdE : d 0 ∈ (E (R ^ m)).support := by
    rw [MvPolynomial.support_finSuccEquiv]
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have htrailPow : (E (R ^ m)).natTrailingDegree =
      m * (E R).natTrailingDegree := by
    rw [show E (R ^ m) = (E R) ^ m from map_pow E R m]
    exact natTrailingDegree_pow_of_ne_zero (E R) hERne m
  have hle := Polynomial.natTrailingDegree_le_of_mem_supp (d 0) hdE
  rw [htrailPow] at hle
  exact le_trans (Nat.mul_le_mul_left m htrail) hle

/-- Both actual endpoints of a homogeneous face scale under an outer power.
This is the support-level interface needed for G13's `C₀,C₁` normalization. -/
theorem homogeneous_power_endpoint_pair
    (R : MvPolynomial (Fin 2) ℂ) (ρ s m u v r t : ℕ) (degree : ℤ)
    (hRne : R ≠ 0) (hs : 0 < s)
    (hhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degree)
    (hend : expo u v ∈ R.support)
    (hstart : expo r t ∈ R.support)
    (hmax : ∀ d ∈ R.support, d 0 ≤ u)
    (hmin : ∀ d ∈ R.support, r ≤ d 0) :
    expo (m * u) (m * v) ∈ (R ^ m).support ∧
      expo (m * r) (m * t) ∈ (R ^ m).support ∧
      (∀ d ∈ (R ^ m).support, d 0 ≤ m * u) ∧
      (∀ d ∈ (R ^ m).support, m * r ≤ d 0) := by
  exact ⟨homogeneous_power_max_x_endpoint R ρ s m u v degree hRne hs hhom hend hmax,
    homogeneous_power_min_x_endpoint R ρ s m r t degree hRne hs hhom hstart hmin,
    homogeneous_power_max_x_bound R m u hRne hmax,
    homogeneous_power_min_x_bound R m r hRne hmin⟩

/-- The same endpoint normalization for an actual Weyl leading face written
as a nonzero scalar multiple of a homogeneous power. -/
theorem leadingFace_power_endpoint_pair
    (P : A1 ℂ) (R : MvPolynomial (Fin 2) ℂ) (μ : ℂ)
    (ρ s m u v r t : ℕ) (degree : ℤ)
    (hRne : R ≠ 0) (hμ : μ ≠ 0) (hs : 0 < s)
    (hhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degree)
    (hend : expo u v ∈ R.support)
    (hstart : expo r t ∈ R.support)
    (hmax : ∀ d ∈ R.support, d 0 ≤ u)
    (hmin : ∀ d ∈ R.support, r ≤ d 0)
    (hface : leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ * R ^ m) :
    expo (m * u) (m * v) ∈ (leadingForm ρ (-(s : ℤ)) P.1).support ∧
      expo (m * r) (m * t) ∈ (leadingForm ρ (-(s : ℤ)) P.1).support ∧
      (∀ d ∈ (leadingForm ρ (-(s : ℤ)) P.1).support, d 0 ≤ m * u) ∧
      (∀ d ∈ (leadingForm ρ (-(s : ℤ)) P.1).support, m * r ≤ d 0) := by
  have hsupp : (leadingForm ρ (-(s : ℤ)) P.1).support = (R ^ m).support := by
    rw [hface, MvPolynomial.C_mul', MvPolynomial.support_smul_eq hμ]
  simpa only [hsupp] using
    homogeneous_power_endpoint_pair R ρ s m u v r t degree
      hRne hs hhom hend hstart hmax hmin

/-- Two support points of one homogeneous negative-direction face satisfy
the natural-coordinate weighted-line equation used in G13's finite table. -/
theorem homogeneous_endpoints_weight_equation
    (R : MvPolynomial (Fin 2) ℂ) (ρ s u v r t : ℕ) (degree : ℤ)
    (hhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degree)
    (hend : expo u v ∈ R.support)
    (hstart : expo r t ∈ R.support) :
    ρ * u + s * t = ρ * r + s * v := by
  have hu := hhom (MvPolynomial.mem_support_iff.mp hend)
  have hr := hhom (MvPolynomial.mem_support_iff.mp hstart)
  rw [expo_weight] at hu hr
  exact_mod_cast (show (ρ : ℤ) * u + (s : ℤ) * t =
    (ρ : ℤ) * r + (s : ℤ) * v by nlinarith [hu, hr])

/-- A negative-slope homogeneous polynomial has at most one support point at
its maximal `x` coordinate. -/
theorem homogeneous_max_x_unique
    (F : MvPolynomial (Fin 2) ℂ) (ρ s u v : ℕ) (degree : ℤ)
    (hs : 0 < s)
    (hhom : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degree)
    (hend : expo u v ∈ F.support)
    (d : Fin 2 →₀ ℕ) (hd : d ∈ F.support) (hdx : d 0 = u) :
    d = expo u v := by
  have hendWeight := hhom (MvPolynomial.mem_support_iff.mp hend)
  have hdWeight := hhom (MvPolynomial.mem_support_iff.mp hd)
  rw [expo_weight] at hendWeight
  have hcoord : (d 0 : ℤ) * ρ - (d 1 : ℤ) * s = degree := by
    simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two, sub_eq_add_neg] using hdWeight
  have hsz : (s : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  have hmul : (s : ℤ) * (d 1 : ℤ) = (s : ℤ) * v := by
    rw [hdx] at hcoord
    nlinarith [hcoord, hendWeight]
  have hdy : d 1 = v := by
    exact_mod_cast (mul_left_cancel₀ hsz hmul)
  ext i
  fin_cases i <;> simp [expo, hdx, hdy]

/-- Opposite grades at the two powered endpoints give the strict crossing
inequalities for the unpowered homogeneous root. -/
theorem homogeneous_power_crossing_coordinates
    (R : MvPolynomial (Fin 2) ℂ) (ρ s m u v r t : ℕ) (degree : ℤ)
    (hs : 0 < s)
    (hhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degree)
    (hend : expo u v ∈ R.support) (hstart : expo r t ∈ R.support)
    (hmax : ∀ d ∈ R.support, d 0 ≤ u)
    (hstartGrade : 0 < grade (expo (m * r) (m * t)))
    (hendGrade : grade (expo (m * u) (m * v)) < 0) :
    t < r ∧ u < v ∧ r < u := by
  have hmtZ : ((m * t : ℕ) : ℤ) < ((m * r : ℕ) : ℤ) := by
    simpa [grade, expo] using hstartGrade
  have hmt : m * t < m * r := by exact_mod_cast hmtZ
  have htr : t < r := by
    by_contra hn
    have hle : m * r ≤ m * t := Nat.mul_le_mul_left m (by omega)
    omega
  have huvZ : ((m * u : ℕ) : ℤ) < ((m * v : ℕ) : ℤ) := by
    simpa [grade, expo] using hendGrade
  have huv : u < v := by
    by_contra hn
    have hle : m * v ≤ m * u := Nat.mul_le_mul_left m (by omega)
    omega
  have hruLe : r ≤ u := by simpa [expo] using hmax (expo r t) hstart
  have hline := homogeneous_endpoints_weight_equation R ρ s u v r t degree
    hhom hend hstart
  have hru : r < u := by
    by_contra hn
    have heq : r = u := by omega
    rw [heq] at hline
    have hmul : s * t = s * v := by omega
    have htv : t = v := Nat.eq_of_mul_eq_mul_left hs hmul
    omega
  exact ⟨htr, huv, hru⟩

/-- A nonmonomial homogeneous companion of positive weight that starts at
`(1,1)` must have maximal `x` coordinate at least two. -/
theorem homogeneous_companion_end_x_ge_two
    (F : MvPolynomial (Fin 2) ℂ) (ρ s f₁ : ℕ) (degree : ℤ)
    (hs : 0 < s) (hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    (hhom : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degree)
    (hbase : expo 1 1 ∈ F.support)
    (hmax : ∀ d ∈ F.support, d 0 ≤ f₁)
    (hnonmono : 1 < F.support.card) :
    2 ≤ f₁ := by
  by_contra hn
  have hf₁le : f₁ ≤ 1 := by omega
  have hbaseWeight := hhom (MvPolynomial.mem_support_iff.mp hbase)
  rw [expo_weight] at hbaseWeight
  have hsum : (0 : ℤ) < (ρ : ℤ) - s := by
    simpa [IsDirection] using hdir.2
  have hsz : (0 : ℤ) < s := by exact_mod_cast hs
  have hdeg : degree = (ρ : ℤ) - s := by
    simpa [sub_eq_add_neg] using hbaseWeight.symm
  have heqbase : ∀ d ∈ F.support, d = expo 1 1 := by
    intro d hd
    have hdWeight := hhom (MvPolynomial.mem_support_iff.mp hd)
    simp [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two] at hdWeight
    have hd0le : d 0 ≤ 1 := le_trans (hmax d hd) hf₁le
    have hd0 : d 0 = 1 := by
      by_contra hz
      have hd0zero : d 0 = 0 := by omega
      have hd1nonneg : (0 : ℤ) ≤ (d 1 : ℤ) := by exact_mod_cast Nat.zero_le (d 1)
      rw [hd0zero, hdeg] at hdWeight
      have hprod : (0 : ℤ) ≤ (d 1 : ℤ) * s :=
        mul_nonneg hd1nonneg (le_of_lt hsz)
      simp only [Int.natCast_zero, zero_mul, zero_add] at hdWeight
      omega
    have hd1 : d 1 = 1 := by
      have hd1nonneg : (0 : ℤ) ≤ (d 1 : ℤ) := by exact_mod_cast Nat.zero_le (d 1)
      rw [hd0, hdeg] at hdWeight
      have hmul : (s : ℤ) * (d 1 : ℤ) = (s : ℤ) * 1 := by
        nlinarith [hdWeight]
      have heq : (d 1 : ℤ) = 1 := mul_left_cancel₀ (ne_of_gt hsz) hmul
      exact_mod_cast heq
    ext i
    fin_cases i <;> simp [expo, hd0, hd1]
  have hcard : F.support.card ≤ 1 :=
    Finset.card_le_one_iff.mpr (by
      intro d e hd he
      exact (heqbase d hd).trans (heqbase e he).symm)
  omega

/-- At maximal `x` degree, `poisson R F = R` has a vanishing top component
when the companion end has `x` coordinate at least two. The resulting
monomial determinant makes the two end vectors proportional. -/
theorem homogeneous_companion_end_proportional
    (R F : MvPolynomial (Fin 2) ℂ) (ρ s u v f₁ f₂ : ℕ)
    (degree degreeF : ℤ)
    (hs : 0 < s) (hf₁ : 2 ≤ f₁)
    (hRhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degree)
    (hFhom : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degreeF)
    (hRend : expo u v ∈ R.support)
    (hFend : expo f₁ f₂ ∈ F.support)
    (hRmax : ∀ d ∈ R.support, d 0 ≤ u)
    (hFmax : ∀ d ∈ F.support, d 0 ≤ f₁)
    (hPoisson : poisson R F = R) :
    f₁ * v = f₂ * u := by
  let w : Fin 2 → ℤ := wt 1 0
  have hw (d : Fin 2 →₀ ℕ) : Finsupp.weight w d = (d 0 : ℤ) := by
    simp [w, wt, Finsupp.weight_eq_sum, Fin.sum_univ_two]
  have htopZero : MvPolynomial.weightedHomogeneousComponent w
      (Finsupp.weight w (expo u v) + Finsupp.weight w (expo f₁ f₂) -
        (w 0 + w 1)) (poisson R F) = 0 := by
    have htarget : Finsupp.weight w (expo u v) +
        Finsupp.weight w (expo f₁ f₂) - (w 0 + w 1) =
          (u : ℤ) + f₁ - 1 := by
      rw [hw, hw]
      simp [w, wt, expo]
    rw [hPoisson, htarget]
    apply MvPolynomial.support_eq_empty.mp
    rw [MvPolynomial.support_weightedHomogeneousComponent]
    apply Finset.filter_eq_empty_iff.mpr
    intro d hd heq
    have hdBound := hRmax d hd
    rw [hw] at heq
    omega
  have hRmaxW : ∀ d ∈ R.support,
      Finsupp.weight w d ≤ Finsupp.weight w (expo u v) := by
    intro d hd
    rw [hw, hw]
    simpa [expo] using hRmax d hd
  have hFmaxW : ∀ d ∈ F.support,
      Finsupp.weight w d ≤ Finsupp.weight w (expo f₁ f₂) := by
    intro d hd
    rw [hw, hw]
    simpa [expo] using hFmax d hd
  have hRunique : ∀ d ∈ R.support,
      Finsupp.weight w d = Finsupp.weight w (expo u v) → d = expo u v := by
    intro d hd heq
    rw [hw, hw] at heq
    exact homogeneous_max_x_unique R ρ s u v degree hs hRhom hRend d hd
      (by simpa [expo] using heq)
  have hFunique : ∀ d ∈ F.support,
      Finsupp.weight w d = Finsupp.weight w (expo f₁ f₂) →
        d = expo f₁ f₂ := by
    intro d hd heq
    rw [hw, hw] at heq
    exact homogeneous_max_x_unique F ρ s f₁ f₂ degreeF hs hFhom hFend d hd
      (by simpa [expo] using heq)
  have hdet := poisson_unique_maximizers_collinear_of_top_zero w R F
    htopZero hRend hFend hRmaxW hFmaxW hRunique hFunique
  have hcomplex : (v : ℂ) * f₁ = (u : ℂ) * f₂ := by
    simpa [expo, sub_eq_zero] using (sub_eq_zero.mp hdet)
  have hint : (v : ℤ) * f₁ = (u : ℤ) * f₂ := by exact_mod_cast hcomplex
  exact_mod_cast (show (f₁ : ℤ) * v = (f₂ : ℤ) * u by nlinarith [hint])

/-- G13 Proposition 7.3(3) at the homogeneous-root level: the companion
endpoint is a proper integral point on the root endpoint's ray. This does not
use the small-degree hypothesis or the finite coordinate table. -/
theorem homogeneous_companion_end_nonprimitive
    (R F : MvPolynomial (Fin 2) ℂ) (ρ s u v r t f₁ f₂ : ℕ)
    (degree : ℤ)
    (hs : 0 < s) (hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    (hRhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degree)
    (hFhom : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) ((ρ : ℤ) - s))
    (hRend : expo u v ∈ R.support) (hRstart : expo r t ∈ R.support)
    (hRmax : ∀ d ∈ R.support, d 0 ≤ u)
    (hFend : expo f₁ f₂ ∈ F.support)
    (hFmax : ∀ d ∈ F.support, d 0 ≤ f₁)
    (hPoisson : poisson R F = R)
    (hstartGrade : 0 < grade (expo r t))
    (hendGrade : grade (expo u v) < 0) :
    f₁ < u ∧ f₂ < v ∧ 1 < Nat.gcd u v := by
  obtain ⟨htr, huv, _⟩ := homogeneous_power_crossing_coordinates
    R ρ s 1 u v r t degree hs hRhom hRend hRstart hRmax
      (by simpa using hstartGrade) (by simpa using hendGrade)
  have hsρ : s < ρ := by
    have := hdir.2
    omega
  have hRne : R ≠ 0 := MvPolynomial.support_nonempty.mp ⟨expo r t, hRstart⟩
  have hFbase : expo 1 1 ∈ F.support :=
    homogeneous_companion_base_mem R F ρ s hs hsρ hRne hFhom hPoisson
  have hFnonmono := crossing_poisson_companion_nonmonomial
    R F (expo r t) (expo u v) hFbase hPoisson hRstart hRend
      hstartGrade hendGrade
  have hf₁ := homogeneous_companion_end_x_ge_two F ρ s f₁ ((ρ : ℤ) - s)
    hs hdir hFhom hFbase hFmax hFnonmono
  have hprop := homogeneous_companion_end_proportional R F ρ s u v f₁ f₂
    degree ((ρ : ℤ) - s) hs hf₁ hRhom hFhom hRend hFend hRmax hFmax hPoisson
  have hline := homogeneous_endpoints_weight_equation R ρ s u v r t degree
    hRhom hRend hRstart
  have hcomp := homogeneous_endpoints_weight_equation F ρ s f₁ f₂ 1 1 ((ρ : ℤ) - s)
    hFhom hFend hFbase
  have hproper := companion_endpoint_both_proper_nat ρ s u v r t f₁ f₂
    hs hsρ (by omega) (by omega) htr hline (by omega) hprop
  exact ⟨hproper.1, hproper.2,
    proportional_lattice_point_gcd_gt_one u v f₁ f₂ (by omega) hproper.1 hprop⟩

/-- A homogeneous companion supported at `(1,1)` and `(f₁,f₂)` recovers
the primitive direction from their difference, as in G13 Proposition 7.3(5). -/
theorem companion_support_recovers_primitive_direction
    (F : MvPolynomial (Fin 2) ℂ) (ρ s f₁ f₂ : ℕ) (degree : ℤ)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    (hf₁ : 2 ≤ f₁)
    (hhom : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degree)
    (hbase : expo 1 1 ∈ F.support)
    (hend : expo f₁ f₂ ∈ F.support) :
    ρ = (f₂ - 1) / Nat.gcd (f₁ - 1) (f₂ - 1) ∧
      s = (f₁ - 1) / Nat.gcd (f₁ - 1) (f₂ - 1) := by
  have hρ : 0 < ρ := by
    have hsum := hdir.2
    omega
  have hcop : Nat.Coprime ρ s := by
    simpa [IsDirection, Nat.Coprime, Int.gcd_def] using hdir.1
  have hbaseWeight := hhom (MvPolynomial.mem_support_iff.mp hbase)
  have hendWeight := hhom (MvPolynomial.mem_support_iff.mp hend)
  rw [expo_weight] at hbaseWeight hendWeight
  have hf₂ : 1 ≤ f₂ := by
    by_contra hn
    have hz : f₂ = 0 := by omega
    rw [hz] at hendWeight
    have hρz : (0 : ℤ) < ρ := by exact_mod_cast hρ
    have hf₁z : (1 : ℤ) < f₁ := by exact_mod_cast hf₁
    have hprod : (0 : ℤ) < (ρ : ℤ) * ((f₁ : ℤ) - 1) :=
      mul_pos hρz (by omega)
    have hsz : (0 : ℤ) ≤ s := by exact_mod_cast Nat.zero_le s
    simp only [Int.natCast_one, one_mul, Int.natCast_zero, zero_mul,
      add_zero] at hbaseWeight hendWeight
    nlinarith
  have hlineZ : (ρ : ℤ) * ((f₁ - 1 : ℕ) : ℤ) =
      (s : ℤ) * ((f₂ - 1 : ℕ) : ℤ) := by
    have hf₁sub : ((f₁ - 1 : ℕ) : ℤ) = f₁ - 1 := by omega
    have hf₂sub : ((f₂ - 1 : ℕ) : ℤ) = f₂ - 1 := by omega
    rw [hf₁sub, hf₂sub]
    linear_combination hendWeight - hbaseWeight
  have hline : ρ * (f₁ - 1) = s * (f₂ - 1) := by exact_mod_cast hlineZ
  exact primitive_direction_of_weight_line ρ s (f₁ - 1) (f₂ - 1)
    hρ (by omega) hcop hline

/-- The finite G13 arithmetic endpoint applied to actual support endpoints
of a homogeneous polynomial. The companion proportionality and the source's
small-degree endpoint inequalities remain explicit hypotheses. -/
theorem homogeneous_small_degree_forbidden_corner
    (R F : MvPolynomial (Fin 2) ℂ) (ρ s u v r t f₁ f₂ : ℕ)
    (degree degreeF : ℤ)
    (hhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degree)
    (hFhom : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degreeF)
    (hend : expo u v ∈ R.support) (hstart : expo r t ∈ R.support)
    (hFbase : expo 1 1 ∈ F.support) (hFend : expo f₁ f₂ ∈ F.support)
    (huv : u < v) (hsmall : u + v ≤ 15)
    (hf₁ : 2 ≤ f₁) (hprop : f₁ * v = f₂ * u)
    (htr : t < r) (hru : r < u)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ))) :
    let d := Nat.gcd (f₁ - 1) (f₂ - 1)
    let ρ' := (f₂ - 1) / d
    let s' := (f₁ - 1) / d
    d = 1 ∧ 0 < ρ' ∧
      ∃ h : ℕ, 2 ≤ h ∧ t ≤ h ∧ v = t + ρ' * h ∧
        ρ' * r + (h - t) * s' = ρ' * h - 1 := by
  have hnormalizedDir := companion_support_recovers_primitive_direction
    F ρ s f₁ f₂ degreeF hdir hf₁ hFhom hFbase hFend
  have hline := homogeneous_endpoints_weight_equation R ρ s u v r t degree
    hhom hend hstart
  have hnormalized :
      let d := Nat.gcd (f₁ - 1) (f₂ - 1)
      let ρ' := (f₂ - 1) / d
      let s' := (f₁ - 1) / d
      ρ' * u + s' * t = ρ' * r + s' * v := by
    dsimp
    rw [← hnormalizedDir.1, ← hnormalizedDir.2]
    exact hline
  exact ggv_small_degree_coordinates_forbidden_corner u v f₁ f₂ r t
    huv hsmall hf₁ hprop htr hru hnormalized

/-- The common homogeneous root fixes the exact weighted degree of a face
written as its outer power. -/
theorem leadingFace_root_power_weight
    (P : A1 ℂ) (R : MvPolynomial (Fin 2) ℂ) (μ : ℂ)
    (ρ s m u v : ℕ) (degree : ℤ)
    (hRne : R ≠ 0) (hμ : μ ≠ 0) (hs : 0 < s)
    (hhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degree)
    (hend : expo u v ∈ R.support)
    (hmax : ∀ d ∈ R.support, d 0 ≤ u)
    (hface : leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ * R ^ m) :
    vDeg ρ (-(s : ℤ)) P.1 =
      (m : ℤ) * ((ρ : ℤ) * u - (s : ℤ) * v) := by
  have hpoint := homogeneous_power_max_x_endpoint R ρ s m u v degree
    hRne hs hhom hend hmax
  have hfacepoint : expo (m * u) (m * v) ∈
      (leadingForm ρ (-(s : ℤ)) P.1).support := by
    rw [hface, MvPolynomial.C_mul', MvPolynomial.support_smul_eq hμ]
    exact hpoint
  have hweight : Finsupp.weight (wt ρ (-(s : ℤ))) (expo (m * u) (m * v)) =
      vDeg ρ (-(s : ℤ)) P.1 := by
    change expo (m * u) (m * v) ∈
      (MvPolynomial.weightedHomogeneousComponent (wt ρ (-(s : ℤ)))
        (vDeg ρ (-(s : ℤ)) P.1) (symbol P.1)).support at hfacepoint
    rw [MvPolynomial.support_weightedHomogeneousComponent] at hfacepoint
    exact (Finset.mem_filter.mp hfacepoint).2
  rw [expo_weight] at hweight
  calc
    vDeg ρ (-(s : ℤ)) P.1 =
        ((m * u : ℕ) : ℤ) * ρ + ((m * v : ℕ) : ℤ) * -(s : ℤ) := hweight.symm
    _ = (m : ℤ) * ((ρ : ℤ) * u - (s : ℤ) * v) := by push_cast; ring

/-- G13's equality of the weighted and total-degree ratios yields the
cross-multiplied total-degree equation once both faces are powers of the
same nonzero-weight homogeneous polynomial. -/
theorem commonPower_weight_ratio_implies_totalDeg_ratio
    (P Q : A1 ℂ) (R : MvPolynomial (Fin 2) ℂ) (μ ν : ℂ)
    (ρ s m n u v : ℕ) (degree : ℤ)
    (hRne : R ≠ 0) (hμ : μ ≠ 0) (hν : ν ≠ 0) (hs : 0 < s)
    (hhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degree)
    (hend : expo u v ∈ R.support)
    (hmax : ∀ d ∈ R.support, d 0 ≤ u)
    (hPface : leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ * R ^ m)
    (hQface : leadingForm ρ (-(s : ℤ)) Q.1 = MvPolynomial.C ν * R ^ n)
    (hrootWeight : (ρ : ℤ) * u - (s : ℤ) * v ≠ 0)
    (hratio : vDeg ρ (-(s : ℤ)) P.1 * (totalDeg Q.1 : ℤ) =
      vDeg ρ (-(s : ℤ)) Q.1 * (totalDeg P.1 : ℤ)) :
    totalDeg P.1 * n = totalDeg Q.1 * m := by
  have hp := leadingFace_root_power_weight P R μ ρ s m u v degree
    hRne hμ hs hhom hend hmax hPface
  have hq := leadingFace_root_power_weight Q R ν ρ s n u v degree
    hRne hν hs hhom hend hmax hQface
  rw [hp, hq] at hratio
  have hcancel : ((ρ : ℤ) * u - (s : ℤ) * v) *
      ((m : ℤ) * totalDeg Q.1) =
      ((ρ : ℤ) * u - (s : ℤ) * v) *
      ((n : ℤ) * totalDeg P.1) := by
    calc
      _ = (m : ℤ) * ((ρ : ℤ) * u - (s : ℤ) * v) * totalDeg Q.1 := by ring
      _ = (n : ℤ) * ((ρ : ℤ) * u - (s : ℤ) * v) * totalDeg P.1 := hratio
      _ = _ := by ring
  have hcross := mul_left_cancel₀ hrootWeight hcancel
  exact_mod_cast (show (totalDeg P.1 : ℤ) * n =
    (totalDeg Q.1 : ℤ) * m by nlinarith [hcross])

/-- The powered endpoint of an actual leading face cannot have larger total
degree than the source Weyl operator. The outer exponent is retained, as in
the degree normalization before the finite table in G13 Corollary 7.4. -/
theorem leadingFace_root_endpoint_scaled_totalDeg_le
    (P : A1 ℂ) (R : MvPolynomial (Fin 2) ℂ) (μ : ℂ)
    (ρ s m u v : ℕ) (degree : ℤ)
    (hRne : R ≠ 0) (hμ : μ ≠ 0) (hs : 0 < s)
    (hhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degree)
    (hend : expo u v ∈ R.support)
    (hmax : ∀ d ∈ R.support, d 0 ≤ u)
    (hface : leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ * R ^ m) :
    m * (u + v) ≤ totalDeg P.1 := by
  have hpoint := homogeneous_power_max_x_endpoint R ρ s m u v degree
    hRne hs hhom hend hmax
  have hfacepoint : expo (m * u) (m * v) ∈
      (leadingForm ρ (-(s : ℤ)) P.1).support := by
    rw [hface, MvPolynomial.C_mul', MvPolynomial.support_smul_eq hμ]
    exact hpoint
  have hsource := weightedComponent_support_subset (symbol P.1)
    ρ (-(s : ℤ)) (vDeg ρ (-(s : ℤ)) P.1) hfacepoint
  have hdegree := MvPolynomial.le_totalDegree hsource
  have hsum : (expo (m * u) (m * v)).sum (fun _ e => e) = m * (u + v) := by
    rw [Finsupp.sum_fintype (expo (m * u) (m * v)) (fun _ e => e) (by simp)]
    simp [Fin.sum_univ_two, expo, Nat.mul_add]
  change (expo (m * u) (m * v)).sum (fun _ e => e) ≤ totalDeg P.1 at hdegree
  rw [hsum] at hdegree
  exact hdegree

/-- The finite G13 obstruction with the degree bound stated as the gcd of the
two source operators' total degrees. The common-power degree ratio remains an
explicit source hypothesis. -/
theorem leadingFace_small_degree_forbidden_corner
    (P Q : A1 ℂ) (R F : MvPolynomial (Fin 2) ℂ) (μ ν : ℂ)
    (ρ s m n u v r t f₁ f₂ : ℕ) (degree : ℤ)
    (hRne : R ≠ 0) (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hs : 0 < s) (hm : 1 ≤ m)
    (hhom : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) degree)
    (hFhom : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) ((ρ : ℤ) - s))
    (hend : expo u v ∈ R.support) (hstart : expo r t ∈ R.support)
    (hmax : ∀ d ∈ R.support, d 0 ≤ u)
    (hFend : expo f₁ f₂ ∈ F.support)
    (hFmax : ∀ d ∈ F.support, d 0 ≤ f₁)
    (hPoisson : poisson R F = R)
    (hface : leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ * R ^ m)
    (hQface : leadingForm ρ (-(s : ℤ)) Q.1 = MvPolynomial.C ν * R ^ n)
    (hPweightPos : 0 < vDeg ρ (-(s : ℤ)) P.1)
    (hcop : Nat.Coprime m n)
    (hweightedRatio : vDeg ρ (-(s : ℤ)) P.1 * (totalDeg Q.1 : ℤ) =
      vDeg ρ (-(s : ℤ)) Q.1 * (totalDeg P.1 : ℤ))
    (hsmall : Nat.gcd (totalDeg P.1) (totalDeg Q.1) ≤ 15)
    (hstartGrade : 0 < grade (expo (m * r) (m * t)))
    (hendGrade : grade (expo (m * u) (m * v)) < 0)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ))) :
    let d := Nat.gcd (f₁ - 1) (f₂ - 1)
    let ρ' := (f₂ - 1) / d
    let s' := (f₁ - 1) / d
    d = 1 ∧ 0 < ρ' ∧
      ∃ h : ℕ, 2 ≤ h ∧ t ≤ h ∧ v = t + ρ' * h ∧
        ρ' * r + (h - t) * s' = ρ' * h - 1 := by
  have hendDegree := leadingFace_root_endpoint_scaled_totalDeg_le P R μ ρ s m u v
    degree hRne hμ hs hhom hend hmax hface
  have hrootWeight : (ρ : ℤ) * u - (s : ℤ) * v ≠ 0 := by
    intro hz
    have hp := leadingFace_root_power_weight P R μ ρ s m u v degree
      hRne hμ hs hhom hend hmax hface
    have hpzero : vDeg ρ (-(s : ℤ)) P.1 = 0 := by simpa [hz] using hp
    omega
  have hratio := commonPower_weight_ratio_implies_totalDeg_ratio
    P Q R μ ν ρ s m n u v degree hRne hμ hν hs hhom hend hmax
    hface hQface hrootWeight hweightedRatio
  have hnormalized := coprime_degree_ratio_normalization
    (totalDeg P.1) (totalDeg Q.1) m n (by omega) hcop hratio
  have hPbound : totalDeg P.1 ≤ m * 15 := by
    rw [hnormalized.1]
    exact Nat.mul_le_mul_left m hsmall
  have hrootSmall : u + v ≤ 15 := by
    by_contra hn
    have hlt : 15 < u + v := by omega
    have hmul : m * 15 < m * (u + v) :=
      Nat.mul_lt_mul_of_pos_left hlt (by omega)
    omega
  obtain ⟨htr, huv, hru⟩ := homogeneous_power_crossing_coordinates
    R ρ s m u v r t degree hs hhom hend hstart hmax hstartGrade hendGrade
  have hrootStartGrade : 0 < grade (expo r t) := by
    simp [grade, expo]
    omega
  have hrootEndGrade : grade (expo u v) < 0 := by
    simp [grade, expo]
    omega
  have hsρ : s < ρ := by
    have := hdir.2
    omega
  have hFbase : expo 1 1 ∈ F.support :=
    homogeneous_companion_base_mem R F ρ s hs hsρ hRne hFhom hPoisson
  have hFnonmono := crossing_poisson_companion_nonmonomial
    R F (expo r t) (expo u v) hFbase hPoisson hstart hend
      hrootStartGrade hrootEndGrade
  have hf₁ := homogeneous_companion_end_x_ge_two F ρ s f₁ ((ρ : ℤ) - s)
    hs hdir hFhom hFbase hFmax hFnonmono
  have hprop := homogeneous_companion_end_proportional R F ρ s u v f₁ f₂
    degree ((ρ : ℤ) - s) hs hf₁ hhom hFhom hend hFend hmax hFmax hPoisson
  exact homogeneous_small_degree_forbidden_corner R F ρ s u v r t f₁ f₂
    degree ((ρ : ℤ) - s) hhom hFhom hend hstart hFbase hFend huv
    hrootSmall hf₁ hprop htr hru hdir

end Dixmier.Weyl
