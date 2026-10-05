/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Validation
public import DixmierFormal.Weyl.NewtonRoofSupport
public import Mathlib.Analysis.Convex.Combination

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Exponents selected on commuting Poisson faces

This module proves the exact Poisson bracket formula for two PBW monomials, extracts a
collinearity constraint for unique maximizers, and selects collinear endpoint pairs from any two
Poisson-commuting polynomials homogeneous for a common nonzero integer weight. These are local
inputs to the zero-bracket Newton-roof comparison; the positive-cone comparison itself remains separate.
-/

namespace Dixmier.Weyl

private theorem coeff_sub_local (d : Fin 2 →₀ ℕ) (p q : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.coeff d (p-q) = MvPolynomial.coeff d p - MvPolynomial.coeff d q := by
  simpa only [MvPolynomial.coeffAddMonoidHom_apply] using
    (MvPolynomial.coeffAddMonoidHom d).map_sub p q

private theorem expo_sub_y (i j : ℕ) :
    expo i j - Finsupp.single 1 1 = expo i (j-1) := by
  ext n
  fin_cases n <;> simp [expo]

private theorem expo_sub_x (i j : ℕ) :
    expo i j - Finsupp.single 0 1 = expo (i-1) j := by
  ext n
  fin_cases n <;> simp [expo]

private theorem pderiv_monomial_y (i j : ℕ) (a : ℂ) :
    MvPolynomial.pderiv 1 (MvPolynomial.monomial (expo i j) a) =
      MvPolynomial.monomial (expo i (j-1)) (a * (j : ℂ)) := by
  rw [MvPolynomial.pderiv_monomial, expo_sub_y]
  congr 1
  simp [expo]

private theorem pderiv_monomial_x (i j : ℕ) (a : ℂ) :
    MvPolynomial.pderiv 0 (MvPolynomial.monomial (expo i j) a) =
      MvPolynomial.monomial (expo (i-1) j) (a * (i : ℂ)) := by
  rw [MvPolynomial.pderiv_monomial, expo_sub_x]
  congr 1
  simp [expo]

private theorem expo_subsum_term1 (i j k l : ℕ) (hj : 0 < j) (hk : 0 < k) :
    expo i (j-1) + expo (k-1) l = expo (i+k-1) (j+l-1) := by
  ext n
  fin_cases n <;> simp [expo] <;> omega

private theorem expo_subsum_term2 (i j k l : ℕ) (hi : 0 < i) (hl : 0 < l) :
    expo (i-1) j + expo k (l-1) = expo (i+k-1) (j+l-1) := by
  ext n
  fin_cases n <;> simp [expo] <;> omega

private theorem monomial_sub (e : Fin 2 →₀ ℕ) (a b : ℂ) :
    MvPolynomial.monomial e a - MvPolynomial.monomial e b =
      MvPolynomial.monomial e (a-b) := by
  apply MvPolynomial.ext
  intro d
  rw [coeff_sub_local]
  simp only [MvPolynomial.coeff_monomial]
  by_cases hd : e = d
  · simp [hd]
  · simp [hd]

private theorem aligned_formula (e : Fin 2 →₀ ℕ) (c1 c2 : ℂ) (a b det : ℂ)
    (h : c1-c2 = det*(a*b)) :
    MvPolynomial.monomial e c1 - MvPolynomial.monomial e c2 =
      det • MvPolynomial.monomial e (a*b) := by
  rw [monomial_sub, h, MvPolynomial.smul_monomial]
  rfl

private theorem monomial_eq_smul (e : Fin 2 →₀ ℕ) (c r d : ℂ)
    (h : c = r*d) :
    MvPolynomial.monomial e c = r • MvPolynomial.monomial e d := by
  rw [MvPolynomial.smul_monomial, h]
  simp only [smul_eq_mul]

/-- The Poisson bracket of two PBW monomials, including the exponent reductions on the axes. -/
theorem poisson_monomial_formula (i j k l : ℕ) (a b : ℂ) :
    poisson (MvPolynomial.monomial (expo i j) a)
      (MvPolynomial.monomial (expo k l) b) =
      (((j : ℂ) * (k : ℂ) - (i : ℂ) * (l : ℂ)) : ℂ) •
        MvPolynomial.monomial (expo (i+k-1) (j+l-1)) (a*b) := by
  unfold poisson
  rw [pderiv_monomial_y i j a, pderiv_monomial_x k l b,
      pderiv_monomial_x i j a, pderiv_monomial_y k l b]
  by_cases hjk : j = 0 ∨ k = 0
  · by_cases hil : i = 0 ∨ l = 0
    · rcases hjk with hj | hk
      · rcases hil with hi | hl <;> simp_all
      · rcases hil with hi | hl <;> simp_all
    · have hi : 0 < i := by omega
      have hl : 0 < l := by omega
      rcases hjk with hj | hk
      · simp [hj]
        rw [expo_subsum_term2 i 0 k l hi hl]
        simp only [zero_add]
        apply monomial_eq_smul
        ring
      · simp [hk]
        rw [expo_subsum_term2 i j 0 l hi hl]
        apply monomial_eq_smul
        ring
  · have hj : 0 < j := by omega
    have hk : 0 < k := by omega
    by_cases hil : i = 0 ∨ l = 0
    · rcases hil with hi | hl
      · simp [hi]
        rw [expo_subsum_term1 0 j k l hj hk]
        simp only [zero_add]
        apply monomial_eq_smul
        ring
      · simp [hl]
        rw [expo_subsum_term1 i j k 0 hj hk]
        apply monomial_eq_smul
        ring
    · have hi : 0 < i := by omega
      have hl : 0 < l := by omega
      rw [MvPolynomial.monomial_mul, MvPolynomial.monomial_mul]
      rw [expo_subsum_term1 i j k l hj hk,
          expo_subsum_term2 i j k l hi hl]
      apply aligned_formula
      ring


/-- The monomial Poisson formula in coordinate-free `Finsupp` exponent notation. -/
theorem poisson_monomial_general (d e : Fin 2 →₀ ℕ) (a b : ℂ) :
    poisson (MvPolynomial.monomial d a) (MvPolynomial.monomial e b) =
      ((d 1 : ℂ) * (e 0 : ℂ) - (d 0 : ℂ) * (e 1 : ℂ)) •
        MvPolynomial.monomial (d + e - Finsupp.single 0 1 - Finsupp.single 1 1) (a*b) := by
  obtain ⟨⟨i,j⟩, hd⟩ := expo_surjective d
  obtain ⟨⟨k,l⟩, he⟩ := expo_surjective e
  change expo i j = d at hd
  change expo k l = e at he
  have hexp : expo (i+k-1) (j+l-1) =
      expo i j + expo k l - Finsupp.single 0 1 - Finsupp.single 1 1 := by
    ext n
    fin_cases n <;> simp [expo]
  rw [← hd, ← he, poisson_monomial_formula, hexp]
  simp [expo]

/-- Unique maximizing endpoints are collinear whenever the top allowed
component of their Poisson bracket vanishes. The full bracket need not be zero. -/
theorem poisson_unique_maximizers_collinear_of_top_zero (v : Fin 2 → ℤ)
    (p q : MvPolynomial (Fin 2) ℂ)
    {d e : Fin 2 →₀ ℕ}
    (htopZero : MvPolynomial.weightedHomogeneousComponent v
      (Finsupp.weight v d + Finsupp.weight v e - (v 0 + v 1)) (poisson p q) = 0)
    (hd : d ∈ p.support) (he : e ∈ q.support)
    (hdmax : ∀ x ∈ p.support, Finsupp.weight v x ≤ Finsupp.weight v d)
    (hemax : ∀ x ∈ q.support, Finsupp.weight v x ≤ Finsupp.weight v e)
    (hduniq : ∀ x ∈ p.support, Finsupp.weight v x = Finsupp.weight v d → x = d)
    (heuniq : ∀ x ∈ q.support, Finsupp.weight v x = Finsupp.weight v e → x = e) :
    (d 1 : ℂ) * (e 0 : ℂ) - (d 0 : ℂ) * (e 1 : ℂ) = 0 := by
  let m : ℤ := Finsupp.weight v d
  let n : ℤ := Finsupp.weight v e
  have hpbound : ∀ x ∈ p.support, Finsupp.weight v x ≤ m := by
    intro x hx
    simpa [m] using hdmax x hx
  have hqbound : ∀ x ∈ q.support, Finsupp.weight v x ≤ n := by
    intro x hx
    simpa [n] using hemax x hx
  have hpc : MvPolynomial.weightedHomogeneousComponent v m p =
      MvPolynomial.monomial d (MvPolynomial.coeff d p) := by
    calc
      _ = MvPolynomial.monomial d
          (MvPolynomial.coeff d (MvPolynomial.weightedHomogeneousComponent v m p)) :=
        MvPolynomial.eq_monomial_of_support_subset_singleton (by
          intro x hx
          simp only [MvPolynomial.support_weightedHomogeneousComponent, Finset.mem_filter] at hx
          exact hduniq x hx.1 hx.2)
      _ = MvPolynomial.monomial d (MvPolynomial.coeff d p) := by
        congr 1
        simp [MvPolynomial.coeff_weightedHomogeneousComponent, m]
  have hqc : MvPolynomial.weightedHomogeneousComponent v n q =
      MvPolynomial.monomial e (MvPolynomial.coeff e q) := by
    calc
      _ = MvPolynomial.monomial e
          (MvPolynomial.coeff e (MvPolynomial.weightedHomogeneousComponent v n q)) :=
        MvPolynomial.eq_monomial_of_support_subset_singleton (by
          intro x hx
          simp only [MvPolynomial.support_weightedHomogeneousComponent, Finset.mem_filter] at hx
          exact heuniq x hx.1 hx.2)
      _ = MvPolynomial.monomial e (MvPolynomial.coeff e q) := by
        congr 1
        simp [MvPolynomial.coeff_weightedHomogeneousComponent, n]
  have htop := poisson_weightedComponent_of_bounds v p q m n hpbound hqbound
  have hmono :
      poisson (MvPolynomial.monomial d (MvPolynomial.coeff d p))
        (MvPolynomial.monomial e (MvPolynomial.coeff e q)) = 0 := by
    simpa [m, n, hpc, hqc] using htop.symm.trans htopZero
  rw [poisson_monomial_general] at hmono
  have hcoeffp : MvPolynomial.coeff d p ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have hcoeffq : MvPolynomial.coeff e q ≠ 0 := MvPolynomial.mem_support_iff.mp he
  have hmon : MvPolynomial.monomial
      (d + e - Finsupp.single 0 1 - Finsupp.single 1 1)
      (MvPolynomial.coeff d p * MvPolynomial.coeff e q) ≠ 0 := by
    intro hz
    have hzeroCoeff := MvPolynomial.monomial_eq_zero.mp hz
    exact (mul_ne_zero hcoeffp hcoeffq) hzeroCoeff
  exact (smul_eq_zero.mp hmono).resolve_right hmon

/-- If two Poisson-commuting polynomials have unique maximizers for a common
integer weight, then the maximizing exponent vectors are collinear. -/
theorem poisson_unique_maximizers_collinear (v : Fin 2 → ℤ)
    (p q : MvPolynomial (Fin 2) ℂ)
    (hbr : poisson p q = 0)
    {d e : Fin 2 →₀ ℕ}
    (hd : d ∈ p.support) (he : e ∈ q.support)
    (hdmax : ∀ x ∈ p.support, Finsupp.weight v x ≤ Finsupp.weight v d)
    (hemax : ∀ x ∈ q.support, Finsupp.weight v x ≤ Finsupp.weight v e)
    (hduniq : ∀ x ∈ p.support, Finsupp.weight v x = Finsupp.weight v d → x = d)
    (heuniq : ∀ x ∈ q.support, Finsupp.weight v x = Finsupp.weight v e → x = e) :
    (d 1 : ℂ) * (e 0 : ℂ) - (d 0 : ℂ) * (e 1 : ℂ) = 0 := by
  apply poisson_unique_maximizers_collinear_of_top_zero v p q
  · simp [hbr]
  · exact hd
  · exact he
  · exact hdmax
  · exact hemax
  · exact hduniq
  · exact heuniq

/-- The integer weight perpendicular to a nonzero weight in two variables. -/
def perpWeight (w : Fin 2 → ℤ) : Fin 2 → ℤ := ![w 1, -w 0]

theorem exponent_eq_of_weights_eq_of_perp_eq
    (w : Fin 2 → ℤ) {d e : Fin 2 →₀ ℕ}
    (hw : w 0 ≠ 0 ∨ w 1 ≠ 0)
    (h₁ : Finsupp.weight w d = Finsupp.weight w e)
    (h₂ : Finsupp.weight (perpWeight w) d = Finsupp.weight (perpWeight w) e) : d = e := by
  have h₁' : (d 0 : ℤ) * w 0 + (d 1 : ℤ) * w 1 =
      (e 0 : ℤ) * w 0 + (e 1 : ℤ) * w 1 := by
    simpa [Finsupp.weight_eq_sum, Fin.sum_univ_succ, Fin.sum_univ_succ] using h₁
  have h₂' : (d 0 : ℤ) * w 1 - (d 1 : ℤ) * w 0 =
      (e 0 : ℤ) * w 1 - (e 1 : ℤ) * w 0 := by
    simpa [perpWeight, Finsupp.weight_eq_sum, Fin.sum_univ_succ, sub_eq_add_neg] using h₂
  have hc0 : (w 0 * w 0 + w 1 * w 1) * ((d 0 : ℤ) - e 0) = 0 := by
    linear_combination w 0 * h₁' + w 1 * h₂'
  have hc1 : (w 0 * w 0 + w 1 * w 1) * ((d 1 : ℤ) - e 1) = 0 := by
    linear_combination w 1 * h₁' - w 0 * h₂'
  have hsq : w 0 * w 0 + w 1 * w 1 ≠ 0 := by
    intro hz
    rcases hw with h0 | h1
    · have hpos : 0 < w 0 * w 0 := mul_self_pos.mpr h0
      nlinarith [mul_self_nonneg (w 1)]
    · have hpos : 0 < w 1 * w 1 := mul_self_pos.mpr h1
      nlinarith [mul_self_nonneg (w 0)]
  have hdiff0 : (d 0 : ℤ) = e 0 := by
    have := (mul_eq_zero.mp hc0).resolve_left hsq
    exact sub_eq_zero.mp this
  have hdiff1 : (d 1 : ℤ) = e 1 := by
    have := (mul_eq_zero.mp hc1).resolve_left hsq
    exact sub_eq_zero.mp this
  ext i
  fin_cases i
  · exact_mod_cast hdiff0
  · exact_mod_cast hdiff1

private theorem perp_neg_eq (w : Fin 2 → ℤ) :
    (fun i => -perpWeight w i) = ![-w 1, w 0] := by
  funext i
  fin_cases i <;> simp [perpWeight]

private theorem endpointOfHomogeneousSupport
    (w : Fin 2 → ℤ) (p : MvPolynomial (Fin 2) ℂ) (degree : ℤ)
    (aux : Fin 2 → ℤ) (hwnz : w 0 ≠ 0 ∨ w 1 ≠ 0)
    (haux : aux = perpWeight w ∨ aux = ![-w 1, w 0])
    (hdeg : ∀ d ∈ p.support, Finsupp.weight w d = degree)
    (hpne : p ≠ 0) :
    ∃ d ∈ p.support, (∀ x ∈ p.support, Finsupp.weight aux x ≤ Finsupp.weight aux d) ∧
      (∀ x ∈ p.support, Finsupp.weight aux x = Finsupp.weight aux d → x = d) := by
  classical
  have hpsupport : p.support.Nonempty := MvPolynomial.support_nonempty.mpr hpne
  obtain ⟨d, hd, hdmax⟩ := Finset.exists_max_image p.support (Finsupp.weight aux) hpsupport
  refine ⟨d, hd, hdmax, ?_⟩
  intro x hx hxaux
  have hwd : Finsupp.weight w x = Finsupp.weight w d := (hdeg x hx).trans (hdeg d hd).symm
  have haux' : Finsupp.weight (perpWeight w) x = Finsupp.weight (perpWeight w) d := by
    rcases haux with h | h
    · simpa [h] using hxaux
    · have hxaux' := hxaux
      have hneg : - Finsupp.weight (perpWeight w) x =
          - Finsupp.weight (perpWeight w) d := by
        simp [h, perpWeight, Finsupp.weight_eq_sum, Fin.sum_univ_succ] at hxaux' ⊢
        linarith
      exact neg_injective hneg
  exact exponent_eq_of_weights_eq_of_perp_eq w hwnz hwd haux'

/-- For two nonzero polynomials homogeneous for the same nonzero integer weight and with zero
Poisson bracket, the maximizing and minimizing endpoints selected by the perpendicular weight
are pairwise collinear across the two supports. This also resolves ties on the original
homogeneous faces by selecting unique extrema with the perpendicular weight. -/
theorem poisson_homogeneous_support_endpoints_collinear
    (w : Fin 2 → ℤ) (degreeP degreeQ : ℤ)
    (p q : MvPolynomial (Fin 2) ℂ)
    (hwnz : w 0 ≠ 0 ∨ w 1 ≠ 0)
    (hpdeg : ∀ d ∈ p.support, Finsupp.weight w d = degreeP)
    (hqdeg : ∀ e ∈ q.support, Finsupp.weight w e = degreeQ)
    (hpne : p ≠ 0) (hqne : q ≠ 0)
    (hbr : poisson p q = 0) :
    ∃ dp dm ep em, dp ∈ p.support ∧ dm ∈ p.support ∧
      ep ∈ q.support ∧ em ∈ q.support ∧
      (∀ x ∈ p.support, Finsupp.weight (perpWeight w) x ≤ Finsupp.weight (perpWeight w) dp) ∧
      (∀ x ∈ p.support, Finsupp.weight (perpWeight w) dm ≤ Finsupp.weight (perpWeight w) x) ∧
      (∀ x ∈ q.support, Finsupp.weight (perpWeight w) x ≤ Finsupp.weight (perpWeight w) ep) ∧
      (∀ x ∈ q.support, Finsupp.weight (perpWeight w) em ≤ Finsupp.weight (perpWeight w) x) ∧
      (dp 1 : ℂ) * (ep 0 : ℂ) - (dp 0 : ℂ) * (ep 1 : ℂ) = 0 ∧
      (dm 1 : ℂ) * (em 0 : ℂ) - (dm 0 : ℂ) * (em 1 : ℂ) = 0 := by
  classical
  let v : Fin 2 → ℤ := perpWeight w
  let vm : Fin 2 → ℤ := ![-w 1, w 0]
  have hv : v = perpWeight w := rfl
  have hvm : vm = ![-w 1, w 0] := rfl
  obtain ⟨dp, hdp, hdpmax, hdpuniq⟩ :=
    endpointOfHomogeneousSupport w p degreeP v hwnz (Or.inl hv) hpdeg hpne
  obtain ⟨ep, hep, hepmax, hepuniq⟩ :=
    endpointOfHomogeneousSupport w q degreeQ v hwnz (Or.inl hv) hqdeg hqne
  obtain ⟨dm, hdm, hdmmax, hdmuniq⟩ :=
    endpointOfHomogeneousSupport w p degreeP vm hwnz (Or.inr hvm) hpdeg hpne
  obtain ⟨em, hem, hemmax, hemuniq⟩ :=
    endpointOfHomogeneousSupport w q degreeQ vm hwnz (Or.inr hvm) hqdeg hqne
  have hminus := poisson_unique_maximizers_collinear vm p q hbr hdm hem hdmmax hemmax hdmuniq hemuniq
  have hdmmin : ∀ x ∈ p.support, Finsupp.weight (perpWeight w) dm ≤ Finsupp.weight (perpWeight w) x := by
    intro x hx
    have hle := hdmmax x hx
    have hle' := hle
    simp [vm, Finsupp.weight_eq_sum, Fin.sum_univ_succ] at hle'
    have hneg : - Finsupp.weight (perpWeight w) x ≤
        - Finsupp.weight (perpWeight w) dm := by
      simp [perpWeight, Finsupp.weight_eq_sum, Fin.sum_univ_succ]
      linarith
    exact (neg_le_neg_iff.mp hneg)
  have hemmin : ∀ x ∈ q.support, Finsupp.weight (perpWeight w) em ≤ Finsupp.weight (perpWeight w) x := by
    intro x hx
    have hle := hemmax x hx
    have hle' := hle
    simp [vm, Finsupp.weight_eq_sum, Fin.sum_univ_succ] at hle'
    have hneg : - Finsupp.weight (perpWeight w) x ≤
        - Finsupp.weight (perpWeight w) em := by
      simp [perpWeight, Finsupp.weight_eq_sum, Fin.sum_univ_succ]
      linarith
    exact (neg_le_neg_iff.mp hneg)
  have hplus := poisson_unique_maximizers_collinear v p q hbr hdp hep hdpmax hepmax hdpuniq hepuniq
  exact ⟨dp, dm, ep, em, hdp, hdm, hep, hem, hdpmax, hdmmin,
    hepmax, hemmin, hplus, hminus⟩

def realWeight (w : Fin 2 → ℤ) (d : Fin 2 →₀ ℕ) : ℝ :=
  (w 0 : ℝ) * (d 0 : ℝ) + (w 1 : ℝ) * (d 1 : ℝ)

def realPerpWeight (w : Fin 2 → ℤ) (d : Fin 2 →₀ ℕ) : ℝ :=
  (w 1 : ℝ) * (d 0 : ℝ) - (w 0 : ℝ) * (d 1 : ℝ)

def pointWeight (w : Fin 2 → ℤ) (z : ℝ × ℝ) : ℝ :=
  (w 0 : ℝ) * z.1 + (w 1 : ℝ) * z.2

def pointPerpWeight (w : Fin 2 → ℤ) (z : ℝ × ℝ) : ℝ :=
  (w 1 : ℝ) * z.1 - (w 0 : ℝ) * z.2

private theorem realWeight_eq_cast (w : Fin 2 → ℤ) (d : Fin 2 →₀ ℕ) :
    realWeight w d = ((Finsupp.weight w d : ℤ) : ℝ) := by
  simp [realWeight, Finsupp.weight_eq_sum, Fin.sum_univ_succ]
  ring

private theorem realPerpWeight_eq_cast (w : Fin 2 → ℤ) (d : Fin 2 →₀ ℕ) :
    realPerpWeight w d = ((Finsupp.weight (perpWeight w) d : ℤ) : ℝ) := by
  simp [realPerpWeight, perpWeight, Finsupp.weight_eq_sum, Fin.sum_univ_succ]
  ring

/-- Every exponent on a nonzero weighted-homogeneous support lies on the segment joining the
unique perpendicular-weight maximum and minimum. This turns endpoint information into a
statement about the entire Newton face, including faces with ties in the original weight. -/
theorem homogeneous_support_exponent_mem_endpoint_hull
    (w : Fin 2 → ℤ) (degree : ℤ) (p : MvPolynomial (Fin 2) ℂ)
    (hwnz : w 0 ≠ 0 ∨ w 1 ≠ 0)
    (hdeg : ∀ x ∈ p.support, Finsupp.weight w x = degree)
    {dhi dlo : Fin 2 →₀ ℕ}
    (hdhi : dhi ∈ p.support) (hdlo : dlo ∈ p.support)
    (hmax : ∀ x ∈ p.support,
      Finsupp.weight (perpWeight w) x ≤ Finsupp.weight (perpWeight w) dhi)
    (hmin : ∀ x ∈ p.support,
      Finsupp.weight (perpWeight w) dlo ≤ Finsupp.weight (perpWeight w) x)
    (x : Fin 2 →₀ ℕ) (hx : x ∈ p.support) :
    exponentPoint x ∈ convexHull ℝ {exponentPoint dhi, exponentPoint dlo} := by
  classical
  have hW (y : Fin 2 →₀ ℕ) (hy : y ∈ p.support) :
      realWeight w y = (degree : ℝ) := by
    rw [realWeight_eq_cast]
    exact_mod_cast hdeg y hy
  have hupper : realPerpWeight w x ≤ realPerpWeight w dhi := by
    rw [realPerpWeight_eq_cast, realPerpWeight_eq_cast]
    exact_mod_cast hmax x hx
  have hlower : realPerpWeight w dlo ≤ realPerpWeight w x := by
    rw [realPerpWeight_eq_cast, realPerpWeight_eq_cast]
    exact_mod_cast hmin x hx
  have hdifference : realPerpWeight w dlo ≤ realPerpWeight w dhi := by
    rw [realPerpWeight_eq_cast w dlo, realPerpWeight_eq_cast w dhi]
    exact_mod_cast hmax dlo hdlo
  by_cases heq : realPerpWeight w dhi = realPerpWeight w dlo
  · have haux : Finsupp.weight (perpWeight w) x = Finsupp.weight (perpWeight w) dhi := by
      have heqInt : Finsupp.weight (perpWeight w) dlo =
          Finsupp.weight (perpWeight w) dhi := by
        rw [realPerpWeight_eq_cast w dhi, realPerpWeight_eq_cast w dlo] at heq
        exact_mod_cast heq.symm
      have hleft : Finsupp.weight (perpWeight w) dhi ≤
          Finsupp.weight (perpWeight w) x := by
        simpa [heqInt] using hmin x hx
      have hright : Finsupp.weight (perpWeight w) x ≤
          Finsupp.weight (perpWeight w) dhi := hmax x hx
      exact le_antisymm hright hleft
    have hw : Finsupp.weight w x = Finsupp.weight w dhi :=
      (hdeg x hx).trans (hdeg dhi hdhi).symm
    have heqPoint : x = dhi := exponent_eq_of_weights_eq_of_perp_eq w hwnz hw haux
    subst x
    exact subset_convexHull ℝ _ (by simp)
  · have hstrict : realPerpWeight w dlo < realPerpWeight w dhi :=
      lt_of_le_of_ne hdifference (Ne.symm heq)
    let t : ℝ := (realPerpWeight w x - realPerpWeight w dlo) /
      (realPerpWeight w dhi - realPerpWeight w dlo)
    have ht0 : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg (sub_nonneg.mpr hlower)
        (le_of_lt (sub_pos.mpr hstrict))
    have ht1 : t ≤ 1 := by
      dsimp [t]
      rw [div_le_one (sub_pos.mpr hstrict)]
      linarith [hupper, hlower]
    let z : ℝ × ℝ := t • exponentPoint dhi + (1-t) • exponentPoint dlo
    have hWz' : pointWeight w z = (degree : ℝ) := by
      have h1 := hW dhi hdhi
      have h2 := hW dlo hdlo
      dsimp [pointWeight, z, exponentPoint, realWeight] at h1 h2 ⊢
      nlinarith
    have hWz : realWeight w x = pointWeight w z := (hW x hx).trans hWz'.symm
    have hdenne : realPerpWeight w dhi - realPerpWeight w dlo ≠ 0 :=
      ne_of_gt (sub_pos.mpr hstrict)
    have htEq : (realPerpWeight w dhi - realPerpWeight w dlo) * t =
        realPerpWeight w x - realPerpWeight w dlo := by
      dsimp [t]
      field_simp [hdenne]
    have htInterp : realPerpWeight w x =
        t * realPerpWeight w dhi + (1-t) * realPerpWeight w dlo := by
      nlinarith [htEq]
    have hVz' : pointPerpWeight w z =
        t * realPerpWeight w dhi + (1-t) * realPerpWeight w dlo := by
      dsimp [pointPerpWeight, z, exponentPoint, realPerpWeight]
      ring_nf
    have hVz : realPerpWeight w x = pointPerpWeight w z := htInterp.trans hVz'.symm
    let a : ℝ := (w 0 : ℝ)
    let b : ℝ := (w 1 : ℝ)
    have hwDiff : a * ((exponentPoint x).1-z.1) +
        b * ((exponentPoint x).2-z.2) = 0 := by
      have := hWz
      dsimp [realWeight, pointWeight, a, b, exponentPoint] at this ⊢
      linarith
    have hvDiff : b * ((exponentPoint x).1-z.1) -
        a * ((exponentPoint x).2-z.2) = 0 := by
      have := hVz
      dsimp [realPerpWeight, pointPerpWeight, a, b, exponentPoint] at this ⊢
      linarith
    have hsq : a*a+b*b ≠ 0 := by
      rcases hwnz with h0 | h1
      · have ha : a ≠ 0 := by dsimp [a]; exact_mod_cast h0
        have hp : 0 < a*a := mul_self_pos.mpr ha
        nlinarith [mul_self_nonneg b]
      · have hb : b ≠ 0 := by dsimp [b]; exact_mod_cast h1
        have hp : 0 < b*b := mul_self_pos.mpr hb
        nlinarith [mul_self_nonneg a]
    have hx0 : (a*a+b*b)*((exponentPoint x).1-z.1) = 0 := by
      linear_combination a*hwDiff + b*hvDiff
    have hx1 : (a*a+b*b)*((exponentPoint x).2-z.2) = 0 := by
      linear_combination b*hwDiff - a*hvDiff
    have hpoint : exponentPoint x = z := by
      apply Prod.ext
      · have hzero := (mul_eq_zero.mp hx0).resolve_left hsq
        exact sub_eq_zero.mp hzero
      · have hzero := (mul_eq_zero.mp hx1).resolve_left hsq
        exact sub_eq_zero.mp hzero
    rw [hpoint]
    apply mem_convexHull_of_exists_fintype
      (w := ![t,1-t]) (z := ![exponentPoint dhi, exponentPoint dlo])
    · intro i
      fin_cases i <;> simp [ht0, ht1]
    · simp [Fin.sum_univ_succ]
    · intro i
      fin_cases i <;> simp
    · simp [Fin.sum_univ_succ, z]

end Dixmier.Weyl
