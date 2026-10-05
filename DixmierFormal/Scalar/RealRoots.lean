/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Complex.Basic

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Real roots and the first-root sign argument

* a real polynomial of odd degree has a real root;
* the first-root sign argument: a real polynomial with negative constant term whose real roots
  `γ` all satisfy `γ F'(γ) < 0` has no real roots;
* a complex polynomial with real coefficients is the image of a real polynomial.
-/

namespace Dixmier

open Polynomial Filter

/-- A real polynomial of odd degree has a real root. -/
theorem exists_isRoot_of_odd_natDegree {p : ℝ[X]} (hp : Odd p.natDegree) : ∃ x, p.IsRoot x := by
  suffices H : ∀ q : ℝ[X], Odd q.natDegree → 0 < q.leadingCoeff → ∃ x, q.IsRoot x by
    have hp0 : p ≠ 0 := ne_zero_of_natDegree_gt hp.pos
    rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp0) with hneg | hpos
    · obtain ⟨x, hx⟩ := H (-p) (by rwa [natDegree_neg]) (by rw [leadingCoeff_neg]; linarith)
      exact ⟨x, by simpa using hx⟩
    · exact H p hp hpos
  intro q hq hlc
  have hqdeg : 0 < q.degree := natDegree_pos_iff_degree_pos.mp hq.pos
  obtain ⟨b, hb⟩ := ((q.tendsto_atTop_of_leadingCoeff_nonneg hqdeg hlc.le).eventually
    (eventually_gt_atTop 0)).exists
  have hq'deg : (q.comp (-X)).natDegree = q.natDegree := by
    rw [natDegree_comp, natDegree_neg, natDegree_X, mul_one]
  have hq'lc : (q.comp (-X)).leadingCoeff = -q.leadingCoeff := by
    rw [leadingCoeff_comp (by rw [natDegree_neg, natDegree_X]; exact one_ne_zero),
      leadingCoeff_neg, leadingCoeff_X, hq.neg_one_pow, mul_neg_one]
  have hq'deg' : 0 < (q.comp (-X)).degree := natDegree_pos_iff_degree_pos.mp (hq'deg ▸ hq.pos)
  obtain ⟨a, ha⟩ := (((q.comp (-X)).tendsto_atBot_of_leadingCoeff_nonpos hq'deg'
    (by rw [hq'lc]; linarith)).eventually (eventually_lt_atBot 0)).exists
  have hqa : q.eval (-a) < 0 := by simpa [eval_comp] using ha
  obtain ⟨x, hx⟩ := intermediate_value_univ (-a) b q.continuous ⟨hqa.le, hb.le⟩
  exact ⟨x, hx⟩

/-- A real polynomial with no real root has even degree. -/
theorem even_natDegree_of_forall_not_isRoot {p : ℝ[X]} (h : ∀ x, ¬ p.IsRoot x) :
    Even p.natDegree := by
  by_contra hodd
  obtain ⟨x, hx⟩ := exists_isRoot_of_odd_natDegree (Nat.not_even_iff_odd.mp hodd)
  exact h x hx

/-- No positive root: if `F(0) < 0` and `γ F'(γ) < 0` at every real root, then `F` has no
positive root.  The first positive root would have to be crossed upwards. -/
theorem not_isRoot_of_pos {F : ℝ[X]} (hF0 : F.eval 0 < 0)
    (hslope : ∀ γ, F.IsRoot γ → γ * (derivative F).eval γ < 0) {γ : ℝ} (hγ : 0 < γ) :
    ¬ F.IsRoot γ := by
  classical
  intro hroot
  have hF : F ≠ 0 := by rintro rfl; simp at hF0
  set P := F.roots.toFinset.filter (fun x => 0 < x) with hPdef
  have hmemP : ∀ x, x ∈ P ↔ F.IsRoot x ∧ 0 < x := by
    intro x; simp [hPdef, Multiset.mem_toFinset, mem_roots hF]
  have hP : P.Nonempty := ⟨γ, (hmemP γ).mpr ⟨hroot, hγ⟩⟩
  set γ₀ := P.min' hP with hγ₀def
  obtain ⟨hγ₀root, hγ₀pos⟩ := (hmemP γ₀).mp (Finset.min'_mem P hP)
  have hmin : ∀ x, 0 < x → F.IsRoot x → γ₀ ≤ x :=
    fun x hx hrx => Finset.min'_le P x ((hmemP x).mpr ⟨hrx, hx⟩)
  obtain ⟨G, hG⟩ : ∃ G, F = (X - C γ₀) * G :=
    ⟨F /ₘ (X - C γ₀), (mul_divByMonic_eq_iff_isRoot.mpr hγ₀root).symm⟩
  have hGγ : G.eval γ₀ = (derivative F).eval γ₀ := by rw [hG, derivative_mul]; simp
  have hGγneg : G.eval γ₀ < 0 := by
    have h := hslope γ₀ hγ₀root
    rw [← hGγ] at h
    by_contra hge; push Not at hge
    exact absurd h (not_lt.mpr (mul_nonneg hγ₀pos.le hge))
  have hG0pos : 0 < G.eval 0 := by
    have e : F.eval 0 = -γ₀ * G.eval 0 := by rw [hG]; simp
    rw [e] at hF0
    by_contra hle; push Not at hle
    have : 0 ≤ -γ₀ * G.eval 0 := mul_nonneg_of_nonpos_of_nonpos (by linarith) hle
    linarith
  obtain ⟨x, hx, hGx⟩ := intermediate_value_Icc' hγ₀pos.le G.continuous.continuousOn
    ⟨hGγneg.le, hG0pos.le⟩
  have hx0 : 0 < x := lt_of_le_of_ne hx.1 (by rintro rfl; linarith)
  have hxγ : x < γ₀ := lt_of_le_of_ne hx.2 (by rintro rfl; linarith)
  have hFx : F.IsRoot x := by rw [IsRoot, hG]; simp [hGx]
  exact absurd (hmin x hx0 hFx) (not_le.mpr hxγ)

/-- First-root sign argument: a real polynomial with `F(0) < 0` whose real roots all satisfy
`γ F'(γ) < 0` has no real roots. -/
theorem forall_not_isRoot_of_slope_neg {F : ℝ[X]} (hF0 : F.eval 0 < 0)
    (hslope : ∀ γ, F.IsRoot γ → γ * (derivative F).eval γ < 0) : ∀ γ, ¬ F.IsRoot γ := by
  intro γ hγ
  rcases lt_trichotomy γ 0 with hneg | rfl | hpos
  · have hF'0 : (F.comp (-X)).eval 0 < 0 := by simpa [eval_comp] using hF0
    have hslope' : ∀ y, (F.comp (-X)).IsRoot y → y * (derivative (F.comp (-X))).eval y < 0 := by
      intro y hy
      have hy' : F.IsRoot (-y) := by simpa [IsRoot, eval_comp] using hy
      have h := hslope (-y) hy'
      rw [derivative_comp]
      simp only [derivative_neg, derivative_X, eval_mul, eval_neg, eval_one, eval_comp, eval_X]
      linarith
    exact not_isRoot_of_pos hF'0 hslope' (neg_pos.mpr hneg) (by simpa [IsRoot, eval_comp] using hγ)
  · rw [IsRoot] at hγ; linarith
  · exact not_isRoot_of_pos hF0 hslope hpos hγ

/-- A complex polynomial with real coefficients is the image of a real polynomial. -/
theorem exists_map_ofReal_eq {p : ℂ[X]} (h : ∀ n, (p.coeff n).im = 0) :
    ∃ q : ℝ[X], q.map Complex.ofRealHom = p := by
  have hl : p ∈ lifts Complex.ofRealHom := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨(p.coeff n).re, Complex.ext (by simp) (by simp [h n])⟩
  exact (mem_lifts p).mp hl

end Dixmier
