/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PoissonEndpoints
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Hull

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Positive-cone comparison for homogeneous supports

The exact monomial Poisson bracket aligns the perpendicular endpoints of two commuting
homogeneous supports. Each support lies on the segment between those endpoints. This module
turns those facts into equality of positive cones in the integer-weight zero-bracket case. The
proof handles both zero degrees, both nonzero degrees, and rules out the mixed-degree boundary
for nonconstant homogeneous polynomials.
-/

namespace Dixmier.Weyl

def spanTwo (a b : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ z = s • a + t • b}

private theorem cone_pair_hull_eq_span (a b : ℝ × ℝ) :
    positiveScalarCone (convexHull ℝ {a,b}) = spanTwo a b := by
  ext z
  constructor
  · rintro ⟨r, hr, y, hy, rfl⟩
    rw [convexHull_pair] at hy
    rw [segment_eq_image₂] at hy
    rcases hy with ⟨uv, huv, rfl⟩
    rcases huv with ⟨hu, hv, huv⟩
    refine ⟨r*uv.1, r*uv.2, mul_nonneg hr hu, mul_nonneg hr hv, ?_⟩
    simp only [smul_add, smul_smul]
  · rintro ⟨s,t,hs,ht,rfl⟩
    by_cases hsum : s+t=0
    · have hs0 : s=0 := by nlinarith
      have ht0 : t=0 := by nlinarith
      subst s; subst t
      refine ⟨0, le_rfl, a, ?_, ?_⟩
      · exact subset_convexHull ℝ {a,b} (by simp)
      · simp
    · have hsumpos : 0 < s+t := lt_of_le_of_ne (by linarith) (Ne.symm hsum)
      let r : ℝ := s+t
      let u : ℝ := s/r
      let v : ℝ := t/r
      have hr : r ≠ 0 := ne_of_gt (by dsimp [r]; exact hsumpos)
      have hu : 0 ≤ u := by dsimp [u]; exact div_nonneg hs (le_of_lt hsumpos)
      have hv : 0 ≤ v := by dsimp [v]; exact div_nonneg ht (le_of_lt hsumpos)
      have huv : u+v=1 := by dsimp [u,v,r]; field_simp [hr]
      have hy : u • a + v • b ∈ convexHull ℝ {a,b} := by
        rw [convexHull_pair, segment_eq_image₂]
        exact ⟨(u,v), ⟨hu,hv,huv⟩, rfl⟩
      refine ⟨r, le_of_lt hsumpos, u • a + v • b, hy, ?_⟩
      dsimp [u,v,r]
      simp only [smul_add, smul_smul]
      congr 1 <;> field_simp [hr]

private lemma nonzero_ray_of_det (a b : ℝ × ℝ)
    (ha0 : 0 ≤ a.1) (ha1 : 0 ≤ a.2)
    (hb0 : 0 ≤ b.1) (hb1 : 0 ≤ b.2)
    (hane : a ≠ 0) (hbne : b ≠ 0)
    (hdet : a.2*b.1 - a.1*b.2 = 0) :
    ∃ c : ℝ, 0 < c ∧ a = c • b := by
  by_cases hb0z : b.1 = 0
  · have hb2 : 0 < b.2 := by
      have : b.2 ≠ 0 := by intro hz; apply hbne; apply Prod.ext <;> simp [hb0z,hz]
      exact lt_of_le_of_ne hb1 (Ne.symm this)
    have ha0z : a.1 = 0 := by nlinarith [hdet, hb2]
    have ha2 : 0 < a.2 := by
      have : a.2 ≠ 0 := by intro hz; apply hane; apply Prod.ext <;> simp [ha0z,hz]
      exact lt_of_le_of_ne ha1 (Ne.symm this)
    refine ⟨a.2/b.2, div_pos ha2 hb2, ?_⟩
    apply Prod.ext
    · simp [ha0z, hb0z]
    · dsimp
      field_simp [ne_of_gt hb2]
  · have hb1p : 0 < b.1 := lt_of_le_of_ne hb0 (Ne.symm hb0z)
    have ha1p : 0 < a.1 := by
      by_contra hnot
      have hz : a.1=0 := le_antisymm (not_lt.mp hnot) ha0
      have ha2z : a.2=0 := by nlinarith [hdet, hb1p]
      exact hane (by apply Prod.ext <;> simp [hz,ha2z])
    refine ⟨a.1/b.1, div_pos ha1p hb1p, ?_⟩
    apply Prod.ext
    · dsimp
      field_simp [ne_of_gt hb1p]
    · dsimp
      field_simp [ne_of_gt hb1p]
      nlinarith [hdet]

private theorem spanTwo_eq_of_endpoint_rays (a b c d : ℝ × ℝ)
    (h1 : ∃ c₁ : ℝ, 0 < c₁ ∧ a = c₁ • c)
    (h2 : ∃ c₂ : ℝ, 0 < c₂ ∧ b = c₂ • d) : spanTwo a b = spanTwo c d := by
  rcases h1 with ⟨c₁,hc₁,ha⟩
  rcases h2 with ⟨c₂,hc₂,hb⟩
  have hc : c = c₁⁻¹ • a := by rw [ha]; simp [smul_smul, hc₁.ne']
  have hd : d = c₂⁻¹ • b := by rw [hb]; simp [smul_smul, hc₂.ne']
  ext z
  constructor
  · rintro ⟨s,t,hs,ht,rfl⟩
    refine ⟨s*c₁,t*c₂,mul_nonneg hs (le_of_lt hc₁),mul_nonneg ht (le_of_lt hc₂),?_⟩
    simp only [ha, hb, smul_smul]
  · rintro ⟨s,t,hs,ht,rfl⟩
    refine ⟨s*c₁⁻¹,t*c₂⁻¹,mul_nonneg hs (le_of_lt (inv_pos.mpr hc₁)),mul_nonneg ht (le_of_lt (inv_pos.mpr hc₂)),?_⟩
    simp only [hc, hd, smul_smul]

private lemma exponentPoint_ne_zero {d : Fin 2 →₀ ℕ} (hd : d ≠ 0) :
    exponentPoint d ≠ (0 : ℝ × ℝ) := by
  intro h
  have h0r : ((d 0 : ℕ) : ℝ) = 0 := by simpa [exponentPoint] using congrArg Prod.fst h
  have h1r : ((d 1 : ℕ) : ℝ) = 0 := by simpa [exponentPoint] using congrArg Prod.snd h
  have h0 : d 0 = 0 := by exact_mod_cast h0r
  have h1 : d 1 = 0 := by exact_mod_cast h1r
  apply hd
  ext i
  fin_cases i <;> assumption

private theorem support_hull_eq_endpoint_pair
    (w : Fin 2 → ℤ) (degree : ℤ) (p : MvPolynomial (Fin 2) ℂ)
    (hwnz : w 0 ≠ 0 ∨ w 1 ≠ 0)
    (hdeg : ∀ x ∈ p.support, Finsupp.weight w x = degree)
    {dhi dlo : Fin 2 →₀ ℕ}
    (hdhi : dhi ∈ p.support) (hdlo : dlo ∈ p.support)
    (hmax : ∀ x ∈ p.support,
      Finsupp.weight (perpWeight w) x ≤ Finsupp.weight (perpWeight w) dhi)
    (hmin : ∀ x ∈ p.support,
      Finsupp.weight (perpWeight w) dlo ≤ Finsupp.weight (perpWeight w) x) :
    convexHull ℝ (exponentPoint '' (p.support : Set (Fin 2 →₀ ℕ))) =
      convexHull ℝ {exponentPoint dhi, exponentPoint dlo} := by
  apply le_antisymm
  · apply convexHull_min ?_ (convex_convexHull ℝ _)
    rintro z ⟨x,hx,rfl⟩
    exact homogeneous_support_exponent_mem_endpoint_hull w degree p hwnz hdeg
      hdhi hdlo hmax hmin x hx
  · apply convexHull_mono
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · subst z
      exact ⟨dhi,hdhi,rfl⟩
    · subst z
      exact ⟨dlo,hdlo,rfl⟩

theorem poisson_homogeneous_support_cones_equal_of_nonzero_degrees
    (w : Fin 2 → ℤ) (degreeP degreeQ : ℤ)
    (p q : MvPolynomial (Fin 2) ℂ)
    (hwnz : w 0 ≠ 0 ∨ w 1 ≠ 0)
    (hpdeg : ∀ d ∈ p.support, Finsupp.weight w d = degreeP)
    (hqdeg : ∀ e ∈ q.support, Finsupp.weight w e = degreeQ)
    (hpne : p ≠ 0) (hqne : q ≠ 0)
    (hbr : poisson p q = 0)
    (hpdegree : degreeP ≠ 0) (hqdegree : degreeQ ≠ 0) :
    positiveScalarCone (convexHull ℝ (exponentPoint '' (p.support : Set (Fin 2 →₀ ℕ)))) =
    positiveScalarCone (convexHull ℝ (exponentPoint '' (q.support : Set (Fin 2 →₀ ℕ)))) := by
  obtain ⟨dp,dm,ep,em,hdp,hdm,hep,hem,hdpmax,hdpmin,hepmax,hepmin,hplus,hminus⟩ :=
    poisson_homogeneous_support_endpoints_collinear w degreeP degreeQ p q hwnz hpdeg hqdeg hpne hqne hbr
  have hdpne : dp ≠ 0 := by
    intro hz
    subst dp
    have hzero : Finsupp.weight w (0 : Fin 2 →₀ ℕ) = 0 := by simp
    exact hpdegree ((hpdeg 0 hdp).symm.trans hzero)
  have hdmne : dm ≠ 0 := by
    intro hz
    subst dm
    have hzero : Finsupp.weight w (0 : Fin 2 →₀ ℕ) = 0 := by simp
    exact hpdegree ((hpdeg 0 hdm).symm.trans hzero)
  have hepne : ep ≠ 0 := by
    intro hz
    subst ep
    have hzero : Finsupp.weight w (0 : Fin 2 →₀ ℕ) = 0 := by simp
    exact hqdegree ((hqdeg 0 hep).symm.trans hzero)
  have hemne : em ≠ 0 := by
    intro hz
    subst em
    have hzero : Finsupp.weight w (0 : Fin 2 →₀ ℕ) = 0 := by simp
    exact hqdegree ((hqdeg 0 hem).symm.trans hzero)
  have hplusNat : dp 1 * ep 0 = dp 0 * ep 1 := by
    have h := sub_eq_zero.mp hplus
    exact_mod_cast h
  have hminusNat : dm 1 * em 0 = dm 0 * em 1 := by
    have h := sub_eq_zero.mp hminus
    exact_mod_cast h
  have hplusR : (exponentPoint dp).2 * (exponentPoint ep).1 -
      (exponentPoint dp).1 * (exponentPoint ep).2 = 0 := by
    change ((dp 1 : ℕ) : ℝ) * ((ep 0 : ℕ) : ℝ) -
      ((dp 0 : ℕ) : ℝ) * ((ep 1 : ℕ) : ℝ) = 0
    rw [sub_eq_zero]
    exact_mod_cast hplusNat
  have hminusR : (exponentPoint dm).2 * (exponentPoint em).1 -
      (exponentPoint dm).1 * (exponentPoint em).2 = 0 := by
    change ((dm 1 : ℕ) : ℝ) * ((em 0 : ℕ) : ℝ) -
      ((dm 0 : ℕ) : ℝ) * ((em 1 : ℕ) : ℝ) = 0
    rw [sub_eq_zero]
    exact_mod_cast hminusNat
  have hdp0 : 0 ≤ (exponentPoint dp).1 := by
    change (0 : ℝ) ≤ ((dp 0 : ℕ) : ℝ)
    exact_mod_cast Nat.zero_le (dp 0)
  have hdp1 : 0 ≤ (exponentPoint dp).2 := by
    change (0 : ℝ) ≤ ((dp 1 : ℕ) : ℝ)
    exact_mod_cast Nat.zero_le (dp 1)
  have hep0 : 0 ≤ (exponentPoint ep).1 := by
    change (0 : ℝ) ≤ ((ep 0 : ℕ) : ℝ)
    exact_mod_cast Nat.zero_le (ep 0)
  have hep1 : 0 ≤ (exponentPoint ep).2 := by
    change (0 : ℝ) ≤ ((ep 1 : ℕ) : ℝ)
    exact_mod_cast Nat.zero_le (ep 1)
  have hdm0 : 0 ≤ (exponentPoint dm).1 := by
    change (0 : ℝ) ≤ ((dm 0 : ℕ) : ℝ)
    exact_mod_cast Nat.zero_le (dm 0)
  have hdm1 : 0 ≤ (exponentPoint dm).2 := by
    change (0 : ℝ) ≤ ((dm 1 : ℕ) : ℝ)
    exact_mod_cast Nat.zero_le (dm 1)
  have hem0 : 0 ≤ (exponentPoint em).1 := by
    change (0 : ℝ) ≤ ((em 0 : ℕ) : ℝ)
    exact_mod_cast Nat.zero_le (em 0)
  have hem1 : 0 ≤ (exponentPoint em).2 := by
    change (0 : ℝ) ≤ ((em 1 : ℕ) : ℝ)
    exact_mod_cast Nat.zero_le (em 1)
  have hdpRay := nonzero_ray_of_det (exponentPoint dp) (exponentPoint ep)
    hdp0 hdp1 hep0 hep1 (exponentPoint_ne_zero hdpne) (exponentPoint_ne_zero hepne) hplusR
  have hdmRay := nonzero_ray_of_det (exponentPoint dm) (exponentPoint em)
    hdm0 hdm1 hem0 hem1 (exponentPoint_ne_zero hdmne) (exponentPoint_ne_zero hemne) hminusR
  have hhp := support_hull_eq_endpoint_pair w degreeP p hwnz hpdeg hdp hdm hdpmax hdpmin
  have hhq := support_hull_eq_endpoint_pair w degreeQ q hwnz hqdeg hep hem hepmax hepmin
  rw [hhp, hhq, cone_pair_hull_eq_span, cone_pair_hull_eq_span]
  exact spanTwo_eq_of_endpoint_rays _ _ _ _ hdpRay hdmRay


def nonnegativeRay (v : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ t : ℝ, 0 ≤ t ∧ z = t • v}

private theorem spanTwo_eq_nonnegativeRay (a b v : ℝ × ℝ)
    (hav : ∃ r : ℝ, 0 ≤ r ∧ a = r • v)
    (hbv : ∃ s : ℝ, 0 ≤ s ∧ b = s • v)
    (hpos : (∃ r : ℝ, 0 < r ∧ a = r • v) ∨
      (∃ s : ℝ, 0 < s ∧ b = s • v)) :
    spanTwo a b = nonnegativeRay v := by
  rcases hav with ⟨r,hr,hra⟩
  rcases hbv with ⟨s,hs,hsb⟩
  ext z
  constructor
  · rintro ⟨u,t,hu,ht,rfl⟩
    refine ⟨u*r+t*s, add_nonneg (mul_nonneg hu hr) (mul_nonneg ht hs), ?_⟩
    rw [hra, hsb]
    simp only [smul_smul]
    rw [← add_smul]
  · rintro ⟨t,ht,rfl⟩
    rcases hpos with h | h
    · rcases h with ⟨r',hr',hra'⟩
      refine ⟨t/r',0,div_nonneg ht (le_of_lt hr'),le_rfl,?_⟩
      rw [hra']
      simp only [smul_smul, zero_smul, add_zero]
      congr 1
      field_simp [ne_of_gt hr']
    · rcases h with ⟨s',hs',hsb'⟩
      refine ⟨0,t/s',le_rfl,div_nonneg ht (le_of_lt hs'),?_⟩
      rw [hsb']
      simp only [zero_smul, smul_smul, zero_add]
      congr 1
      field_simp [ne_of_gt hs']

def endpointConeRealWeight (w : Fin 2 → ℤ) (d : Fin 2 →₀ ℕ) : ℝ :=
  (w 0 : ℝ) * (d 0 : ℝ) + (w 1 : ℝ) * (d 1 : ℝ)

private theorem realWeight_eq_cast (w : Fin 2 → ℤ) (d : Fin 2 →₀ ℕ) :
    endpointConeRealWeight w d = ((Finsupp.weight w d : ℤ) : ℝ) := by
  simp [endpointConeRealWeight, Finsupp.weight_eq_sum, Fin.sum_univ_succ]
  ring

private theorem determinant_eq_zero_of_common_weight_zero
    (w : Fin 2 → ℤ) (a b : Fin 2 →₀ ℕ)
    (hwnz : w 0 ≠ 0 ∨ w 1 ≠ 0)
    (ha : Finsupp.weight w a = 0) (hb : Finsupp.weight w b = 0) :
    (exponentPoint a).2 * (exponentPoint b).1 -
      (exponentPoint a).1 * (exponentPoint b).2 = 0 := by
  have haR : endpointConeRealWeight w a = 0 := by
    rw [realWeight_eq_cast]
    exact_mod_cast ha
  have hbR : endpointConeRealWeight w b = 0 := by
    rw [realWeight_eq_cast]
    exact_mod_cast hb
  have ha' : (w 0 : ℝ) * (exponentPoint a).1 +
      (w 1 : ℝ) * (exponentPoint a).2 = 0 := by
    simpa [endpointConeRealWeight, exponentPoint] using haR
  have hb' : (w 0 : ℝ) * (exponentPoint b).1 +
      (w 1 : ℝ) * (exponentPoint b).2 = 0 := by
    simpa [endpointConeRealWeight, exponentPoint] using hbR
  by_cases hw0 : w 0 ≠ 0
  · have hmul : (w 0 : ℝ) *
        ((exponentPoint a).2 * (exponentPoint b).1 -
          (exponentPoint a).1 * (exponentPoint b).2) = 0 := by
      linear_combination (exponentPoint a).2 * hb' - (exponentPoint b).2 * ha'
    have hw0R : (w 0 : ℝ) ≠ 0 := by exact_mod_cast hw0
    exact (mul_eq_zero.mp hmul).resolve_left hw0R
  · have hw1 : w 1 ≠ 0 := by
      rcases hwnz with h | h
      · exact (hw0 h).elim
      · exact h
    have hmul : (w 1 : ℝ) *
        ((exponentPoint a).2 * (exponentPoint b).1 -
          (exponentPoint a).1 * (exponentPoint b).2) = 0 := by
      linear_combination (exponentPoint b).1 * ha' - (exponentPoint a).1 * hb'
    have hw1R : (w 1 : ℝ) ≠ 0 := by exact_mod_cast hw1
    exact (mul_eq_zero.mp hmul).resolve_left hw1R

private theorem endpoint_as_nonnegative_multiple_of_common_zero_weight
    (w : Fin 2 → ℤ) (d v : Fin 2 →₀ ℕ)
    (hwnz : w 0 ≠ 0 ∨ w 1 ≠ 0)
    (hdwt : Finsupp.weight w d = 0) (hvwt : Finsupp.weight w v = 0)
    (hvne : v ≠ 0) :
    ∃ c : ℝ, 0 ≤ c ∧ exponentPoint d = c • exponentPoint v := by
  by_cases hdne : d ≠ 0
  · have hdet := determinant_eq_zero_of_common_weight_zero w d v hwnz hdwt hvwt
    rcases nonzero_ray_of_det (exponentPoint d) (exponentPoint v)
        (by change 0 ≤ ((d 0 : ℕ) : ℝ); exact_mod_cast Nat.zero_le (d 0))
        (by change 0 ≤ ((d 1 : ℕ) : ℝ); exact_mod_cast Nat.zero_le (d 1))
        (by change 0 ≤ ((v 0 : ℕ) : ℝ); exact_mod_cast Nat.zero_le (v 0))
        (by change 0 ≤ ((v 1 : ℕ) : ℝ); exact_mod_cast Nat.zero_le (v 1))
        (exponentPoint_ne_zero hdne) (exponentPoint_ne_zero hvne) hdet with
      ⟨c,hc,h⟩
    exact ⟨c,le_of_lt hc,h⟩
  · have hdz : d = 0 := by simpa using hdne
    subst d
    exact ⟨0,le_rfl,by simp [exponentPoint]⟩

private theorem support_endpoints_not_both_zero
    (w : Fin 2 → ℤ) (degree : ℤ) (p : MvPolynomial (Fin 2) ℂ)
    (hwnz : w 0 ≠ 0 ∨ w 1 ≠ 0)
    (hdeg : ∀ x ∈ p.support, Finsupp.weight w x = degree)
    (hnonconst : ∃ x ∈ p.support, x ≠ 0)
    {dhi dlo : Fin 2 →₀ ℕ}
    (hdhi : dhi ∈ p.support) (hdlo : dlo ∈ p.support)
    (hmax : ∀ x ∈ p.support,
      Finsupp.weight (perpWeight w) x ≤ Finsupp.weight (perpWeight w) dhi)
    (hmin : ∀ x ∈ p.support,
      Finsupp.weight (perpWeight w) dlo ≤ Finsupp.weight (perpWeight w) x) :
    dhi ≠ 0 ∨ dlo ≠ 0 := by
  by_contra h
  have hhi : dhi = 0 := by
    by_contra hn
    exact h (Or.inl hn)
  have hlo : dlo = 0 := by
    by_contra hn
    exact h (Or.inr hn)
  rcases hnonconst with ⟨x,hx,hxne⟩
  have hxHull := homogeneous_support_exponent_mem_endpoint_hull
    w degree p hwnz hdeg hdhi hdlo hmax hmin x hx
  rw [hhi,hlo] at hxHull
  have hxPoint : exponentPoint x = (0 : ℝ × ℝ) := by
    simpa [exponentPoint] using hxHull
  exact (exponentPoint_ne_zero hxne) hxPoint

private theorem zero_degree_support_cone_eq_ray
    (w : Fin 2 → ℤ) (degree : ℤ) (p : MvPolynomial (Fin 2) ℂ)
    (hwnz : w 0 ≠ 0 ∨ w 1 ≠ 0)
    (hdeg : ∀ x ∈ p.support, Finsupp.weight w x = degree)
    (hnonconst : ∃ x ∈ p.support, x ≠ 0)
    {dhi dlo : Fin 2 →₀ ℕ}
    (hdhi : dhi ∈ p.support) (hdlo : dlo ∈ p.support)
    (hmax : ∀ x ∈ p.support,
      Finsupp.weight (perpWeight w) x ≤ Finsupp.weight (perpWeight w) dhi)
    (hmin : ∀ x ∈ p.support,
      Finsupp.weight (perpWeight w) dlo ≤ Finsupp.weight (perpWeight w) x)
    (hdegree : degree = 0) :
    positiveScalarCone (convexHull ℝ (exponentPoint '' (p.support : Set (Fin 2 →₀ ℕ)))) =
      nonnegativeRay (exponentPoint (if dhi ≠ 0 then dhi else dlo)) := by
  have hpair := support_endpoints_not_both_zero w degree p hwnz hdeg hnonconst
    hdhi hdlo hmax hmin
  have hpair' : (if dhi ≠ 0 then dhi else dlo) ≠ 0 := by
    by_cases h : dhi ≠ 0
    · simp [h]
    · have hlo := hpair.resolve_left h
      simpa [h] using hlo
  let v := if dhi ≠ 0 then dhi else dlo
  have hv : v ≠ 0 := hpair'
  have hv_mem : v ∈ p.support := by
    by_cases h : dhi ≠ 0
    · simpa [v,h] using hdhi
    · have h0 : dhi = 0 := by
        by_contra hn
        exact h hn
      simpa [v,h0] using hdlo
  have hweight (d : Fin 2 →₀ ℕ) (hd : d ∈ p.support) :
      Finsupp.weight w d = 0 := by simpa [hdegree] using hdeg d hd
  have hscaleDhi := endpoint_as_nonnegative_multiple_of_common_zero_weight
    w dhi v hwnz (hweight dhi hdhi) (hweight v hv_mem) hv
  have hscaleDlo := endpoint_as_nonnegative_multiple_of_common_zero_weight
    w dlo v hwnz (hweight dlo hdlo) (hweight v hv_mem) hv
  have hpos : (∃ c : ℝ, 0 < c ∧ exponentPoint dhi = c • exponentPoint v) ∨
      (∃ c : ℝ, 0 < c ∧ exponentPoint dlo = c • exponentPoint v) := by
    by_cases h : dhi ≠ 0
    · left
      refine ⟨1, by norm_num, ?_⟩
      simp [v,h]
    · right
      have h0 : dhi = 0 := by
        by_contra hn
        exact h hn
      have hdlone : dlo ≠ 0 := hpair.resolve_left h
      refine ⟨1, by norm_num, ?_⟩
      simp [v,h0]
  have hhull := support_hull_eq_endpoint_pair w degree p hwnz hdeg
    hdhi hdlo hmax hmin
  rw [hhull, cone_pair_hull_eq_span]
  exact spanTwo_eq_nonnegativeRay _ _ _ hscaleDhi hscaleDlo hpos

private theorem nonnegativeRay_eq_of_positive_ray (v w : ℝ × ℝ)
    (hvw : ∃ c : ℝ, 0 < c ∧ v = c • w) :
    nonnegativeRay v = nonnegativeRay w := by
  rcases hvw with ⟨c,hc,hv⟩
  have hwv : w = c⁻¹ • v := by rw [hv]; simp [smul_smul, hc.ne']
  ext z
  constructor
  · rintro ⟨t,ht,rfl⟩
    refine ⟨t*c,mul_nonneg ht (le_of_lt hc),?_⟩
    rw [hv]
    simp [smul_smul]
  · rintro ⟨t,ht,rfl⟩
    exact ⟨t*c⁻¹,mul_nonneg ht (le_of_lt (inv_pos.mpr hc)),
      by rw [hwv]; simp [smul_smul]⟩

theorem poisson_homogeneous_support_cones_equal_of_zero_degrees
    (w : Fin 2 → ℤ) (p q : MvPolynomial (Fin 2) ℂ)
    (hwnz : w 0 ≠ 0 ∨ w 1 ≠ 0)
    (hpdeg : ∀ d ∈ p.support, Finsupp.weight w d = 0)
    (hqdeg : ∀ e ∈ q.support, Finsupp.weight w e = 0)
    (hpnonconst : ∃ d ∈ p.support, d ≠ 0)
    (hqnonconst : ∃ e ∈ q.support, e ≠ 0)
    (hpne : p ≠ 0) (hqne : q ≠ 0) (hbr : poisson p q = 0) :
    positiveScalarCone (convexHull ℝ (exponentPoint '' (p.support : Set (Fin 2 →₀ ℕ)))) =
      positiveScalarCone (convexHull ℝ (exponentPoint '' (q.support : Set (Fin 2 →₀ ℕ)))) := by
  obtain ⟨dp,dm,ep,em,hdp,hdm,hep,hem,hdpmax,hdpmin,hepmax,hepmin,hplus,hminus⟩ :=
    poisson_homogeneous_support_endpoints_collinear w 0 0 p q hwnz hpdeg hqdeg hpne hqne hbr
  have hdpOrdm := support_endpoints_not_both_zero w 0 p hwnz hpdeg hpnonconst
    hdp hdm hdpmax hdpmin
  have hepOrem := support_endpoints_not_both_zero w 0 q hwnz hqdeg hqnonconst
    hep hem hepmax hepmin
  let vp : Fin 2 →₀ ℕ := if dp ≠ 0 then dp else dm
  let vq : Fin 2 →₀ ℕ := if ep ≠ 0 then ep else em
  have hvpne : vp ≠ 0 := by
    by_cases h : dp ≠ 0
    · simp [vp,h]
    · have h0 : dp = 0 := by
        by_contra hn
        exact h hn
      have hdm : dm ≠ 0 := hdpOrdm.resolve_left h
      simpa [vp,h0] using hdm
  have hvqne : vq ≠ 0 := by
    by_cases h : ep ≠ 0
    · simp [vq,h]
    · have h0 : ep = 0 := by
        by_contra hn
        exact h hn
      have hem : em ≠ 0 := hepOrem.resolve_left h
      simpa [vq,h0] using hem
  have hvpMem : vp ∈ p.support := by
    by_cases h : dp ≠ 0
    · simpa [vp,h] using hdp
    · have h0 : dp = 0 := by
        by_contra hn
        exact h hn
      simpa [vp,h0] using hdm
  have hvqMem : vq ∈ q.support := by
    by_cases h : ep ≠ 0
    · simpa [vq,h] using hep
    · have h0 : ep = 0 := by
        by_contra hn
        exact h hn
      simpa [vq,h0] using hem
  have hvpWt : Finsupp.weight w vp = 0 := hpdeg vp hvpMem
  have hvqWt : Finsupp.weight w vq = 0 := hqdeg vq hvqMem
  have hdet := determinant_eq_zero_of_common_weight_zero w vp vq hwnz hvpWt hvqWt
  have hray := nonzero_ray_of_det (exponentPoint vp) (exponentPoint vq)
    (by change 0 ≤ ((vp 0 : ℕ) : ℝ); exact_mod_cast Nat.zero_le (vp 0))
    (by change 0 ≤ ((vp 1 : ℕ) : ℝ); exact_mod_cast Nat.zero_le (vp 1))
    (by change 0 ≤ ((vq 0 : ℕ) : ℝ); exact_mod_cast Nat.zero_le (vq 0))
    (by change 0 ≤ ((vq 1 : ℕ) : ℝ); exact_mod_cast Nat.zero_le (vq 1))
    (exponentPoint_ne_zero hvpne) (exponentPoint_ne_zero hvqne) hdet
  have hconeP := zero_degree_support_cone_eq_ray w 0 p hwnz hpdeg hpnonconst
    hdp hdm hdpmax hdpmin rfl
  have hconeQ := zero_degree_support_cone_eq_ray w 0 q hwnz hqdeg hqnonconst
    hep hem hepmax hepmin rfl
  rw [hconeP,hconeQ]
  have hray' : ∃ c : ℝ, 0 < c ∧ exponentPoint vp = c • exponentPoint vq := by simpa [vp,vq] using hray
  exact nonnegativeRay_eq_of_positive_ray _ _ hray'

private theorem endpoint_det_complex_to_real
    (a b : Fin 2 →₀ ℕ)
    (h : (a 1 : ℂ) * (b 0 : ℂ) - (a 0 : ℂ) * (b 1 : ℂ) = 0) :
    (exponentPoint a).2 * (exponentPoint b).1 -
      (exponentPoint a).1 * (exponentPoint b).2 = 0 := by
  have hNat : a 1 * b 0 = a 0 * b 1 := by
    have h' := sub_eq_zero.mp h
    exact_mod_cast h'
  change ((a 1 : ℕ) : ℝ) * ((b 0 : ℕ) : ℝ) -
    ((a 0 : ℕ) : ℝ) * ((b 1 : ℕ) : ℝ) = 0
  rw [sub_eq_zero]
  exact_mod_cast hNat

private theorem exponent_ne_zero_of_weight_ne_zero
    (w : Fin 2 → ℤ) (degree : ℤ) (d : Fin 2 →₀ ℕ)
    (hdeg : Finsupp.weight w d = degree) (hdegree : degree ≠ 0) : d ≠ 0 := by
  intro hd
  subst d
  have hzero : Finsupp.weight w (0 : Fin 2 →₀ ℕ) = 0 := by simp
  exact hdegree (hdeg.symm.trans hzero)

def endpointConePointWeight (w : Fin 2 → ℤ) (z : ℝ × ℝ) : ℝ :=
  (w 0 : ℝ) * z.1 + (w 1 : ℝ) * z.2

private theorem realWeight_scale
    (w : Fin 2 → ℤ) (a b : Fin 2 →₀ ℕ) (c : ℝ)
    (h : exponentPoint a = c • exponentPoint b) :
    endpointConeRealWeight w a = c * endpointConeRealWeight w b := by
  have h0 : ((a 0 : ℕ) : ℝ) = c * ((b 0 : ℕ) : ℝ) := by
    simpa [exponentPoint] using congrArg Prod.fst h
  have h1 : ((a 1 : ℕ) : ℝ) = c * ((b 1 : ℕ) : ℝ) := by
    simpa [exponentPoint] using congrArg Prod.snd h
  dsimp [endpointConeRealWeight]
  rw [h0, h1]
  ring

private theorem false_of_zero_nonzero_endpoint_weights
    (w : Fin 2 → ℤ) (a b : Fin 2 →₀ ℕ) (degree : ℤ)
    (hwa : Finsupp.weight w a = 0) (hwb : Finsupp.weight w b = degree)
    (hdegree : degree ≠ 0)
    (hray : ∃ c : ℝ, 0 < c ∧ exponentPoint a = c • exponentPoint b) : False := by
  rcases hray with ⟨c,hc,h⟩
  have hwaR : endpointConeRealWeight w a = 0 := by
    rw [realWeight_eq_cast]
    exact_mod_cast hwa
  have hwbR : endpointConeRealWeight w b = (degree : ℝ) := by
    rw [realWeight_eq_cast]
    exact_mod_cast hwb
  have hscale := realWeight_scale w a b c h
  rw [hwaR,hwbR] at hscale
  have hdegreeR : (degree : ℝ) ≠ 0 := by exact_mod_cast hdegree
  have hprod : c * (degree : ℝ) ≠ 0 := mul_ne_zero hc.ne' hdegreeR
  exact hprod hscale.symm

private lemma exponent_coords_nonneg (d : Fin 2 →₀ ℕ) :
    0 ≤ (exponentPoint d).1 ∧ 0 ≤ (exponentPoint d).2 := by
  constructor
  · change (0 : ℝ) ≤ ((d 0 : ℕ) : ℝ)
    exact_mod_cast Nat.zero_le (d 0)
  · change (0 : ℝ) ≤ ((d 1 : ℕ) : ℝ)
    exact_mod_cast Nat.zero_le (d 1)

private theorem zero_nonzero_degree_impossible
    (w : Fin 2 → ℤ) (degreeQ : ℤ)
    (p q : MvPolynomial (Fin 2) ℂ)
    (hwnz : w 0 ≠ 0 ∨ w 1 ≠ 0)
    (hpdeg : ∀ d ∈ p.support, Finsupp.weight w d = 0)
    (hqdeg : ∀ e ∈ q.support, Finsupp.weight w e = degreeQ)
    (hpnonconst : ∃ d ∈ p.support, d ≠ 0)
    (hpne : p ≠ 0) (hqne : q ≠ 0) (hbr : poisson p q = 0)
    (hqdegree : degreeQ ≠ 0) : False := by
  obtain ⟨dp,dm,ep,em,hdp,hdm,hep,hem,hdpmax,hdpmin,hepmax,hepmin,hplus,hminus⟩ :=
    poisson_homogeneous_support_endpoints_collinear w 0 degreeQ p q hwnz hpdeg hqdeg hpne hqne hbr
  have hpair := support_endpoints_not_both_zero w 0 p hwnz hpdeg hpnonconst
    hdp hdm hdpmax hdpmin
  have hepne : ep ≠ 0 := exponent_ne_zero_of_weight_ne_zero w degreeQ ep
    (hqdeg ep hep) hqdegree
  have hemne : em ≠ 0 := exponent_ne_zero_of_weight_ne_zero w degreeQ em
    (hqdeg em hem) hqdegree
  rcases hpair with hdpne | hdmne
  · have hdet := endpoint_det_complex_to_real dp ep hplus
    rcases nonzero_ray_of_det (exponentPoint dp) (exponentPoint ep)
      (exponent_coords_nonneg dp).1 (exponent_coords_nonneg dp).2
      (exponent_coords_nonneg ep).1 (exponent_coords_nonneg ep).2
      (exponentPoint_ne_zero hdpne) (exponentPoint_ne_zero hepne) hdet with
      ⟨c,hc,hray⟩
    exact false_of_zero_nonzero_endpoint_weights w dp ep degreeQ
      (hpdeg dp hdp) (hqdeg ep hep) hqdegree ⟨c,hc,hray⟩
  · have hdet := endpoint_det_complex_to_real dm em hminus
    rcases nonzero_ray_of_det (exponentPoint dm) (exponentPoint em)
      (exponent_coords_nonneg dm).1 (exponent_coords_nonneg dm).2
      (exponent_coords_nonneg em).1 (exponent_coords_nonneg em).2
      (exponentPoint_ne_zero hdmne) (exponentPoint_ne_zero hemne) hdet with
      ⟨c,hc,hray⟩
    exact false_of_zero_nonzero_endpoint_weights w dm em degreeQ
      (hpdeg dm hdm) (hqdeg em hem) hqdegree ⟨c,hc,hray⟩

theorem poisson_homogeneous_support_cones_equal
    (w : Fin 2 → ℤ) (degreeP degreeQ : ℤ)
    (p q : MvPolynomial (Fin 2) ℂ)
    (hwnz : w 0 ≠ 0 ∨ w 1 ≠ 0)
    (hpdeg : ∀ d ∈ p.support, Finsupp.weight w d = degreeP)
    (hqdeg : ∀ e ∈ q.support, Finsupp.weight w e = degreeQ)
    (hpnonconst : ∃ d ∈ p.support, d ≠ 0)
    (hqnonconst : ∃ e ∈ q.support, e ≠ 0)
    (hpne : p ≠ 0) (hqne : q ≠ 0) (hbr : poisson p q = 0) :
    positiveScalarCone (convexHull ℝ (exponentPoint '' (p.support : Set (Fin 2 →₀ ℕ)))) =
    positiveScalarCone (convexHull ℝ (exponentPoint '' (q.support : Set (Fin 2 →₀ ℕ)))) := by
  by_cases hp0 : degreeP = 0
  · by_cases hq0 : degreeQ = 0
    · have hpdeg0 : ∀ d ∈ p.support, Finsupp.weight w d = 0 := by
        intro d hd
        simpa [hp0] using hpdeg d hd
      have hqdeg0 : ∀ e ∈ q.support, Finsupp.weight w e = 0 := by
        intro e he
        simpa [hq0] using hqdeg e he
      exact poisson_homogeneous_support_cones_equal_of_zero_degrees w p q hwnz
        hpdeg0 hqdeg0 hpnonconst hqnonconst hpne hqne hbr
    · have hfalse := zero_nonzero_degree_impossible w degreeQ p q hwnz
        (by intro d hd; simpa [hp0] using hpdeg d hd) hqdeg hpnonconst hpne hqne hbr hq0
      exact hfalse.elim
  · by_cases hq0 : degreeQ = 0
    · have hanti : poisson q p = - poisson p q := by
        unfold poisson
        ring
      have hbr' : poisson q p = 0 := by rw [hanti,hbr]; simp
      have hfalse := zero_nonzero_degree_impossible w degreeP q p hwnz
        (by intro e he; simpa [hq0] using hqdeg e he) hpdeg hqnonconst hqne hpne hbr' hp0
      exact hfalse.elim
    · exact poisson_homogeneous_support_cones_equal_of_nonzero_degrees w degreeP degreeQ
        p q hwnz hpdeg hqdeg hpne hqne hbr hp0 hq0

/-- If every positive-sum integer face of two symbols is nonconstant and the corresponding
Poisson brackets vanish, then their integer Newton roofs have the same positive cone. This is
the directionwise assembly in Han--Tan's Lemma 3.6. -/
theorem integerPositiveNewtonRoof_cones_equal_of_facewise_poisson_eq
    (P Q : Module.End ℂ (Polynomial ℂ))
    (hPface : ∀ ρ σ : ℤ, 0 < ρ + σ →
      ∃ d ∈ (leadingForm ρ σ P).support, d ≠ 0)
    (hQface : ∀ ρ σ : ℤ, 0 < ρ + σ →
      ∃ d ∈ (leadingForm ρ σ Q).support, d ≠ 0)
    (hbr : ∀ ρ σ : ℤ, 0 < ρ + σ → poisson (leadingForm ρ σ P)
      (leadingForm ρ σ Q) = 0) :
    positiveScalarCone (integerPositiveNewtonRoof P) =
      positiveScalarCone (integerPositiveNewtonRoof Q) := by
  have hfacecone : ∀ ρ σ : ℤ, 0 < ρ + σ →
      positiveScalarCone (convexHull ℝ
        (exponentPoint '' ((leadingForm ρ σ P).support : Set (Fin 2 →₀ ℕ)))) =
      positiveScalarCone (convexHull ℝ
        (exponentPoint '' ((leadingForm ρ σ Q).support : Set (Fin 2 →₀ ℕ)))) := by
    intro ρ σ hsum
    have hwnz : (wt ρ σ) 0 ≠ 0 ∨ (wt ρ σ) 1 ≠ 0 := by
      by_contra hh
      push Not at hh
      have hρ : ρ = 0 := by simpa [wt] using hh.1
      have hσ : σ = 0 := by simpa [wt] using hh.2
      omega
    have hPdeg (d : Fin 2 →₀ ℕ) (hd : d ∈ (leadingForm ρ σ P).support) :
        Finsupp.weight (wt ρ σ) d = vDeg ρ σ P := by
      change d ∈ (MvPolynomial.weightedHomogeneousComponent (wt ρ σ)
        (vDeg ρ σ P) (symbol P)).support at hd
      rw [MvPolynomial.support_weightedHomogeneousComponent] at hd
      exact (Finset.mem_filter.mp hd).2
    have hQdeg (d : Fin 2 →₀ ℕ) (hd : d ∈ (leadingForm ρ σ Q).support) :
        Finsupp.weight (wt ρ σ) d = vDeg ρ σ Q := by
      change d ∈ (MvPolynomial.weightedHomogeneousComponent (wt ρ σ)
        (vDeg ρ σ Q) (symbol Q)).support at hd
      rw [MvPolynomial.support_weightedHomogeneousComponent] at hd
      exact (Finset.mem_filter.mp hd).2
    rcases hPface ρ σ hsum with ⟨dP, hdP, hdPne⟩
    rcases hQface ρ σ hsum with ⟨dQ, hdQ, hdQne⟩
    have hPne : leadingForm ρ σ P ≠ 0 := by
      intro hz
      simp [hz] at hdP
    have hQne : leadingForm ρ σ Q ≠ 0 := by
      intro hz
      simp [hz] at hdQ
    exact poisson_homogeneous_support_cones_equal (wt ρ σ)
      (vDeg ρ σ P) (vDeg ρ σ Q) (leadingForm ρ σ P) (leadingForm ρ σ Q)
      hwnz hPdeg hQdeg ⟨dP, hdP, hdPne⟩ ⟨dQ, hdQ, hdQne⟩ hPne hQne (hbr ρ σ hsum)
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨ρ, σ, hsum, hy⟩, hxy⟩
    have hcone : x ∈ positiveScalarCone (convexHull ℝ
        (exponentPoint '' ((leadingForm ρ σ P).support : Set (Fin 2 →₀ ℕ)))) :=
      ⟨r, hr, y, hy, hxy⟩
    rw [hfacecone ρ σ hsum] at hcone
    rcases hcone with ⟨r', hr', y', hy', hxy'⟩
    exact ⟨r', hr', y', ⟨ρ, σ, hsum, hy'⟩, hxy'⟩
  · rintro ⟨r, hr, y, ⟨ρ, σ, hsum, hy⟩, hxy⟩
    have hcone : x ∈ positiveScalarCone (convexHull ℝ
        (exponentPoint '' ((leadingForm ρ σ Q).support : Set (Fin 2 →₀ ℕ)))) :=
      ⟨r, hr, y, hy, hxy⟩
    rw [← hfacecone ρ σ hsum] at hcone
    rcases hcone with ⟨r', hr', y', hy', hxy'⟩
    exact ⟨r', hr', y', ⟨ρ, σ, hsum, hy'⟩, hxy'⟩

/-- In the setting of Han--Tan's roof lemma, removing the scalar terms makes every nonzero
integer exposed face nonconstant. Thus its facewise zero-Poisson-bracket hypothesis is enough
to apply the preceding roof-cone assembly. -/
theorem integerPositiveNewtonRoof_cones_equal_of_zeroBracket_and_no_constant_terms
    (P Q : Module.End ℂ (Polynomial ℂ))
    (hPsymbol : symbol P ≠ 0) (hQsymbol : symbol Q ≠ 0)
    (hPconstant : (0 : Fin 2 →₀ ℕ) ∉ (symbol P).support)
    (hQconstant : (0 : Fin 2 →₀ ℕ) ∉ (symbol Q).support)
    (hbr : ∀ ρ σ : ℤ, 0 < ρ + σ → poisson (leadingForm ρ σ P)
      (leadingForm ρ σ Q) = 0) :
    positiveScalarCone (integerPositiveNewtonRoof P) =
      positiveScalarCone (integerPositiveNewtonRoof Q) := by
  have hleading_ne (T : Module.End ℂ (Polynomial ℂ)) (hT : symbol T ≠ 0)
      (ρ σ : ℤ) : leadingForm ρ σ T ≠ 0 := by
    have hdegree : MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol T) =
        (vDeg ρ σ T : WithBot ℤ) := by
      have hnotbot : MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol T) ≠ ⊥ := by
        intro hbot
        exact hT ((MvPolynomial.weightedTotalDegree'_eq_bot_iff _ _).mp hbot)
      obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hnotbot
      unfold vDeg
      rw [← hm, WithBot.unbotD_coe]
    exact weightedComponent_ne_zero_of_weightedTotalDegree_eq (wt ρ σ)
      (symbol T) (vDeg ρ σ T) hdegree
  have hfaceP : ∀ ρ σ : ℤ, 0 < ρ + σ →
      ∃ d ∈ (leadingForm ρ σ P).support, d ≠ 0 := by
    intro ρ σ hsum
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr
      (hleading_ne P hPsymbol ρ σ)
    have hsubset : d ∈ (symbol P).support := by
      change d ∈ (MvPolynomial.weightedHomogeneousComponent (wt ρ σ)
        (vDeg ρ σ P) (symbol P)).support at hd
      rw [MvPolynomial.support_weightedHomogeneousComponent] at hd
      exact (Finset.mem_filter.mp hd).1
    refine ⟨d, hd, ?_⟩
    intro hd0
    exact hPconstant (hd0 ▸ hsubset)
  have hfaceQ : ∀ ρ σ : ℤ, 0 < ρ + σ →
      ∃ d ∈ (leadingForm ρ σ Q).support, d ≠ 0 := by
    intro ρ σ hsum
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr
      (hleading_ne Q hQsymbol ρ σ)
    have hsubset : d ∈ (symbol Q).support := by
      change d ∈ (MvPolynomial.weightedHomogeneousComponent (wt ρ σ)
        (vDeg ρ σ Q) (symbol Q)).support at hd
      rw [MvPolynomial.support_weightedHomogeneousComponent] at hd
      exact (Finset.mem_filter.mp hd).1
    refine ⟨d, hd, ?_⟩
    intro hd0
    exact hQconstant (hd0 ▸ hsubset)
  exact integerPositiveNewtonRoof_cones_equal_of_facewise_poisson_eq P Q
    hfaceP hfaceQ hbr

/-- Weyl-algebra form of the integer-direction roof lemma: if two nonconstant operators have
their scalar terms removed and every positive-sum integer pair of leading forms Poisson-commutes,
then the cones over their Newton roofs agree. -/
theorem integerPositiveNewtonRoof_cones_equal_of_zeroBracket_and_scalarFree
    (P Q : A1 ℂ)
    (hPnonconstant : ∃ d ∈ (symbol (P : Module.End ℂ (Polynomial ℂ))).support, d ≠ 0)
    (hQnonconstant : ∃ d ∈ (symbol (Q : Module.End ℂ (Polynomial ℂ))).support, d ≠ 0)
    (hPconstant : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (P : Module.End ℂ (Polynomial ℂ))).support)
    (hQconstant : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (Q : Module.End ℂ (Polynomial ℂ))).support)
    (hbr : ∀ ρ σ : ℤ, 0 < ρ + σ → poisson
      (leadingForm ρ σ (P : Module.End ℂ (Polynomial ℂ)))
      (leadingForm ρ σ (Q : Module.End ℂ (Polynomial ℂ))) = 0) :
    positiveScalarCone (integerPositiveNewtonRoof (P : Module.End ℂ (Polynomial ℂ))) =
      positiveScalarCone (integerPositiveNewtonRoof (Q : Module.End ℂ (Polynomial ℂ))) := by
  have hPsymbol : symbol (P : Module.End ℂ (Polynomial ℂ)) ≠ 0 := by
    intro hz
    rcases hPnonconstant with ⟨d, hd, hdne⟩
    simp [hz] at hd
  have hQsymbol : symbol (Q : Module.End ℂ (Polynomial ℂ)) ≠ 0 := by
    intro hz
    rcases hQnonconstant with ⟨d, hd, hdne⟩
    simp [hz] at hd
  exact integerPositiveNewtonRoof_cones_equal_of_zeroBracket_and_no_constant_terms
    (P : Module.End ℂ (Polynomial ℂ)) (Q : Module.End ℂ (Polynomial ℂ))
    hPsymbol hQsymbol hPconstant hQconstant hbr
end Dixmier.Weyl
