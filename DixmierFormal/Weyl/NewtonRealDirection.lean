/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.NewtonSolidSupport
public import Mathlib.Topology.Instances.Real.Lemmas

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Real and integer Newton faces

For finite integral exponent support, every nonempty face exposed by a real direction with
positive coordinate sum is exposed by a positive-sum integer direction. Nonsingleton faces use an
integer normal to two support points; singleton faces use rational density inside the open set of
directions preserving the strict inequalities. This identifies the corresponding PBW face with an
actual integer leading-form support. The operator roof-cone comparison remains separate.
-/

namespace Dixmier.Weyl

open Polynomial

/-- The real linear weight of an exponent point. -/
def realNewtonWeight (ρ σ : ℝ) (d : Fin 2 →₀ ℕ) : ℝ :=
  ρ * (d 0 : ℝ) + σ * (d 1 : ℝ)

/-- The set of support exponents maximizing a real linear weight. -/
def realExposedFace (ρ σ : ℝ) (S : Set (Fin 2 →₀ ℕ)) : Set (Fin 2 →₀ ℕ) :=
  {d | d ∈ S ∧ ∀ e ∈ S, realNewtonWeight ρ σ e ≤ realNewtonWeight ρ σ d}

/-- The real-direction Newton roof: the union of convex hulls of faces exposed by real weights
whose coordinate sum is positive, matching Han--Tan's convention. -/
def realPositiveNewtonRoof (T : Module.End ℂ ℂ[X]) : Set (ℝ × ℝ) :=
  {p | ∃ ρ σ : ℝ, 0 < ρ + σ ∧
    p ∈ convexHull ℝ
      (exponentPoint '' realExposedFace ρ σ ((symbol T).support : Set (Fin 2 →₀ ℕ)))}

private theorem realNewtonWeight_eq_cast_integerWeight
    (ρ σ : ℤ) (d : Fin 2 →₀ ℕ) :
    realNewtonWeight (ρ : ℝ) (σ : ℝ) d =
      ((Finsupp.weight (wt ρ σ) d : ℤ) : ℝ) := by
  simp [realNewtonWeight, wt, Finsupp.weight_eq_sum]
  ring

private theorem weightedDegree_eq_vDeg_of_mem_symbol_support
    (ρ σ : ℤ) (T : Module.End ℂ ℂ[X]) {d : Fin 2 →₀ ℕ}
    (hd : d ∈ (symbol T).support) :
    MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol T) =
      (vDeg ρ σ T : WithBot ℤ) := by
  have hsymbol : symbol T ≠ 0 := by
    intro hz
    have hsupport : (symbol T).support = ∅ := by simp [hz]
    rw [hsupport] at hd
    exact Finset.notMem_empty d hd
  have hnotbot : MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol T) ≠ ⊥ := by
    intro hbot
    exact hsymbol ((MvPolynomial.weightedTotalDegree'_eq_bot_iff _ _).mp hbot)
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hnotbot
  rw [← hm]
  simp [vDeg, ← hm]

/-- Membership in an integer leading-form support is exactly maximization of the corresponding
real linear weight on the PBW support. -/
theorem leadingForm_mem_iff_realExposedFace
    (ρ σ : ℤ) (T : Module.End ℂ ℂ[X]) (d : Fin 2 →₀ ℕ) :
    d ∈ (leadingForm ρ σ T).support ↔
      d ∈ realExposedFace (ρ : ℝ) (σ : ℝ)
        ((symbol T).support : Set (Fin 2 →₀ ℕ)) := by
  simp only [leadingForm, MvPolynomial.support_weightedHomogeneousComponent,
    Finset.mem_filter, Set.mem_ofPred_eq, realExposedFace]
  constructor
  · rintro ⟨hd, hdegree⟩
    refine ⟨hd, ?_⟩
    intro e he
    have htop := weightedDegree_eq_vDeg_of_mem_symbol_support ρ σ T he
    have hleBot :
        (Finsupp.weight (wt ρ σ) e : WithBot ℤ) ≤
          MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol T) := by
      rw [MvPolynomial.weightedTotalDegree']
      exact Finset.le_sup
        (f := fun x => (Finsupp.weight (wt ρ σ) x : WithBot ℤ)) he
    rw [htop] at hleBot
    have hle : Finsupp.weight (wt ρ σ) e ≤ Finsupp.weight (wt ρ σ) d := by
      have hleV : Finsupp.weight (wt ρ σ) e ≤ vDeg ρ σ T :=
        WithBot.coe_le_coe.mp hleBot
      rw [← hdegree] at hleV
      exact hleV
    calc
      realNewtonWeight (ρ : ℝ) (σ : ℝ) e =
          ((Finsupp.weight (wt ρ σ) e : ℤ) : ℝ) :=
        realNewtonWeight_eq_cast_integerWeight ρ σ e
      _ ≤ ((Finsupp.weight (wt ρ σ) d : ℤ) : ℝ) := by exact_mod_cast hle
      _ = realNewtonWeight (ρ : ℝ) (σ : ℝ) d :=
        (realNewtonWeight_eq_cast_integerWeight ρ σ d).symm
  · rintro ⟨hd, hmax⟩
    have htop := weightedDegree_eq_vDeg_of_mem_symbol_support ρ σ T hd
    have hsup_le :
        MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol T) ≤
          (Finsupp.weight (wt ρ σ) d : WithBot ℤ) := by
      rw [MvPolynomial.weightedTotalDegree', Finset.sup_le_iff]
      intro e he
      have hleReal := hmax e he
      have hleInt : Finsupp.weight (wt ρ σ) e ≤ Finsupp.weight (wt ρ σ) d := by
        simpa [realNewtonWeight_eq_cast_integerWeight] using hleReal
      exact WithBot.coe_le_coe.mpr hleInt
    have hle_sup :
        (Finsupp.weight (wt ρ σ) d : WithBot ℤ) ≤
          MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol T) := by
      rw [MvPolynomial.weightedTotalDegree']
      exact Finset.le_sup
        (f := fun x => (Finsupp.weight (wt ρ σ) x : WithBot ℤ)) hd
    have htop_weight :
        MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol T) =
          (Finsupp.weight (wt ρ σ) d : WithBot ℤ) := le_antisymm hsup_le hle_sup
    have hcast : (vDeg ρ σ T : WithBot ℤ) =
        (Finsupp.weight (wt ρ σ) d : WithBot ℤ) := htop.symm.trans htop_weight
    have hdegree : Finsupp.weight (wt ρ σ) d = vDeg ρ σ T := by
      exact_mod_cast hcast.symm
    exact ⟨hd, hdegree⟩

private theorem exponent_eq_of_int_coordinates
    {d e : Fin 2 →₀ ℕ}
    (h0 : (d 0 : ℤ) = (e 0 : ℤ)) (h1 : (d 1 : ℤ) = (e 1 : ℤ)) : d = e := by
  ext i
  fin_cases i
  · exact_mod_cast h0
  · exact_mod_cast h1

/-- If a real positive-sum direction exposes two distinct integer exponent points, its entire
exposed face is also exposed by an integer direction with positive coordinate sum. -/
theorem realExposedFace_eq_integer_of_two_points
    (ρ σ : ℝ) (S : Set (Fin 2 →₀ ℕ))
    (hsum : 0 < ρ + σ) {d e : Fin 2 →₀ ℕ}
    (hd : d ∈ realExposedFace ρ σ S)
    (he : e ∈ realExposedFace ρ σ S)
    (hne : d ≠ e) :
    ∃ r s : ℤ, 0 < r + s ∧
      realExposedFace ρ σ S = realExposedFace (r : ℝ) (s : ℝ) S := by
  have hde : realNewtonWeight ρ σ d = realNewtonWeight ρ σ e :=
    le_antisymm (he.2 d hd.1) (hd.2 e he.1)
  let a : ℤ := (d 0 : ℤ) - (e 0 : ℤ)
  let b : ℤ := (d 1 : ℤ) - (e 1 : ℤ)
  have hdot : ρ * (a : ℝ) + σ * (b : ℝ) = 0 := by
    dsimp [a, b, realNewtonWeight] at hde ⊢
    push_cast
    linear_combination hde
  have hcoords : (d 0 : ℤ) ≠ (e 0 : ℤ) ∨ (d 1 : ℤ) ≠ (e 1 : ℤ) := by
    by_contra h
    push Not at h
    exact hne (exponent_eq_of_int_coordinates h.1 h.2)
  have hnormal : b - a ≠ 0 := by
    intro hc
    have hba : b = a := sub_eq_zero.mp hc
    have hprod : (a : ℝ) * (ρ + σ) = 0 := by
      rw [hba] at hdot
      linear_combination hdot
    have haR : (a : ℝ) = 0 :=
      (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hsum)
    have ha : a = 0 := by exact_mod_cast haR
    have hb : b = 0 := by omega
    have hcoord0 : (d 0 : ℤ) = (e 0 : ℤ) := by
      dsimp [a] at ha
      omega
    have hcoord1 : (d 1 : ℤ) = (e 1 : ℤ) := by
      dsimp [b] at hb
      omega
    exact hcoords.elim (fun h => h hcoord0) (fun h => h hcoord1)
  have hface_eq {r s : ℤ}
      (hk : 0 < r + s)
      (hρ : ρ * ((r + s : ℤ) : ℝ) = (r : ℝ) * (ρ + σ))
      (hσ : σ * ((r + s : ℤ) : ℝ) = (s : ℝ) * (ρ + σ)) :
      realExposedFace ρ σ S = realExposedFace (r : ℝ) (s : ℝ) S := by
    have hkR : 0 < ((r + s : ℤ) : ℝ) := by exact_mod_cast hk
    have hsumR : 0 < ρ + σ := hsum
    have hscale (x : Fin 2 →₀ ℕ) :
        realNewtonWeight ρ σ x * ((r + s : ℤ) : ℝ) =
          realNewtonWeight (r : ℝ) (s : ℝ) x * (ρ + σ) := by
      calc
        _ = (ρ * ((r + s : ℤ) : ℝ)) * (x 0 : ℝ) +
              (σ * ((r + s : ℤ) : ℝ)) * (x 1 : ℝ) := by
                dsimp [realNewtonWeight]
                ring
        _ = ((r : ℝ) * (ρ + σ)) * (x 0 : ℝ) +
              ((s : ℝ) * (ρ + σ)) * (x 1 : ℝ) := by rw [hρ, hσ]
        _ = realNewtonWeight (r : ℝ) (s : ℝ) x * (ρ + σ) := by
              dsimp [realNewtonWeight]
              ring
    ext x
    change (x ∈ S ∧ ∀ y ∈ S,
        realNewtonWeight ρ σ y ≤ realNewtonWeight ρ σ x) ↔
      (x ∈ S ∧ ∀ y ∈ S,
        realNewtonWeight (r : ℝ) (s : ℝ) y ≤ realNewtonWeight (r : ℝ) (s : ℝ) x)
    constructor
    · rintro ⟨hx, hmax⟩
      refine ⟨hx, ?_⟩
      intro y hy
      have hmul := mul_le_mul_of_nonneg_right (hmax y hy) (le_of_lt hkR)
      rw [hscale y, hscale x] at hmul
      exact (mul_le_mul_iff_of_pos_right hsumR).mp hmul
    · rintro ⟨hx, hmax⟩
      refine ⟨hx, ?_⟩
      intro y hy
      have hmul := mul_le_mul_of_nonneg_right (hmax y hy) (le_of_lt hsumR)
      rw [← hscale y, ← hscale x] at hmul
      exact (mul_le_mul_iff_of_pos_right hkR).mp hmul
  by_cases hc : 0 < b - a
  · have hsumZ : 0 < b + -a := by omega
    have hρ : ρ * ((b + -a : ℤ) : ℝ) = (b : ℝ) * (ρ + σ) := by
      push_cast
      linear_combination -hdot
    have hσ : σ * ((b + -a : ℤ) : ℝ) = (-a : ℝ) * (ρ + σ) := by
      push_cast
      linear_combination hdot
    exact ⟨b, -a, hsumZ, hface_eq hsumZ hρ (by simpa only [Int.cast_neg] using hσ)⟩
  · have hneg : b - a < 0 := by omega
    have hsumZ : 0 < -b + a := by omega
    have hρ : ρ * ((-b + a : ℤ) : ℝ) = (-b : ℝ) * (ρ + σ) := by
      push_cast
      linear_combination hdot
    have hσ : σ * ((-b + a : ℤ) : ℝ) = (a : ℝ) * (ρ + σ) := by
      push_cast
      linear_combination -hdot
    exact ⟨-b, a, hsumZ, hface_eq hsumZ (by simpa only [Int.cast_neg] using hρ) hσ⟩

/-- A nonsingleton real exposed face of the PBW support is exactly the support of an integer
leading form in a positive-sum direction. -/
theorem realExposedFace_eq_leadingForm_support_of_two_points
    (ρ σ : ℝ) (T : Module.End ℂ ℂ[X])
    (hsum : 0 < ρ + σ) {d e : Fin 2 →₀ ℕ}
    (hd : d ∈ realExposedFace ρ σ ((symbol T).support : Set (Fin 2 →₀ ℕ)))
    (he : e ∈ realExposedFace ρ σ ((symbol T).support : Set (Fin 2 →₀ ℕ)))
    (hne : d ≠ e) :
    ∃ r s : ℤ, 0 < r + s ∧
      realExposedFace ρ σ ((symbol T).support : Set (Fin 2 →₀ ℕ)) =
        ((leadingForm r s T).support : Set (Fin 2 →₀ ℕ)) := by
  obtain ⟨r, s, hrs, hface⟩ :=
    realExposedFace_eq_integer_of_two_points ρ σ
      ((symbol T).support : Set (Fin 2 →₀ ℕ)) hsum hd he hne
  have hfaceLeading : realExposedFace (r : ℝ) (s : ℝ)
      ((symbol T).support : Set (Fin 2 →₀ ℕ)) =
        ((leadingForm r s T).support : Set (Fin 2 →₀ ℕ)) := by
    ext x
    exact (leadingForm_mem_iff_realExposedFace r s T x).symm
  exact ⟨r, s, hrs, hface.trans hfaceLeading⟩

/-- The convex hull of a nonsingleton real exposed face is one of the faces in the integer
positive Newton roof. -/
theorem realExposedFace_convexHull_subset_integerPositiveNewtonRoof_of_two_points
    (ρ σ : ℝ) (T : Module.End ℂ ℂ[X])
    (hsum : 0 < ρ + σ) {d e : Fin 2 →₀ ℕ}
    (hd : d ∈ realExposedFace ρ σ ((symbol T).support : Set (Fin 2 →₀ ℕ)))
    (he : e ∈ realExposedFace ρ σ ((symbol T).support : Set (Fin 2 →₀ ℕ)))
    (hne : d ≠ e) :
    convexHull ℝ
      (exponentPoint '' realExposedFace ρ σ
        ((symbol T).support : Set (Fin 2 →₀ ℕ))) ⊆ integerPositiveNewtonRoof T := by
  obtain ⟨r, s, hrs, hface⟩ :=
    realExposedFace_eq_leadingForm_support_of_two_points ρ σ T hsum hd he hne
  intro p hp
  rw [hface] at hp
  exact ⟨r, s, hrs, hp⟩

/-- A real direction that strictly exposes one point of finite integral support can be replaced
by an integer direction with positive coordinate sum and the same exposed face. -/
theorem realExposedFace_eq_integer_of_unique_point
    (ρ σ : ℝ) (S : Set (Fin 2 →₀ ℕ))
    (hsum : 0 < ρ + σ) (hS : S.Finite) {d : Fin 2 →₀ ℕ}
    (hd : d ∈ realExposedFace ρ σ S)
    (hstrict : ∀ e ∈ S, e ≠ d → realNewtonWeight ρ σ e < realNewtonWeight ρ σ d) :
    ∃ r s : ℤ, 0 < r + s ∧
      realExposedFace ρ σ S = realExposedFace (r : ℝ) (s : ℝ) S := by
  let t₀ : ℝ := ρ / (ρ + σ)
  have hnormpos : 0 < ρ + σ := hsum
  have hnorm (x : Fin 2 →₀ ℕ) :
      realNewtonWeight t₀ (1 - t₀) x = realNewtonWeight ρ σ x / (ρ + σ) := by
    dsimp [t₀, realNewtonWeight]
    field_simp
    ring
  let U : Set ℝ := ⋂ e ∈ S,
    {t | e = d ∨ realNewtonWeight t (1 - t) e < realNewtonWeight t (1 - t) d}
  have hUopen : IsOpen U := by
    apply hS.isOpen_biInter
    intro e he
    by_cases hed : e = d
    · simp [hed]
    · have hc₁ : Continuous (fun t : ℝ => realNewtonWeight t (1 - t) e) := by
        dsimp [realNewtonWeight]
        fun_prop
      have hc₂ : Continuous (fun t : ℝ => realNewtonWeight t (1 - t) d) := by
        dsimp [realNewtonWeight]
        fun_prop
      have hopen : IsOpen {t : ℝ | realNewtonWeight t (1 - t) e <
          realNewtonWeight t (1 - t) d} := isOpen_lt hc₁ hc₂
      simpa [hed] using hopen
  have ht₀ : t₀ ∈ U := by
    apply Set.mem_iInter.2
    intro e
    apply Set.mem_iInter.2
    intro he
    by_cases hed : e = d
    · exact Or.inl hed
    · right
      rw [hnorm e, hnorm d]
      exact (div_lt_div_iff_of_pos_right hnormpos).2 (hstrict e he hed)
  obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hUopen ⟨t₀, ht₀⟩
  let r : ℤ := q.num
  let s : ℤ := (q.den : ℤ) - q.num
  have hdenNat : 0 < q.den := Rat.den_pos q
  have hdenInt : 0 < (q.den : ℤ) := by exact_mod_cast hdenNat
  have hsumPositive : 0 < r + s := by dsimp [r, s]; omega
  have hdenRealPos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast hdenNat
  have hqmul : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by
    rw [Rat.cast_def]
    field_simp
  have hscale (x : Fin 2 →₀ ℕ) :
      realNewtonWeight (r : ℝ) (s : ℝ) x =
        (q.den : ℝ) * realNewtonWeight (q : ℝ) (1 - q) x := by
    dsimp [r, s, realNewtonWeight]
    push_cast
    rw [← hqmul]
    ring
  have hleftEq : realExposedFace ρ σ S = {d} := by
    ext x
    simp only [realExposedFace, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hmax⟩
      by_contra hne
      have hlt := hstrict x hx hne
      exact (not_lt_of_ge (hmax d hd.1)) hlt
    · intro hx
      subst x
      exact ⟨hd.1, hd.2⟩
  have hrightEq : realExposedFace (r : ℝ) (s : ℝ) S = {d} := by
    ext x
    simp only [realExposedFace, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hmax⟩
      by_contra hne
      have hqmem := Set.mem_iInter.1 (Set.mem_iInter.1 hq x) hx
      have hgood := hqmem
      have hltNorm : realNewtonWeight (q : ℝ) (1 - q) x <
          realNewtonWeight (q : ℝ) (1 - q) d := by
        rcases hgood with hEq | hlt
        · exact (hne hEq).elim
        · exact hlt
      have hlt : realNewtonWeight (r : ℝ) (s : ℝ) x <
          realNewtonWeight (r : ℝ) (s : ℝ) d := by
        calc
          _ = (q.den : ℝ) * realNewtonWeight (q : ℝ) (1 - q) x := hscale x
          _ < (q.den : ℝ) * realNewtonWeight (q : ℝ) (1 - q) d :=
            mul_lt_mul_of_pos_left hltNorm hdenRealPos
          _ = _ := (hscale d).symm
      exact (not_lt_of_ge (hmax d hd.1)) hlt
    · intro hx
      subst x
      refine ⟨hd.1, ?_⟩
      intro y hy
      by_cases heq : y = d
      · subst y
        exact le_rfl
      · have hqmem := Set.mem_iInter.1 (Set.mem_iInter.1 hq y) hy
        rcases hqmem with hEq | hlt
        · exact (heq hEq).elim
        · have hlt' : realNewtonWeight (r : ℝ) (s : ℝ) y <
            realNewtonWeight (r : ℝ) (s : ℝ) d := by
              calc
                _ = (q.den : ℝ) * realNewtonWeight (q : ℝ) (1 - q) y := hscale y
                _ < (q.den : ℝ) * realNewtonWeight (q : ℝ) (1 - q) d :=
                  mul_lt_mul_of_pos_left hlt hdenRealPos
                _ = _ := (hscale d).symm
          exact hlt'.le
  exact ⟨r, s, hsumPositive, hleftEq.trans hrightEq.symm⟩

/-- Every nonempty real exposed face of finite integral support is realized by an integer
direction with positive coordinate sum. The nonsingleton case uses an integral normal to two
lattice points; the singleton case uses rational density in the open set of directions preserving
the strict inequalities. -/
theorem realExposedFace_eq_integer_of_nonempty_finite
    (ρ σ : ℝ) (S : Set (Fin 2 →₀ ℕ))
    (hsum : 0 < ρ + σ) (hS : S.Finite)
    (hface : (realExposedFace ρ σ S).Nonempty) :
    ∃ r s : ℤ, 0 < r + s ∧
      realExposedFace ρ σ S = realExposedFace (r : ℝ) (s : ℝ) S := by
  obtain ⟨d, hd⟩ := hface
  by_cases htwo : ∃ e, e ∈ realExposedFace ρ σ S ∧ e ≠ d
  · obtain ⟨e, he, hne⟩ := htwo
    exact realExposedFace_eq_integer_of_two_points ρ σ S hsum hd he hne.symm
  · have hstrict (e : Fin 2 →₀ ℕ) (he : e ∈ S) (hne : e ≠ d) :
        realNewtonWeight ρ σ e < realNewtonWeight ρ σ d := by
      have hle := hd.2 e he
      by_contra hnotlt
      have hge : realNewtonWeight ρ σ d ≤ realNewtonWeight ρ σ e :=
        le_of_not_gt hnotlt
      have heq : realNewtonWeight ρ σ e = realNewtonWeight ρ σ d :=
        le_antisymm hle hge
      have heface : e ∈ realExposedFace ρ σ S := by
        refine ⟨he, ?_⟩
        intro y hy
        calc
          realNewtonWeight ρ σ y ≤ realNewtonWeight ρ σ d := hd.2 y hy
          _ = realNewtonWeight ρ σ e := heq.symm
      exact htwo ⟨e, heface, hne⟩
    exact realExposedFace_eq_integer_of_unique_point
      ρ σ S hsum hS hd hstrict

/-- Every nonempty real exposed face of an operator's PBW support is the support of an integer
leading form with positive coordinate sum. -/
theorem realExposedFace_eq_leadingForm_support_of_nonempty_finite
    (ρ σ : ℝ) (T : Module.End ℂ ℂ[X]) (hsum : 0 < ρ + σ)
    (hface : (realExposedFace ρ σ
      ((symbol T).support : Set (Fin 2 →₀ ℕ))).Nonempty) :
    ∃ r s : ℤ, 0 < r + s ∧
      realExposedFace ρ σ ((symbol T).support : Set (Fin 2 →₀ ℕ)) =
        ((leadingForm r s T).support : Set (Fin 2 →₀ ℕ)) := by
  have hS : ((symbol T).support : Set (Fin 2 →₀ ℕ)).Finite := Set.toFinite _
  obtain ⟨r, s, hrs, hfaceEq⟩ :=
    realExposedFace_eq_integer_of_nonempty_finite ρ σ
      ((symbol T).support : Set (Fin 2 →₀ ℕ)) hsum hS hface
  have hleading : realExposedFace (r : ℝ) (s : ℝ)
      ((symbol T).support : Set (Fin 2 →₀ ℕ)) =
        ((leadingForm r s T).support : Set (Fin 2 →₀ ℕ)) := by
    ext d
    exact (leadingForm_mem_iff_realExposedFace r s T d).symm
  exact ⟨r, s, hrs, hfaceEq.trans hleading⟩

/-- The convex hull of any nonempty real exposed face of an operator's PBW support lies in the
integer positive Newton roof. -/
theorem realExposedFace_convexHull_subset_integerPositiveNewtonRoof_of_nonempty_finite
    (ρ σ : ℝ) (T : Module.End ℂ ℂ[X]) (hsum : 0 < ρ + σ)
    (hface : (realExposedFace ρ σ
      ((symbol T).support : Set (Fin 2 →₀ ℕ))).Nonempty) :
    convexHull ℝ
      (exponentPoint '' realExposedFace ρ σ
        ((symbol T).support : Set (Fin 2 →₀ ℕ))) ⊆ integerPositiveNewtonRoof T := by
  obtain ⟨r, s, hrs, hfaceEq⟩ :=
    realExposedFace_eq_leadingForm_support_of_nonempty_finite ρ σ T hsum hface
  intro p hp
  rw [hfaceEq] at hp
  exact ⟨r, s, hrs, hp⟩

/-- The real-direction roof and the formalized integer-direction roof agree for every finite PBW
support. The forward inclusion uses the finite exposed-face theorem; the reverse inclusion regards
an integer direction as a real direction. -/
theorem realPositiveNewtonRoof_eq_integerPositiveNewtonRoof
    (T : Module.End ℂ ℂ[X]) :
    realPositiveNewtonRoof T = integerPositiveNewtonRoof T := by
  ext p
  constructor
  · rintro ⟨ρ, σ, hsum, hp⟩
    have hface : (realExposedFace ρ σ
        ((symbol T).support : Set (Fin 2 →₀ ℕ))).Nonempty := by
      have hconv :
          (convexHull ℝ (exponentPoint '' realExposedFace ρ σ
            ((symbol T).support : Set (Fin 2 →₀ ℕ)))).Nonempty := ⟨p, hp⟩
      exact Set.image_nonempty.mp (convexHull_nonempty_iff.mp hconv)
    obtain ⟨r, s, hrs, hfaceEq⟩ :=
      realExposedFace_eq_leadingForm_support_of_nonempty_finite ρ σ T hsum hface
    rw [hfaceEq] at hp
    exact ⟨r, s, hrs, hp⟩
  · rintro ⟨r, s, hrs, hp⟩
    have hfaceReal : realExposedFace (r : ℝ) (s : ℝ)
        ((symbol T).support : Set (Fin 2 →₀ ℕ)) =
          ((leadingForm r s T).support : Set (Fin 2 →₀ ℕ)) := by
      ext d
      exact (leadingForm_mem_iff_realExposedFace r s T d).symm
    have hsumReal : 0 < (r : ℝ) + (s : ℝ) := by exact_mod_cast hrs
    rw [← hfaceReal] at hp
    exact ⟨(r : ℝ), (s : ℝ), hsumReal, hp⟩

end Dixmier.Weyl
