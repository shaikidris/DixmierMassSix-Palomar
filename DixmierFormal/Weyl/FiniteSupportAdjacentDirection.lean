/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PolynomialCutMateAlignment

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# First adjacent direction of a finite Newton support

This finite-support lemma constructs the first lower supporting slope
from a point below the derivative order of the old-face endpoint. The
existence of such a point in the G13 exact-pair setting is separate.
-/

namespace Dixmier.Weyl

/-- If a finite support has a top face whose first point has derivative
order `M`, and some support point has smaller order, there is a positive
rational slope at which the old endpoint meets a lower-order point on a
new maximal face. -/
theorem finiteSupport_exists_adjacent_rational_slope
    (S : Finset (ℤ × ℕ)) (w : ℤ × ℕ → ℤ)
    (V : ℤ) (M : ℕ)
    (htop : ∀ p ∈ S, w p ≤ V)
    (hfirst : ∀ p ∈ S, w p = V → M ≤ p.2)
    (hbelow : ∃ p ∈ S, p.2 < M) :
    ∃ t : ℚ, 0 < t ∧
      (∀ p ∈ S,
        (w p : ℚ) - t * (p.2 : ℚ) ≤ (V : ℚ) - t * (M : ℚ)) ∧
      (∃ B ∈ S, B.2 < M ∧
        (w B : ℚ) - t * (B.2 : ℚ) = (V : ℚ) - t * (M : ℚ)) := by
  classical
  let L : Finset (ℤ × ℕ) := S.filter (fun p => p.2 < M)
  let gap : ℤ × ℕ → ℚ := fun p =>
    ((V - w p : ℤ) : ℚ) / ((M - p.2 : ℕ) : ℚ)
  have hL : L.Nonempty := by
    obtain ⟨p,hp,hpm⟩ := hbelow
    exact ⟨p, Finset.mem_filter.mpr ⟨hp,hpm⟩⟩
  have hgapPos (p : ℤ × ℕ) (hp : p ∈ L) : 0 < gap p := by
    obtain ⟨hpS,hpm⟩ := Finset.mem_filter.mp hp
    have hstrict : w p < V := by
      have hle := htop p hpS
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · exact False.elim (Nat.not_lt_of_ge (hfirst p hpS heq) hpm)
    have hnum : (0 : ℚ) < ((V - w p : ℤ) : ℚ) := by exact_mod_cast sub_pos.mpr hstrict
    have hden : (0 : ℚ) < ((M - p.2 : ℕ) : ℚ) := by
      have hnat : 0 < M - p.2 := by omega
      exact_mod_cast hnat
    exact div_pos hnum hden
  let values : Finset ℚ := L.image gap
  have hvalues : values.Nonempty := hL.image gap
  let t : ℚ := values.min' hvalues
  obtain ⟨B,hBL,hBt⟩ := Finset.mem_image.mp (Finset.min'_mem values hvalues)
  have htpos : 0 < t := by
    change 0 < values.min' hvalues
    rw [← hBt]
    exact hgapPos B hBL
  refine ⟨t,htpos,?_,?_⟩
  · intro p hpS
    by_cases hpm : p.2 < M
    · have hpL : p ∈ L := Finset.mem_filter.mpr ⟨hpS,hpm⟩
      have hmin : t ≤ gap p :=
        Finset.min'_le values (gap p) (Finset.mem_image.mpr ⟨p,hpL,rfl⟩)
      have hden : (0 : ℚ) < ((M - p.2 : ℕ) : ℚ) := by
        have hnat : 0 < M - p.2 := by omega
        exact_mod_cast hnat
      have hcast : ((M - p.2 : ℕ) : ℚ) = (M : ℚ) - (p.2 : ℚ) := by
        rw [Nat.cast_sub (Nat.le_of_lt hpm)]
      dsimp [gap] at hmin
      rw [le_div_iff₀ hden] at hmin
      rw [hcast] at hmin
      push_cast at hmin
      nlinarith [hmin]
    · have hmn : M ≤ p.2 := Nat.le_of_not_gt hpm
      have hw : (w p : ℚ) ≤ (V : ℚ) := by exact_mod_cast htop p hpS
      have hn : (M : ℚ) ≤ (p.2 : ℚ) := by exact_mod_cast hmn
      nlinarith [mul_nonneg (le_of_lt htpos) (sub_nonneg.mpr hn)]
  · have hBS : B ∈ S := (Finset.mem_filter.mp hBL).1
    have hBM : B.2 < M := (Finset.mem_filter.mp hBL).2
    refine ⟨B,hBS,hBM,?_⟩
    have hcast : ((M - B.2 : ℕ) : ℚ) = (M : ℚ) - (B.2 : ℚ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hBM)]
    have hden : (0 : ℚ) < ((M - B.2 : ℕ) : ℚ) := by
      have hnat : 0 < M - B.2 := by omega
      exact_mod_cast hnat
    change gap B = t at hBt
    dsimp [gap] at hBt
    rw [div_eq_iff (ne_of_gt hden), hcast] at hBt
    push_cast at hBt
    nlinarith [hBt]

/-- At any positive downward tilt supported at the old endpoint,
every point of the new face has derivative order at most that of the
old endpoint. Thus an old-face start becomes a new-face end. -/
theorem finiteSupport_tilted_face_order_le_old_start
    (S : Finset (ℤ × ℕ)) (w : ℤ × ℕ → ℤ)
    (V : ℤ) (M : ℕ) (t : ℚ) (ht : 0 < t)
    (htop : ∀ p ∈ S, w p ≤ V)
    (p : ℤ × ℕ) (hp : p ∈ S)
    (hface : (w p : ℚ) - t * (p.2 : ℚ) =
      (V : ℚ) - t * (M : ℚ)) :
    p.2 ≤ M := by
  have hw : (w p : ℚ) ≤ (V : ℚ) := by
    exact_mod_cast htop p hp
  by_contra hbad
  have hn : (M : ℚ) < (p.2 : ℚ) := by
    exact_mod_cast Nat.lt_of_not_ge hbad
  nlinarith [mul_pos ht (sub_pos.mpr hn)]

/-- Before the first supporting tilt of a finite support, any point
that still ties the old endpoint must have the endpoint's derivative
order and old weight. This is the finite-support content of the
singleton-face step in G13 Proposition 5.3's differing-direction
argument. -/
theorem finiteSupport_before_first_slope_old_endpoint
    (S : Finset (ℤ × ℕ)) (w : ℤ × ℕ → ℤ)
    (V : ℤ) (M : ℕ) (t tFirst : ℚ)
    (ht : 0 < t) (hbefore : t < tFirst)
    (htop : ∀ p ∈ S, w p ≤ V)
    (hfirst : ∀ p ∈ S,
      (w p : ℚ) - tFirst * (p.2 : ℚ) ≤
        (V : ℚ) - tFirst * (M : ℚ))
    (p : ℤ × ℕ) (hp : p ∈ S)
    (htie : (w p : ℚ) - t * (p.2 : ℚ) =
      (V : ℚ) - t * (M : ℚ)) :
    p.2 = M ∧ w p = V := by
  have hle : p.2 ≤ M :=
    finiteSupport_tilted_face_order_le_old_start
      S w V M t ht htop p hp htie
  have hq := hfirst p hp
  by_contra hbad
  have hlt : p.2 < M := by
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · have hw : w p = V := by
        have hcast : (p.2 : ℚ) = (M : ℚ) := by exact_mod_cast heq
        rw [hcast] at htie
        exact_mod_cast (by linarith [htie] : (w p : ℚ) = (V : ℚ))
      exact False.elim (hbad ⟨heq,hw⟩)
  have hltQ : (p.2 : ℚ) < (M : ℚ) := by exact_mod_cast hlt
  nlinarith [htie,hq]

/-- An old endpoint remains a support maximum at every nonnegative
tilt up to the support's first adjacent slope. This complements the
singleton-on-strictly-earlier-tilts theorem above. -/
theorem finiteSupport_before_first_slope_bound
    (S : Finset (ℤ × ℕ)) (w : ℤ × ℕ → ℤ)
    (V : ℤ) (M : ℕ) (t tFirst : ℚ)
    (ht : 0 ≤ t) (hbefore : t ≤ tFirst)
    (htop : ∀ p ∈ S, w p ≤ V)
    (hfirst : ∀ p ∈ S,
      (w p : ℚ) - tFirst * (p.2 : ℚ) ≤
        (V : ℚ) - tFirst * (M : ℚ)) :
    ∀ p ∈ S,
      (w p : ℚ) - t * (p.2 : ℚ) ≤
        (V : ℚ) - t * (M : ℚ) := by
  intro p hp
  have hw : (w p : ℚ) ≤ (V : ℚ) := by exact_mod_cast htop p hp
  by_cases hbelow : p.2 ≤ M
  · have hdiff : (0 : ℚ) ≤ (M : ℚ) - (p.2 : ℚ) := by
      have hle : (p.2 : ℚ) ≤ (M : ℚ) := by exact_mod_cast hbelow
      linarith
    have hgap : 0 ≤ (tFirst-t)*((M : ℚ)-(p.2 : ℚ)) :=
      mul_nonneg (sub_nonneg.mpr hbefore) hdiff
    nlinarith [hfirst p hp, hgap]
  · have horder : (M : ℚ) ≤ (p.2 : ℚ) := by
      exact_mod_cast Nat.le_of_not_ge hbelow
    have hprod : 0 ≤ t*((p.2 : ℚ)-(M : ℚ)) :=
      mul_nonneg ht (sub_nonneg.mpr horder)
    nlinarith

/-- For the actual ramified PBW weight, equal order and equal old
weight determine the entire endpoint. Thus before its first adjacent
tilt a support has a singleton face at its old endpoint. -/
theorem ramifiedSupport_before_first_slope_singleton
    (l : ℕ) (ρ σ : ℤ) (hρ : 0 < ρ)
    (S : Finset (ℤ × ℕ)) (V : ℤ) (E : ℤ × ℕ)
    (hE : ramifiedWeight l ρ σ E = V)
    (t tFirst : ℚ) (ht : 0 < t) (hbefore : t < tFirst)
    (htop : ∀ p ∈ S, ramifiedWeight l ρ σ p ≤ V)
    (hfirst : ∀ p ∈ S,
      (ramifiedWeight l ρ σ p : ℚ) - tFirst * (p.2 : ℚ) ≤
        (V : ℚ) - tFirst * (E.2 : ℚ))
    (p : ℤ × ℕ) (hp : p ∈ S)
    (htie : (ramifiedWeight l ρ σ p : ℚ) - t * (p.2 : ℚ) =
      (V : ℚ) - t * (E.2 : ℚ)) :
    p = E := by
  obtain ⟨hn,hw⟩ := finiteSupport_before_first_slope_old_endpoint
    S (ramifiedWeight l ρ σ) V E.2 t tFirst ht hbefore
      htop hfirst p hp htie
  rcases p with ⟨u,n⟩
  rcases E with ⟨v,m⟩
  dsimp at hn hw hE
  have hu : u = v := by
    dsimp [ramifiedWeight] at hw hE
    rw [hn] at hw
    nlinarith
  exact Prod.ext hu hn

/-- If a support point already beats the old endpoint at a later
tilt, then the first supporting tilt occurs strictly earlier. -/
theorem finiteSupport_first_slope_lt_of_later_exceedance
    (S : Finset (ℤ × ℕ)) (w : ℤ × ℕ → ℤ)
    (V : ℤ) (M : ℕ) (tFirst tLater : ℚ)
    (hLater : 0 < tLater)
    (htop : ∀ p ∈ S, w p ≤ V)
    (hfirst : ∀ p ∈ S,
      (w p : ℚ) - tFirst * (p.2 : ℚ) ≤
        (V : ℚ) - tFirst * (M : ℚ))
    (B : ℤ × ℕ) (hB : B ∈ S)
    (hexceed : (V : ℚ) - tLater * (M : ℚ) <
      (w B : ℚ) - tLater * (B.2 : ℚ)) :
    tFirst < tLater := by
  have hw : (w B : ℚ) ≤ (V : ℚ) := by
    exact_mod_cast htop B hB
  have horder : B.2 < M := by
    by_contra hnot
    have hn : (M : ℚ) ≤ (B.2 : ℚ) := by
      exact_mod_cast Nat.le_of_not_gt hnot
    nlinarith [mul_nonneg (le_of_lt hLater) (sub_nonneg.mpr hn)]
  have hn : (B.2 : ℚ) < (M : ℚ) := by exact_mod_cast horder
  have hf := hfirst B hB
  by_contra hnot
  have ht : tLater ≤ tFirst := le_of_not_gt hnot
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr (le_of_lt hn))]

/-- A negative-grade old endpoint and a nonnegative-grade support
point force the first adjacent tilt to occur before the grade
direction. The latter is at tilt `l*(ρ+σ)`, so the resulting direction
has positive sum after normalization. -/
theorem ramifiedSupport_first_slope_before_grade_direction
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (S : Finset (ℤ × ℕ)) (V : ℤ)
    (E B : ℤ × ℕ) (tFirst : ℚ)
    (hEweight : ramifiedWeight l ρ σ E = V)
    (hEgrade : E.1 - (l : ℤ) * (E.2 : ℤ) < 0)
    (hBgrade : 0 ≤ B.1 - (l : ℤ) * (B.2 : ℤ))
    (htop : ∀ p ∈ S, ramifiedWeight l ρ σ p ≤ V)
    (hfirst : ∀ p ∈ S,
      (ramifiedWeight l ρ σ p : ℚ) - tFirst * (p.2 : ℚ) ≤
        (V : ℚ) - tFirst * (E.2 : ℚ))
    (hB : B ∈ S) :
    tFirst < (l : ℚ) * ((ρ + σ : ℤ) : ℚ) := by
  let tLater : ℚ := (l : ℚ) * ((ρ + σ : ℤ) : ℚ)
  have htLater : 0 < tLater := by
    dsimp [tLater]
    exact mul_pos (by exact_mod_cast hl) (by exact_mod_cast hsum)
  have hidentity (p : ℤ × ℕ) :
      (ramifiedWeight l ρ σ p : ℚ) - tLater * (p.2 : ℚ) =
        (ρ : ℚ) * ((p.1 : ℚ) - (l : ℚ) * (p.2 : ℚ)) := by
    dsimp [ramifiedWeight, tLater]
    push_cast
    ring
  have hneg : (E.1 : ℚ) - (l : ℚ) * (E.2 : ℚ) < 0 := by
    exact_mod_cast hEgrade
  have hnonneg : 0 ≤ (B.1 : ℚ) - (l : ℚ) * (B.2 : ℚ) := by
    exact_mod_cast hBgrade
  have hρQ : (0 : ℚ) < (ρ : ℚ) := by exact_mod_cast hρ
  have hexceed : (V : ℚ) - tLater * (E.2 : ℚ) <
      (ramifiedWeight l ρ σ B : ℚ) - tLater * (B.2 : ℚ) := by
    rw [← hEweight, hidentity E, hidentity B]
    nlinarith [mul_neg_of_pos_of_neg hρQ hneg,
      mul_nonneg (le_of_lt hρQ) hnonneg]
  exact finiteSupport_first_slope_lt_of_later_exceedance
    S (ramifiedWeight l ρ σ) V E.2 tFirst tLater htLater
      htop hfirst B hB hexceed

/-- The finite-support slope lemma applied to the actual polynomial
source after a ramified cut. A lower-order PBW point is the explicit
remaining premise; G13 derives it from additional companion geometry. -/
theorem polynomialRamifiedCut_exists_adjacent_slope_of_lower_order_point
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (i j : ℕ)
    (hface : expo i j ∈ (leadingForm ρ σ P.1).support)
    (c : ℂ)
    (hbelow : ∃ u : ℤ, ∃ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) ∧
      n < (cutPoly ρ σ P.1).rootMultiplicity c) :
    let r := ((l : ℤ) / ρ) * vDeg ρ σ P.1
    let m := (cutPoly ρ σ P.1).rootMultiplicity c
    let U := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)
    ∃ t : ℚ, 0 < t ∧
      (∀ p ∈ ramifiedPBWSupport l hl U,
        (ramifiedWeight l ρ σ p : ℚ) - t * (p.2 : ℚ) ≤
          ((ρ*r : ℤ) : ℚ) - t * (m : ℚ)) ∧
      (∃ B ∈ ramifiedPBWSupport l hl U, B.2 < m ∧
        (ramifiedWeight l ρ σ B : ℚ) - t * (B.2 : ℚ) =
          ((ρ*r : ℤ) : ℚ) - t * (m : ℚ)) ∧
      (∀ p ∈ ramifiedPBWSupport l hl U,
        (ramifiedWeight l ρ σ p : ℚ) - t * (p.2 : ℚ) =
          ((ρ*r : ℤ) : ℚ) - t * (m : ℚ) → p.2 ≤ m) := by
  obtain ⟨u,n,hum,hnm⟩ := hbelow
  have hs := polynomialRamifiedCut_root_start_on_old_face
    l hl P ρ σ hρ hdiv hpos i j hface c
  have hsource : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl (polynomialRamifiedLift l P) →
      ramifiedWeight l ρ σ (u,n) ≤
        ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1) := by
    intro u n hu
    exact polynomialRamifiedLift_weight_le_scaled_vDeg
      l hl P ρ σ hdiv u n hu
  have htop := ramifiedCutAut_weight_upper l hl ρ σ
    (((l : ℤ) / ρ) * vDeg ρ σ P.1)
    hρ hdiv hpos c (polynomialRamifiedLift l P) hsource
  have hfin := finiteSupport_exists_adjacent_rational_slope
    (ramifiedPBWSupport l hl
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)))
    (ramifiedWeight l ρ σ)
    (ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1))
    ((cutPoly ρ σ P.1).rootMultiplicity c)
    (by intro p hp; exact htop p.1 p.2 hp)
    (by intro p hp hw; exact hs.2 p.1 p.2 hp hw)
    ⟨(u,n),hum,hnm⟩
  obtain ⟨t,ht,hall,hB⟩ := hfin
  refine ⟨t,ht,hall,hB,?_⟩
  intro p hp hnew
  exact finiteSupport_tilted_face_order_le_old_start
    (ramifiedPBWSupport l hl
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)))
    (ramifiedWeight l ρ σ)
    (ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1))
    ((cutPoly ρ σ P.1).rootMultiplicity c) t ht
    (by intro q hq; exact htop q.1 q.2 hq) p hp hnew

/-- The order-zero ramified PBW coefficient is the value of the
operator on the constant Laurent polynomial `1`. -/
theorem ramified_apply_one_eq_pbwCoeff_zero
    (l : ℕ) (hl : 0 < l) (T : ramifiedOperatorAlgebra l) :
    (T : Module.End ℂ (LaurentPolynomial ℂ)) 1 =
      (ramifiedPBWCoeffs l hl T) 0 := by
  have h := congrArg
    (fun U : Module.End ℂ (LaurentPolynomial ℂ) =>
      U (1 : LaurentPolynomial ℂ))
    (ramifiedPBWCoeffs_eval l hl T)
  rw [ramifiedNormalEval_apply] at h
  have hsum : (ramifiedPBWCoeffs l hl T).sum
      (fun j f => f * ((ramifiedDerivative l)^j)
        (1 : LaurentPolynomial ℂ)) =
      (ramifiedPBWCoeffs l hl T) 0 := by
    rw [Finsupp.sum]
    calc
      (∑ j ∈ (ramifiedPBWCoeffs l hl T).support,
          (ramifiedPBWCoeffs l hl T) j *
            ((ramifiedDerivative l)^j) (1 : LaurentPolynomial ℂ)) =
          (ramifiedPBWCoeffs l hl T) 0 *
            ((ramifiedDerivative l)^0) (1 : LaurentPolynomial ℂ) := by
        apply Finset.sum_eq_single 0
        · intro j hj hj0
          have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
          have hzero := ramifiedDerivative_pow_X_pow_zero
            l hl 0 j hjpos
          rw [show (1 : LaurentPolynomial ℂ) =
            (LaurentPolynomial.T (l : ℤ))^0 by simp]
          rw [hzero]
          simp
        · intro hnot
          have hz : (ramifiedPBWCoeffs l hl T) 0 = 0 :=
            Finsupp.notMem_support_iff.mp hnot
          simp [hz]
      _ = (ramifiedPBWCoeffs l hl T) 0 := by simp
  exact h.symm.trans hsum

/-- If all occupied PBW terms have positive derivative order, the
operator annihilates the constant polynomial. -/
theorem ramified_apply_one_eq_zero_of_no_order_zero
    (l : ℕ) (hl : 0 < l) (T : ramifiedOperatorAlgebra l)
    (hno : ∀ i : ℤ, (i,0) ∉ ramifiedPBWSupport l hl T) :
    (T : Module.End ℂ (LaurentPolynomial ℂ)) 1 = 0 := by
  rw [ramified_apply_one_eq_pbwCoeff_zero l hl T]
  apply LaurentPolynomial.ext
  intro i
  by_contra hne
  exact hno i ((ramifiedPBWSupport_mem_iff l hl T i 0).mpr hne)

/-- An exact ramified Weyl pair has an order-zero term in at least
one member. This is an exact-operator statement, not a Poisson
approximation. -/
theorem ramified_exact_pair_has_order_zero_point
    (l : ℕ) (hl : 0 < l) (P Q : ramifiedOperatorAlgebra l)
    (hQP : Q * P - P * Q = 1) :
    (∃ i : ℤ, (i,0) ∈ ramifiedPBWSupport l hl P) ∨
      (∃ i : ℤ, (i,0) ∈ ramifiedPBWSupport l hl Q) := by
  by_contra hnone
  push Not at hnone
  have hP : (P : Module.End ℂ (LaurentPolynomial ℂ)) 1 = 0 :=
    ramified_apply_one_eq_zero_of_no_order_zero l hl P hnone.1
  have hQ : (Q : Module.End ℂ (LaurentPolynomial ℂ)) 1 = 0 :=
    ramified_apply_one_eq_zero_of_no_order_zero l hl Q hnone.2
  have h := congrArg
    (fun U : ramifiedOperatorAlgebra l =>
      (U : Module.End ℂ (LaurentPolynomial ℂ))
        (1 : LaurentPolynomial ℂ)) hQP
  change (Q : Module.End ℂ (LaurentPolynomial ℂ))
      ((P : Module.End ℂ (LaurentPolynomial ℂ)) 1) -
      (P : Module.End ℂ (LaurentPolynomial ℂ))
        ((Q : Module.End ℂ (LaurentPolynomial ℂ)) 1) = 1 at h
  rw [hP,hQ] at h
  simp at h

/-- Under the source hypotheses of the maximum-root cut, at least one
of the two sheared operators has a PBW point strictly below its
selected old-face derivative order. The theorem does not determine
which member; proving a *common* new direction needs further input. -/
theorem exactPair_maxRoot_cut_has_lower_order_point_on_one_member
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hP : 0 < vDeg ρ σ P.1) (hQ : 0 < vDeg ρ σ Q.1)
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hQP : Q * P - P * Q = 1)
    (hsum : ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1) :
    ∃ c : ℂ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ P.1).rootMultiplicity c =
        maxRootMult (cutPoly ρ σ P.1) ∧
      (cutPoly ρ σ Q.1).IsRoot c ∧
      ((∃ u : ℤ, ∃ n : ℕ,
          (u,n) ∈ ramifiedPBWSupport l hl
            (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) ∧
          n < (cutPoly ρ σ P.1).rootMultiplicity c) ∨
        (∃ u : ℤ, ∃ n : ℕ,
          (u,n) ∈ ramifiedPBWSupport l hl
            (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)) ∧
          n < (cutPoly ρ σ Q.1).rootMultiplicity c)) := by
  obtain ⟨c,hrootP,hmP,hrootQ,hratio,hpointP,hpointQ,hexact⟩ :=
    exactPair_maxRoot_cut_mate_oldFace_endpoints
      l hl P Q ρ σ hdir hρ hdiv hP hQ hdirP hdirQ hQP hsum
  have hpne := cutPoly_ne_zero_of_InDir P ρ σ hρ hdirP
  have hqne := cutPoly_ne_zero_of_InDir Q ρ σ hρ hdirQ
  have hmPpos : 0 < (cutPoly ρ σ P.1).rootMultiplicity c :=
    (Polynomial.rootMultiplicity_pos hpne).mpr hrootP
  have hmQpos : 0 < (cutPoly ρ σ Q.1).rootMultiplicity c :=
    (Polynomial.rootMultiplicity_pos hqne).mpr hrootQ
  have horder := ramified_exact_pair_has_order_zero_point l hl
    (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))
    (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)) hexact
  refine ⟨c,hrootP,hmP,hrootQ,?_⟩
  rcases horder with ⟨u,hu⟩ | ⟨u,hu⟩
  · left
    exact ⟨u,0,hu,hmPpos⟩
  · right
    exact ⟨u,0,hu,hmQpos⟩

end Dixmier.Weyl
