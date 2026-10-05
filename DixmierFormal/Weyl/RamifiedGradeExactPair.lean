/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.FiniteSupportAdjacentDirection
public import DixmierFormal.Weyl.RamifiedShearPBWSum

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Grade support of an exact ramified Weyl pair

An operator supported strictly below grade zero lowers the upper
Laurent exponent of every input. Two such operators cannot have
commutator one. This supplies an exact-operator support condition for
the adjacent-direction argument.
-/

namespace Dixmier.Weyl

theorem LaurentUpper_derivative_pow (l : ℕ)
    (f : LaurentPolynomial ℂ) (B : ℤ)
    (hf : LaurentUpper f B) (j : ℕ) :
    LaurentUpper (((ramifiedDerivative l)^j) f)
      (B - (l : ℤ) * (j : ℤ)) := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
      rw [pow_succ']
      change LaurentUpper
        (ramifiedDerivative l (((ramifiedDerivative l)^j) f))
        (B - (l : ℤ) * ((j+1 : ℕ) : ℤ))
      convert LaurentUpper_derivative l _ _ ih using 1
      push_cast
      ring

theorem LaurentUpper_neg_local (f : LaurentPolynomial ℂ) (B : ℤ)
    (hf : LaurentUpper f B) : LaurentUpper (-f) B := by
  intro i hi
  have hnz : (-f).coeff i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hfi : f.coeff i ≠ 0 := by
    intro hz
    simp [hz] at hnz
  exact hf i (Finsupp.mem_support_iff.mpr hfi)

theorem LaurentUpper_sub_local (f g : LaurentPolynomial ℂ) (B : ℤ)
    (hf : LaurentUpper f B) (hg : LaurentUpper g B) :
    LaurentUpper (f-g) B := by
  rw [sub_eq_add_neg]
  exact LaurentUpper_add f (-g) B hf (LaurentUpper_neg_local g B hg)

theorem ramified_negative_grade_lowers_upper
    (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l)
    (hneg : ∀ p ∈ ramifiedPBWSupport l hl T,
      p.1 - (l : ℤ) * (p.2 : ℤ) < 0)
    (f : LaurentPolynomial ℂ) (B : ℤ)
    (hf : LaurentUpper f B) :
    LaurentUpper
      ((T : Module.End ℂ (LaurentPolynomial ℂ)) f) (B-1) := by
  rw [← ramifiedPBWCoeffs_eval l hl T,
    ramifiedNormalEval_apply, Finsupp.sum]
  apply LaurentUpper_finset_sum
  intro j hj
  have hcoeff : LaurentUpper ((ramifiedPBWCoeffs l hl T) j)
      ((l : ℤ) * (j : ℤ) - 1) := by
    intro i hi
    have hmem : (i,j) ∈ ramifiedPBWSupport l hl T :=
      (ramifiedPBWSupport_mem_iff l hl T i j).mpr
        (Finsupp.mem_support_iff.mp hi)
    have h := hneg (i,j) hmem
    dsimp at h
    omega
  have hder := LaurentUpper_derivative_pow l f B hf j
  have hmul := LaurentUpper_mul
    ((ramifiedPBWCoeffs l hl T) j)
    (((ramifiedDerivative l)^j) f)
    ((l : ℤ) * (j : ℤ) - 1)
    (B - (l : ℤ) * (j : ℤ)) hcoeff hder
  convert hmul using 1
  omega

theorem LaurentUpper_one_not_negative :
    ¬ LaurentUpper (1 : LaurentPolynomial ℂ) (-1) := by
  intro h
  have hmem : (0 : ℤ) ∈ (1 : LaurentPolynomial ℂ).coeff.support := by
    apply Finsupp.mem_support_iff.mpr
    simp [← LaurentPolynomial.T_zero, LaurentPolynomial.T_apply]
  have := h 0 hmem
  omega

/-- At least one member of an exact ramified Weyl pair has an occupied
PBW point of nonnegative grade. The mate's order and support are
unrestricted. -/
theorem ramified_exact_pair_has_nonnegative_grade_point
    (l : ℕ) (hl : 0 < l)
    (P Q : ramifiedOperatorAlgebra l)
    (hQP : Q * P - P * Q = 1) :
    (∃ p ∈ ramifiedPBWSupport l hl P,
      0 ≤ p.1 - (l : ℤ) * (p.2 : ℤ)) ∨
    (∃ p ∈ ramifiedPBWSupport l hl Q,
      0 ≤ p.1 - (l : ℤ) * (p.2 : ℤ)) := by
  by_contra hnone
  push Not at hnone
  have hPneg : ∀ p ∈ ramifiedPBWSupport l hl P,
      p.1 - (l : ℤ) * (p.2 : ℤ) < 0 := by
    intro p hp
    exact hnone.1 p hp
  have hQneg : ∀ p ∈ ramifiedPBWSupport l hl Q,
      p.1 - (l : ℤ) * (p.2 : ℤ) < 0 := by
    intro p hp
    exact hnone.2 p hp
  have hone : LaurentUpper (1 : LaurentPolynomial ℂ) 0 := LaurentUpper_one
  have hPone := ramified_negative_grade_lowers_upper
    l hl P hPneg 1 0 hone
  have hQone := ramified_negative_grade_lowers_upper
    l hl Q hQneg 1 0 hone
  have hQPone := ramified_negative_grade_lowers_upper
    l hl Q hQneg _ (-1) hPone
  have hPQone := ramified_negative_grade_lowers_upper
    l hl P hPneg _ (-1) hQone
  have h := congrArg
    (fun U : ramifiedOperatorAlgebra l =>
      (U : Module.End ℂ (LaurentPolynomial ℂ))
        (1 : LaurentPolynomial ℂ)) hQP
  change (Q : Module.End ℂ (LaurentPolynomial ℂ))
      ((P : Module.End ℂ (LaurentPolynomial ℂ)) 1) -
      (P : Module.End ℂ (LaurentPolynomial ℂ))
        ((Q : Module.End ℂ (LaurentPolynomial ℂ)) 1) = 1 at h
  have hupper : LaurentUpper (1 : LaurentPolynomial ℂ) (-2) := by
    rw [← h]
    exact LaurentUpper_sub_local _ _ _ hQPone hPQone
  exact LaurentUpper_one_not_negative
    (LaurentUpper_mono _ (-2) (-1) (by omega) hupper)

/-- Relative to a negative-grade old endpoint of maximum old weight,
any nonnegative-grade support point has smaller derivative order. -/
theorem ramified_nonnegative_grade_below_old_order
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (E B : ℤ × ℕ)
    (hweight : ramifiedWeight l ρ σ B ≤
      ramifiedWeight l ρ σ E)
    (hEgrade : E.1 - (l : ℤ) * (E.2 : ℤ) < 0)
    (hBgrade : 0 ≤ B.1 - (l : ℤ) * (B.2 : ℤ)) :
    B.2 < E.2 := by
  by_contra hbad
  have horder : E.2 ≤ B.2 := Nat.le_of_not_gt hbad
  have hρz : (0 : ℤ) < ρ := hρ
  have hlz : (0 : ℤ) < l := by exact_mod_cast hl
  have hsumz : (0 : ℤ) < ρ + σ := hsum
  have hgap : 0 <
      (B.1 - (l : ℤ) * (B.2 : ℤ)) -
      (E.1 - (l : ℤ) * (E.2 : ℤ)) := by omega
  have hprod : 0 < ρ *
      ((B.1 - (l : ℤ) * (B.2 : ℤ)) -
       (E.1 - (l : ℤ) * (E.2 : ℤ))) := mul_pos hρz hgap
  have horderZ : (0 : ℤ) ≤ (B.2 : ℤ) - (E.2 : ℤ) := by
    have hcast : (E.2 : ℤ) ≤ (B.2 : ℤ) := by exact_mod_cast horder
    omega
  have hprod2 : 0 ≤ ((l : ℤ) * (ρ + σ)) *
      ((B.2 : ℤ) - (E.2 : ℤ)) :=
    mul_nonneg (le_of_lt (mul_pos hlz hsumz)) horderZ
  dsimp [ramifiedWeight] at hweight
  nlinarith [hprod,hprod2]

/-- A nonnegative-grade support point gives an actual first adjacent
face before the grade direction when the old endpoint is negative. -/
theorem ramifiedSupport_exists_early_adjacent_slope
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (S : Finset (ℤ × ℕ)) (V : ℤ) (E B : ℤ × ℕ)
    (hEweight : ramifiedWeight l ρ σ E = V)
    (hEgrade : E.1 - (l : ℤ) * (E.2 : ℤ) < 0)
    (hBgrade : 0 ≤ B.1 - (l : ℤ) * (B.2 : ℤ))
    (hB : B ∈ S)
    (htop : ∀ p ∈ S, ramifiedWeight l ρ σ p ≤ V)
    (hstart : ∀ p ∈ S,
      ramifiedWeight l ρ σ p = V → E.2 ≤ p.2) :
    ∃ t : ℚ, 0 < t ∧ t < (l : ℚ) * ((ρ + σ : ℤ) : ℚ) ∧
      (∀ p ∈ S,
        (ramifiedWeight l ρ σ p : ℚ) - t * (p.2 : ℚ) ≤
          (V : ℚ) - t * (E.2 : ℚ)) ∧
      (∃ C ∈ S, C.2 < E.2 ∧
        (ramifiedWeight l ρ σ C : ℚ) - t * (C.2 : ℚ) =
          (V : ℚ) - t * (E.2 : ℚ)) := by
  have hbelow : B.2 < E.2 :=
    ramified_nonnegative_grade_below_old_order l hl ρ σ hρ hsum
      E B (by rw [hEweight]; exact htop B hB) hEgrade hBgrade
  obtain ⟨t,ht,hall,hC⟩ :=
    finiteSupport_exists_adjacent_rational_slope
      S (ramifiedWeight l ρ σ) V E.2 htop hstart
        ⟨B,hB,hbelow⟩
  have hearly := ramifiedSupport_first_slope_before_grade_direction
    l hl ρ σ hρ hsum S V E B t hEweight hEgrade hBgrade
      htop hall hB
  exact ⟨t,ht,hearly,hall,hC⟩

/-- Under the selected negative-grade old-endpoint data for both
members, an exact ramified pair has a positive-sum adjacent face on
at least one member. The theorem does not yet make it a common face. -/
theorem ramified_exact_pair_exists_early_adjacent_slope
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hQP : Q * P - P * Q = 1)
    (VP VQ : ℤ) (EP EQ : ℤ × ℕ)
    (hEPweight : ramifiedWeight l ρ σ EP = VP)
    (hEQweight : ramifiedWeight l ρ σ EQ = VQ)
    (hEPgrade : EP.1 - (l : ℤ) * (EP.2 : ℤ) < 0)
    (hEQgrade : EQ.1 - (l : ℤ) * (EQ.2 : ℤ) < 0)
    (hPtop : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p ≤ VP)
    (hQtop : ∀ p ∈ ramifiedPBWSupport l hl Q,
      ramifiedWeight l ρ σ p ≤ VQ)
    (hPstart : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p = VP → EP.2 ≤ p.2)
    (hQstart : ∀ p ∈ ramifiedPBWSupport l hl Q,
      ramifiedWeight l ρ σ p = VQ → EQ.2 ≤ p.2) :
    (∃ t : ℚ, 0 < t ∧ t < (l : ℚ) * ((ρ + σ : ℤ) : ℚ) ∧
      (∀ p ∈ ramifiedPBWSupport l hl P,
        (ramifiedWeight l ρ σ p : ℚ) - t * (p.2 : ℚ) ≤
          (VP : ℚ) - t * (EP.2 : ℚ)) ∧
      (∃ C ∈ ramifiedPBWSupport l hl P, C.2 < EP.2 ∧
        (ramifiedWeight l ρ σ C : ℚ) - t * (C.2 : ℚ) =
          (VP : ℚ) - t * (EP.2 : ℚ))) ∨
    (∃ t : ℚ, 0 < t ∧ t < (l : ℚ) * ((ρ + σ : ℤ) : ℚ) ∧
      (∀ p ∈ ramifiedPBWSupport l hl Q,
        (ramifiedWeight l ρ σ p : ℚ) - t * (p.2 : ℚ) ≤
          (VQ : ℚ) - t * (EQ.2 : ℚ)) ∧
      (∃ C ∈ ramifiedPBWSupport l hl Q, C.2 < EQ.2 ∧
        (ramifiedWeight l ρ σ C : ℚ) - t * (C.2 : ℚ) =
          (VQ : ℚ) - t * (EQ.2 : ℚ))) := by
  rcases ramified_exact_pair_has_nonnegative_grade_point l hl P Q hQP with
    ⟨B,hB,hBg⟩ | ⟨B,hB,hBg⟩
  · left
    exact ramifiedSupport_exists_early_adjacent_slope
      l hl ρ σ hρ hsum (ramifiedPBWSupport l hl P) VP EP B
        hEPweight hEPgrade hBg hB hPtop hPstart
  · right
    exact ramifiedSupport_exists_early_adjacent_slope
      l hl ρ σ hρ hsum (ramifiedPBWSupport l hl Q) VQ EQ B
        hEQweight hEQgrade hBg hB hQtop hQstart

/-- The source polynomial pair inherits the exact-pair early-face
conclusion after a shared ramified shear. The two selected old endpoints
must have negative grade; deriving that negativity from G13's
homogeneous companion geometry is a separate obligation. -/
theorem polynomial_cut_exact_pair_exists_early_adjacent_slope
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ)
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hQP : Q * P - P * Q = 1) (c : ℂ)
    (hPgrade : (((l : ℤ) / ρ) * vDeg ρ σ P.1 -
        ramifiedCutExponent l ρ σ *
          ((cutPoly ρ σ P.1).rootMultiplicity c : ℤ)) -
        (l : ℤ) * ((cutPoly ρ σ P.1).rootMultiplicity c : ℤ) < 0)
    (hQgrade : (((l : ℤ) / ρ) * vDeg ρ σ Q.1 -
        ramifiedCutExponent l ρ σ *
          ((cutPoly ρ σ Q.1).rootMultiplicity c : ℤ)) -
        (l : ℤ) * ((cutPoly ρ σ Q.1).rootMultiplicity c : ℤ) < 0) :
    let U := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)
    let V := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)
    let wP := ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1)
    let wQ := ρ * (((l : ℤ) / ρ) * vDeg ρ σ Q.1)
    let mP := (cutPoly ρ σ P.1).rootMultiplicity c
    let mQ := (cutPoly ρ σ Q.1).rootMultiplicity c
    (∃ t : ℚ, 0 < t ∧ t < (l : ℚ) * ((ρ + σ : ℤ) : ℚ) ∧
      (∀ p ∈ ramifiedPBWSupport l hl U,
        (ramifiedWeight l ρ σ p : ℚ) - t * (p.2 : ℚ) ≤
          (wP : ℚ) - t * (mP : ℚ)) ∧
      (∃ C ∈ ramifiedPBWSupport l hl U, C.2 < mP ∧
        (ramifiedWeight l ρ σ C : ℚ) - t * (C.2 : ℚ) =
          (wP : ℚ) - t * (mP : ℚ))) ∨
    (∃ t : ℚ, 0 < t ∧ t < (l : ℚ) * ((ρ + σ : ℤ) : ℚ) ∧
      (∀ p ∈ ramifiedPBWSupport l hl V,
        (ramifiedWeight l ρ σ p : ℚ) - t * (p.2 : ℚ) ≤
          (wQ : ℚ) - t * (mQ : ℚ)) ∧
      (∃ C ∈ ramifiedPBWSupport l hl V, C.2 < mQ ∧
        (ramifiedWeight l ρ σ C : ℚ) - t * (C.2 : ℚ) =
          (wQ : ℚ) - t * (mQ : ℚ))) := by
  obtain ⟨dP₁,dP₂,hdP₁,_,_⟩ := Finset.one_lt_card_iff.mp hdirP
  obtain ⟨⟨iP,jP⟩,rfl⟩ := expo_surjective dP₁
  obtain ⟨dQ₁,dQ₂,hdQ₁,_,_⟩ := Finset.one_lt_card_iff.mp hdirQ
  obtain ⟨⟨iQ,jQ⟩,rfl⟩ := expo_surjective dQ₁
  have hsP := polynomialRamifiedCut_root_start_on_old_face
    l hl P ρ σ hρ hdiv hpos iP jP hdP₁ c
  have hsQ := polynomialRamifiedCut_root_start_on_old_face
    l hl Q ρ σ hρ hdiv hpos iQ jQ hdQ₁ c
  have hsourceP : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl (polynomialRamifiedLift l P) →
      ramifiedWeight l ρ σ (u,n) ≤
        ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1) := by
    intro u n hu
    exact polynomialRamifiedLift_weight_le_scaled_vDeg
      l hl P ρ σ hdiv u n hu
  have hsourceQ : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl (polynomialRamifiedLift l Q) →
      ramifiedWeight l ρ σ (u,n) ≤
        ρ * (((l : ℤ) / ρ) * vDeg ρ σ Q.1) := by
    intro u n hu
    exact polynomialRamifiedLift_weight_le_scaled_vDeg
      l hl Q ρ σ hdiv u n hu
  have htopP := ramifiedCutAut_weight_upper l hl ρ σ
    (((l : ℤ) / ρ) * vDeg ρ σ P.1)
    hρ hdiv hpos c (polynomialRamifiedLift l P) hsourceP
  have htopQ := ramifiedCutAut_weight_upper l hl ρ σ
    (((l : ℤ) / ρ) * vDeg ρ σ Q.1)
    hρ hdiv hpos c (polynomialRamifiedLift l Q) hsourceQ
  have hexact :
      ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q) *
          ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P) -
        ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P) *
          ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q) = 1 := by
    exact ramifiedCutAut_exact_pair l hl ρ σ c _ _
      (polynomialRamifiedLift_bracket_one l hl P Q hQP)
  exact ramified_exact_pair_exists_early_adjacent_slope
    l hl ρ σ hρ hpos
    (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))
    (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q))
    hexact
    (ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1))
    (ρ * (((l : ℤ) / ρ) * vDeg ρ σ Q.1))
    ((((l : ℤ) / ρ) * vDeg ρ σ P.1 -
      ramifiedCutExponent l ρ σ *
        ((cutPoly ρ σ P.1).rootMultiplicity c : ℤ)),
      (cutPoly ρ σ P.1).rootMultiplicity c)
    ((((l : ℤ) / ρ) * vDeg ρ σ Q.1 -
      ramifiedCutExponent l ρ σ *
        ((cutPoly ρ σ Q.1).rootMultiplicity c : ℤ)),
      (cutPoly ρ σ Q.1).rootMultiplicity c)
    hsP.1.2 hsQ.1.2 hPgrade hQgrade
    (by intro p hp; exact htopP p.1 p.2 hp)
    (by intro p hp; exact htopQ p.1 p.2 hp)
    (by intro p hp hw; exact hsP.2 p.1 p.2 hp hw)
    (by intro p hp hw; exact hsQ.2 p.1 p.2 hp hw)

/-- The parallel ending exponents of the original face and its
homogeneous companion imply the integer identity used in G13 (5.17).
The first endpoint has old top weight `ρ*r`, while the companion
endpoint has weight `l*(ρ+σ)`. No root count is used here. -/
theorem ramified_companion_endpoint_parallel_degree_identity
    (l : ℕ) (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (r u uF : ℤ) (N M : ℕ)
    (hPweight : ρ*u + (l : ℤ)*σ*(N : ℤ) = ρ*r)
    (hFweight : ρ*uF + (l : ℤ)*σ*(M : ℤ) =
      (l : ℤ)*(ρ+σ))
    (hparallel : u*(M : ℤ) = uF*(N : ℤ)) :
    r*(M : ℤ) =
      ((l : ℤ) + ramifiedCutExponent l ρ σ)*(N : ℤ) := by
  have hcut := ramifiedCutExponent_weight l ρ σ hdiv
  have hPM := congrArg (fun z : ℤ => z*(M : ℤ)) hPweight
  have hFN := congrArg (fun z : ℤ => z*(N : ℤ)) hFweight
  have hkey : ρ*(r*(M : ℤ)) =
      (l : ℤ)*(ρ+σ)*(N : ℤ) := by
    nlinarith [hPM, hFN, hparallel]
  have hfactor : ρ*((l : ℤ) + ramifiedCutExponent l ρ σ) =
      (l : ℤ)*(ρ+σ) := by nlinarith [hcut]
  have heq : ρ*(r*(M : ℤ)) =
      ρ*(((l : ℤ) + ramifiedCutExponent l ρ σ)*(N : ℤ)) := by
    calc
      _ = (l : ℤ)*(ρ+σ)*(N : ℤ) := hkey
      _ = ρ*(((l : ℤ) + ramifiedCutExponent l ρ σ)*(N : ℤ)) := by
        rw [← hfactor]
        ring
  exact mul_left_cancel₀ (ne_of_gt hρ) heq

/-- Arithmetic core of G13 Proposition 5.3's selected-start grade
argument. A companion endpoint proportional to the old endpoint gives
`r*M=(l+k)*N`; a maximum root of multiplicity `m` with `N≤M*m`
then puts the cut endpoint at nonpositive grade. Strict negativity
requires the separate source assertion that its grade is nonzero. -/
theorem ramified_cut_endpoint_grade_nonpositive_of_companion
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ)
    (r : ℤ) (N M m : ℕ)
    (hM : 0 < M)
    (hcomp : r * (M : ℤ) =
      ((l : ℤ) + ramifiedCutExponent l ρ σ) * (N : ℤ))
    (hroot : N ≤ M * m) :
    r - (ramifiedCutExponent l ρ σ + (l : ℤ)) * (m : ℤ) ≤ 0 := by
  have hkl : (0 : ℤ) < (l : ℤ) + ramifiedCutExponent l ρ σ := by
    have h := ramifiedCutExponent_gt_neg_index l hl ρ σ hρ hdiv hpos
    omega
  have hrootZ : (N : ℤ) ≤ (M : ℤ) * (m : ℤ) := by
    exact_mod_cast hroot
  have hprod := mul_le_mul_of_nonneg_left hrootZ (le_of_lt hkl)
  have hMz : (0 : ℤ) < M := by exact_mod_cast hM
  by_contra hbad
  have hgt : (0 : ℤ) <
      r - (ramifiedCutExponent l ρ σ + (l : ℤ)) * (m : ℤ) := by omega
  have hcontr := mul_pos hMz hgt
  nlinarith [hprod,hcontr,hcomp]

/-- Combining the companion's parallel endpoint with a distinct-root
budget puts the selected maximum-root cut endpoint on or below the
grade diagonal. The strict step remains the separate non-diagonal
assertion of G13 Theorem 4.1(3). -/
theorem ramified_cut_endpoint_grade_nonpositive_of_parallel_companion
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ)
    (r u uF : ℤ) (N M m : ℕ) (hM : 0 < M)
    (hPweight : ρ*u + (l : ℤ)*σ*(N : ℤ) = ρ*r)
    (hFweight : ρ*uF + (l : ℤ)*σ*(M : ℤ) =
      (l : ℤ)*(ρ+σ))
    (hparallel : u*(M : ℤ) = uF*(N : ℤ))
    (hroot : N ≤ M*m) :
    r - (ramifiedCutExponent l ρ σ + (l : ℤ)) * (m : ℤ) ≤ 0 := by
  have hcomp := ramified_companion_endpoint_parallel_degree_identity
    l ρ σ hρ hdiv r u uF N M hPweight hFweight hparallel
  exact ramified_cut_endpoint_grade_nonpositive_of_companion
    l hl ρ σ hρ hdiv hpos r N M m hM hcomp hroot

/-- The nonzero-grade clause of the G13 companion theorem upgrades
the preceding nonpositive bound to the negative grade required by the
polynomial cut adapter. -/
theorem ramified_cut_endpoint_grade_negative_of_companion
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ)
    (r : ℤ) (N M m : ℕ)
    (hM : 0 < M)
    (hcomp : r * (M : ℤ) =
      ((l : ℤ) + ramifiedCutExponent l ρ σ) * (N : ℤ))
    (hroot : N ≤ M * m)
    (hgrade : r - (ramifiedCutExponent l ρ σ +
      (l : ℤ)) * (m : ℤ) ≠ 0) :
    r - (ramifiedCutExponent l ρ σ + (l : ℤ)) * (m : ℤ) < 0 := by
  have hle := ramified_cut_endpoint_grade_nonpositive_of_companion
    l hl ρ σ hρ hdiv hpos r N M m hM hcomp hroot
  omega

/-- In an algebraically closed coefficient field, the degree is at
most the number of distinct roots times the largest multiplicity.
This is the root-budget step behind G13 (5.9). -/
theorem complex_polynomial_degree_le_distinct_roots_mul_maxRootMult
    (f : Polynomial ℂ) :
    f.natDegree ≤ f.roots.toFinset.card * maxRootMult f := by
  classical
  have hdegree : f.natDegree = f.roots.card :=
    (IsAlgClosed.splits f).natDegree_eq_card_roots
  have hsum : f.roots.card =
      ∑ a ∈ f.roots.toFinset, Polynomial.rootMultiplicity a f := by
    rw [← Multiset.toFinset_sum_count_eq f.roots]
    simp only [Polynomial.count_roots]
  have hbound : ∀ a ∈ f.roots.toFinset,
      Polynomial.rootMultiplicity a f ≤ maxRootMult f := by
    intro a ha
    unfold maxRootMult
    exact Finset.le_sup (f := fun b => Polynomial.rootMultiplicity b f) ha
  calc
    f.natDegree = ∑ a ∈ f.roots.toFinset,
        Polynomial.rootMultiplicity a f := hdegree.trans hsum
    _ ≤ ∑ _a ∈ f.roots.toFinset, maxRootMult f :=
      Finset.sum_le_sum hbound
    _ = f.roots.toFinset.card * maxRootMult f := by simp

/-- A bound on the number of companion-controlled root positions
turns the maximum root multiplicity into the exact inequality needed
for the selected cut endpoint. -/
theorem complex_polynomial_companion_root_budget
    (f : Polynomial ℂ) (M : ℕ)
    (hcount : f.roots.toFinset.card ≤ M) :
    f.natDegree ≤ M * maxRootMult f := by
  have hdegree := complex_polynomial_degree_le_distinct_roots_mul_maxRootMult f
  exact hdegree.trans (Nat.mul_le_mul_right _ hcount)

/-- The companion root-count and endpoint-proportionality data
produce the selected maximum-root negative grade once the source's
nonzero-grade assertion is available. -/
theorem polynomial_cut_maxRoot_endpoint_grade_negative_of_companion
    (l : ℕ) (hl : 0 < l) (P : A1 ℂ)
    (ρ σ : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (M : ℕ) (hM : 0 < M)
    (hcount : (cutPoly ρ σ P.1).roots.toFinset.card ≤ M)
    (hcomp : (((l : ℤ) / ρ) * vDeg ρ σ P.1) * (M : ℤ) =
      ((l : ℤ) + ramifiedCutExponent l ρ σ) *
        ((cutPoly ρ σ P.1).natDegree : ℤ))
    (hnonzero : (((l : ℤ) / ρ) * vDeg ρ σ P.1) -
      (ramifiedCutExponent l ρ σ + (l : ℤ)) *
        (maxRootMult (cutPoly ρ σ P.1) : ℤ) ≠ 0) :
    (((l : ℤ) / ρ) * vDeg ρ σ P.1) -
      (ramifiedCutExponent l ρ σ + (l : ℤ)) *
        (maxRootMult (cutPoly ρ σ P.1) : ℤ) < 0 := by
  have hroot := complex_polynomial_companion_root_budget
    (cutPoly ρ σ P.1) M hcount
  exact ramified_cut_endpoint_grade_negative_of_companion
    l hl ρ σ hρ hdiv hpos
    (((l : ℤ) / ρ) * vDeg ρ σ P.1)
    (cutPoly ρ σ P.1).natDegree M
    (maxRootMult (cutPoly ρ σ P.1))
    hM hcomp hroot hnonzero

/-- Proportional old-face endpoints transfer strict negativity from
the selected P endpoint to its exact mate. -/
theorem proportional_cut_endpoints_grade_negative
    (l : ℕ) (wP wQ uP uQ : ℤ) (M N : ℕ)
    (hP : 0 < wP) (hQ : 0 < wQ)
    (hu : wQ * uP = wP * uQ)
    (horder : wQ * (M : ℤ) = wP * (N : ℤ))
    (hgrade : uP - (l : ℤ) * (M : ℤ) < 0) :
    uQ - (l : ℤ) * (N : ℤ) < 0 := by
  have hscaled : wQ * (uP - (l : ℤ) * (M : ℤ)) =
      wP * (uQ - (l : ℤ) * (N : ℤ)) := by
    rw [mul_sub, mul_sub, hu]
    nlinarith [horder]
  have hneg : wQ * (uP - (l : ℤ) * (M : ℤ)) < 0 :=
    mul_neg_of_pos_of_neg hQ hgrade
  by_contra hbad
  have hnonneg : 0 ≤ uQ - (l : ℤ) * (N : ℤ) := le_of_not_gt hbad
  have hright := mul_nonneg (le_of_lt hP) hnonneg
  omega

/-- For the selected maximum root of a polynomial exact pair,
negative grade of P's cut endpoint forces negative grade of its
mate's endpoint. No separate companion for Q is required. -/
theorem exactPair_maxRoot_cut_both_endpoint_grades_negative
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hP : 0 < vDeg ρ σ P.1) (hQ : 0 < vDeg ρ σ Q.1)
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hQP : Q * P - P * Q = 1)
    (hsum : ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1)
    (hPgrade : (((l : ℤ) / ρ) * vDeg ρ σ P.1) -
      (ramifiedCutExponent l ρ σ + (l : ℤ)) *
        (maxRootMult (cutPoly ρ σ P.1) : ℤ) < 0) :
    ∃ c : ℂ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ P.1).rootMultiplicity c =
        maxRootMult (cutPoly ρ σ P.1) ∧
      (cutPoly ρ σ Q.1).IsRoot c ∧
      ((((l : ℤ) / ρ) * vDeg ρ σ Q.1) -
        (ramifiedCutExponent l ρ σ + (l : ℤ)) *
          ((cutPoly ρ σ Q.1).rootMultiplicity c : ℤ) < 0) := by
  obtain ⟨c,hrootP,hmP,hrootQ,hratio,_,_,_⟩ :=
    exactPair_maxRoot_cut_mate_oldFace_endpoints
      l hl P Q ρ σ hdir hρ hdiv hP hQ
        hdirP hdirQ hQP hsum
  obtain ⟨hu,horder⟩ := cut_oldFace_endpoints_proportional
    l ρ σ (vDeg ρ σ P.1) (vDeg ρ σ Q.1)
      (maxRootMult (cutPoly ρ σ P.1))
      ((cutPoly ρ σ Q.1).rootMultiplicity c)
      hP hQ hratio
  have hPgrade' :
      (((l : ℤ) / ρ) * vDeg ρ σ P.1 -
        ramifiedCutExponent l ρ σ *
          (maxRootMult (cutPoly ρ σ P.1) : ℤ)) -
        (l : ℤ) * (maxRootMult (cutPoly ρ σ P.1) : ℤ) < 0 := by
    nlinarith [hPgrade]
  have hQgrade := proportional_cut_endpoints_grade_negative
    l (vDeg ρ σ P.1) (vDeg ρ σ Q.1)
    (((l : ℤ) / ρ) * vDeg ρ σ P.1 -
      ramifiedCutExponent l ρ σ *
        (maxRootMult (cutPoly ρ σ P.1) : ℤ))
    (((l : ℤ) / ρ) * vDeg ρ σ Q.1 -
      ramifiedCutExponent l ρ σ *
        ((cutPoly ρ σ Q.1).rootMultiplicity c : ℤ))
    (maxRootMult (cutPoly ρ σ P.1))
    ((cutPoly ρ σ Q.1).rootMultiplicity c)
    hP hQ hu horder hPgrade'
  refine ⟨c,hrootP,hmP,hrootQ,?_⟩
  nlinarith [hQgrade]

/-- The maximum-root polynomial cut has a first adjacent face before
the grade direction, assuming only P's selected endpoint is negative.
Mate negativity follows from the exact-pair root-order ratio. -/
theorem exactPair_maxRoot_cut_exists_early_adjacent_slope_of_P_grade
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hP : 0 < vDeg ρ σ P.1) (hQ : 0 < vDeg ρ σ Q.1)
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hQP : Q * P - P * Q = 1)
    (hsum : ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1)
    (hPgrade : (((l : ℤ) / ρ) * vDeg ρ σ P.1) -
      (ramifiedCutExponent l ρ σ + (l : ℤ)) *
        (maxRootMult (cutPoly ρ σ P.1) : ℤ) < 0) :
    ∃ c : ℂ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      (cutPoly ρ σ P.1).rootMultiplicity c =
        maxRootMult (cutPoly ρ σ P.1) ∧
      (cutPoly ρ σ Q.1).IsRoot c ∧
      (let U := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)
       let V := ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)
       let wP := ρ * (((l : ℤ) / ρ) * vDeg ρ σ P.1)
       let wQ := ρ * (((l : ℤ) / ρ) * vDeg ρ σ Q.1)
       let mP := (cutPoly ρ σ P.1).rootMultiplicity c
       let mQ := (cutPoly ρ σ Q.1).rootMultiplicity c
       (∃ t : ℚ, 0 < t ∧ t < (l : ℚ) * ((ρ + σ : ℤ) : ℚ) ∧
         (∀ p ∈ ramifiedPBWSupport l hl U,
           (ramifiedWeight l ρ σ p : ℚ) - t * (p.2 : ℚ) ≤
             (wP : ℚ) - t * (mP : ℚ)) ∧
         (∃ C ∈ ramifiedPBWSupport l hl U, C.2 < mP ∧
           (ramifiedWeight l ρ σ C : ℚ) - t * (C.2 : ℚ) =
             (wP : ℚ) - t * (mP : ℚ))) ∨
       (∃ t : ℚ, 0 < t ∧ t < (l : ℚ) * ((ρ + σ : ℤ) : ℚ) ∧
         (∀ p ∈ ramifiedPBWSupport l hl V,
           (ramifiedWeight l ρ σ p : ℚ) - t * (p.2 : ℚ) ≤
             (wQ : ℚ) - t * (mQ : ℚ)) ∧
         (∃ C ∈ ramifiedPBWSupport l hl V, C.2 < mQ ∧
           (ramifiedWeight l ρ σ C : ℚ) - t * (C.2 : ℚ) =
             (wQ : ℚ) - t * (mQ : ℚ)))) := by
  obtain ⟨c,hrootP,hmP,hrootQ,hQgrade⟩ :=
    exactPair_maxRoot_cut_both_endpoint_grades_negative
      l hl P Q ρ σ hdir hρ hdiv hP hQ
        hdirP hdirQ hQP hsum hPgrade
  have hPgradeC : (((l : ℤ) / ρ) * vDeg ρ σ P.1 -
      ramifiedCutExponent l ρ σ *
        ((cutPoly ρ σ P.1).rootMultiplicity c : ℤ)) -
      (l : ℤ) * ((cutPoly ρ σ P.1).rootMultiplicity c : ℤ) < 0 := by
    rw [hmP]
    nlinarith [hPgrade]
  have hQgradeC : (((l : ℤ) / ρ) * vDeg ρ σ Q.1 -
      ramifiedCutExponent l ρ σ *
        ((cutPoly ρ σ Q.1).rootMultiplicity c : ℤ)) -
      (l : ℤ) * ((cutPoly ρ σ Q.1).rootMultiplicity c : ℤ) < 0 := by
    nlinarith [hQgrade]
  exact ⟨c,hrootP,hmP,hrootQ,
    polynomial_cut_exact_pair_exists_early_adjacent_slope
      l hl P Q ρ σ hρ hdiv hdir.2 hdirP hdirQ hQP c
        hPgradeC hQgradeC⟩

end Dixmier.Weyl
