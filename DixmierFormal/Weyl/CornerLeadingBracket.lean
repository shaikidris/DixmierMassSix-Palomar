/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVPositiveWeight

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The first contradiction in G13 Proposition 5.6

At the forbidden normalized corner, a nonzero leading Poisson bracket
would force the weight of every positive-grade monomial above the weight
of the whole first operator. This is the first, bracket-zero stage of the
published corner proof; the later descending cut is separate.
-/

namespace Dixmier.Weyl

open MvPolynomial

private theorem corner_weight_arithmetic
    (ρ σ d n h wP wQ : ℤ)
    (hd : 1 < d) (hn : 1 < n) (hh : 2 ≤ h)
    (hPpos : 0 < wP)
    (hcorner : wP = d * (ρ * (h - 1) + σ * h))
    (hratio : wQ * d = wP * n)
    (hsum : wP + wQ = ρ + σ) :
    wP < ρ := by
  let W : ℤ := ρ * (h - 1) + σ * h
  have hWpos : 0 < W := by
    dsimp [W] at *
    nlinarith [hcorner]
  have hQ : wQ = n * W := by
    have hmul : (wQ - n * W) * d = 0 := by
      dsimp [W] at *
      nlinarith [hratio, hcorner]
    have hdne : d ≠ 0 := by omega
    nlinarith [hmul]
  have hTeq : ρ + σ = (d + n) * W := by
    dsimp [W] at *
    nlinarith [hsum, hcorner, hQ]
  have hρ : ρ = (h * (d + n) - 1) * W := by
    dsimp [W] at *
    nlinarith [hTeq]
  have hcoef : 0 < h * (d + n) - 1 - d := by
    nlinarith [mul_nonneg (show 0 ≤ h - 2 by omega)
      (show 0 ≤ d + n by omega)]
  have hdiff : ρ - wP = (h * (d + n) - 1 - d) * W := by
    dsimp [W] at *
    nlinarith [hρ, hcorner]
  nlinarith [mul_pos hcoef hWpos]

/-- A positive-weight point on the ray through a corner below the diagonal
is itself below the diagonal. This is the numerical sign transfer used for
the mate endpoint in the first stage of G13 Proposition 5.6. -/
theorem corner_proportional_mate_grade_negative
    (ρ σ a b c e : ℤ)
    (haPos : 0 < a)
    (hweight : 0 < ρ * c + σ * e)
    (hcornerWeight : 0 < ρ * a + σ * b)
    (hcornerGrade : a < b)
    (hcollinear : a * e = b * c) :
    c < e := by
  have hdiff : 0 < b - a := by omega
  have hcross : a * (e - c) = (b - a) * c := by nlinarith [hcollinear]
  have hweighted : a * (ρ * c + σ * e) = c * (ρ * a + σ * b) := by
    calc
      a * (ρ * c + σ * e) = ρ * a * c + σ * (a * e) := by ring
      _ = ρ * a * c + σ * (b * c) := by rw [hcollinear]
      _ = c * (ρ * a + σ * b) := by ring
  have hcPos : 0 < c := by
    nlinarith [mul_pos haPos hweight]
  nlinarith [hcross]

/-- At the normalized integer corner `(h-1,h)`, the leading Poisson
bracket of an exact counterexample pair must vanish. This is G13
Proposition 5.6, proof statement (1), before its descending-cut step. -/
theorem corner_leading_poisson_zero
    (P Q : A1 ℂ) (ρ σ : ℤ) (a b n d h : ℕ)
    (hpair : IsCounterexamplePair P Q)
    (hdir : IsDirection ρ σ)
    (hPpos : 0 < vDeg ρ σ P.1)
    (hend : expo a b ∈ (leadingForm ρ σ P.1).support)
    (hratio : vDeg ρ σ Q.1 * d = vDeg ρ σ P.1 * n)
    (hd : 1 < d) (hn : 1 < n) (hh : 2 ≤ h)
    (ha : (a : ℤ) = d * ((h : ℤ) - 1))
    (hb : (b : ℤ) = d * (h : ℤ)) :
    poisson (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1) = 0 := by
  by_contra hbr
  have hsum := (leadingForm_commutator P Q ρ σ hdir.2 hbr).1
  rw [hpair.1, vDeg_one_A1] at hsum
  have hsum' : vDeg ρ σ P.1 + vDeg ρ σ Q.1 = ρ + σ := by omega
  have hfaceWeight : Finsupp.weight (wt ρ σ) (expo a b) = vDeg ρ σ P.1 := by
    have h := hend
    simp only [leadingForm, MvPolynomial.support_weightedHomogeneousComponent,
      Finset.mem_filter] at h
    exact h.2
  have hcorner : vDeg ρ σ P.1 = (d : ℤ) *
      (ρ * ((h : ℤ) - 1) + σ * h) := by
    rw [expo_weight] at hfaceWeight
    rw [ha, hb] at hfaceWeight
    linear_combination -hfaceWeight
  have hρgt := corner_weight_arithmetic ρ σ d n h
    (vDeg ρ σ P.1) (vDeg ρ σ Q.1)
    (by exact_mod_cast hd) (by exact_mod_cast hn) (by exact_mod_cast hh)
    hPpos hcorner hratio hsum'
  obtain ⟨e, he, hgrade⟩ := (ggv_grades_opposite_proved P Q hpair).1
  have heBound : Finsupp.weight (wt ρ σ) e ≤ vDeg ρ σ P.1 := by
    have hle : (Finsupp.weight (wt ρ σ) e : WithBot ℤ) ≤
        MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol P.1) := by
      change (Finsupp.weight (wt ρ σ) e : WithBot ℤ) ≤
        (symbol P.1).support.sup (fun x =>
          (Finsupp.weight (wt ρ σ) x : WithBot ℤ))
      exact Finset.le_sup (f := fun x : Fin 2 →₀ ℕ =>
        (Finsupp.weight (wt ρ σ) x : WithBot ℤ)) he
    have hwd : MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol P.1) =
        (vDeg ρ σ P.1 : WithBot ℤ) := by
      cases h : MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol P.1) with
      | bot => simp [vDeg, h] at hPpos
      | coe m => simp [vDeg, h]
    rw [hwd] at hle
    exact WithBot.coe_le_coe.mp hle
  have hxy : 1 ≤ (e 0 : ℤ) - e 1 := by
    simp [grade] at hgrade
    omega
  have hρpos : 0 < ρ := lt_trans hPpos hρgt
  have hnonneg1 : 0 ≤ ρ * ((e 0 : ℤ) - e 1 - 1) :=
    mul_nonneg (le_of_lt hρpos) (by omega)
  have hnonneg2 : 0 ≤ (ρ + σ) * (e 1 : ℤ) :=
    mul_nonneg (le_of_lt hdir.2) (by exact_mod_cast Nat.zero_le (e 1))
  have hform : Finsupp.weight (wt ρ σ) e = ρ * e 0 + σ * e 1 := by
    simp [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two]
    ring
  nlinarith [heBound]

/-- The same bracket-zero stage with the rational normalized-corner
coordinates used literally by the frozen `GGVInputs.corner` contract. -/
theorem corner_leading_poisson_zero_of_normalized
    (P Q : A1 ℂ) (ρ σ : ℤ) (a b n d h : ℕ)
    (hpair : IsCounterexamplePair P Q)
    (hdir : IsDirection ρ σ)
    (hPpos : 0 < vDeg ρ σ P.1)
    (hend : expo a b ∈ (leadingForm ρ σ P.1).support)
    (hratio : vDeg ρ σ Q.1 * d = vDeg ρ σ P.1 * n)
    (hd : 1 < d) (hn : 1 < n) (hh : 2 ≤ h)
    (ha : (a : ℚ) / d = h - 1)
    (hb : (b : ℚ) / d = h) :
    poisson (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1) = 0 := by
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < d))
  have haQ : (a : ℚ) = (d : ℚ) * ((h : ℚ) - 1) := by
    apply (div_eq_iff hdQ).mp at ha
    nlinarith [ha]
  have hbQ : (b : ℚ) = (d : ℚ) * (h : ℚ) := by
    apply (div_eq_iff hdQ).mp at hb
    nlinarith [hb]
  have haZ : (a : ℤ) = (d : ℤ) * ((h : ℤ) - 1) := by exact_mod_cast haQ
  have hbZ : (b : ℤ) = (d : ℤ) * (h : ℤ) := by exact_mod_cast hbQ
  exact corner_leading_poisson_zero P Q ρ σ a b n d h hpair hdir
    hPpos hend hratio hd hn hh haZ hbZ

end Dixmier.Weyl
