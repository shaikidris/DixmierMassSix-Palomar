/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedExactWeightLower

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Weight barrier at a normalized ramified corner

If a first contraction could produce the scalar commutator at a
normalized corner, both top weights lie below every non-origin
support point of nonnegative grade. This is the weight calculation
in G13 Proposition 5.6, separated from the grade-support theorem.
-/

namespace Dixmier.Weyl

theorem ramified_corner_top_weights_below_steps
    (l : ℕ) (ρ σ d n h wP wQ : ℤ)
    (_hl : 0 < l) (_hsum : 0 < ρ+σ)
    (hd : 1 < d) (hn : 1 < n) (hh : 2 ≤ h)
    (hPpos : 0 < wP)
    (hcorner : wP = d*(ρ*((l : ℤ)*h-1)+(l : ℤ)*σ*h))
    (hratio : wQ*d = wP*n)
    (hstep : wP+wQ = (l : ℤ)*(ρ+σ)) :
    wP < ρ ∧ wQ < ρ ∧
      wP < (l : ℤ)*(ρ+σ) ∧ wQ < (l : ℤ)*(ρ+σ) := by
  let W : ℤ := ρ*((l : ℤ)*h-1)+(l : ℤ)*σ*h
  have hWpos : 0 < W := by
    dsimp [W] at *
    nlinarith [hcorner]
  have hQ : wQ = n*W := by
    have hmul : (wQ-n*W)*d=0 := by
      dsimp [W] at *
      nlinarith [hcorner,hratio]
    nlinarith [hmul]
  have hsumW : (l : ℤ)*(ρ+σ) = (d+n)*W := by
    dsimp [W] at *
    nlinarith [hcorner,hQ,hstep]
  have hρW : ρ = (h*(d+n)-1)*W := by
    have hWform : W = (l : ℤ)*h*(ρ+σ)-ρ := by
      dsimp [W]
      ring
    nlinarith [hWform, congrArg (fun z : ℤ => h*z) hsumW]
  have hdlt : 0 < h*(d+n)-1-d := by nlinarith
  have hnlt : 0 < h*(d+n)-1-n := by nlinarith
  have hPρ : wP < ρ := by
    have : ρ-wP = (h*(d+n)-1-d)*W := by
      dsimp [W] at *
      nlinarith [hρW,hcorner]
    nlinarith [mul_pos hdlt hWpos]
  have hQρ : wQ < ρ := by
    have : ρ-wQ = (h*(d+n)-1-n)*W := by
      nlinarith [hρW,hQ]
    nlinarith [mul_pos hnlt hWpos]
  have hPl : wP < (l : ℤ)*(ρ+σ) := by
    nlinarith [hstep,hQ, mul_pos (by omega : 0 < n) hWpos]
  have hQl : wQ < (l : ℤ)*(ρ+σ) := by omega
  exact ⟨hPρ,hQρ,hPl,hQl⟩

/-- A non-origin PBW point of nonnegative grade has at least one
positive weight step. -/
theorem ramified_nonnegative_nonorigin_weight_lower
    (l : ℕ) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (p : ℤ × ℕ)
    (hgrade : 0 ≤ p.1-(l : ℤ)*(p.2 : ℤ))
    (hnonorigin : p ≠ (0,0)) :
    ρ ≤ ramifiedWeight l ρ σ p ∨
      (l : ℤ)*(ρ+σ) ≤ ramifiedWeight l ρ σ p := by
  by_cases hj : p.2 = 0
  · left
    have hgrade0 : 0 ≤ p.1 := by simpa [hj] using hgrade
    have hi : 0 < p.1 := by
      have hne : p.1 ≠ 0 := by
        intro hz
        exact hnonorigin (Prod.ext hz hj)
      omega
    simp only [ramifiedWeight, hj, Nat.cast_zero, mul_zero, add_zero]
    nlinarith [mul_nonneg (le_of_lt hρ) (show 0 ≤ p.1-1 by omega)]
  · right
    have hjpos : (0 : ℤ) < p.2 := by exact_mod_cast (Nat.pos_of_ne_zero hj)
    have hnonneg := mul_nonneg (le_of_lt hρ) hgrade
    have hstep := mul_nonneg (le_of_lt hsum)
      (show (0 : ℤ) ≤ (l : ℤ)*((p.2 : ℤ)-1) by
        exact mul_nonneg (by omega) (by omega))
    dsimp [ramifiedWeight]
    nlinarith [hnonneg,hstep]



/-- Every occupied PBW point lies below the actual attained top weight. -/
theorem ramifiedWeight_le_weightDeg_of_mem
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (T : ramifiedOperatorAlgebra l) (p : ℤ × ℕ)
    (hp : p ∈ ramifiedPBWSupport l hl T) :
    ramifiedWeight l ρ σ p ≤ ramifiedWeightDeg l hl ρ σ T := by
  obtain ⟨A,hatta,hupper⟩ :=
    exists_ramifiedPBWSupport_max_weight l hl ρ σ T ⟨p,hp⟩
  rw [ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ A T hatta hupper]
  exact hupper p hp

/-- If the first-contraction weight reaches zero at the normalized
corner, any nonnegative-grade support point must be the origin.
The separate exact-pair grade theorem currently gives only a
nonnegative point, so this statement identifies its precise gap. -/
theorem ramified_corner_first_step_nonnegative_only_origin
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (E : ℤ × ℕ)
    (hEtop : ramifiedWeight l ρ σ E =
      ramifiedWeightDeg l hl ρ σ P)
    (d n h : ℕ) (hd : 1 < d) (hn : 1 < n) (hh : 2 ≤ h)
    (hEfirst : E.1 = (d : ℤ)*((h : ℤ)*(l : ℤ)-1))
    (hEsecond : E.2 = d*h)
    (hPpos : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hratio : ramifiedWeightDeg l hl ρ σ Q*(d : ℤ) =
      ramifiedWeightDeg l hl ρ σ P*(n : ℤ))
    (hstep : ramifiedWeightDeg l hl ρ σ P +
      ramifiedWeightDeg l hl ρ σ Q = (l : ℤ)*(ρ+σ)) :
    (∀ p ∈ ramifiedPBWSupport l hl P,
      0 ≤ p.1-(l : ℤ)*(p.2 : ℤ) → p = (0,0)) ∧
    (∀ q ∈ ramifiedPBWSupport l hl Q,
      0 ≤ q.1-(l : ℤ)*(q.2 : ℤ) → q = (0,0)) := by
  have hcorner : ramifiedWeightDeg l hl ρ σ P =
      (d : ℤ)*(ρ*((l : ℤ)*(h : ℤ)-1)+(l : ℤ)*σ*h) := by
    rw [← hEtop]
    simp only [ramifiedWeight,hEfirst,hEsecond]
    push_cast
    ring
  obtain ⟨hPρ,hQρ,hPl,hQl⟩ := ramified_corner_top_weights_below_steps
    l ρ σ d n h _ _ hl hsum
    (by exact_mod_cast hd) (by exact_mod_cast hn)
    (by exact_mod_cast hh) hPpos hcorner hratio hstep
  constructor
  · intro p hp hgrade
    by_contra hne
    have hupper := ramifiedWeight_le_weightDeg_of_mem l hl ρ σ P p hp
    rcases ramified_nonnegative_nonorigin_weight_lower
      l ρ σ hρ hsum p hgrade hne with hw | hw
    · omega
    · omega
  · intro q hq hgrade
    by_contra hne
    have hupper := ramifiedWeight_le_weightDeg_of_mem l hl ρ σ Q q hq
    rcases ramified_nonnegative_nonorigin_weight_lower
      l ρ σ hρ hsum q hgrade hne with hw | hw
    · omega
    · omega

end Dixmier.Weyl
