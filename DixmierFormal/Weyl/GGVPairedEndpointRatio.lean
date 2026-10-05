/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVPairedFaceSuccessor
public import DixmierFormal.Weyl.GGVCommonFaceEndpoints

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Extreme points on negative faces

On a negative face of positive first weight, the `X` and `Y` coordinates
increase together. This identifies the maximum-order shared successor
point with the proportional maximum endpoint of the preceding face.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- On a negative weighted face, an occupied point maximal in its `Y`
coordinate is also the unique occupied point maximal in its `X` coordinate. -/
theorem leadingFace_max_y_eq_max_x
    (P : A1 ℂ) (ρ s : ℕ) (hρ : 0 < ρ) (hs : 0 < s)
    {a b : Fin 2 →₀ ℕ}
    (ha : a ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support)
    (hb : b ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support)
    (hya : b 1 ≤ a 1) (hxb : a 0 ≤ b 0) : a = b := by
  have haw : (ρ : ℤ) * a 0 - (s : ℤ) * a 1 =
      vDeg (ρ : ℤ) (-(s : ℤ)) P.1 := by
    change a ∈ (MvPolynomial.weightedHomogeneousComponent
      (wt (ρ : ℤ) (-(s : ℤ)))
      (vDeg (ρ : ℤ) (-(s : ℤ)) P.1) (symbol P.1)).support at ha
    rw [MvPolynomial.support_weightedHomogeneousComponent] at ha
    simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two, mul_comm, sub_eq_add_neg] using
      (Finset.mem_filter.mp ha).2
  have hbw : (ρ : ℤ) * b 0 - (s : ℤ) * b 1 =
      vDeg (ρ : ℤ) (-(s : ℤ)) P.1 := by
    change b ∈ (MvPolynomial.weightedHomogeneousComponent
      (wt (ρ : ℤ) (-(s : ℤ)))
      (vDeg (ρ : ℤ) (-(s : ℤ)) P.1) (symbol P.1)).support at hb
    rw [MvPolynomial.support_weightedHomogeneousComponent] at hb
    simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two, mul_comm, sub_eq_add_neg] using
      (Finset.mem_filter.mp hb).2
  have hρz : (0 : ℤ) < ρ := by exact_mod_cast hρ
  have hsz : (0 : ℤ) < s := by exact_mod_cast hs
  have hxz : (a 0 : ℤ) ≤ b 0 := by exact_mod_cast hxb
  have hyz : (b 1 : ℤ) ≤ a 1 := by exact_mod_cast hya
  have hxeq : a 0 = b 0 := by
    have h : (a 0 : ℤ) = b 0 := by nlinarith
    exact_mod_cast h
  have hyeq : a 1 = b 1 := by
    have h : (a 1 : ℤ) = b 1 := by rw [hxeq] at haw; nlinarith
    exact_mod_cast h
  ext i
  fin_cases i
  · exact hxeq
  · exact hyeq

/-- Maximum-order points on the two members' common negative face have
proportional coordinates, with the reduced exponents supplied by the
actual leading weights. -/
theorem counterexample_negative_face_maxima_proportional
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ s : ℕ) (hρ : 0 < ρ) (hs : 0 < s)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    {a b : Fin 2 →₀ ℕ}
    (ha : a ∈ (leadingForm ρ (-(s : ℤ)) P.1).support)
    (hb : b ∈ (leadingForm ρ (-(s : ℤ)) Q.1).support)
    (haMax : ∀ e ∈ (leadingForm ρ (-(s : ℤ)) P.1).support, e 1 ≤ a 1)
    (hbMax : ∀ e ∈ (leadingForm ρ (-(s : ℤ)) Q.1).support, e 1 ≤ b 1) :
    ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ Nat.Coprime d n ∧
      n * a 0 = d * b 0 ∧ n * a 1 = d * b 1 := by
  obtain ⟨n, d, u, v, r, t, hn, hd, hcop,
      hpMax, hqMax, _, _, hpBounds, hqBounds⟩ :=
    counterexample_strict_negative_face_proportional_endpoints
      P Q hpair ρ s hs hdir
  have haEq : a = expo (d * u) (d * v) :=
    leadingFace_max_y_eq_max_x P ρ s hρ hs ha hpMax
      (haMax _ hpMax) (by simpa [expo] using (hpBounds a ha).2)
  have hbEq : b = expo (n * u) (n * v) :=
    leadingFace_max_y_eq_max_x Q ρ s hρ hs hb hqMax
      (hbMax _ hqMax) (by simpa [expo] using (hqBounds b hb).2)
  refine ⟨n, d, hn, hd, hcop, ?_, ?_⟩
  · rw [haEq, hbEq]
    simp [expo]
    ac_rfl
  · rw [haEq, hbEq]
    simp [expo]
    ac_rfl

/-- At two consecutive actual negative faces of an exact counterexample
pair, their shared vertices are proportional across the two operators.
The proportionality is established on the earlier face and requires no
bound on either operator's differential order. -/
theorem counterexample_paired_successor_proportional_vertices
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ₁ s₁ ρ₂ s₂ : ℕ)
    (hρ₁ : 0 < ρ₁) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hdir₁ : IsDirection (ρ₁ : ℤ) (-(s₁ : ℤ)))
    (hdir₂ : IsDirection (ρ₂ : ℤ) (-(s₂ : ℤ)))
    (j : ℕ) (hj : j + 1 < (ggvOrderedNegativeFaceSlopes P).length)
    (hfirst : (ggvOrderedNegativeFaceSlopes P)[j] =
      (-(s₁ : ℤ) : ℚ) / ρ₁)
    (hsecond : (ggvOrderedNegativeFaceSlopes P)[j+1] =
      (-(s₂ : ℤ) : ℚ) / ρ₂)
    (hface₁ : InDir (ρ₁ : ℤ) (-(s₁ : ℤ)) P.1)
    (hface₂ : InDir (ρ₂ : ℤ) (-(s₂ : ℤ)) P.1) :
    ∃ (a b : Fin 2 →₀ ℕ) (n d : ℕ),
      a ∈ (leadingForm (ρ₁ : ℤ) (-(s₁ : ℤ)) P.1).support ∧
      a ∈ (leadingForm (ρ₂ : ℤ) (-(s₂ : ℤ)) P.1).support ∧
      b ∈ (leadingForm (ρ₁ : ℤ) (-(s₁ : ℤ)) Q.1).support ∧
      b ∈ (leadingForm (ρ₂ : ℤ) (-(s₂ : ℤ)) Q.1).support ∧
      0 < n ∧ 0 < d ∧ Nat.Coprime d n ∧
      n * a 0 = d * b 0 ∧ n * a 1 = d * b 1 := by
  obtain ⟨⟨a, ha₁, ha₂, haMax, _⟩,
      ⟨b, hb₁, hb₂, hbMax, _⟩⟩ :=
    counterexample_paired_successor_shared_endpoints
      P Q hpair (ρ₁ : ℤ) (-(s₁ : ℤ)) (ρ₂ : ℤ) (-(s₂ : ℤ))
      hdir₁ hdir₂ (by omega) (by omega)
      j hj hfirst hsecond hface₁ hface₂
  obtain ⟨n, d, hn, hd, hcop, hx, hy⟩ :=
    counterexample_negative_face_maxima_proportional
      P Q hpair ρ₁ s₁ hρ₁ hs₁ hdir₁ ha₁ hb₁ haMax hbMax
  exact ⟨a, b, n, d, ha₁, ha₂, hb₁, hb₂, hn, hd, hcop, hx, hy⟩

end Dixmier.Weyl
