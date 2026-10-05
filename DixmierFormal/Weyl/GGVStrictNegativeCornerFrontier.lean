/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.HorizontalCornerPolynomialDescent
public import DixmierFormal.Weyl.GGVGeometricRemainingInputs

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Polynomial corner exclusion reduces to strict-negative directions

The horizontal sector descends by a polynomial automorphism to a
strict-negative face with the same normalized corner and reduced ratio.
The remaining exclusion is a source obligation, not a project axiom.
-/

namespace Dixmier.Weyl

def GGVStrictNegativeCornerInput : Prop :=
  ∀ (P Q : A1 ℂ) (ρ σ : ℤ) (a b n d h : ℕ), IsCounterexamplePair P Q →
    IsDirection ρ σ → σ < 0 → InDir ρ σ P.1 → InDir ρ σ Q.1 →
    0 < vDeg ρ σ P.1 → 0 < vDeg ρ σ Q.1 →
    ¬ (vDeg ρ σ P.1 ∣ vDeg ρ σ Q.1) → ¬ (vDeg ρ σ Q.1 ∣ vDeg ρ σ P.1) →
    expo a b ∈ (leadingForm ρ σ P.1).support →
    (∀ e ∈ (leadingForm ρ σ P.1).support, grade (expo a b) ≤ grade e) →
    vDeg ρ σ Q.1 * d = vDeg ρ σ P.1 * n → 1 < n → 1 < d → Nat.Coprime n d → 2 ≤ h →
    ¬ ((a : ℚ) / d = h - 1 ∧ (b : ℚ) / d = h)

theorem coprime_positive_weight_ratio_neither_dvd
    (wP wQ : ℤ) (hP : 0 < wP) (hQ : 0 < wQ)
    (n d : ℕ) (hn : 1 < n) (hd : 1 < d) (hcop : Nat.Coprime n d)
    (hratio : wQ * (d : ℤ) = wP * (n : ℤ)) :
    ¬ wP ∣ wQ ∧ ¬ wQ ∣ wP := by
  constructor
  · rintro ⟨k,hk⟩
    have heq : wP * ((d : ℤ) * k) = wP * (n : ℤ) := by
      rw [hk] at hratio
      nlinarith only [hratio]
    have heq' := mul_left_cancel₀ (ne_of_gt hP) heq
    have hdivZ : (d : ℤ) ∣ (n : ℤ) := ⟨k,heq'.symm⟩
    have hdiv : d ∣ n := by exact_mod_cast hdivZ
    have hone := Nat.eq_one_of_dvd_coprimes hcop hdiv (dvd_refl d)
    omega
  · rintro ⟨k,hk⟩
    have heq : wQ * (d : ℤ) = wQ * ((n : ℤ) * k) := by
      rw [hk] at hratio
      nlinarith only [hratio]
    have heq' := mul_left_cancel₀ (ne_of_gt hQ) heq
    have hdivZ : (n : ℤ) ∣ (d : ℤ) := ⟨k,heq'⟩
    have hdiv : n ∣ d := by exact_mod_cast hdivZ
    have hone := Nat.eq_one_of_dvd_coprimes hcop (dvd_refl n) hdiv
    omega

theorem ggv_polynomial_corner_of_strict_negative
    (H : GGVStrictNegativeCornerInput) :
    ∀ (P Q : A1 ℂ) (ρ σ : ℤ) (a b n d h : ℕ), IsCounterexamplePair P Q →
      IsDirection ρ σ → σ ≤ 0 → InDir ρ σ P.1 → InDir ρ σ Q.1 →
      0 < vDeg ρ σ P.1 → 0 < vDeg ρ σ Q.1 →
      ¬ (vDeg ρ σ P.1 ∣ vDeg ρ σ Q.1) → ¬ (vDeg ρ σ Q.1 ∣ vDeg ρ σ P.1) →
      expo a b ∈ (leadingForm ρ σ P.1).support →
      (∀ e ∈ (leadingForm ρ σ P.1).support, grade (expo a b) ≤ grade e) →
      vDeg ρ σ Q.1 * d = vDeg ρ σ P.1 * n → 1 < n → 1 < d → Nat.Coprime n d → 2 ≤ h →
      ¬ ((a : ℚ) / d = h - 1 ∧ (b : ℚ) / d = h) := by
  intro P Q ρ σ a b n d h hpair hdir hσ hdirP hdirQ hP hQ hnd₁ hnd₂
    hend hmin hratio hn hd hcop hh hcorner
  by_cases hneg : σ < 0
  · exact H P Q ρ σ a b n d h hpair hdir hneg hdirP hdirQ hP hQ
      hnd₁ hnd₂ hend hmin hratio hn hd hcop hh hcorner
  have hσzero : σ = 0 := by omega
  subst σ
  have hρone : ρ = 1 := by
    have hg := hdir.1
    simp only [Int.gcd_zero_right] at hg
    have hρpos : 0 < ρ := by have ht := hdir.2; omega
    have hcast : (ρ : ℤ) = (ρ.natAbs : ℤ) := by
      simpa [abs_of_pos hρpos] using (Int.natCast_natAbs ρ).symm
    rw [hg] at hcast
    simpa using hcast
  subst ρ
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (by omega : 0 < d)
  have haQ := (div_eq_iff hdQ).mp hcorner.1
  have hbQ := (div_eq_iff hdQ).mp hcorner.2
  have ha : a = d * (h - 1) := by
    have hcast : ((h - 1 : ℕ) : ℚ) = (h : ℚ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ h by omega),Nat.cast_one]
    have heq : (a : ℚ) = (d : ℚ) * ((h - 1 : ℕ) : ℚ) := by
      rw [hcast]
      nlinarith only [haQ]
    exact_mod_cast heq
  have hb : b = d * h := by exact_mod_cast (by nlinarith only [hbQ] : (b : ℚ) = (d : ℚ)*(h : ℚ))
  obtain ⟨c,R,S,r,s,hpairNew,hdirNew,hr,hs,hR,hS,hRdir,hSdir,hendNew,
      hminNew,hRpos,hSpos,hratioNew⟩ := horizontal_corner_polynomial_descent
    P Q hpair hdir hdirP hdirQ a b d n h hd hn hh ha hb hend hmin hratio hcop
  have hnd := coprime_positive_weight_ratio_neither_dvd
    (vDeg r s R.1) (vDeg r s S.1) hRpos hSpos n d hn hd hcop hratioNew
  exact H R S r s a b n d h hpairNew hdirNew hs hRdir hSdir hRpos hSpos
    hnd.1 hnd.2 hendNew hminNew hratioNew hn hd hcop hh hcorner

/-- The full characteristic-zero generation statement, still conditional
on the degree bound, ramified cut exclusion, and strict-negative corner exclusion. -/
theorem massSixGeneration_of_degree_cut_strict_corner
    (hdegree : ∀ P Q : A1 ℂ, IsCounterexamplePair P Q →
      15 < Nat.gcd (totalDeg P.1) (totalDeg Q.1))
    (hcut : ∀ (P Q : A1 ℂ) (ρ σ : ℤ) (u v₀ n d h : ℕ), IsCounterexamplePair P Q →
      IsDirection ρ σ → 0 < ρ → σ ≤ 0 → InDir ρ σ P.1 → InDir ρ σ Q.1 →
      0 < vDeg ρ σ P.1 → 0 < vDeg ρ σ Q.1 → ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1 →
      ¬ (vDeg ρ σ P.1 ∣ vDeg ρ σ Q.1) → ¬ (vDeg ρ σ Q.1 ∣ vDeg ρ σ P.1) →
      (∃ e ∈ (leadingForm ρ σ P.1).support, grade e < 0) →
      (∃ e ∈ (leadingForm ρ σ Q.1).support, grade e < 0) →
      expo u v₀ ∈ (leadingForm ρ σ P.1).support →
      (∀ e ∈ (leadingForm ρ σ P.1).support, grade e ≤ grade (expo u v₀)) →
      vDeg ρ σ Q.1 * d = vDeg ρ σ P.1 * n → 1 < n → 1 < d → Nat.Coprime n d → 2 ≤ h →
      ¬ (((u : ℚ) + ((v₀ : ℚ) - maxRootMult (cutPoly ρ σ P.1)) * σ / ρ) / d = h - 1 / ρ ∧
          (maxRootMult (cutPoly ρ σ P.1) : ℚ) / d = h))
    (hcorner : GGVStrictNegativeCornerInput) : Statement.MassSixGeneration :=
  massSixGeneration_of_geometric_GGV
    { degreeBound := hdegree
      cutCorner := hcut
      corner := ggv_polynomial_corner_of_strict_negative hcorner }

end Dixmier.Weyl
