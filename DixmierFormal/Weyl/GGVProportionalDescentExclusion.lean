/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PositiveSingletonMateFace
public import DixmierFormal.Weyl.GGVMinimalPair

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Gcd decrease for proportional positive endpoints

Removing a common positive slope greater than one decreases the gcd of
the two degrees. The actual mate endpoint and finite descent are derived
from the exact pair, including nonzero residual first-axis exponents.
-/
namespace Dixmier.Weyl

theorem proportional_positive_degree_gcd_drop
    (σ a b c d : ℕ) (hσ : 1 < σ) (hb : 0 < b)
    (hprop : a*d=b*c) :
    Nat.gcd (a+b) (c+d) < Nat.gcd (a+σ*b) (c+σ*d) := by
  have hratio : (a+σ*b)*(c+d)=(a+b)*(c+σ*d) := by
    have hh := congrArg (fun n : ℕ => σ*n) hprop
    nlinarith [hprop,hh]
  have hscale : (a+b)*Nat.gcd (a+σ*b) (c+σ*d) =
      (a+σ*b)*Nat.gcd (a+b) (c+d) := by
    calc
      _ = Nat.gcd ((a+b)*(a+σ*b)) ((a+b)*(c+σ*d)) :=
        (Nat.gcd_mul_left (a+b) (a+σ*b) (c+σ*d)).symm
      _ = Nat.gcd ((a+σ*b)*(a+b)) ((a+σ*b)*(c+d)) :=
        congrArg₂ Nat.gcd (Nat.mul_comm _ _) hratio.symm
      _ = _ := Nat.gcd_mul_left (a+σ*b) (a+b) (c+d)
  have hpos : 0 < Nat.gcd (a+b) (c+d) := Nat.gcd_pos_of_pos_left (c+d) (by omega)
  have hdegree : a+b < a+σ*b := by nlinarith
  by_contra hn
  have hle : Nat.gcd (a+σ*b) (c+σ*d) ≤ Nat.gcd (a+b) (c+d) := by omega
  have hm := Nat.mul_le_mul_left (a+b) hle
  have hlt := Nat.mul_lt_mul_of_pos_right hdegree hpos
  omega

theorem degreeMinimal_proportional_positive_descent_impossible
    (P Q R S : A1 ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q)
    (hRS : IsCounterexamplePair R S) (σ a b : ℕ)
    (hσ : 1 < σ) (hb : 0 < b)
    (hPdegree : totalDeg P.1 = a+σ*b)
    (hQdegree : totalDeg Q.1 = (vDeg 1 (σ : ℤ) S.1).toNat)
    (hmem : expo a b ∈ (leadingForm 1 (σ : ℤ) R.1).support)
    (hunique : ∀ e ∈ (leadingForm 1 (σ : ℤ) R.1).support, e = expo a b) : False := by
  obtain ⟨c,d,T,U,_,hprop,hw,hTU,hT,hU⟩ :=
    counterexample_positive_singleton_finite_descent_pair R S hRS
      σ a b (by omega) hb hmem hunique
  have hQ : totalDeg Q.1 = c+σ*d := by
    rw [hQdegree,hw]
    omega
  have hleast := hmin.2 T U hTU
  rw [hPdegree,hQ,hT,hU] at hleast
  have hdrop := proportional_positive_degree_gcd_drop σ a b c d hσ hb hprop
  omega

end Dixmier.Weyl
