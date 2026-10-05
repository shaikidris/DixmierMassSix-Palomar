module

public import DixmierFormal.Weyl.WronskianRatio

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Factor resonance for ordinary polynomial face brackets

A factor occurring excessively in a weighted derivative bracket forces
resonance between the factor orders of its two arguments. This is the
ordinary-polynomial form needed for canonical ramified face polynomials.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 400000

theorem polynomial_power_derivative_cleared (u : ℂ[X]) (a : ℕ) :
    u * (u^a).derivative = C (a:ℂ) * u^a * u.derivative := by
  cases a with
  | zero => simp
  | succ a =>
    rw [derivative_pow]
    simp only [Nat.succ_sub_one, Nat.cast_succ, pow_succ, map_add, map_one]
    ring

theorem polynomial_cleared_factor_derivative_identity
    (u F G : ℂ[X]) (a b : ℕ) (m n : ℤ) :
    u * (C (m:ℂ) * (u^a*F) * (u^b*G).derivative -
      C (n:ℂ) * (u^b*G) * (u^a*F).derivative) =
    u^(a+b) * (C ((m:ℂ)*(b:ℂ)-(n:ℂ)*(a:ℂ))*F*G*u.derivative +
      u*(C (m:ℂ)*F*G.derivative-C (n:ℂ)*G*F.derivative)) := by
  have ha := polynomial_power_derivative_cleared u a
  have hb := polynomial_power_derivative_cleared u b
  rw [derivative_mul, derivative_mul, pow_add, map_sub, map_mul, map_mul]
  linear_combination C (m:ℂ)*u^a*F*G*hb-C (n:ℂ)*u^b*F*G*ha

theorem polynomial_high_bracket_factor_resonance
    (u F G h t : ℂ[X]) (a b : ℕ) (m n : ℤ)
    (hu : Prime u) (hF : ¬ u ∣ F) (hG : ¬ u ∣ G)
    (hdu : ¬ u ∣ u.derivative) (hhigh : u^(a+b) ∣ h)
    (he : C (m:ℂ)*(u^a*F)*(u^b*G).derivative -
      C (n:ℂ)*(u^b*G)*(u^a*F).derivative = t*h) :
    m*(b:ℤ) = n*(a:ℤ) := by
  obtain ⟨H,hH⟩ := hhigh
  have hf := polynomial_cleared_factor_derivative_identity u F G a b m n
  rw [he,hH] at hf
  have hc : C ((m:ℂ)*(b:ℂ)-(n:ℂ)*(a:ℂ))*F*G*u.derivative +
      u*(C (m:ℂ)*F*G.derivative-C (n:ℂ)*G*F.derivative) = u*t*H := by
    apply mul_left_cancel₀ (pow_ne_zero (a+b) hu.ne_zero)
    linear_combination -hf
  have hd : u ∣ C ((m:ℂ)*(b:ℂ)-(n:ℂ)*(a:ℂ))*F*G*u.derivative := by
    refine ⟨t*H-(C (m:ℂ)*F*G.derivative-C (n:ℂ)*G*F.derivative), ?_⟩
    linear_combination hc
  have hcc : u ∣ C ((m:ℂ)*(b:ℂ)-(n:ℂ)*(a:ℂ)) := by
    have h1 := (hu.dvd_mul.mp hd).resolve_right hdu
    have h2 := (hu.dvd_mul.mp h1).resolve_right hG
    exact (hu.dvd_mul.mp h2).resolve_right hF
  have hz : (m:ℂ)*(b:ℂ)-(n:ℂ)*(a:ℂ) = 0 := by
    by_contra hn
    exact hu.not_isUnit (isUnit_of_dvd_unit hcc
      ((isUnit_iff_ne_zero.mpr hn).map (Polynomial.C : ℂ →+* ℂ[X])))
  exact_mod_cast sub_eq_zero.mp hz

end Dixmier.Weyl
