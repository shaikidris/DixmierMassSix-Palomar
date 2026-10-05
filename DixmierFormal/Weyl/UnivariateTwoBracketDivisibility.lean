module

public import DixmierFormal.Weyl.UnivariateTwoBracketFactors
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Divisibility of the ordinary two-bracket numerator

At positive source weight, the centralizer multiplicity relation and
factor resonance force the first bracket to divide the product of its inputs.
The contraction weight may be any positive integer.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 800000

theorem polynomial_prime_derivative_not_dvd (u : ℂ[X]) (hu : Prime u) :
    ¬ u ∣ u.derivative := by
  intro hd
  have hz : u.derivative = 0 :=
    eq_zero_of_dvd_of_degree_lt hd (degree_derivative_lt hu.ne_zero)
  have he := eq_C_of_derivative_eq_zero hz
  have hc : u.coeff 0 ≠ 0 := by
    intro hc
    exact hu.ne_zero (by simpa [hc] using he)
  apply hu.not_isUnit
  rw [he]
  exact hc.isUnit.map (Polynomial.C : ℂ →+* ℂ[X])

theorem polynomial_zero_bracket_multiplicity_ratio
    (f h : ℂ[X]) (m r : ℤ) (hf : f ≠ 0) (hh : h ≠ 0)
    (he : C (m:ℂ)*f*h.derivative-C (r:ℂ)*h*f.derivative=0)
    (u : ℂ[X]) (hu : Prime u) :
    m*(multiplicity u h:ℤ)=r*(multiplicity u f:ℤ) := by
  have hfinf := FiniteMultiplicity.of_prime_left hu hf
  have hfinh := FiniteMultiplicity.of_prime_left hu hh
  obtain ⟨F,hF,huF⟩ := hfinf.exists_eq_pow_mul_and_not_dvd
  obtain ⟨H,hH,huH⟩ := hfinh.exists_eq_pow_mul_and_not_dvd
  apply polynomial_high_bracket_factor_resonance u F H 0 0
    (multiplicity u f) (multiplicity u h) m r hu huF huH
    (polynomial_prime_derivative_not_dvd u hu) (dvd_zero _)
  simpa only [← hF,← hH, mul_zero] using he

theorem polynomial_two_bracket_numerator_divisibility
    (f g h : ℂ[X]) (m n r δ : ℤ) (t : ℂ[X])
    (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (hm : 0 < m) (hδ : 0 < δ)
    (hweight : r = m+n-δ)
    (hfirst : C (m:ℂ)*f*g.derivative-C (n:ℂ)*g*f.derivative=t*h)
    (hsecond : C (m:ℂ)*f*h.derivative-C (r:ℂ)*f.derivative*h=0) :
    h ∣ f*g := by
  classical
  apply (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hh).mpr
  intro u hu
  have hfinf := FiniteMultiplicity.of_prime_left hu hf
  have hfing := FiniteMultiplicity.of_prime_left hu hg
  have hfinh := FiniteMultiplicity.of_prime_left hu hh
  have hcount := polynomial_zero_bracket_multiplicity_ratio f h m r hf hh
    (by linear_combination hsecond) u hu
  have hsmall : multiplicity u h ≤ multiplicity u f+ multiplicity u g := by
    by_contra hn
    obtain ⟨F,hF,huF⟩ := hfinf.exists_eq_pow_mul_and_not_dvd
    obtain ⟨G,hG,huG⟩ := hfing.exists_eq_pow_mul_and_not_dvd
    have hhigh : u^(multiplicity u f+ multiplicity u g) ∣ h :=
      (pow_dvd_pow u (by omega : multiplicity u f+ multiplicity u g ≤ multiplicity u h)).trans
        (pow_multiplicity_dvd u h)
    have he' : C (m:ℂ)*(u^multiplicity u f*F)*(u^multiplicity u g*G).derivative-
        C (n:ℂ)*(u^multiplicity u g*G)*(u^multiplicity u f*F).derivative=t*h := by
      simpa only [← hF,← hG] using hfirst
    have hres := polynomial_high_bracket_factor_resonance u F G h t
      (multiplicity u f) (multiplicity u g) m n hu huF huG
      (polynomial_prime_derivative_not_dvd u hu) hhigh he'
    have hbalance : m*((multiplicity u h:ℤ)-(multiplicity u f:ℤ)-(multiplicity u g:ℤ)) =
        -δ*(multiplicity u f:ℤ) := by
      linear_combination hcount-hres+(multiplicity u f:ℤ)*hweight
    have hlt : ((multiplicity u f+ multiplicity u g : ℕ):ℤ) < (multiplicity u h:ℤ) := by
      exact_mod_cast (lt_of_not_ge hn)
    push_cast at hlt
    have hpos : 0 < m*((multiplicity u h:ℤ)-(multiplicity u f:ℤ)-(multiplicity u g:ℤ)) :=
      mul_pos hm (by omega)
    have hnonpos : -δ*(multiplicity u f:ℤ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by omega) (by positivity)
    rw [hbalance] at hpos
    omega
  rw [emultiplicity_mul hu,hfinh.emultiplicity_eq_multiplicity,
    hfinf.emultiplicity_eq_multiplicity,hfing.emultiplicity_eq_multiplicity]
  exact_mod_cast hsmall

theorem polynomial_two_bracket_fixed_point_of_division
    (f g h q t : ℂ[X]) (m n r δ : ℤ) (hh : h ≠ 0)
    (hweight : r = m+n-δ)
    (hfirst : C (m:ℂ)*f*g.derivative-C (n:ℂ)*g*f.derivative=t*h)
    (hsecond : C (m:ℂ)*f*h.derivative-C (r:ℂ)*f.derivative*h=0)
    (hdivision : h*q=f*g) :
    C (m:ℂ)*f*q.derivative-C (δ:ℂ)*f.derivative*q=t*f := by
  have hderiv := congrArg Polynomial.derivative hdivision
  rw [derivative_mul, derivative_mul] at hderiv
  have hw : (r:ℂ)=(m:ℂ)+(n:ℂ)-(δ:ℂ) := by exact_mod_cast hweight
  rw [hw, map_sub, map_add] at hsecond
  apply mul_left_cancel₀ hh
  linear_combination C (m:ℂ)*f*hderiv-q*hsecond+f*hfirst-
    (C (m:ℂ)+C (n:ℂ))*f.derivative*hdivision

theorem polynomial_two_bracket_fixed_point_exists
    (f g h : ℂ[X]) (m n r δ : ℤ) (t : ℂ[X])
    (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (hm : 0 < m) (hδ : 0 < δ) (hweight : r = m+n-δ)
    (hfirst : C (m:ℂ)*f*g.derivative-C (n:ℂ)*g*f.derivative=t*h)
    (hsecond : C (m:ℂ)*f*h.derivative-C (r:ℂ)*f.derivative*h=0) :
    ∃ q : ℂ[X], h*q=f*g ∧
      C (m:ℂ)*f*q.derivative-C (δ:ℂ)*f.derivative*q=t*f := by
  obtain ⟨q,hq⟩ := polynomial_two_bracket_numerator_divisibility
    f g h m n r δ t hf hg hh hm hδ hweight hfirst hsecond
  exact ⟨q,hq.symm,polynomial_two_bracket_fixed_point_of_division
    f g h q t m n r δ hh hweight hfirst hsecond hq.symm⟩

end Dixmier.Weyl
