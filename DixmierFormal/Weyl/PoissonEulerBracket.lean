module

public import DixmierFormal.Weyl.PoissonHomogeneousWeight
public import DixmierFormal.Weyl.DerivativeStableKernel
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Cleared weighted Euler identities for a nonzero Poisson bracket

These identities retain the actual first bracket. They permit comparison
of its irreducible-factor multiplicities with those of its two arguments.
-/
set_option maxHeartbeats 0
namespace Dixmier.Weyl
open MvPolynomial

 theorem homogeneous_poisson_euler_bracket_identities
    (f g : MvPolynomial (Fin 2) ℂ) (ρ σ m n : ℤ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m)
    (hg : g.IsWeightedHomogeneous (wt ρ σ) n) :
    (C (m:ℂ)*f*pderiv 0 g-C (n:ℂ)*g*pderiv 0 f =
      C (σ:ℂ)*X 1*poisson f g) ∧
    (C (m:ℂ)*f*pderiv 1 g-C (n:ℂ)*g*pderiv 1 f =
      -C (ρ:ℂ)*X 0*poisson f g) := by
  have hEf := signedWeightedEuler f ρ σ m hf
  have hEg := signedWeightedEuler g ρ σ n hg
  simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq] at hEf hEg
  simp only [poisson]
  constructor
  · linear_combination -pderiv 0 g*hEf+pderiv 0 f*hEg
  · linear_combination -pderiv 1 g*hEf+pderiv 1 f*hEg

 theorem pderiv_power_cleared (u : MvPolynomial (Fin 2) ℂ) (a : ℕ) (i : Fin 2) :
    u*pderiv i (u^a)=C (a:ℂ)*u^a*pderiv i u := by
  cases a with
  | zero => simp
  | succ a =>
    rw [pderiv_pow]
    simp only [Nat.succ_sub_one,Nat.cast_succ,pow_succ,map_add,map_one,map_natCast]
    ring

 theorem prime_polynomial_pderiv_not_dvd
    (u : MvPolynomial (Fin 2) ℂ) (hu : Prime u) :
    ∃ i : Fin 2, ¬ u ∣ pderiv i u := by
  classical
  by_contra hn
  have hdiv : ∀ i : Fin 2, u ∣ pderiv i u := by
    intro i
    by_contra hi
    exact hn ⟨i,hi⟩
  have hz : ∀ i : Fin 2, pderiv i u=0 := by
    intro i
    by_contra hi
    have hlt := bivariate_pderiv_totalDegree_lt u i hi
    have hle := totalDegree_le_of_dvd_of_isDomain (hdiv i) hi
    omega
  obtain ⟨c,hc⟩ := bivariate_cross_derivatives_constant u 1 one_ne_zero
    (by simp [hz]) (by simp [hz])
  have hcne : c ≠ 0 := by
    intro h
    apply hu.ne_zero
    simpa only [h,map_zero,zero_mul] using hc
  apply hu.not_isUnit
  rw [hc,mul_one]
  exact hcne.isUnit.map (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)

 theorem cleared_factor_derivative_identity
    (u F G : MvPolynomial (Fin 2) ℂ) (a b : ℕ) (m n : ℤ) (i : Fin 2) :
    u*(C (m:ℂ)*(u^a*F)*pderiv i (u^b*G)-C (n:ℂ)*(u^b*G)*pderiv i (u^a*F)) =
      u^(a+b)*(C ((m:ℂ)*(b:ℂ)-(n:ℂ)*(a:ℂ))*F*G*pderiv i u +
        u*(C (m:ℂ)*F*pderiv i G-C (n:ℂ)*G*pderiv i F)) := by
  have ha := pderiv_power_cleared u a i
  have hb := pderiv_power_cleared u b i
  rw [pderiv_mul,pderiv_mul,pow_add,map_sub,map_mul,map_mul]
  linear_combination C (m:ℂ)*u^a*F*G*hb-C (n:ℂ)*u^b*F*G*ha

 theorem prime_high_bracket_forces_multiplicity_resonance
    (u F G h t : MvPolynomial (Fin 2) ℂ) (a b : ℕ) (m n : ℤ) (i : Fin 2)
    (hu : Prime u) (hF : ¬ u ∣ F) (hG : ¬ u ∣ G) (hdu : ¬ u ∣ pderiv i u)
    (hhigh : u^(a+b) ∣ h)
    (he : C (m:ℂ)*(u^a*F)*pderiv i (u^b*G)-C (n:ℂ)*(u^b*G)*pderiv i (u^a*F)=t*h) :
    m*(b:ℤ)=n*(a:ℤ) := by
  obtain ⟨H,hH⟩ := hhigh
  have hf := cleared_factor_derivative_identity u F G a b m n i
  rw [he,hH] at hf
  have hc : C ((m:ℂ)*(b:ℂ)-(n:ℂ)*(a:ℂ))*F*G*pderiv i u +
      u*(C (m:ℂ)*F*pderiv i G-C (n:ℂ)*G*pderiv i F)=u*t*H := by
    apply mul_left_cancel₀ (pow_ne_zero (a+b) hu.ne_zero)
    linear_combination -hf
  have hd : u ∣ C ((m:ℂ)*(b:ℂ)-(n:ℂ)*(a:ℂ))*F*G*pderiv i u := by
    refine ⟨t*H-(C (m:ℂ)*F*pderiv i G-C (n:ℂ)*G*pderiv i F),?_⟩
    linear_combination hc
  have hcc : u ∣ C ((m:ℂ)*(b:ℂ)-(n:ℂ)*(a:ℂ)) := by
    have h1 := (hu.dvd_mul.mp hd).resolve_right hdu
    have h2 := (hu.dvd_mul.mp h1).resolve_right hG
    exact (hu.dvd_mul.mp h2).resolve_right hF
  have hz : (m:ℂ)*(b:ℂ)-(n:ℂ)*(a:ℂ)=0 := by
    by_contra hn
    exact hu.not_isUnit (isUnit_of_dvd_unit hcc
      ((isUnit_iff_ne_zero.mpr hn).map (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)))
  exact_mod_cast sub_eq_zero.mp hz

end Dixmier.Weyl
