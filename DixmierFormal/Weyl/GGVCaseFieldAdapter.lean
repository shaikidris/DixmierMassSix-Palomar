/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.UniversalDiagonalCaseMap

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Frozen companion and degree fields imply the case field

The degree-gcd bound implies the uniform degree bound for every exact
counterexample. Scaling the base companion by the inverse outer exponent
recovers the whole-face preliminary companion. The universal case map
therefore requires no independent caseSplit premise.
-/
namespace Dixmier.Weyl
open MvPolynomial

/-- The exact degree-gcd source field supplies the uniform degree bound. -/
theorem uniform_degree_bound_of_degree_gcd
    (hdegree : ∀ P Q : A1 ℂ, IsCounterexamplePair P Q →
      15 < Nat.gcd (totalDeg P.1) (totalDeg Q.1)) :
    ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → 16 ≤ totalDeg P.1 := by
  intro P Q hpair
  have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 1
    (by norm_num [IsDirection])
  have hd := totalDeg_eq_vDeg_one_one P hp
  have hpos : 0<totalDeg P.1 := by omega
  have hg := hdegree P Q hpair
  have hle := Nat.gcd_le_left (totalDeg Q.1) hpos
  omega

/-- Scaling a base companion recovers the source preliminary companion. -/
theorem preliminary_companion_of_power_companion_field
    (hcomp : ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ, IsDirection ρ σ →
      ∃ (μ : ℂ) (k : ℕ) (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ),
        μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧ IsWeightedHomogeneous (wt ρ σ) R m ∧
        IsWeightedHomogeneous (wt ρ σ) F (ρ+σ) ∧
        leadingForm ρ σ P.1 = C μ * R^k ∧ poisson R F=R) :
    GGVPreliminaryCompanionInput := by
  intro P Q hpair ρ σ hdir
  obtain ⟨μ,k,R,F,m,hμ,hk,hR,hRhom,hFhom,hface,hbr⟩ := hcomp P Q hpair ρ σ hdir
  refine ⟨C ((k : ℂ)⁻¹)*F,hFhom.C_mul _,?_⟩
  have hkn : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hscale : poisson (C μ*R^k) (C ((k : ℂ)⁻¹)*F) =
      C μ*C ((k : ℂ)⁻¹)*poisson (R^k) F := by
    simp only [poisson,MvPolynomial.pderiv_C_mul]
    ring
  rw [hface,hscale,poisson_power_left,hbr]
  have hpow : R^(k-1)*R=R^k := by rw [← pow_succ]; congr 1; omega
  have hcast : (k : MvPolynomial (Fin 2) ℂ)=C (k : ℂ) := by simp
  rw [hcast]
  calc
    C μ*C ((k : ℂ)⁻¹)*(C (k : ℂ)*R^(k-1)*R) =
        C μ*(C ((k : ℂ)⁻¹)*C (k : ℂ))*(R^(k-1)*R) := by ring
    _ = C μ*R^k := by rw [← map_mul,inv_mul_cancel₀ hkn,map_one,hpow]; simp

/-- The frozen caseSplit conclusion is derived from the companion and
 degreeBound fields, with no separate caseSplit hypothesis. -/
theorem ggv_caseSplit_of_companion_degree_fields
    (hcomp : ∀ P Q : A1 ℂ, IsCounterexamplePair P Q → ∀ ρ σ : ℤ, IsDirection ρ σ →
      ∃ (μ : ℂ) (k : ℕ) (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ),
        μ ≠ 0 ∧ 2 ≤ k ∧ R ≠ 0 ∧ IsWeightedHomogeneous (wt ρ σ) R m ∧
        IsWeightedHomogeneous (wt ρ σ) F (ρ+σ) ∧
        leadingForm ρ σ P.1 = C μ * R^k ∧ poisson R F=R)
    (hdegree : ∀ P Q : A1 ℂ, IsCounterexamplePair P Q →
      15 < Nat.gcd (totalDeg P.1) (totalDeg Q.1)) :
    ∀ P Q : A1 ℂ, IsCounterexamplePair P Q →
      CaseAlternative P.1 ∨ CaseAlternative (fourier P.1) :=
  preliminary_universal_caseSplit (preliminary_companion_of_power_companion_field hcomp)
    (uniform_degree_bound_of_degree_gcd hdegree)

end Dixmier.Weyl
