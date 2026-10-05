/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.SignedEuler

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Weighted homogeneity of polynomial roots

Euler differentiation detects the weight of each support monomial. This is
the direct route from a homogeneous proper-power face to a homogeneous root.
-/

namespace Dixmier.Weyl

open MvPolynomial

noncomputable def signedEuler (F : MvPolynomial (Fin 2) ℂ) (ρ σ : ℤ) :
    MvPolynomial (Fin 2) ℂ :=
  (ρ : ℂ) • (X 0 * pderiv 0 F) + (σ : ℂ) • (X 1 * pderiv 1 F)

private theorem signedEuler_coeff (F : MvPolynomial (Fin 2) ℂ)
    (ρ σ : ℤ) (e : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff e (signedEuler F ρ σ) =
      ((ρ : ℂ) * (e 0 : ℂ) + (σ : ℂ) * (e 1 : ℂ)) * MvPolynomial.coeff e F := by
  induction F using MvPolynomial.induction_on' with
  | add F G ihF ihG =>
      simp only [signedEuler, map_add, mul_add, smul_add, MvPolynomial.coeff_add] at *
      linear_combination ihF + ihG
  | monomial d c =>
      simp only [signedEuler, X_mul_pderiv_monomial, MvPolynomial.coeff_add, coeff_smul,
        coeff_monomial]
      split_ifs with h
      · subst e
        ring
      · simp

/-- Coefficientwise signed Euler differentiation, exposed for companion
arguments that compare two different PBW grades. -/
theorem signedEuler_coeff_explicit (F : MvPolynomial (Fin 2) ℂ)
    (ρ σ : ℤ) (e : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff e ((ρ : ℂ) • (X 0 * pderiv 0 F) +
      (σ : ℂ) • (X 1 * pderiv 1 F)) =
      ((ρ : ℂ) * (e 0 : ℂ) + (σ : ℂ) * (e 1 : ℂ)) * MvPolynomial.coeff e F := by
  exact signedEuler_coeff F ρ σ e

/-- Signed Euler differentiation of a power, without any sign restriction
on the coordinate weights. -/
theorem signedEuler_pow (F : MvPolynomial (Fin 2) ℂ)
    (ρ σ : ℤ) (d : ℕ) :
    signedEuler (F ^ d) ρ σ =
      (d : ℂ) • (F ^ (d - 1) * signedEuler F ρ σ) := by
  simp only [signedEuler, pderiv_pow, Algebra.smul_def,
    MvPolynomial.algebraMap_eq]
  have hcast : ((d : ℕ) : MvPolynomial (Fin 2) ℂ) = MvPolynomial.C (d : ℂ) := by
    exact (map_natCast (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ) d).symm
  rw [hcast]
  ring

/-- A nonzero polynomial root of a positive weighted-homogeneous power
is itself weighted homogeneous, for arbitrary signed integer weights. -/
theorem weighted_homogeneous_root_of_power
    (S : MvPolynomial (Fin 2) ℂ) (ρ σ N : ℤ) (d : ℕ)
    (hS : S ≠ 0) (hd : 0 < d)
    (hpow : (S ^ d).IsWeightedHomogeneous (wt ρ σ) N) :
    ∃ m : ℤ, S.IsWeightedHomogeneous (wt ρ σ) m ∧ N = (d : ℤ) * m := by
  have hpowexpr : S ^ d = S ^ (d - 1) * S := by
    calc
      S ^ d = S ^ (d - 1 + 1) := by congr 1; omega
      _ = S ^ (d - 1) * S := pow_succ _ _
  have hEuler := signedWeightedEuler (S ^ d) ρ σ N hpow
  change signedEuler (S ^ d) ρ σ = (N : ℂ) • S ^ d at hEuler
  rw [signedEuler_pow, hpowexpr] at hEuler
  have hfactor : S ^ (d - 1) *
      ((d : ℂ) • signedEuler S ρ σ - (N : ℂ) • S) = 0 := by
    simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq] at hEuler ⊢
    linear_combination hEuler
  have hnonzero : S ^ (d - 1) ≠ 0 := pow_ne_zero _ hS
  have hcancel : (d : ℂ) • signedEuler S ρ σ = (N : ℂ) • S :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hnonzero)
  have hweightC (a : Fin 2 →₀ ℕ) :
      (ρ : ℂ) * (a 0 : ℂ) + (σ : ℂ) * (a 1 : ℂ) =
        (Finsupp.weight (wt ρ σ) a : ℂ) := by
    rw [Finsupp.weight_eq_sum]
    simp [Fin.sum_univ_two, wt]
    ring
  have hcoeff (a : Fin 2 →₀ ℕ) (ha : MvPolynomial.coeff a S ≠ 0) :
      (d : ℤ) * Finsupp.weight (wt ρ σ) a = N := by
    have hc := congrArg (MvPolynomial.coeff a) hcancel
    simp only [MvPolynomial.coeff_smul, signedEuler_coeff] at hc
    rw [hweightC] at hc
    have hcomplex : (d : ℂ) * (Finsupp.weight (wt ρ σ) a : ℂ) = (N : ℂ) := by
      apply mul_right_cancel₀ ha
      linear_combination hc
    exact_mod_cast hcomplex
  obtain ⟨e, he⟩ := MvPolynomial.exists_coeff_ne_zero hS
  refine ⟨Finsupp.weight (wt ρ σ) e, ?_, (hcoeff e he).symm⟩
  intro a ha
  exact mul_left_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hd))
    ((hcoeff a ha).trans (hcoeff e he).symm)

end Dixmier.Weyl
