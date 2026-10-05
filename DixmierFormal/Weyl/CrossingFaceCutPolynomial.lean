/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CrossingFaceStart
public import Mathlib.Analysis.Complex.Polynomial.Basic

public import DixmierFormal.MvPolynomialCompat

@[expose] public section
/-!
# Cut polynomial and maximum root multiplicity

Specializing an explicit crossing face at `x=1` gives a power of a
univariate binomial. In characteristic zero, its nonzero roots are simple,
and algebraic closure supplies at least one root. Hence the maximum root
multiplicity of the powered face is its exponent.
-/
set_option maxHeartbeats 1000000
namespace Dixmier.Weyl
open MvPolynomial Polynomial

theorem crossingFace_cutPoly
    (α ν : ℂ) (q ρ s e : ℕ)
    (T : A1 ℂ)
    (hface : leadingForm ρ (-(s : ℤ)) T.1 = MvPolynomial.C ν *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ e) :
    cutPoly ρ (-(s : ℤ)) T.1 =
      Polynomial.C ν * (1 + Polynomial.C α * Polynomial.X ^ ρ) ^ (q * e) := by
  rw [cutPoly, hface]
  simp [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, pow_mul]

theorem binomial_rootMultiplicity_le_one (α : ℂ) (ρ : ℕ)
    (hα : α ≠ 0) (hρ : 0 < ρ) (z : ℂ) :
    Polynomial.rootMultiplicity z
      (1 + Polynomial.C α * Polynomial.X ^ ρ) ≤ 1 := by
  let g : ℂ[X] := 1 + Polynomial.C α * Polynomial.X ^ ρ
  have hg : g ≠ 0 := by
    intro hz
    have hzero : g.eval 0 = 0 := by rw [hz]; simp
    have hone : g.eval 0 = 1 := by simp [g, hρ.ne']
    exact one_ne_zero (hone.symm.trans hzero)
  by_contra hle
  change ¬ g.rootMultiplicity z ≤ 1 at hle
  have hgt : 1 < g.rootMultiplicity z := by omega
  have hdroot : g.derivative.IsRoot z :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hg).mp hgt |>.2
  have hroot : g.IsRoot z :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hg).mp hgt |>.1
  have hz : z ≠ 0 := by
    intro hzz
    have : g.eval z = 1 := by simp [g, hzz, hρ.ne']
    exact one_ne_zero (this.symm.trans hroot)
  have hderiv : g.derivative.eval z = α * ρ * z ^ (ρ - 1) := by
    simp [g, Polynomial.derivative_X_pow]
    ring
  have hnonzero : α * ρ * z ^ (ρ - 1) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero hα (by exact_mod_cast hρ.ne')
    · exact pow_ne_zero _ hz
  change g.derivative.eval z = 0 at hdroot
  rw [hderiv] at hdroot
  exact hnonzero hdroot

theorem binomial_exists_root (α : ℂ) (ρ : ℕ)
    (hα : α ≠ 0) (hρ : 0 < ρ) :
    ∃ z : ℂ, (1 + Polynomial.C α * Polynomial.X ^ ρ).IsRoot z := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-α⁻¹) hρ
  refine ⟨z, ?_⟩
  change (1 + Polynomial.C α * Polynomial.X ^ ρ).eval z = 0
  simp [hz]
  field_simp
  ring

theorem maxRootMult_binomial_power (α ν : ℂ) (ρ N : ℕ)
    (hα : α ≠ 0) (hν : ν ≠ 0) (hρ : 0 < ρ) (hN : 0 < N) :
    maxRootMult (Polynomial.C ν *
      (1 + Polynomial.C α * Polynomial.X ^ ρ) ^ N) = N := by
  let g : ℂ[X] := 1 + Polynomial.C α * Polynomial.X ^ ρ
  let p : ℂ[X] := Polynomial.C ν * g ^ N
  have hg : g ≠ 0 := by
    intro hzero
    have hzero_eval : g.eval 0 = 0 := by rw [hzero]; simp
    have hone : g.eval 0 = 1 := by simp [g, hρ.ne']
    exact one_ne_zero (hone.symm.trans hzero_eval)
  have hp : p ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hν) (pow_ne_zero _ hg)
  have hcount (z : ℂ) : rootMultiplicity z p = N * rootMultiplicity z g := by
    rw [← Polynomial.count_roots, show p = Polynomial.C ν * g ^ N from rfl,
      Polynomial.roots_C_mul _ hν, Polynomial.roots_pow, Multiset.count_nsmul,
      Polynomial.count_roots]
  have hupper : maxRootMult p ≤ N := by
    change p.roots.toFinset.sup (fun z => rootMultiplicity z p) ≤ N
    apply Finset.sup_le
    intro z hz
    rw [hcount z]
    have hsimple := binomial_rootMultiplicity_le_one α ρ hα hρ z
    simpa [g] using Nat.mul_le_mul_left N hsimple
  obtain ⟨z, hz⟩ := binomial_exists_root α ρ hα hρ
  have hmult : rootMultiplicity z g = 1 := by
    have hpos : 0 < rootMultiplicity z g :=
      (Polynomial.rootMultiplicity_pos hg).mpr hz
    have hle := binomial_rootMultiplicity_le_one α ρ hα hρ z
    change rootMultiplicity z g ≤ 1 at hle
    omega
  have hpcount : rootMultiplicity z p = N := by rw [hcount, hmult, mul_one]
  have hmem : z ∈ p.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots]
    · exact (Polynomial.rootMultiplicity_pos hp).mp (hpcount ▸ hN)
    · exact hp
  have hlower : N ≤ maxRootMult p := by
    change N ≤ p.roots.toFinset.sup (fun z => rootMultiplicity z p)
    rw [← hpcount]
    exact Finset.le_sup (f := fun z : ℂ => rootMultiplicity z p) hmem
  exact le_antisymm hupper hlower

/-- For the explicit crossing face, the cut polynomial has maximum root
multiplicity `q*e`, with no degree bound on the operator. -/
theorem crossingFace_cutPoly_maxRootMult
    (α ν : ℂ) (q ρ s e : ℕ) (T : A1 ℂ)
    (hα : α ≠ 0) (hν : ν ≠ 0) (hq : 0 < q) (hρ : 0 < ρ) (he : 0 < e)
    (hface : leadingForm ρ (-(s : ℤ)) T.1 = MvPolynomial.C ν *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ e) :
    maxRootMult (cutPoly ρ (-(s : ℤ)) T.1) = q * e := by
  rw [crossingFace_cutPoly α ν q ρ s e T hface]
  exact maxRootMult_binomial_power α ν ρ (q * e) hα hν hρ (Nat.mul_pos hq he)

end Dixmier.Weyl
