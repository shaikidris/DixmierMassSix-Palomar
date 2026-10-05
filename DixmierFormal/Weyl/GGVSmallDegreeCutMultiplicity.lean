/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVSmallDegreeScalarHeight
public import DixmierFormal.Weyl.CrossingExpandMultiplicity

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Actual cut multiplicity from the scalar full-root height -/
namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 1000000

theorem crossingFace_general_cutPoly_maxRootMult_of_full_scalar_root
    (μ : ℂ) (a b s ρ k : ℕ) (p : ℂ[X]) (T : A1 ℂ) (α : ℂ)
    (hμ : μ ≠ 0) (hρ : 0 < ρ) (hk : 0 < k) (hp0 : p.coeff 0=1)
    (hα : α ≠ 0) (hmult : p.rootMultiplicity α=p.natDegree)
    (hpdeg : 0 < p.natDegree) (hb : b ≤ p.natDegree)
    (hface : leadingForm ρ (-(s : ℤ)) T.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0^a * MvPolynomial.X 1^b *
        p.eval₂ MvPolynomial.C (MvPolynomial.X 0^s * MvPolynomial.X 1^ρ))^k) :
    maxRootMult (cutPoly ρ (-(s : ℤ)) T.1)=k*p.natDegree := by
  classical
  have hpne : p ≠ 0 := ne_zero_of_natDegree_gt hpdeg
  have hcutne : cutPoly ρ (-(s : ℤ)) T.1 ≠ 0 := by
    rw [crossingFace_general_cutPoly μ a b s ρ k p T hface]
    exact mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hμ)
      (pow_ne_zero _ X_ne_zero))
      ((Polynomial.expand_ne_zero hρ).mpr (pow_ne_zero _ hpne))
  have hupper : maxRootMult (cutPoly ρ (-(s : ℤ)) T.1) ≤ k*p.natDegree := by
    unfold maxRootMult
    apply Finset.sup_le
    intro z hz
    by_cases hz0 : z=0
    · subst z
      rw [crossingFace_general_cutPoly_zero_rootMultiplicity μ a b s ρ k p T
        hμ hρ hp0 hface]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left k hb
    · rw [crossingFace_general_cutPoly_nonzero_rootMultiplicity μ a b s ρ k p T z
        hμ hρ hp0 hz0 hface]
      have hd := natDegree_le_of_dvd (pow_rootMultiplicity_dvd p (z^ρ)) hpne
      rw [natDegree_pow,natDegree_X_sub_C,Nat.mul_one] at hd
      have hbound : p.rootMultiplicity (z^ρ) ≤ p.natDegree := hd
      exact Nat.mul_le_mul_left k hbound
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq α hρ
  have hz0 : z ≠ 0 := by intro h; subst z; simp [hρ.ne'] at hz; exact hα hz.symm
  have hzm : (cutPoly ρ (-(s : ℤ)) T.1).rootMultiplicity z=k*p.natDegree := by
    rw [crossingFace_general_cutPoly_nonzero_rootMultiplicity μ a b s ρ k p T z
      hμ hρ hp0 hz0 hface,hz,hmult]
  have hmem : z ∈ (cutPoly ρ (-(s : ℤ)) T.1).roots.toFinset := by
    rw [Multiset.mem_toFinset,mem_roots hcutne]
    exact (rootMultiplicity_pos hcutne).mp (hzm ▸ Nat.mul_pos hk hpdeg)
  have hlower : k*p.natDegree ≤ maxRootMult (cutPoly ρ (-(s : ℤ)) T.1) := by
    rw [← hzm]
    exact Finset.le_sup (f := fun z => (cutPoly ρ (-(s : ℤ)) T.1).rootMultiplicity z) hmem
  exact Nat.le_antisymm hupper hlower

/-- The maximum root order of the actual selected cut is the reduced outer
denominator times the scalar height. This includes the possible zero root. -/
theorem smallDegreeCrossing_cutPoly_maxRootMult
    (P Q : A1 ℂ) (H : GGVSmallDegreeCrossingData P Q) :
    maxRootMult (cutPoly H.rho (-(H.s : ℤ)) H.left.1)=H.d*H.h := by
  obtain ⟨c,p,f,α,hc,hp0,hR,hF,hpdeg,hα,hroot,hmult⟩ :=
    smallDegreeCrossing_scalar_root_at_height P Q H
  have hμ : H.nu*c^H.d ≠ 0 := mul_ne_zero H.nuNonzero (pow_ne_zero _ hc)
  have hface : leadingForm H.rho (-(H.s : ℤ)) H.left.1 =
      MvPolynomial.C (H.nu*c^H.d) *
      (MvPolynomial.X 0^H.r * MvPolynomial.X 1^H.t *
        p.eval₂ MvPolynomial.C (MvPolynomial.X 0^H.s*MvPolynomial.X 1^H.rho))^H.d := by
    rw [H.leftFace,hR,mul_pow,←map_pow,map_mul]
    ring
  have hk : 0 < H.d := by have := H.dProper; omega
  have hpPos : 0 < p.natDegree := by rw [hpdeg]; have := H.hProper; omega
  have hb : H.t ≤ p.natDegree := by rw [hpdeg]; exact H.tBound
  have hmax := crossingFace_general_cutPoly_maxRootMult_of_full_scalar_root
    (H.nu*c^H.d) H.r H.t H.s H.rho H.d p H.left α hμ H.rhoPos hk hp0
      hα (hmult.trans hpdeg.symm) hpPos hb hface
  simpa [hpdeg] using hmax

end Dixmier.Weyl
