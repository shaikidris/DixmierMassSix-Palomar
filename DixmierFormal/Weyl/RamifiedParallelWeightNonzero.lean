/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedExactWeightLower
public import DixmierFormal.Weyl.RamifiedUnequalSlopeGeometry

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Parallel endpoints cannot both acquire zero new weight

If two old endpoints are parallel, their weights stay proportional
under any new direction. When they are the two new top endpoints of
an exact pair, the positive first-contraction weight bound rules out
zero new weight.
-/

namespace Dixmier.Weyl

theorem ramified_exact_pair_parallel_new_weight_nonzero
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q*P-P*Q = 1)
    (E F : ℤ × ℕ)
    (hEpos : 0 < E.2)
    (hOld : (E.2 : ℤ)*F.1 = (F.2 : ℤ)*E.1)
    (hEtop : ramifiedWeight l ρ σ E =
      ramifiedWeightDeg l hl ρ σ P)
    (hFtop : ramifiedWeight l ρ σ F =
      ramifiedWeightDeg l hl ρ σ Q) :
    ramifiedWeight l ρ σ E ≠ 0 := by
  have hratio : (E.2 : ℤ) * ramifiedWeight l ρ σ F =
      (F.2 : ℤ) * ramifiedWeight l ρ σ E := by
    dsimp [ramifiedWeight]
    nlinarith [congrArg (fun z : ℤ => ρ*z) hOld]
  intro hzero
  have hEne : (E.2 : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hEpos
  have hFzero : ramifiedWeight l ρ σ F = 0 := by
    rw [hzero, mul_zero] at hratio
    exact (mul_eq_zero.mp hratio).resolve_left hEne
  have hlz : (0 : ℤ) < (l : ℤ) := by exact_mod_cast hl
  have hstep : 0 < (l : ℤ)*(ρ+σ) := mul_pos hlz hsum
  have hbound := ramified_exact_pair_weightDeg_sum_lower
    l hl ρ σ hρ hsum Q P hcomm
  rw [← hEtop, ← hFtop, hzero, hFzero] at hbound
  omega

end Dixmier.Weyl
