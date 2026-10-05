/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedParallelWeightNonzero

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Positive weights and ratio at a common ramified face

For parallel old-face endpoints on the two top faces of an exact pair,
the first-contraction weight bound forces both new top weights positive.
The root-order ratio then transfers to the new weight ratio.
-/

namespace Dixmier.Weyl

theorem ramified_exact_pair_parallel_top_weights_positive_ratio
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
      ramifiedWeightDeg l hl ρ σ Q)
    (d n : ℕ) (hd : 0 < d) (hn : 0 < n)
    (horder : (E.2 : ℤ)*(n : ℤ) = (F.2 : ℤ)*(d : ℤ)) :
    0 < ramifiedWeightDeg l hl ρ σ P ∧
    0 < ramifiedWeightDeg l hl ρ σ Q ∧
    ramifiedWeightDeg l hl ρ σ Q * (d : ℤ) =
      ramifiedWeightDeg l hl ρ σ P * (n : ℤ) := by
  have hratio : (E.2 : ℤ) * ramifiedWeight l ρ σ F =
      (F.2 : ℤ) * ramifiedWeight l ρ σ E := by
    dsimp [ramifiedWeight]
    nlinarith [congrArg (fun z : ℤ => ρ*z) hOld]
  have hEposZ : (0 : ℤ) < E.2 := by exact_mod_cast hEpos
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  have hFposZ : (0 : ℤ) < F.2 := by
    by_contra h
    have hnonpos : (F.2 : ℤ) ≤ 0 := by omega
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hnonpos (le_of_lt hdZ)]
  have hstep : (0 : ℤ) < (l : ℤ)*(ρ+σ) := by
    exact mul_pos (by exact_mod_cast hl) hsum
  have hbound := ramified_exact_pair_weightDeg_sum_lower
    l hl ρ σ hρ hsum Q P hcomm
  rw [← hEtop, ← hFtop] at hbound
  have hEweight : 0 < ramifiedWeight l ρ σ E := by
    by_contra h
    have hnonpos : ramifiedWeight l ρ σ E ≤ 0 := by omega
    have hFnonpos : ramifiedWeight l ρ σ F ≤ 0 := by
      by_contra hF
      have hFpositive : 0 < ramifiedWeight l ρ σ F := by omega
      nlinarith [mul_pos hEposZ hFpositive,
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hFposZ) hnonpos]
    omega
  have hFweight : 0 < ramifiedWeight l ρ σ F := by
    by_contra h
    have hnonpos : ramifiedWeight l ρ σ F ≤ 0 := by omega
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt hEposZ) hnonpos,
      mul_pos hFposZ hEweight]
  have hnewratio : ramifiedWeight l ρ σ F * (d : ℤ) =
      ramifiedWeight l ρ σ E * (n : ℤ) := by
    have hmul : (E.2 : ℤ) *
        (ramifiedWeight l ρ σ F * (d : ℤ)) =
        (E.2 : ℤ) *
        (ramifiedWeight l ρ σ E * (n : ℤ)) := by
      calc
        (E.2 : ℤ) * (ramifiedWeight l ρ σ F * (d : ℤ)) =
            ((E.2 : ℤ) * ramifiedWeight l ρ σ F) * (d : ℤ) := by ring
        _ = ((F.2 : ℤ) * ramifiedWeight l ρ σ E) * (d : ℤ) := by rw [hratio]
        _ = ramifiedWeight l ρ σ E * ((F.2 : ℤ) * (d : ℤ)) := by ring
        _ = ramifiedWeight l ρ σ E * ((E.2 : ℤ) * (n : ℤ)) := by rw [← horder]
        _ = (E.2 : ℤ) * (ramifiedWeight l ρ σ E * (n : ℤ)) := by ring
    exact mul_left_cancel₀ (ne_of_gt hEposZ) hmul
  rw [← hEtop, ← hFtop]
  exact ⟨hEweight, hFweight, hnewratio⟩

end Dixmier.Weyl
