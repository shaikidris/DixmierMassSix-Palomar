/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PolynomialCutStartAlignment

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Endpoint nonparallelism at a genuinely new face

This division-free lattice lemma is used in the differing-first-slope
branch of the common-direction argument. If the old endpoints are
parallel, and the first member acquires a lower-order point on a
nonzero-weight face, that new point cannot be parallel to the mate's
unchanged endpoint.
-/

namespace Dixmier.Weyl

theorem ramified_new_face_point_not_parallel_to_old_mate
    (e g f a b : ℤ) (N n M : ℕ)
    (hM : 0 < M) (hn : n < N)
    (hOld : (N : ℤ)*f = (M : ℤ)*e)
    (hFace : a*e+b*(N : ℤ) = a*g+b*(n : ℤ))
    (hWeight : a*e+b*(N : ℤ) ≠ 0) :
    (n : ℤ)*f ≠ (M : ℤ)*g := by
  intro hNew
  have hMne : (M : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  have hCross : (M : ℤ) *
      ((N : ℤ)*g-(n : ℤ)*e) = 0 := by
    nlinarith [congrArg (fun z : ℤ => (n : ℤ)*z) hOld,
      congrArg (fun z : ℤ => (N : ℤ)*z) hNew]
  have hEG : (N : ℤ)*g = (n : ℤ)*e := by
    have hz := (mul_eq_zero.mp hCross).resolve_left hMne
    exact sub_eq_zero.mp hz
  have hFactor : ((N : ℤ)-(n : ℤ)) *
      (a*e+b*(N : ℤ)) = 0 := by
    nlinarith [congrArg (fun z : ℤ => (N : ℤ)*z) hFace,
      congrArg (fun z : ℤ => a*z) hEG]
  have hDiff : (N : ℤ)-(n : ℤ) ≠ 0 := by omega
  exact hWeight ((mul_eq_zero.mp hFactor).resolve_left hDiff)

/-- The same endpoint obstruction in the rational-tilt coordinates used
by the finite-support first-slope construction. The new weight must be
nonzero; that positivity is supplied separately by the source
configuration. -/
theorem ramified_first_tilt_new_point_not_parallel
    (l : ℕ) (ρ σ : ℤ) (V : ℤ) (t : ℚ)
    (E G F : ℤ × ℕ)
    (hM : 0 < F.2) (hbelow : G.2 < E.2)
    (hOld : (E.2 : ℤ) * F.1 = (F.2 : ℤ) * E.1)
    (hE : ramifiedWeight l ρ σ E = V)
    (hG : (ramifiedWeight l ρ σ G : ℚ) - t * (G.2 : ℚ) =
      (V : ℚ) - t * (E.2 : ℚ))
    (hNewWeight : (V : ℚ) - t * (E.2 : ℚ) ≠ 0) :
    (G.2 : ℤ) * F.1 ≠ (F.2 : ℤ) * G.1 := by
  intro hNew
  have hMne : (F.2 : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  have hOldQ : (E.2 : ℚ) * (F.1 : ℚ) = (F.2 : ℚ) * (E.1 : ℚ) := by
    exact_mod_cast hOld
  have hNewQ : (G.2 : ℚ) * (F.1 : ℚ) = (F.2 : ℚ) * (G.1 : ℚ) := by
    exact_mod_cast hNew
  have hCross : (F.2 : ℚ) *
      ((E.2 : ℚ) * (G.1 : ℚ) - (G.2 : ℚ) * (E.1 : ℚ)) = 0 := by
    nlinarith [congrArg (fun z : ℚ => (G.2 : ℚ) * z) hOldQ,
      congrArg (fun z : ℚ => (E.2 : ℚ) * z) hNewQ]
  have hEG : (E.2 : ℚ) * (G.1 : ℚ) = (G.2 : ℚ) * (E.1 : ℚ) := by
    have hz := (mul_eq_zero.mp hCross).resolve_left hMne
    exact sub_eq_zero.mp hz
  have hFace : (ρ : ℚ) * (E.1 : ℚ) +
      (((l : ℚ) * (σ : ℚ)) - t) * (E.2 : ℚ) =
      (ρ : ℚ) * (G.1 : ℚ) +
        (((l : ℚ) * (σ : ℚ)) - t) * (G.2 : ℚ) := by
    rw [← hE] at hG
    dsimp [ramifiedWeight] at hG
    push_cast at hG
    nlinarith [hG]
  have hFactor : ((E.2 : ℚ) - (G.2 : ℚ)) *
      ((ρ : ℚ) * (E.1 : ℚ) +
        (((l : ℚ) * (σ : ℚ)) - t) * (E.2 : ℚ)) = 0 := by
    nlinarith [congrArg (fun z : ℚ => (E.2 : ℚ) * z) hFace,
      congrArg (fun z : ℚ => (ρ : ℚ) * z) hEG]
  have hDiff : (E.2 : ℚ) - (G.2 : ℚ) ≠ 0 := by
    have hlt : (G.2 : ℚ) < (E.2 : ℚ) := by exact_mod_cast hbelow
    linarith
  have hZero := (mul_eq_zero.mp hFactor).resolve_left hDiff
  apply hNewWeight
  rw [← hE]
  dsimp [ramifiedWeight]
  push_cast
  nlinarith [hZero]

end Dixmier.Weyl
