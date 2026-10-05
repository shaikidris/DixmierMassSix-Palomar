/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedEndpointCoefficient

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Reconstruction from canonical ramified PBW coefficients

An arbitrary element of the ramified operator algebra is the finite sum
of its canonical Laurent coefficient operators times derivative powers.
This gives an exact, cutoff-free starting point for the finite-face
commutator calculation.
-/

namespace Dixmier.Weyl

theorem ramifiedPBW_reconstruct (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) :
    (ramifiedPBWCoeffs l hl T).sum
      (fun j f => ramifiedCoeffGen l f * (ramifiedYGen l)^j) = T := by
  apply Subtype.ext
  classical
  simpa [Finsupp.sum, ramifiedNormalEval, ramifiedCoeffGen,
    ramifiedYGen] using ramifiedPBWCoeffs_eval l hl T

private theorem finset_commutator_double_sum
    {R ι κ : Type*} [NonUnitalNonAssocRing R]
    (s : Finset ι) (t : Finset κ) (A : ι → R) (B : κ → R) :
    (∑ j ∈ s, A j) * (∑ k ∈ t, B k) -
      (∑ k ∈ t, B k) * (∑ j ∈ s, A j) =
      ∑ j ∈ s, ∑ k ∈ t, (A j * B k - B k * A j) := by
  classical
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_sub_distrib]

/-- The commutator of arbitrary finite ramified operators is the finite
double sum of commutators of their canonical PBW atoms. Neither member
has an order or support-size cutoff. -/
theorem ramifiedPBW_commutator_double_sum (l : ℕ) (hl : 0 < l)
    (P Q : ramifiedOperatorAlgebra l) :
    P * Q - Q * P =
      ∑ j ∈ (ramifiedPBWCoeffs l hl P).support,
        ∑ k ∈ (ramifiedPBWCoeffs l hl Q).support,
          ((ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl P) j) *
              (ramifiedYGen l)^j) *
              (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl Q) k) *
                (ramifiedYGen l)^k) -
            (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl Q) k) *
              (ramifiedYGen l)^k) *
              (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl P) j) *
                (ramifiedYGen l)^j)) := by
  let A := (ramifiedPBWCoeffs l hl P).sum
    (fun j f => ramifiedCoeffGen l f * (ramifiedYGen l)^j)
  let B := (ramifiedPBWCoeffs l hl Q).sum
    (fun k g => ramifiedCoeffGen l g * (ramifiedYGen l)^k)
  have hA : A = P := ramifiedPBW_reconstruct l hl P
  have hB : B = Q := ramifiedPBW_reconstruct l hl Q
  calc
    P * Q - Q * P = A * B - B * A := by rw [hA, hB]
    _ = _ := by
      dsimp [A, B]
      simp only [Finsupp.sum]
      exact finset_commutator_double_sum
        (R := ramifiedOperatorAlgebra l)
        (ramifiedPBWCoeffs l hl P).support
        (ramifiedPBWCoeffs l hl Q).support
        (fun j => ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl P) j) *
          (ramifiedYGen l)^j)
        (fun k => ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl Q) k) *
          (ramifiedYGen l)^k)

theorem ramifiedPBWCoeffs_finset_sum (l : ℕ) (hl : 0 < l)
    {α : Type*} (s : Finset α) (F : α → ramifiedOperatorAlgebra l) :
    ramifiedPBWCoeffs l hl (∑ a ∈ s, F a) =
      ∑ a ∈ s, ramifiedPBWCoeffs l hl (F a) := by
  classical
  induction s using Finset.induction with
  | empty =>
      apply ramifiedPBWCoeffs_eq_of_eval
      simp [ramifiedNormalEval]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        ramifiedPBWCoeffs_add, ih]

/-- Every canonical derivative coefficient of an arbitrary commutator
is a finite double sum of its PBW-atom commutator coefficients. -/
theorem ramifiedPBWCoeffs_commutator_double_sum (l : ℕ) (hl : 0 < l)
    (P Q : ramifiedOperatorAlgebra l) (m : ℕ) :
    ramifiedPBWCoeffs l hl (P * Q - Q * P) m =
      ∑ j ∈ (ramifiedPBWCoeffs l hl P).support,
        ∑ k ∈ (ramifiedPBWCoeffs l hl Q).support,
          ramifiedPBWCoeffs l hl
            ((ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl P) j) *
                (ramifiedYGen l)^j) *
                (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl Q) k) *
                  (ramifiedYGen l)^k) -
              (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl Q) k) *
                (ramifiedYGen l)^k) *
                (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl P) j) *
                  (ramifiedYGen l)^j)) m := by
  rw [ramifiedPBW_commutator_double_sum]
  rw [ramifiedPBWCoeffs_finset_sum]
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ramifiedPBWCoeffs_finset_sum]
  rw [Finsupp.finsetSum_apply]

end Dixmier.Weyl
