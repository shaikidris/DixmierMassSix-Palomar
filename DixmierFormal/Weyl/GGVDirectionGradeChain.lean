/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.Validation

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The finite grade crossing in G13 Proposition 7.2

The source walks through a finite ordered list of negative directions.
The ending grade of one face is the starting grade of the next. Once
the positive first and negative last grades and exclusion of a zero
intermediate grade are established, one face crosses strictly. The
geometric construction of the list and the zero-grade exclusion remain
separate source obligations.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- G13 Proposition 7.2, equation (7.9) to the weighted-ratio part of
(7.8): proportional occupied endpoints on an actual common leading
direction force the same ratio of the two weighted degrees. -/
theorem proportional_leadingFace_endpoints_weight_ratio
    (P Q : A1 ℂ) (ρ σ : ℤ)
    (uP vP uQ vQ m n : ℕ)
    (hP : expo uP vP ∈ (leadingForm ρ σ P.1).support)
    (hQ : expo uQ vQ ∈ (leadingForm ρ σ Q.1).support)
    (hx : n * uP = m * uQ)
    (hy : n * vP = m * vQ) :
    vDeg ρ σ P.1 * (n : ℤ) = vDeg ρ σ Q.1 * (m : ℤ) := by
  have hpWeight : (ρ : ℤ) * uP + σ * vP = vDeg ρ σ P.1 := by
    change expo uP vP ∈
      (MvPolynomial.weightedHomogeneousComponent (wt ρ σ)
        (vDeg ρ σ P.1) (symbol P.1)).support at hP
    rw [MvPolynomial.support_weightedHomogeneousComponent] at hP
    simpa [expo_weight, mul_comm] using (Finset.mem_filter.mp hP).2
  have hqWeight : (ρ : ℤ) * uQ + σ * vQ = vDeg ρ σ Q.1 := by
    change expo uQ vQ ∈
      (MvPolynomial.weightedHomogeneousComponent (wt ρ σ)
        (vDeg ρ σ Q.1) (symbol Q.1)).support at hQ
    rw [MvPolynomial.support_weightedHomogeneousComponent] at hQ
    simpa [expo_weight, mul_comm] using (Finset.mem_filter.mp hQ).2
  have hxZ : (n : ℤ) * uP = (m : ℤ) * uQ := by exact_mod_cast hx
  have hyZ : (n : ℤ) * vP = (m : ℤ) * vQ := by exact_mod_cast hy
  rw [← hpWeight, ← hqWeight]
  calc
    (ρ * (uP : ℤ) + σ * (vP : ℤ)) * (n : ℤ) =
        ρ * ((n : ℤ) * uP) + σ * ((n : ℤ) * vP) := by ring
    _ = ρ * ((m : ℤ) * uQ) + σ * ((m : ℤ) * vQ) := by rw [hxZ, hyZ]
    _ = (ρ * (uQ : ℤ) + σ * (vQ : ℤ)) * (m : ℤ) := by ring

/-- A finite nonzero integer sequence that starts positive and ends
negative has adjacent entries with opposite strict signs. -/
theorem finite_nonzero_grade_chain_crosses (k : ℕ) :
    ∀ g : ℕ → ℤ,
      0 < g 0 → g (k + 1) < 0 →
      (∀ i, 0 < i → i ≤ k + 1 → g i ≠ 0) →
      ∃ j, j ≤ k ∧ 0 < g j ∧ g (j + 1) < 0 := by
  induction k with
  | zero =>
      intro g hfirst hlast _
      exact ⟨0, le_rfl, hfirst, by simpa using hlast⟩
  | succ k ih =>
      intro g hfirst hlast hnonzero
      by_cases hnext : g 1 < 0
      · exact ⟨0, by omega, hfirst, by simpa using hnext⟩
      · have hnextNonzero : g 1 ≠ 0 := hnonzero 1 (by omega) (by omega)
        have hnextPos : 0 < g 1 := by omega
        obtain ⟨j, hj, hjpos, hjneg⟩ :=
          ih (fun i => g (i + 1)) hnextPos (by simpa [Nat.add_assoc] using hlast)
            (by
              intro i hi hik
              exact hnonzero (i + 1) (by omega) (by omega))
        exact ⟨j + 1, by omega, hjpos, by simpa [Nat.add_assoc] using hjneg⟩

/-- The endpoint-link version used after constructing the ordered
Newton-direction chain. Indices `1,...,k` label genuine faces; index
`k+1` is the terminal starting vertex. -/
theorem finite_direction_chain_has_strict_crossing
    (k : ℕ) (startGrade endGrade : ℕ → ℤ)
    (hk : 0 < k)
    (hfirst : 0 < startGrade 1)
    (hlast : startGrade (k + 1) < 0)
    (hlink : ∀ j, 1 ≤ j → j ≤ k → endGrade j = startGrade (j + 1))
    (hnonzero : ∀ j, 1 ≤ j → j ≤ k → endGrade j ≠ 0) :
    ∃ j, 1 ≤ j ∧ j ≤ k ∧ 0 < startGrade j ∧ endGrade j < 0 := by
  obtain ⟨j, hj, hjpos, hjneg⟩ :=
    finite_nonzero_grade_chain_crosses (k - 1) (fun i => startGrade (i + 1))
      (by simpa using hfirst)
      (by simpa [Nat.sub_add_cancel hk] using hlast)
      (by
        intro i hi hik
        have hbound : i ≤ k := by omega
        rw [← hlink i (by omega) hbound]
        exact hnonzero i (by omega) hbound)
  refine ⟨j + 1, by omega, by omega, hjpos, ?_⟩
  rw [hlink (j + 1) (by omega) (by omega)]
  simpa [Nat.add_assoc] using hjneg

end Dixmier.Weyl
