/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedFullWeightFilter

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# A unique extremal first-contraction atom pair on a Newton face

At the output derivative order determined by the maximal derivative
indices on the two top-weight faces, every other atom pair has zero
coefficient at the selected first-contraction weight. Thus the finite
commutator sum reduces to a single pair without an order cutoff.
-/

namespace Dixmier.Weyl

theorem ramifiedPBWCoeffs_face_endpoint_single_pair
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (B C : ℕ → ℤ) (A D : ℤ)
    (N M j : ℕ) (v : ℤ)
    (hN : N ∈ (ramifiedPBWCoeffs l hl P).support)
    (hM : M ∈ (ramifiedPBWCoeffs l hl Q).support)
    (hfirst : j+1 = N+M)
    (hBP : ∀ n ∈ (ramifiedPBWCoeffs l hl P).support,
      LaurentUpper ((ramifiedPBWCoeffs l hl P) n) (B n))
    (hCQ : ∀ m ∈ (ramifiedPBWCoeffs l hl Q).support,
      LaurentUpper ((ramifiedPBWCoeffs l hl Q) m) (C m))
    (hP : ∀ n ∈ (ramifiedPBWCoeffs l hl P).support,
      ρ*(B n) + (l : ℤ)*σ*(n : ℤ) ≤ A)
    (hQ : ∀ m ∈ (ramifiedPBWCoeffs l hl Q).support,
      ρ*(C m) + (l : ℤ)*σ*(m : ℤ) ≤ D)
    (hNmax : ∀ n ∈ (ramifiedPBWCoeffs l hl P).support,
      ρ*(B n) + (l : ℤ)*σ*(n : ℤ) = A → n ≤ N)
    (hMmax : ∀ m ∈ (ramifiedPBWCoeffs l hl Q).support,
      ρ*(C m) + (l : ℤ)*σ*(m : ℤ) = D → m ≤ M)
    (hv : A+D-(l : ℤ)*(ρ+σ) ≤ ramifiedWeight l ρ σ (v,j)) :
    ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) j).coeff v =
      (ramifiedPBWCoeffs l hl
        ((ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl P) N) *
            (ramifiedYGen l)^N) *
            (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl Q) M) *
              (ramifiedYGen l)^M) -
          (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl Q) M) *
            (ramifiedYGen l)^M) *
            (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl P) N) *
              (ramifiedYGen l)^N)) j).coeff v := by
  classical
  let F : ℕ → ℕ → LaurentPolynomial ℂ := fun n m =>
    ramifiedPBWCoeffs l hl
      ((ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl P) n) *
          (ramifiedYGen l)^n) *
          (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl Q) m) *
            (ramifiedYGen l)^m) -
        (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl Q) m) *
          (ramifiedYGen l)^m) *
          (ramifiedCoeffGen l ((ramifiedPBWCoeffs l hl P) n) *
            (ramifiedYGen l)^n)) j
  have hzero (n m : ℕ)
      (hn : n ∈ (ramifiedPBWCoeffs l hl P).support)
      (hm : m ∈ (ramifiedPBWCoeffs l hl Q).support)
      (hne : n ≠ N ∨ m ≠ M) : (F n m).coeff v = 0 := by
    by_cases htop : n+m ≤ j
    · have hz := ramifiedPBWCoeffs_atomCommutator_zero_at_or_above
        l hl ((ramifiedPBWCoeffs l hl P) n)
        ((ramifiedPBWCoeffs l hl Q) m) n m j htop
      simp [F, hz]
    · have hc : j+1 ≤ n+m := by omega
      have hdefect :
          ρ*(B n) + (l : ℤ)*σ*(n : ℤ) < A ∨
          ρ*(C m) + (l : ℤ)*σ*(m : ℤ) < D ∨
          j+2 ≤ n+m := by
        by_cases hp : ρ*(B n) + (l : ℤ)*σ*(n : ℤ) < A
        · exact Or.inl hp
        by_cases hq : ρ*(C m) + (l : ℤ)*σ*(m : ℤ) < D
        · exact Or.inr (Or.inl hq)
        have hpEq : ρ*(B n) + (l : ℤ)*σ*(n : ℤ) = A := by
          have := hP n hn
          omega
        have hqEq : ρ*(C m) + (l : ℤ)*σ*(m : ℤ) = D := by
          have := hQ m hm
          omega
        have hnle := hNmax n hn hpEq
        have hmle := hMmax m hm hqEq
        have hnEq : n = N := by omega
        have hmEq : m = M := by omega
        exact False.elim (hne.elim (fun h => h hnEq) (fun h => h hmEq))
      by_contra hnz
      have hsupp : v ∈ (F n m).coeff.support :=
        Finsupp.mem_support_iff.mpr hnz
      have hbelow := ramifiedPBWCoeffs_atomCommutator_below_first_of_defect_all
        l hl ρ σ hρ hsum
        ((ramifiedPBWCoeffs l hl P) n)
        ((ramifiedPBWCoeffs l hl Q) m)
        (B n) (C m) A D (hBP n hn) (hCQ m hm)
        n m j hc (hP n hn) (hQ m hm) hdefect v hsupp
      exact (not_lt_of_ge hv) hbelow
  have hinner : (∑ m ∈ (ramifiedPBWCoeffs l hl Q).support,
      (F N m).coeff v) = (F N M).coeff v := by
    apply Finset.sum_eq_single M
    · intro m hm hmne
      exact hzero N m hN hm (Or.inr hmne)
    · intro hmnot
      exact False.elim (hmnot hM)
  have houter : (∑ n ∈ (ramifiedPBWCoeffs l hl P).support,
      ∑ m ∈ (ramifiedPBWCoeffs l hl Q).support,
        (F n m).coeff v) =
      ∑ m ∈ (ramifiedPBWCoeffs l hl Q).support,
        (F N m).coeff v := by
    apply Finset.sum_eq_single N
    · intro n hn hnne
      apply Finset.sum_eq_zero
      intro m hm
      exact hzero n m hn hm (Or.inl hnne)
    · intro hnnot
      exact False.elim (hnnot hN)
  rw [ramifiedPBWCoeffs_commutator_double_sum]
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  change (∑ n ∈ (ramifiedPBWCoeffs l hl P).support,
      ∑ m ∈ (ramifiedPBWCoeffs l hl Q).support,
        (F n m).coeff v) = (F N M).coeff v
  exact houter.trans hinner

/-- The selected Newton-face endpoint coefficient of the **full**
commutator is the determinant coefficient of its unique maximal face
atom pair. This is the no-cancellation formula. -/
theorem ramifiedPBWCoeffs_face_endpoint_extremal
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (B C : ℕ → ℤ) (A D : ℤ) (n m : ℕ)
    (hN : n+1 ∈ (ramifiedPBWCoeffs l hl P).support)
    (hM : m ∈ (ramifiedPBWCoeffs l hl Q).support)
    (hBP : ∀ a ∈ (ramifiedPBWCoeffs l hl P).support,
      LaurentUpper ((ramifiedPBWCoeffs l hl P) a) (B a))
    (hCQ : ∀ b ∈ (ramifiedPBWCoeffs l hl Q).support,
      LaurentUpper ((ramifiedPBWCoeffs l hl Q) b) (C b))
    (hP : ∀ a ∈ (ramifiedPBWCoeffs l hl P).support,
      ρ*(B a) + (l : ℤ)*σ*(a : ℤ) ≤ A)
    (hQ : ∀ b ∈ (ramifiedPBWCoeffs l hl Q).support,
      ρ*(C b) + (l : ℤ)*σ*(b : ℤ) ≤ D)
    (hNmax : ∀ a ∈ (ramifiedPBWCoeffs l hl P).support,
      ρ*(B a) + (l : ℤ)*σ*(a : ℤ) = A → a ≤ n+1)
    (hMmax : ∀ b ∈ (ramifiedPBWCoeffs l hl Q).support,
      ρ*(C b) + (l : ℤ)*σ*(b : ℤ) = D → b ≤ m)
    (hNtop : ρ*(B (n+1)) + (l : ℤ)*σ*((n+1 : ℕ) : ℤ) = A)
    (hMtop : ρ*(C m) + (l : ℤ)*σ*(m : ℤ) = D)
    (hfi : B (n+1) ∈
      ((ramifiedPBWCoeffs l hl P) (n+1)).coeff.support)
    (hgu : C m ∈ ((ramifiedPBWCoeffs l hl Q) m).coeff.support) :
    ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) (n+m)).coeff
        (B (n+1)+C m-(l : ℤ)) =
      (((n+1 : ℂ) * ((C m : ℤ) : ℂ) -
          (m : ℂ) * ((B (n+1) : ℤ) : ℂ)) / (l : ℂ)) *
        ((ramifiedPBWCoeffs l hl P) (n+1)).coeff (B (n+1)) *
        ((ramifiedPBWCoeffs l hl Q) m).coeff (C m) := by
  have hweight : A+D-(l : ℤ)*(ρ+σ) ≤
      ramifiedWeight l ρ σ
        (B (n+1)+C m-(l : ℤ), n+m) := by
    unfold ramifiedWeight
    simp only [Nat.cast_add]
    rw [← hNtop, ← hMtop]
    push_cast
    apply le_of_eq
    ring
  rw [ramifiedPBWCoeffs_face_endpoint_single_pair
    l hl ρ σ hρ hsum P Q B C A D (n+1) m (n+m)
    (B (n+1)+C m-(l : ℤ)) hN hM (by omega)
    hBP hCQ hP hQ hNmax hMmax hweight]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (ramifiedPBWCoeffs_atomCommutator_first_extremal
      l hl ((ramifiedPBWCoeffs l hl P) (n+1))
      ((ramifiedPBWCoeffs l hl Q) m)
      (B (n+1)) (C m) n m
      (hBP (n+1) hN) (hCQ m hM) hfi hgu)

/-- For a commutator-one pair, a positive-order extremal
first-contraction Newton coefficient must have zero determinant.
The uniqueness of its contributing face atom pair is proved above. -/
theorem ramified_exact_pair_face_endpoint_determinant_zero
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (B C : ℕ → ℤ) (A D : ℤ) (n m : ℕ)
    (hcomm : P*Q-Q*P = 1) (hpositive : 0 < n+m)
    (hN : n+1 ∈ (ramifiedPBWCoeffs l hl P).support)
    (hM : m ∈ (ramifiedPBWCoeffs l hl Q).support)
    (hBP : ∀ a ∈ (ramifiedPBWCoeffs l hl P).support,
      LaurentUpper ((ramifiedPBWCoeffs l hl P) a) (B a))
    (hCQ : ∀ b ∈ (ramifiedPBWCoeffs l hl Q).support,
      LaurentUpper ((ramifiedPBWCoeffs l hl Q) b) (C b))
    (hP : ∀ a ∈ (ramifiedPBWCoeffs l hl P).support,
      ρ*(B a) + (l : ℤ)*σ*(a : ℤ) ≤ A)
    (hQ : ∀ b ∈ (ramifiedPBWCoeffs l hl Q).support,
      ρ*(C b) + (l : ℤ)*σ*(b : ℤ) ≤ D)
    (hNmax : ∀ a ∈ (ramifiedPBWCoeffs l hl P).support,
      ρ*(B a) + (l : ℤ)*σ*(a : ℤ) = A → a ≤ n+1)
    (hMmax : ∀ b ∈ (ramifiedPBWCoeffs l hl Q).support,
      ρ*(C b) + (l : ℤ)*σ*(b : ℤ) = D → b ≤ m)
    (hNtop : ρ*(B (n+1)) + (l : ℤ)*σ*((n+1 : ℕ) : ℤ) = A)
    (hMtop : ρ*(C m) + (l : ℤ)*σ*(m : ℤ) = D)
    (hfi : B (n+1) ∈
      ((ramifiedPBWCoeffs l hl P) (n+1)).coeff.support)
    (hgu : C m ∈ ((ramifiedPBWCoeffs l hl Q) m).coeff.support) :
    (n+1 : ℂ) * ((C m : ℤ) : ℂ) -
      (m : ℂ) * ((B (n+1) : ℤ) : ℂ) = 0 := by
  have hcoeff := ramifiedPBWCoeffs_face_endpoint_extremal
    l hl ρ σ hρ hsum P Q B C A D n m
    hN hM hBP hCQ hP hQ hNmax hMmax hNtop hMtop hfi hgu
  have hz : ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) (n+m)).coeff
      (B (n+1)+C m-(l : ℤ)) = 0 := by
    rw [hcomm, ramifiedPBWCoeffs_one_at_positive_order l hl (n+m) hpositive]
    simp
  rw [hz] at hcoeff
  have hfi_ne : ((ramifiedPBWCoeffs l hl P) (n+1)).coeff (B (n+1)) ≠ 0 :=
    Finsupp.mem_support_iff.mp hfi
  have hgu_ne : ((ramifiedPBWCoeffs l hl Q) m).coeff (C m) ≠ 0 :=
    Finsupp.mem_support_iff.mp hgu
  have hl_ne : (l : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hl
  rcases mul_eq_zero.mp hcoeff.symm with hleft | hright
  · rcases mul_eq_zero.mp hleft with hdiv | hfi_zero
    · exact (div_eq_zero_iff).mp hdiv |>.resolve_right hl_ne
    · exact False.elim (hfi_ne hfi_zero)
  · exact False.elim (hgu_ne hright)

end Dixmier.Weyl
