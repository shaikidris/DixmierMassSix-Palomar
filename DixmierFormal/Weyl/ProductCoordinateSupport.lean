module

public import DixmierFormal.Weyl.Validation
public import DixmierFormal.Weyl.LeadingMate

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Coordinate support bounds for Weyl products

Each nonzero product coefficient originates from one pair of input PBW
monomials and a contraction. Both output coordinates are at most the sums
of the corresponding input coordinates.
-/
set_option maxHeartbeats 0
namespace Dixmier.Weyl
open MvPolynomial Polynomial

 theorem symbol_mul_coordinate_le (P Q : A1 ℂ) (a b c d : ℕ)
    (hP : ∀ e ∈ (symbol P.val).support, e 0 ≤ a ∧ e 1 ≤ b)
    (hQ : ∀ e ∈ (symbol Q.val).support, e 0 ≤ c ∧ e 1 ≤ d) :
    ∀ e ∈ (symbol ((P * Q : A1 ℂ).val)).support, e 0 ≤ a + c ∧ e 1 ≤ b + d := by
  intro e he
  obtain ⟨u,hu,v,hv,hx,hy⟩ := symbol_mul_coordinate_bounds P Q e he
  have hp := hP u hu
  have hq := hQ v hv
  constructor <;> omega

 theorem symbol_pow_coordinate_le (P : A1 ℂ) (a b : ℕ)
    (hP : ∀ e ∈ (symbol P.val).support, e 0 ≤ a ∧ e 1 ≤ b) (n : ℕ) :
    ∀ e ∈ (symbol ((P^n : A1 ℂ).val)).support, e 0 ≤ n * a ∧ e 1 ≤ n * b := by
  induction n with
  | zero =>
    intro e he
    simp only [pow_zero,symbol_one_A1,MvPolynomial.support_one,Finset.mem_singleton] at he
    subst e
    simp
  | succ n ih =>
    rw [pow_succ]
    have h := symbol_mul_coordinate_le (P^n) P (n * a) (n * b) a b ih hP
    simpa only [Nat.succ_mul] using h

 theorem symbol_word_coordinate_le (P Q : A1 ℂ) (a b c d i j : ℕ)
    (hP : ∀ e ∈ (symbol P.val).support, e 0 ≤ a ∧ e 1 ≤ b)
    (hQ : ∀ e ∈ (symbol Q.val).support, e 0 ≤ c ∧ e 1 ≤ d) :
    ∀ e ∈ (symbol ((P^i * Q^j : A1 ℂ).val)).support,
      e 0 ≤ i * a + j * c ∧ e 1 ≤ i * b + j * d :=
  symbol_mul_coordinate_le (P^i) (Q^j) (i * a) (i * b) (j * c) (j * d)
    (symbol_pow_coordinate_le P a b hP i) (symbol_pow_coordinate_le Q c d hQ j)

end Dixmier.Weyl
