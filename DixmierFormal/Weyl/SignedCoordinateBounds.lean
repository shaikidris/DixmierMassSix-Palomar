module

public import DixmierFormal.Weyl.ProductCoordinateSupport

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Signed-weight bounds from PBW coordinate bounds

A rectangle in nonnegative exponent coordinates gives a finite interval for
any signed weight, including negative variable weights. Word rectangles
therefore yield bounds linear in the two word exponents.
-/
set_option maxHeartbeats 0
namespace Dixmier.Weyl
open Polynomial

 theorem signed_weight_abs_le_coordinates (ρ σ : ℤ) (e : Fin 2 →₀ ℕ)
    (a b : ℕ) (hx : e 0 ≤ a) (hy : e 1 ≤ b) :
    |Finsupp.weight (wt ρ σ) e| ≤ |ρ| * (a : ℤ) + |σ| * (b : ℤ) := by
  have hw : Finsupp.weight (wt ρ σ) e = ρ * (e 0 : ℤ) + σ * (e 1 : ℤ) := by
    obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective e
    simp [Finsupp.weight_eq_sum,wt,expo]
    ring
  rw [hw]
  calc
    |ρ * (e 0 : ℤ) + σ * (e 1 : ℤ)| ≤ |ρ * (e 0 : ℤ)| + |σ * (e 1 : ℤ)| := abs_add_le _ _
    _ = |ρ| * (e 0 : ℤ) + |σ| * (e 1 : ℤ) := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : (0 : ℤ) ≤ e 0),
        abs_of_nonneg (by positivity : (0 : ℤ) ≤ e 1)]
    _ ≤ |ρ| * (a : ℤ) + |σ| * (b : ℤ) :=
      add_le_add (mul_le_mul_of_nonneg_left (by exact_mod_cast hx) (abs_nonneg ρ))
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hy) (abs_nonneg σ))

 theorem symbol_word_signed_weight_abs_le
    (P Q : A1 ℂ) (ρ σ : ℤ) (a b c d i j : ℕ)
    (hP : ∀ e ∈ (symbol P.val).support, e 0 ≤ a ∧ e 1 ≤ b)
    (hQ : ∀ e ∈ (symbol Q.val).support, e 0 ≤ c ∧ e 1 ≤ d) :
    ∀ e ∈ (symbol ((P^i * Q^j : A1 ℂ).val)).support,
      |Finsupp.weight (wt ρ σ) e| ≤
        |ρ| * ((i * a + j * c : ℕ) : ℤ) + |σ| * ((i * b + j * d : ℕ) : ℤ) := by
  intro e he
  have h := symbol_word_coordinate_le P Q a b c d i j hP hQ e he
  exact signed_weight_abs_le_coordinates ρ σ e _ _ h.1 h.2

 theorem pair_symbol_coordinate_bound_exists (P Q : A1 ℂ) :
    ∃ D : ℕ,
      (∀ e ∈ (symbol P.val).support, e 0 ≤ D ∧ e 1 ≤ D) ∧
      (∀ e ∈ (symbol Q.val).support, e 0 ≤ D ∧ e 1 ≤ D) := by
  classical
  let I := (symbol P.val).support ∪ (symbol Q.val).support
  let D := I.sup (fun e => max (e 0) (e 1))
  have hb : ∀ e ∈ I, e 0 ≤ D ∧ e 1 ≤ D := by
    intro e he
    have hm : max (e 0) (e 1) ≤ D := Finset.le_sup (f := fun e => max (e 0) (e 1)) he
    exact ⟨(le_max_left _ _).trans hm,(le_max_right _ _).trans hm⟩
  refine ⟨D,?_,?_⟩
  · intro e he
    exact hb e (Finset.mem_union_left _ he)
  · intro e he
    exact hb e (Finset.mem_union_right _ he)

end Dixmier.Weyl
