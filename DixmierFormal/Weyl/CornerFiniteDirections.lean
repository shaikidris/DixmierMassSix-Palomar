/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CornerAdjacentDivisibility
public import Mathlib.Data.Finite.Set
public import Mathlib.Order.Monotone.Basic

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Finiteness of directions in the G13 corner descent

For fixed positive ramification index l, there are only finitely many
primitive directions (ρ,σ) with ρ ∣ l, σ ≤ 0 and ρ+σ > 0.
This is the finite-descent endpoint of G13 Proposition 5.6, separated
from the harder operator step that produces the next direction.
-/

namespace Dixmier.Weyl

def cornerAdmissibleDirections (l : ℕ) : Set (ℤ × ℤ) :=
  {v | IsDirection v.1 v.2 ∧ v.2 ≤ 0 ∧ v.1 ∣ (l : ℤ)}

theorem cornerAdmissibleDirections_finite (l : ℕ) (hl : 0 < l) :
    (cornerAdmissibleDirections l).Finite := by
  have hbox : (Set.Icc (1 : ℤ) (l : ℤ) ×ˢ
      Set.Icc (1 - (l : ℤ)) 0).Finite :=
    (Set.finite_Icc (1 : ℤ) (l : ℤ)).prod
      (Set.finite_Icc (1 - (l : ℤ)) 0)
  apply hbox.subset
  rintro ⟨ρ,σ⟩ ⟨hdir,hσ,hdiv⟩
  have hρpos : 0 < ρ := by
    have hsum := hdir.2
    omega
  rcases hdiv with ⟨k,hk⟩
  dsimp at hk
  have hlZ : (0 : ℤ) < l := by exact_mod_cast hl
  have hkpos : 0 < k := by
    by_contra hnot
    have hk0 : k ≤ 0 := by omega
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hρpos) hk0
    omega
  have hρle : ρ ≤ (l : ℤ) := by
    have hnonneg := mul_nonneg (le_of_lt hρpos)
      (show (0 : ℤ) ≤ k-1 by omega)
    nlinarith [hk]
  constructor
  · exact ⟨by omega, hρle⟩
  · have hsum := hdir.2
    exact ⟨by omega, hσ⟩

/-- A fixed positive ramification index admits no infinite strict
decrease in the rational slopes of admissible directions. -/
theorem corner_no_infinite_descending_directions
    (l : ℕ) (hl : 0 < l) (v : ℕ → ℤ × ℤ)
    (hv : ∀ n, v n ∈ cornerAdmissibleDirections l)
    (hdesc : ∀ n, ((v (n+1)).2 : ℚ) / ((v (n+1)).1 : ℚ) <
      ((v n).2 : ℚ) / ((v n).1 : ℚ)) : False := by
  let slope : ℤ × ℤ → ℚ := fun p => (p.2 : ℚ) / (p.1 : ℚ)
  have hsanti : StrictAnti (fun n => slope (v n)) :=
    strictAnti_nat_of_succ_lt hdesc
  have hinj : Function.Injective v := by
    intro a b hab
    exact hsanti.injective (congrArg slope hab)
  have hrange : (Set.range v).Finite :=
    (cornerAdmissibleDirections_finite l hl).subset
      (by rintro p ⟨n,rfl⟩; exact hv n)
  letI : Finite (Set.range v) := hrange.to_subtype
  haveI : Finite ℕ := Finite.of_injective_finite_range hinj
  exact not_finite ℕ

/-- Source-facing finite-descent assembly: a nonempty family of
admissible corner directions cannot be closed under a strictly lower
successor. The operator-level corner-preserving successor remains a
separate obligation. -/
theorem corner_no_total_lower_successor
    (l : ℕ) (hl : 0 < l) (S : Set (ℤ × ℤ))
    (hS : S ⊆ cornerAdmissibleDirections l)
    (hne : S.Nonempty)
    (hstep : ∀ v ∈ S, ∃ w ∈ S,
      ((w.2 : ℚ) / (w.1 : ℚ)) <
        ((v.2 : ℚ) / (v.1 : ℚ))) : False := by
  let slope : ℤ × ℤ → ℚ := fun p => (p.2 : ℚ) / (p.1 : ℚ)
  have hfinite : S.Finite :=
    (cornerAdmissibleDirections_finite l hl).subset hS
  obtain ⟨v,hv,hmin⟩ := Set.exists_min_image S slope hfinite hne
  obtain ⟨w,hw,hlower⟩ := hstep v hv
  exact (not_lt_of_ge (hmin w hw)) hlower

end Dixmier.Weyl
