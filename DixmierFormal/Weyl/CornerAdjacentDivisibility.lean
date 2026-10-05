/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CornerDirectionArithmetic
public import DixmierFormal.Weyl.RamifiedPBWData

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Divisibility from adjacent points on a ramified Newton face

This is the lattice calculation in the first branch of G13 Proposition
5.6, equation (5.41). Two monomials in A₁^(l) on one (ρ,σ)-face whose
derivative orders differ by one force ρ ∣ l when the direction is
primitive.
-/

namespace Dixmier.Weyl

theorem ramified_adjacent_face_first_coordinate_dvd_index
    (l : ℕ) (ρ σ i i' : ℤ) (j : ℕ)
    (hdir : IsDirection ρ σ)
    (hweight : ρ*i + (l : ℤ)*σ*(j : ℤ) =
      ρ*i' + (l : ℤ)*σ*((j+1 : ℕ) : ℤ)) :
    ρ ∣ (l : ℤ) := by
  have hcop : IsCoprime ρ σ :=
    Int.isCoprime_iff_gcd_eq_one.mpr hdir.1
  have hdiv : ρ ∣ σ * (l : ℤ) := by
    refine ⟨i-i', ?_⟩
    push_cast at hweight
    nlinarith [hweight]
  exact hcop.dvd_of_dvd_mul_left hdiv

/-- The same calculation for actual PBW exponent pairs on a common
ramified face. Only face-weight equality and one adjacent derivative
step are needed; no order or mass cutoff is imposed. -/
theorem ramified_adjacent_PBW_face_rho_dvd_index
    (l : ℕ) (ρ σ : ℤ) (E F : ℤ × ℕ)
    (hdir : IsDirection ρ σ)
    (hadj : F.2 = E.2 + 1)
    (hweight : ramifiedWeight l ρ σ E = ramifiedWeight l ρ σ F) :
    ρ ∣ (l : ℤ) := by
  have hraw : ρ*E.1 + (l : ℤ)*σ*(E.2 : ℤ) =
      ρ*F.1 + (l : ℤ)*σ*((E.2+1 : ℕ) : ℤ) := by
    simpa only [ramifiedWeight, hadj] using hweight
  exact ramified_adjacent_face_first_coordinate_dvd_index
    l ρ σ E.1 F.1 E.2 hdir hraw

end Dixmier.Weyl
