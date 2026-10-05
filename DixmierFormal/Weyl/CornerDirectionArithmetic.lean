/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CornerEndpointGrades

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Terminal direction arithmetic for the polynomial corner cut

G13 Proposition 5.6 uses a descent in ramified Weyl algebras. For the
polynomial algebra, the ramification index is one. Once the source cut
establishes `ρ ∣ 1`, a positive-sum direction with nonpositive second
coordinate is necessarily horizontal, so a second strictly lower
direction with the same divisibility cannot exist.
-/

namespace Dixmier.Weyl

/-- A primitive positive-sum direction below or at horizontal whose first
coordinate divides one is exactly horizontal. -/
theorem polynomial_corner_direction_horizontal
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hσ : σ ≤ 0) (hdiv : ρ ∣ (1 : ℤ)) :
    ρ = 1 ∧ σ = 0 := by
  have hρpos : 0 < ρ := by
    have := hdir.2
    omega
  have hρone : ρ = 1 := by
    rcases hdiv with ⟨k, hk⟩
    have hρle : ρ ≤ 1 := by
      have hknz : k ≠ 0 := by
        intro hz
        simp [hz] at hk
      rcases lt_or_gt_of_ne hknz with hkneg | hkpos
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt hρpos) (le_of_lt hkneg)]
      · nlinarith [mul_le_mul_of_nonneg_left (show 1 ≤ k by omega)
          (le_of_lt hρpos)]
    omega
  constructor
  · exact hρone
  · have := hdir.2
    omega

/-- Thus two such directions cannot be related by a strict decrease in
their second coordinate. This is the finite-descent endpoint for `l=1`. -/
theorem polynomial_corner_no_lower_dividing_one
    (ρ σ ρ' σ' : ℤ)
    (hdir : IsDirection ρ σ) (hσ : σ ≤ 0) (hdiv : ρ ∣ (1 : ℤ))
    (hdir' : IsDirection ρ' σ') (hσ' : σ' ≤ 0) (hdiv' : ρ' ∣ (1 : ℤ))
    (hlower : σ' < σ) : False := by
  have h₁ := polynomial_corner_direction_horizontal ρ σ hdir hσ hdiv
  have h₂ := polynomial_corner_direction_horizontal ρ' σ' hdir' hσ' hdiv'
  omega

end Dixmier.Weyl
