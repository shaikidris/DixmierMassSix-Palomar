/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVPairedEndpointRatio
public import DixmierFormal.Weyl.GGVDirectionGradeChain

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The same weight ratio on successive negative faces

The vertices shared by consecutive faces of each exact-pair member are
proportional across the pair. Because those vertices lie on both faces,
the same reduced numerator and denominator relate the two weighted
degrees at each direction.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- Proportional occupied points on both common faces transfer one
ratio simultaneously to the two pairs of weighted degrees. -/
theorem paired_face_points_common_weight_ratio
    (P Q : A1 ℂ) (ρ₁ σ₁ ρ₂ σ₂ : ℤ)
    (a b : Fin 2 →₀ ℕ) (n d : ℕ)
    (ha₁ : a ∈ (leadingForm ρ₁ σ₁ P.1).support)
    (ha₂ : a ∈ (leadingForm ρ₂ σ₂ P.1).support)
    (hb₁ : b ∈ (leadingForm ρ₁ σ₁ Q.1).support)
    (hb₂ : b ∈ (leadingForm ρ₂ σ₂ Q.1).support)
    (hx : n * a 0 = d * b 0)
    (hy : n * a 1 = d * b 1) :
    vDeg ρ₁ σ₁ P.1 * (n : ℤ) = vDeg ρ₁ σ₁ Q.1 * (d : ℤ) ∧
    vDeg ρ₂ σ₂ P.1 * (n : ℤ) = vDeg ρ₂ σ₂ Q.1 * (d : ℤ) := by
  obtain ⟨⟨uP, vP⟩, rfl⟩ := expo_surjective a
  obtain ⟨⟨uQ, vQ⟩, rfl⟩ := expo_surjective b
  have hx' : n * uP = d * uQ := by simpa [expo] using hx
  have hy' : n * vP = d * vQ := by simpa [expo] using hy
  exact ⟨
    proportional_leadingFace_endpoints_weight_ratio
      P Q ρ₁ σ₁ uP vP uQ vQ d n ha₁ hb₁ hx' hy',
    proportional_leadingFace_endpoints_weight_ratio
      P Q ρ₂ σ₂ uP vP uQ vQ d n ha₂ hb₂ hx' hy'⟩

/-- The two consecutive actual strict-negative directions of a
counterexample pair have one common reduced P:Q weighted-degree ratio.
This is the interior ratio propagation in G13 Proposition 7.2. -/
theorem counterexample_paired_successor_common_weight_ratio
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ₁ s₁ ρ₂ s₂ : ℕ)
    (hρ₁ : 0 < ρ₁) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hdir₁ : IsDirection (ρ₁ : ℤ) (-(s₁ : ℤ)))
    (hdir₂ : IsDirection (ρ₂ : ℤ) (-(s₂ : ℤ)))
    (j : ℕ) (hj : j + 1 < (ggvOrderedNegativeFaceSlopes P).length)
    (hfirst : (ggvOrderedNegativeFaceSlopes P)[j] =
      (-(s₁ : ℤ) : ℚ) / ρ₁)
    (hsecond : (ggvOrderedNegativeFaceSlopes P)[j+1] =
      (-(s₂ : ℤ) : ℚ) / ρ₂)
    (hface₁ : InDir (ρ₁ : ℤ) (-(s₁ : ℤ)) P.1)
    (hface₂ : InDir (ρ₂ : ℤ) (-(s₂ : ℤ)) P.1) :
    ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ Nat.Coprime d n ∧
      vDeg ρ₁ (-(s₁ : ℤ)) P.1 * (n : ℤ) =
        vDeg ρ₁ (-(s₁ : ℤ)) Q.1 * (d : ℤ) ∧
      vDeg ρ₂ (-(s₂ : ℤ)) P.1 * (n : ℤ) =
        vDeg ρ₂ (-(s₂ : ℤ)) Q.1 * (d : ℤ) := by
  obtain ⟨a, b, n, d, ha₁, ha₂, hb₁, hb₂, hn, hd, hcop, hx, hy⟩ :=
    counterexample_paired_successor_proportional_vertices
      P Q hpair ρ₁ s₁ ρ₂ s₂ hρ₁ hs₁ hs₂ hdir₁ hdir₂
      j hj hfirst hsecond hface₁ hface₂
  obtain ⟨hweight₁, hweight₂⟩ :=
    paired_face_points_common_weight_ratio P Q
      (ρ₁ : ℤ) (-(s₁ : ℤ)) (ρ₂ : ℤ) (-(s₂ : ℤ))
      a b n d ha₁ ha₂ hb₁ hb₂ hx hy
  exact ⟨n, d, hn, hd, hcop, hweight₁, hweight₂⟩

end Dixmier.Weyl
