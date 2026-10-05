module

public import DixmierFormal.Weyl.RamifiedWeightComponents
public import DixmierFormal.Weyl.RamifiedFaceCentralizerLine
public import DixmierFormal.Weyl.FiniteFiltrationRank
public import Mathlib.Algebra.Module.NatInt

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Finite signed-weight filtrations of ramified operator subspaces

The exact coefficient maps retain cancellations inside an arbitrary finite
subspace. A common signed-support interval and one-dimensional homogeneous
centralizer images bound the entire subspace by the length of that interval.
-/

namespace Dixmier.Weyl
open Polynomial

noncomputable local instance ramifiedSubspaceAddCommGroup (l : ℕ)
    (S : Submodule ℂ (ramifiedOperatorAlgebra l)) : AddCommGroup S :=
  Module.addCommMonoidToAddCommGroup ℂ

noncomputable def ramifiedRestrictedWeightBelow
    (l : ℕ) (hl : 0 < l) (S : Submodule ℂ (ramifiedOperatorAlgebra l))
    (ρ σ b : ℤ) : Submodule ℂ S :=
  (ramifiedWeightBelow l hl ρ σ b).comap S.subtype

noncomputable def ramifiedRestrictedWeightComponent
    (l : ℕ) (hl : 0 < l) (S : Submodule ℂ (ramifiedOperatorAlgebra l))
    (ρ σ b : ℤ) : S →ₗ[ℂ] ℂ[X] :=
  (ramifiedWeightComponent l hl ρ σ b).comp S.subtype

theorem ramifiedRestrictedWeightBelow_mono
    (l : ℕ) (hl : 0 < l) (S : Submodule ℂ (ramifiedOperatorAlgebra l))
    (ρ σ : ℤ) {b d : ℤ} (hbd : b ≤ d) :
    ramifiedRestrictedWeightBelow l hl S ρ σ b ≤
      ramifiedRestrictedWeightBelow l hl S ρ σ d := by
  intro T hT
  exact ramifiedWeightBelow_mono l hl ρ σ hbd hT

theorem ramifiedRestrictedWeightComponent_kernel
    (l : ℕ) (hl : 0 < l) (S : Submodule ℂ (ramifiedOperatorAlgebra l))
    (ρ σ b : ℤ) (hρ : 0 < ρ) :
    LinearMap.ker ((ramifiedRestrictedWeightComponent l hl S ρ σ b).domRestrict
      (ramifiedRestrictedWeightBelow l hl S ρ σ (b+1))) =
      (ramifiedRestrictedWeightBelow l hl S ρ σ b).comap
        (ramifiedRestrictedWeightBelow l hl S ρ σ (b+1)).subtype := by
  ext T
  change ramifiedWeightComponent l hl ρ σ b T.val.val = 0 ↔
    ∀ i j, b ≤ ramifiedWeight l ρ σ (i,j) →
      ((ramifiedPBWCoeffs l hl T.val.val) j).coeff i = 0
  rw [ramifiedWeightComponent_eq_zero_iff l hl ρ σ b hρ T.val.val]
  constructor
  · intro hz i j hi
    by_cases he : ramifiedWeight l ρ σ (i,j) = b
    · exact hz i j he
    · exact T.property i j (by omega)
  · intro hz i j he
    exact hz i j (by omega)

theorem ramifiedRestrictedWeightBelow_eq_bot
    (l : ℕ) (hl : 0 < l) (S : Submodule ℂ (ramifiedOperatorAlgebra l))
    (ρ σ b : ℤ)
    (hlo : ∀ T : S, ∀ i j, ramifiedWeight l ρ σ (i,j) < b →
      ((ramifiedPBWCoeffs l hl T.val) j).coeff i = 0) :
    ramifiedRestrictedWeightBelow l hl S ρ σ b = ⊥ := by
  apply le_antisymm _ bot_le
  intro T hT
  change T = 0
  apply Subtype.ext
  apply (ramifiedPBWEquiv l hl).injective
  change ramifiedPBWCoeffs l hl T.val = ramifiedPBWCoeffs l hl 0
  have hz : ramifiedPBWCoeffs l hl 0 = 0 :=
    (ramifiedPBWCoeffsLinear l hl).map_zero
  rw [hz]
  ext j i
  change ((ramifiedPBWCoeffs l hl T.val) j).coeff i = 0
  by_cases he : b ≤ ramifiedWeight l ρ σ (i,j)
  · exact hT i j he
  · exact hlo T i j (by omega)

theorem ramifiedRestrictedWeightBelow_eq_top
    (l : ℕ) (hl : 0 < l) (S : Submodule ℂ (ramifiedOperatorAlgebra l))
    (ρ σ b : ℤ)
    (hhi : ∀ T : S, ∀ i j, b ≤ ramifiedWeight l ρ σ (i,j) →
      ((ramifiedPBWCoeffs l hl T.val) j).coeff i = 0) :
    ramifiedRestrictedWeightBelow l hl S ρ σ b = ⊤ := by
  apply top_unique
  intro T hT
  exact hhi T

theorem ramified_subspace_finrank_le_interval
    (l : ℕ) (hl : 0 < l) (S : Submodule ℂ (ramifiedOperatorAlgebra l))
    [FiniteDimensional ℂ S] (ρ σ b : ℤ) (hρ : 0 < ρ) (N : ℕ)
    (hlo : ∀ T : S, ∀ i j, ramifiedWeight l ρ σ (i,j) < b →
      ((ramifiedPBWCoeffs l hl T.val) j).coeff i = 0)
    (hhi : ∀ T : S, ∀ i j, b+(N:ℤ) ≤ ramifiedWeight l ρ σ (i,j) →
      ((ramifiedPBWCoeffs l hl T.val) j).coeff i = 0)
    (hrank : ∀ k : ℕ, Module.finrank ℂ (LinearMap.range
      ((ramifiedRestrictedWeightComponent l hl S ρ σ (b+(k:ℤ))).domRestrict
        (ramifiedRestrictedWeightBelow l hl S ρ σ (b+((k+1:ℕ):ℤ))))) ≤ 1) :
    Module.finrank ℂ S ≤ N := by
  apply finite_filtration_top_finrank_le
    (fun k => ramifiedRestrictedWeightBelow l hl S ρ σ (b+(k:ℤ)))
    (fun k => ramifiedRestrictedWeightComponent l hl S ρ σ (b+(k:ℤ))) N
  · simpa using ramifiedRestrictedWeightBelow_eq_bot l hl S ρ σ b hlo
  · exact ramifiedRestrictedWeightBelow_eq_top l hl S ρ σ (b+(N:ℤ)) hhi
  · intro k
    apply ramifiedRestrictedWeightBelow_mono
    omega
  · intro k
    have he : b+((k+1:ℕ):ℤ) = b+(k:ℤ)+1 := by omega
    rw [he]
    exact ramifiedRestrictedWeightComponent_kernel l hl S ρ σ (b+(k:ℤ)) hρ
  · exact hrank

set_option maxHeartbeats 800000 in
/-- The fixed-weight centralizer line bounds every successive image, so
the entire finite subspace is bounded by its signed support interval. -/
theorem ramified_filtered_centralizer_finrank_le_interval
    (l : ℕ) (hl : 0 < l) (S : Submodule ℂ (ramifiedOperatorAlgebra l))
    [FiniteDimensional ℂ S] (ρ σ b : ℤ) (hρ : 0 < ρ) (N : ℕ)
    (P : ramifiedOperatorAlgebra l) (hP : P ≠ 0)
    (hm : ramifiedWeightDeg l hl ρ σ P ≠ 0)
    (hlo : ∀ T : S, ∀ i j, ramifiedWeight l ρ σ (i,j) < b →
      ((ramifiedPBWCoeffs l hl T.val) j).coeff i = 0)
    (hhi : ∀ T : S, ∀ i j, b+(N:ℤ) ≤ ramifiedWeight l ρ σ (i,j) →
      ((ramifiedPBWCoeffs l hl T.val) j).coeff i = 0)
    (hc : ∀ k : ℕ, ∀ T : ramifiedRestrictedWeightBelow l hl S ρ σ (b+((k+1:ℕ):ℤ)),
      C ((ramifiedWeightDeg l hl ρ σ P : ℂ) / ((l:ℂ)*(ρ:ℂ))) *
        ramifiedTopFacePolynomial l hl ρ σ P *
        (ramifiedWeightComponent l hl ρ σ (b+(k:ℤ)) T.val.val).derivative -
      C (((b+(k:ℤ)):ℂ) / ((l:ℂ)*(ρ:ℂ))) *
        (ramifiedTopFacePolynomial l hl ρ σ P).derivative *
        ramifiedWeightComponent l hl ρ σ (b+(k:ℤ)) T.val.val = 0) :
    Module.finrank ℂ S ≤ N := by
  apply ramified_subspace_finrank_le_interval l hl S ρ σ b hρ N hlo hhi
  intro k
  let L := (ramifiedRestrictedWeightComponent l hl S ρ σ (b+(k:ℤ))).domRestrict
    (ramifiedRestrictedWeightBelow l hl S ρ σ (b+((k+1:ℕ):ℤ)))
  change Module.finrank ℂ (LinearMap.range L) ≤ 1
  apply ramified_top_face_centralizer_finrank_le_one l hl ρ σ (b+(k:ℤ)) hρ P hP hm
  intro g
  obtain ⟨T, hT⟩ := g.property
  rw [← hT]
  simpa only [L, ramifiedRestrictedWeightComponent, LinearMap.domRestrict_apply,
    LinearMap.comp_apply, Submodule.subtype_apply, Int.cast_add] using hc k T

end Dixmier.Weyl
