module

public import DixmierFormal.Weyl.RestrictedSignedFiltration
public import DixmierFormal.Weyl.HomogeneousCentralizerLine
public import Mathlib.LinearAlgebra.Dimension.Finite

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Rank bounds for filtered Poisson-centralizer images

The homogeneous centralizer line theorem applies to the image of a component
map restricted to a filtered subspace. Together with bounded signed support,
this bounds the whole subspace, including cancellations of leading terms.
-/
namespace Dixmier.Weyl
open MvPolynomial Finsupp

 theorem filtered_centralizer_component_finrank_le_one
    (S : Submodule ℂ (MvPolynomial (Fin 2) ℂ))
    (f : MvPolynomial (Fin 2) ℂ) (ρ σ m b : ℤ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m) (hfne : f≠0) (hm : m≠0)
    (hc : ∀ p : restrictedWeightBelow S (wt ρ σ) (b+1),
      poisson f (weightedHomogeneousComponent (wt ρ σ) b p.val.val)=0) :
    Module.finrank ℂ (LinearMap.range
      ((restrictedWeightComponent S (wt ρ σ) b).domRestrict
        (restrictedWeightBelow S (wt ρ σ) (b+1)))) ≤ 1 := by
  classical
  let L := (restrictedWeightComponent S (wt ρ σ) b).domRestrict
    (restrictedWeightBelow S (wt ρ σ) (b+1))
  change Module.finrank ℂ (LinearMap.range L) ≤ 1
  by_cases hex : ∃ h : LinearMap.range L, h≠0
  · obtain ⟨h,hh⟩ := hex
    apply finrank_le_one h
    intro g
    obtain ⟨p,hp⟩ := g.property
    obtain ⟨q,hq⟩ := h.property
    have hne : h.val≠0 := by
      intro hz
      apply hh
      exact Subtype.ext hz
    have hg : g.val.IsWeightedHomogeneous (wt ρ σ) b := by
      rw [← hp]
      exact weightedHomogeneousComponent_isWeightedHomogeneous b p.val.val
    have hhom : h.val.IsWeightedHomogeneous (wt ρ σ) b := by
      rw [← hq]
      exact weightedHomogeneousComponent_isWeightedHomogeneous b q.val.val
    have hcg : poisson f g.val=0 := by rw [← hp]; exact hc p
    have hch : poisson f h.val=0 := by rw [← hq]; exact hc q
    obtain ⟨c,hcgh⟩ := homogeneous_poisson_centralizer_scalar_ratio
      f g.val h.val ρ σ m b hf hg hhom hfne hm hne hcg hch
    refine ⟨c,?_⟩
    apply Subtype.ext
    change c • h.val=g.val
    simpa only [Algebra.smul_def,MvPolynomial.algebraMap_eq] using hcgh.symm
  · apply finrank_le_one (0 : LinearMap.range L)
    intro g
    have hg : g=0 := by
      by_contra hgne
      exact hex ⟨g,hgne⟩
    exact ⟨0,by simp [hg]⟩

 theorem filtered_centralizer_finrank_le_interval
    (S : Submodule ℂ (MvPolynomial (Fin 2) ℂ)) [FiniteDimensional ℂ S]
    (f : MvPolynomial (Fin 2) ℂ) (ρ σ m b : ℤ) (N : ℕ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m) (hfne : f≠0) (hm : m≠0)
    (hlo : ∀ p : S, ∀ e, weight (wt ρ σ) e < b → MvPolynomial.coeff e p.val=0)
    (hhi : ∀ p : S, ∀ e, b+(N:ℤ) ≤ weight (wt ρ σ) e → MvPolynomial.coeff e p.val=0)
    (hc : ∀ i : ℕ, ∀ p : restrictedWeightBelow S (wt ρ σ) (b+(i:ℤ)+1),
      poisson f (weightedHomogeneousComponent (wt ρ σ) (b+(i:ℤ)) p.val.val)=0) :
    Module.finrank ℂ S ≤ N := by
  apply signed_subspace_finrank_le_interval S (wt ρ σ) b N hlo hhi
  intro i
  have he : b+((i+1:ℕ):ℤ)=b+(i:ℤ)+1 := by omega
  rw [he]
  exact filtered_centralizer_component_finrank_le_one S f ρ σ m (b+(i:ℤ))
    hf hfne hm (hc i)

end Dixmier.Weyl
