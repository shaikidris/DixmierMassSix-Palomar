module

public import DixmierFormal.Weyl.FilteredCentralizerRank

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # From generated leading faces to filtered components

A nonzero component at the uppermost allowed signed weight is the actual
leading form. Thus centralization of generated leading forms supplies
centralization for the restricted filtration, including its zero images.
-/
namespace Dixmier.Weyl
open MvPolynomial Finsupp Polynomial

 theorem filtered_symbol_component_eq_leadingForm
    (T : A1 ℂ) (ρ σ b : ℤ)
    (hb : symbol T.val ∈ signedWeightBelow (wt ρ σ) (b+1))
    (hne : weightedHomogeneousComponent (wt ρ σ) b (symbol T.val)≠0) :
    weightedHomogeneousComponent (wt ρ σ) b (symbol T.val)=leadingForm ρ σ T.val := by
  obtain ⟨e,he⟩ := exists_coeff_ne_zero hne
  have hwe : weight (wt ρ σ) e=b := by
    by_contra h
    apply he
    rw [coeff_weightedHomogeneousComponent,if_neg h]
  have hce : MvPolynomial.coeff e (symbol T.val)≠0 := by
    simpa only [coeff_weightedHomogeneousComponent,if_pos hwe] using he
  have hdeg : weightedTotalDegree' (wt ρ σ) (symbol T.val)=(b : WithBot ℤ) := by
    apply le_antisymm
    · apply Finset.sup_le
      intro d hd
      have hcd := MvPolynomial.mem_support_iff.mp hd
      have hwb : weight (wt ρ σ) d ≤ b := by
        by_contra h
        exact hcd (hb d (by omega))
      exact WithBot.coe_le_coe.mpr hwb
    · rw [← hwe]
      change (weight (wt ρ σ) e : WithBot ℤ) ≤
        (symbol T.val).support.sup (fun d => (weight (wt ρ σ) d : WithBot ℤ))
      exact Finset.le_sup (f := fun d => (weight (wt ρ σ) d : WithBot ℤ))
        (MvPolynomial.mem_support_iff.mpr hce)
  have hv : vDeg ρ σ T.val=b := by simp [vDeg,hdeg]
  simp only [leadingForm,hv]

 theorem generated_face_centralization_implies_filtered_component
    (P Q T : A1 ℂ) (f : MvPolynomial (Fin 2) ℂ) (ρ σ b : ℤ)
    (hc : ∀ R : A1 ℂ, R ∈ Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ)) →
      poisson f (leadingForm ρ σ R.val)=0)
    (hT : T ∈ Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ)))
    (hb : symbol T.val ∈ signedWeightBelow (wt ρ σ) (b+1)) :
    poisson f (weightedHomogeneousComponent (wt ρ σ) b (symbol T.val))=0 := by
  by_cases hz : weightedHomogeneousComponent (wt ρ σ) b (symbol T.val)=0
  · simp [hz,poisson]
  · rw [filtered_symbol_component_eq_leadingForm T ρ σ b hb hz]
    exact hc T hT

end Dixmier.Weyl
