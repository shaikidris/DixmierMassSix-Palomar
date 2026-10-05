module

public import DixmierFormal.Weyl.SignedWeightFiltration

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Signed-weight filtrations inside polynomial subspaces

Restricting the component maps to a subspace retains the exact kernel
identity. Bounded signed support gives the zero and top steps needed for
the finite-filtration dimension bound.
-/
namespace Dixmier.Weyl
open MvPolynomial Finsupp

noncomputable def restrictedWeightBelow
    (S : Submodule ℂ (MvPolynomial (Fin 2) ℂ)) (w : Fin 2 → ℤ) (b : ℤ) :
    Submodule ℂ S := (signedWeightBelow w b).comap S.subtype

noncomputable def restrictedWeightComponent
    (S : Submodule ℂ (MvPolynomial (Fin 2) ℂ)) (w : Fin 2 → ℤ) (b : ℤ) :
    S →ₗ[ℂ] MvPolynomial (Fin 2) ℂ :=
  (weightedHomogeneousComponent w b).comp S.subtype

 theorem restrictedWeightBelow_mono
    (S : Submodule ℂ (MvPolynomial (Fin 2) ℂ)) (w : Fin 2 → ℤ)
    {b c : ℤ} (hbc : b≤c) : restrictedWeightBelow S w b ≤ restrictedWeightBelow S w c := by
  intro p hp
  exact signedWeightBelow_mono w hbc hp

 theorem restrictedWeightComponent_kernel
    (S : Submodule ℂ (MvPolynomial (Fin 2) ℂ)) (w : Fin 2 → ℤ) (b : ℤ) :
    LinearMap.ker ((restrictedWeightComponent S w b).domRestrict
      (restrictedWeightBelow S w (b+1))) =
      (restrictedWeightBelow S w b).comap (restrictedWeightBelow S w (b+1)).subtype := by
  ext p
  change weightedHomogeneousComponent w b p.val.val=0 ↔
    ∀ e, b ≤ weight w e → MvPolynomial.coeff e p.val.val=0
  constructor
  · intro hz e he
    by_cases hwb : weight w e=b
    · have hc := congrArg (MvPolynomial.coeff e) hz
      simpa only [coeff_weightedHomogeneousComponent,hwb,ite_true,MvPolynomial.coeff_zero,Finsupp.coe_zero,Pi.zero_apply] using hc
    · exact p.property e (by omega)
  · intro hp
    ext e
    rw [coeff_weightedHomogeneousComponent,MvPolynomial.coeff_zero]
    split_ifs with he
    · exact hp e he.ge
    · rfl

 theorem restrictedWeightBelow_eq_bot_of_lower_bound
    (S : Submodule ℂ (MvPolynomial (Fin 2) ℂ)) (w : Fin 2 → ℤ) (b : ℤ)
    (hlo : ∀ p : S, ∀ e, weight w e < b → MvPolynomial.coeff e p.val=0) :
    restrictedWeightBelow S w b=⊥ := by
  apply le_antisymm _ bot_le
  intro p hp
  change p=0
  apply Subtype.ext
  ext e
  by_cases he : b ≤ weight w e
  · exact hp e he
  · exact hlo p e (by omega)

 theorem restrictedWeightBelow_eq_top_of_upper_bound
    (S : Submodule ℂ (MvPolynomial (Fin 2) ℂ)) (w : Fin 2 → ℤ) (b : ℤ)
    (hhi : ∀ p : S, ∀ e, b ≤ weight w e → MvPolynomial.coeff e p.val=0) :
    restrictedWeightBelow S w b=⊤ := by
  apply top_unique
  intro p hp
  exact hhi p

 theorem signed_subspace_finrank_le_interval
    (S : Submodule ℂ (MvPolynomial (Fin 2) ℂ)) [FiniteDimensional ℂ S]
    (w : Fin 2 → ℤ) (b : ℤ) (N : ℕ)
    (hlo : ∀ p : S, ∀ e, weight w e < b → MvPolynomial.coeff e p.val=0)
    (hhi : ∀ p : S, ∀ e, b+(N:ℤ) ≤ weight w e → MvPolynomial.coeff e p.val=0)
    (hrank : ∀ i : ℕ, Module.finrank ℂ
      (LinearMap.range ((restrictedWeightComponent S w (b+(i:ℤ))).domRestrict
        (restrictedWeightBelow S w (b+((i+1:ℕ):ℤ))))) ≤ 1) :
    Module.finrank ℂ S ≤ N := by
  apply finite_filtration_top_finrank_le
    (fun i => restrictedWeightBelow S w (b+(i:ℤ)))
    (fun i => restrictedWeightComponent S w (b+(i:ℤ))) N
  · simpa using restrictedWeightBelow_eq_bot_of_lower_bound S w b hlo
  · exact restrictedWeightBelow_eq_top_of_upper_bound S w (b+(N:ℤ)) hhi
  · intro i
    apply restrictedWeightBelow_mono
    omega
  · intro i
    have he : b+((i+1:ℕ):ℤ)=(b+(i:ℤ))+1 := by omega
    rw [he]
    exact restrictedWeightComponent_kernel S w (b+(i:ℤ))
  · exact hrank

end Dixmier.Weyl
