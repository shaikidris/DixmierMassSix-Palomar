module

public import Mathlib.Data.Complex.Basic
public import DixmierFormal.Weyl.FiniteFiltrationRank
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Signed-weight polynomial filtration

The step below b consists of polynomials with zero coefficients at every
weight at least b. The component at b has exactly the preceding step as
kernel on the step below b+1. No positivity of the variable weights is used.
-/
namespace Dixmier.Weyl
open MvPolynomial Finsupp

noncomputable def signedWeightBelow (w : Fin 2 → ℤ) (b : ℤ) :
    Submodule ℂ (MvPolynomial (Fin 2) ℂ) where
  carrier := {p | ∀ e, b ≤ weight w e → MvPolynomial.coeff e p=0}
  zero_mem' := by intro e he; simp
  add_mem' := by intro p q hp hq e he; simp [hp e he,hq e he]
  smul_mem' := by intro c p hp e he; simp [hp e he]

 theorem signedWeightBelow_mono (w : Fin 2 → ℤ) {b c : ℤ} (hbc : b≤c) :
    signedWeightBelow w b ≤ signedWeightBelow w c := by
  intro p hp e he
  exact hp e (hbc.trans he)

 theorem signedWeightBelow_component_kernel (w : Fin 2 → ℤ) (b : ℤ) :
    LinearMap.ker ((weightedHomogeneousComponent w b).domRestrict
      (signedWeightBelow w (b+1))) =
      (signedWeightBelow w b).comap (signedWeightBelow w (b+1)).subtype := by
  ext p
  change weightedHomogeneousComponent w b p.val=0 ↔
    ∀ e, b ≤ weight w e → MvPolynomial.coeff e p.val=0
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

end Dixmier.Weyl
