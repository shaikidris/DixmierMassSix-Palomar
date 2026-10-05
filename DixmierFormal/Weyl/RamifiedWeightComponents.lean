module

public import DixmierFormal.Weyl.RamifiedShearCandidate
public import DixmierFormal.Weyl.RamifiedPBWSurjectivity
public import Mathlib.LinearAlgebra.Finsupp.LSum

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Linear weight components of finite ramified PBW operators

At a fixed scaled weight and a positive horizontal coordinate, each
derivative order admits at most one Laurent exponent. The component map
extracts that coefficient and records it as an ordinary polynomial.
The divisibility guard excludes derivative orders outside the support lattice.
-/

namespace Dixmier.Weyl
open Polynomial

noncomputable def ramifiedPBWCoeffsLinear (l : ℕ) (hl : 0 < l) :
    ramifiedOperatorAlgebra l →ₗ[ℂ] (ℕ →₀ LaurentPolynomial ℂ) where
  toFun := ramifiedPBWCoeffs l hl
  map_add' := ramifiedPBWCoeffs_add l hl
  map_smul' := ramifiedPBWCoeffs_smul l hl

noncomputable def ramifiedLaurentCoeffLinear (i : ℤ) :
    LaurentPolynomial ℂ →ₗ[ℂ] ℂ :=
  (Finsupp.lapply i).comp (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

noncomputable def ramifiedWeightComponentData (l : ℕ) (ρ σ b : ℤ) :
    (ℕ →₀ LaurentPolynomial ℂ) →ₗ[ℂ] ℂ[X] :=
  Finsupp.lsum ℂ fun (j : ℕ) =>
    if ρ ∣ b - (l : ℤ) * σ * (j : ℤ) then
      (Polynomial.monomial j).comp
        (ramifiedLaurentCoeffLinear ((b - (l : ℤ) * σ * (j : ℤ)) / ρ))
    else 0

noncomputable def ramifiedWeightComponent (l : ℕ) (hl : 0 < l) (ρ σ b : ℤ) :
    ramifiedOperatorAlgebra l →ₗ[ℂ] ℂ[X] :=
  (ramifiedWeightComponentData l ρ σ b).comp (ramifiedPBWCoeffsLinear l hl)

theorem ramifiedWeightComponentData_coeff (l : ℕ) (ρ σ b : ℤ)
    (a : ℕ →₀ LaurentPolynomial ℂ) (j : ℕ) :
    (ramifiedWeightComponentData l ρ σ b a).coeff j =
      if ρ ∣ b - (l : ℤ) * σ * (j : ℤ) then
        (a j).coeff ((b - (l : ℤ) * σ * (j : ℤ)) / ρ) else 0 := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp [map_zero]
  | add a d ha hd =>
    rw [map_add, Polynomial.coeff_add, ha, hd]
    split_ifs <;> simp [AddMonoidAlgebra.coeff_add]
  | single i f =>
    by_cases hij : i = j
    · subst i
      by_cases hdiv : ρ ∣ b - (l : ℤ) * σ * (j : ℤ)
      all_goals simp [ramifiedWeightComponentData, Finsupp.lsum_single, hdiv,
        ramifiedLaurentCoeffLinear]
    · by_cases hdiv : ρ ∣ b - (l : ℤ) * σ * (i : ℤ)
      all_goals simp [ramifiedWeightComponentData, Finsupp.lsum_single, hdiv,
        ramifiedLaurentCoeffLinear, Polynomial.coeff_monomial, hij, Ne.symm hij]

theorem ramifiedWeightComponent_coeff (l : ℕ) (hl : 0 < l) (ρ σ b : ℤ)
    (T : ramifiedOperatorAlgebra l) (j : ℕ) :
    (ramifiedWeightComponent l hl ρ σ b T).coeff j =
      if ρ ∣ b - (l : ℤ) * σ * (j : ℤ) then
        ((ramifiedPBWCoeffs l hl T) j).coeff
          ((b - (l : ℤ) * σ * (j : ℤ)) / ρ) else 0 :=
  ramifiedWeightComponentData_coeff l ρ σ b _ j

theorem ramifiedWeightComponent_coeff_at_weight (l : ℕ) (hl : 0 < l)
    (ρ σ b : ℤ) (hρ : 0 < ρ) (T : ramifiedOperatorAlgebra l)
    (i : ℤ) (j : ℕ) (hwt : ramifiedWeight l ρ σ (i,j) = b) :
    (ramifiedWeightComponent l hl ρ σ b T).coeff j =
      ((ramifiedPBWCoeffs l hl T) j).coeff i := by
  have hnum : b - (l : ℤ) * σ * (j : ℤ) = ρ * i := by
    dsimp [ramifiedWeight] at hwt
    omega
  have hdiv : ρ ∣ b - (l : ℤ) * σ * (j : ℤ) := ⟨i, hnum⟩
  have hquot : (b - (l : ℤ) * σ * (j : ℤ)) / ρ = i := by
    have hc := Int.mul_ediv_cancel' hdiv
    nlinarith
  rw [ramifiedWeightComponent_coeff, if_pos hdiv, hquot]

theorem ramifiedWeightComponent_eq_zero_iff (l : ℕ) (hl : 0 < l)
    (ρ σ b : ℤ) (hρ : 0 < ρ) (T : ramifiedOperatorAlgebra l) :
    ramifiedWeightComponent l hl ρ σ b T = 0 ↔
      ∀ i j, ramifiedWeight l ρ σ (i,j) = b →
        ((ramifiedPBWCoeffs l hl T) j).coeff i = 0 := by
  constructor
  · intro hz i j hwt
    have hc := congrArg (fun p : ℂ[X] => p.coeff j) hz
    simpa only [ramifiedWeightComponent_coeff_at_weight l hl ρ σ b hρ T i j hwt,
      Polynomial.coeff_zero] using hc
  · intro hzero
    ext j
    rw [ramifiedWeightComponent_coeff, Polynomial.coeff_zero]
    split_ifs with hdiv
    · apply hzero
      have hc := Int.mul_ediv_cancel' hdiv
      dsimp [ramifiedWeight]
      omega
    · rfl

noncomputable def ramifiedWeightBelow (l : ℕ) (hl : 0 < l) (ρ σ b : ℤ) :
    Submodule ℂ (ramifiedOperatorAlgebra l) where
  carrier := {T | ∀ i j, b ≤ ramifiedWeight l ρ σ (i,j) →
    ((ramifiedPBWCoeffs l hl T) j).coeff i = 0}
  zero_mem' := by
    intro i j hi
    change (((ramifiedPBWCoeffsLinear l hl) 0) j).coeff i = 0
    rw [map_zero]
    rfl
  add_mem' := by
    intro T U hT hU i j hi
    simp only [ramifiedPBWCoeffs_add, Finsupp.add_apply,
      AddMonoidAlgebra.coeff_add, hT i j hi, hU i j hi, add_zero]
  smul_mem' := by
    intro c T hT i j hi
    simp only [ramifiedPBWCoeffs_smul, Finsupp.smul_apply,
      AddMonoidAlgebra.coeff_smul, hT i j hi, smul_zero]

theorem ramifiedWeightBelow_mono (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    {b d : ℤ} (hbd : b ≤ d) :
    ramifiedWeightBelow l hl ρ σ b ≤ ramifiedWeightBelow l hl ρ σ d := by
  intro T hT i j hi
  exact hT i j (hbd.trans hi)

theorem ramifiedWeightBelow_component_kernel (l : ℕ) (hl : 0 < l)
    (ρ σ b : ℤ) (hρ : 0 < ρ) :
    LinearMap.ker ((ramifiedWeightComponent l hl ρ σ b).domRestrict
      (ramifiedWeightBelow l hl ρ σ (b+1))) =
      (ramifiedWeightBelow l hl ρ σ b).comap
        (ramifiedWeightBelow l hl ρ σ (b+1)).subtype := by
  ext T
  change ramifiedWeightComponent l hl ρ σ b T.val = 0 ↔
    ∀ i j, b ≤ ramifiedWeight l ρ σ (i,j) →
      ((ramifiedPBWCoeffs l hl T.val) j).coeff i = 0
  rw [ramifiedWeightComponent_eq_zero_iff l hl ρ σ b hρ T.val]
  constructor
  · intro hz i j hi
    by_cases he : ramifiedWeight l ρ σ (i,j) = b
    · exact hz i j he
    · exact T.property i j (by omega)
  · intro hz i j he
    exact hz i j (by omega)

end Dixmier.Weyl
