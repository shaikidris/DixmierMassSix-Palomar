/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedShearAutomorphism

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The exact-pair setup for a ramified Newton cut

G13 Proposition 5.3 applies the monomial shear from Proposition 5.1 to an
exact pair. This file records the parameter arithmetic and the exact
commutator invariance in the faithful ramified operator algebra. It does not
assert the root-selected endpoint or new-direction conclusions of 5.3.
-/
namespace Dixmier.Weyl

/-- The exponent of `T=X^(1/l)` representing `X^(σ/ρ)` when `ρ ∣ l`. -/
def ramifiedCutExponent (l : ℕ) (ρ σ : ℤ) : ℤ :=
  ((l : ℤ) / ρ) * σ

theorem ramifiedCutExponent_weight (l : ℕ) (ρ σ : ℤ)
    (hρ : ρ ∣ (l : ℤ)) :
    ρ * ramifiedCutExponent l ρ σ = (l : ℤ) * σ := by
  unfold ramifiedCutExponent
  calc
    ρ * (((l : ℤ) / ρ) * σ) = (ρ * ((l : ℤ) / ρ)) * σ := by ring
    _ = (l : ℤ) * σ := by rw [Int.mul_ediv_cancel' hρ]

/-- The monomial shift at a cut direction, as a Laurent coefficient. -/
noncomputable def ramifiedCutShift (l : ℕ) (ρ σ : ℤ) (c : ℂ) :
    LaurentPolynomial ℂ :=
  c • LaurentPolynomial.T (ramifiedCutExponent l ρ σ)

/-- The source's shear is an actual algebra automorphism for every
admissible positive ramification index. -/
noncomputable def ramifiedCutAut (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (c : ℂ) :
    ramifiedOperatorAlgebra l ≃ₐ[ℂ] ramifiedOperatorAlgebra l :=
  ramifiedShearAut l hl (ramifiedCutShift l ρ σ c)

theorem ramifiedCutAut_coeff (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (c : ℂ) (f : LaurentPolynomial ℂ) :
    ramifiedCutAut l hl ρ σ c (ramifiedCoeffGen l f) =
      ramifiedCoeffGen l f := by
  exact ramifiedShearCandidate_coeffGen l hl _ f

theorem ramifiedCutAut_Y (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (c : ℂ) :
    ramifiedCutAut l hl ρ σ c (ramifiedYGen l) =
      ramifiedYGen l + ramifiedCoeffGen l
        (ramifiedCutShift l ρ σ c) := by
  exact (ramifiedShearCandidate_YGen_sub l hl _).trans
    (ramifiedShiftedYGen_eq_add l _)

/-- The exact Weyl relation survives the cut shear, without a bound on
the orders or supports of either operator. -/
theorem ramifiedCutAut_exact_pair (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (c : ℂ)
    (P Q : ramifiedOperatorAlgebra l)
    (hQP : Q * P - P * Q = 1) :
    ramifiedCutAut l hl ρ σ c Q *
      ramifiedCutAut l hl ρ σ c P -
      ramifiedCutAut l hl ρ σ c P *
      ramifiedCutAut l hl ρ σ c Q = 1 := by
  rw [← map_mul, ← map_mul]
  calc
    _ = ramifiedCutAut l hl ρ σ c (Q * P - P * Q) := by
      exact (map_sub (ramifiedCutAut l hl ρ σ c) (Q * P) (P * Q)).symm
    _ = 1 := by rw [hQP, map_one]

/-- Generation by the pair is preserved under the ramified cut. This is
needed when a cut is applied to a hypothetical nongenerating exact pair. -/
theorem ramifiedCutAut_generates_iff (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (c : ℂ)
    (P Q : ramifiedOperatorAlgebra l) :
    Algebra.adjoin ℂ
      {ramifiedCutAut l hl ρ σ c P,
       ramifiedCutAut l hl ρ σ c Q} = ⊤ ↔
      Algebra.adjoin ℂ {P,Q} = ⊤ := by
  let e := ramifiedCutAut l hl ρ σ c
  have himage : e '' ({P,Q} : Set (ramifiedOperatorAlgebra l)) =
      {e P,e Q} := Set.image_pair e P Q
  rw [← himage]
  change Algebra.adjoin ℂ (e.toAlgHom '' {P,Q}) = ⊤ ↔
    Algebra.adjoin ℂ {P,Q} = ⊤
  rw [Algebra.adjoin_image]
  constructor
  · intro h
    have hmap := congrArg (fun S : Subalgebra ℂ (ramifiedOperatorAlgebra l) =>
      S.map e.symm.toAlgHom) h
    have hcomp : e.symm.toAlgHom.comp e.toAlgHom =
        AlgHom.id ℂ (ramifiedOperatorAlgebra l) := by
      ext x
      simp
    rw [Subalgebra.map_map, hcomp, Algebra.map_top] at hmap
    have hsur : e.symm.toAlgHom.range = ⊤ :=
      (AlgHom.range_eq_top _).mpr e.symm.surjective
    simpa [hsur] using hmap
  · intro h
    rw [h]
    rw [Algebra.map_top]
    exact (AlgHom.range_eq_top _).mpr e.surjective

end Dixmier.Weyl
