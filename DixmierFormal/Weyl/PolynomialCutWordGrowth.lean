module

public import DixmierFormal.Weyl.WordSymbolGrowth
public import DixmierFormal.Weyl.PolynomialCutWordBounds

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Independent word rectangles after a polynomial-source Newton cut

The faithful polynomial lift and cut automorphism preserve word independence.
Thus the same finite spaces that have linear signed-support intervals have
quadratic dimension when both rectangle sides grow.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 400000

noncomputable local instance ramifiedWordAddCommGroup (l : ℕ) :
    AddCommGroup (ramifiedOperatorAlgebra l) := Module.addCommMonoidToAddCommGroup ℂ

theorem exact_pair_rectangular_A1_words_linearIndependent
    (P Q : A1 ℂ) (hp : Q*P-P*Q=1) (N M : ℕ) :
    LinearIndependent ℂ (fun k : Fin N × Fin M => P^k.1.val*Q^k.2.val) := by
  apply LinearIndependent.of_comp weylOperatorLinearMap
  change LinearIndependent ℂ (fun k : Fin N × Fin M =>
    ((P^k.1.val*Q^k.2.val : A1 ℂ).val))
  simpa only [Subalgebra.coe_mul, Subalgebra.coe_pow] using
    exact_pair_rectangular_words_linearIndependent P Q hp N M

theorem exact_pair_rectangular_cut_words_linearIndependent
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (c : ℂ)
    (P Q : A1 ℂ) (hp : Q*P-P*Q=1) (N M : ℕ) :
    LinearIndependent ℂ (fun k : Fin N × Fin M =>
      ramifiedCutAut l hl ρ σ c
        (polynomialRamifiedLift l (P^k.1.val*Q^k.2.val))) := by
  let F : A1 ℂ →ₗ[ℂ] ramifiedOperatorAlgebra l :=
    { toFun := fun R => ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l R)
      map_add' := by
        intro R S
        rw [polynomialRamifiedLift_add l hl]
        exact ramifiedShearCandidate_add l hl (ramifiedCutShift l ρ σ c) _ _
      map_smul' := by
        intro a R
        rw [polynomialRamifiedLift_smul l hl]
        exact ramifiedShearCandidate_smul l hl (ramifiedCutShift l ρ σ c) a _ }
  have hF_apply (R : A1 ℂ) : F R =
      ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l R) := rfl
  have hF_smul (a : ℂ) (R : A1 ℂ) : F (a • R) = a • F R := map_smul F a R
  have hF : Function.Injective F := by
    intro R S hRS
    apply polynomialRamifiedLift_injective l hl
    apply (ramifiedCutAut l hl ρ σ c).injective
    simpa only [hF_apply] using hRS
  apply (linearIndependent_iff' (R := ℂ)
    (v := fun k : Fin N × Fin M => ramifiedCutAut l hl ρ σ c
      (polynomialRamifiedLift l (P^k.1.val*Q^k.2.val)))).mpr
  intro s a hsum i hi
  have hzero : (∑ k ∈ s, a k • (P^k.1.val*Q^k.2.val : A1 ℂ)) = 0 := by
    apply hF
    rw [map_sum, map_zero]
    simp only [hF_smul]
    simpa only [hF_apply] using hsum
  have hcoeff : ∀ t : Finset (Fin N × Fin M), ∀ b : (Fin N × Fin M) → ℂ,
      (∑ k ∈ t, b k • (P^k.1.val*Q^k.2.val : A1 ℂ)) = 0 →
      ∀ k ∈ t, b k = 0 :=
    (linearIndependent_iff' (R := ℂ)
      (v := fun k : Fin N × Fin M => (P^k.1.val*Q^k.2.val : A1 ℂ))).mp
      (exact_pair_rectangular_A1_words_linearIndependent P Q hp N M)
  exact hcoeff s a hzero i hi

theorem exact_pair_rectangular_cut_words_finrank
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (c : ℂ)
    (P Q : A1 ℂ) (hp : Q*P-P*Q=1) (N M : ℕ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun k : Fin N × Fin M =>
      ramifiedCutAut l hl ρ σ c
        (polynomialRamifiedLift l (P^k.1.val*Q^k.2.val))))) = N*M := by
  simpa using finrank_span_eq_card
    (exact_pair_rectangular_cut_words_linearIndependent l hl ρ σ c P Q hp N M)

end Dixmier.Weyl
