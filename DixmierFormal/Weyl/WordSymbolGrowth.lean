module

public import DixmierFormal.Weyl.ExactPairWordGrowth
public import DixmierFormal.Weyl.GeneratedFaceFiltration

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Quadratic dimension of finite word-symbol spaces

The PBW symbol is an injective linear map on the actual Weyl algebra.
Consequently normal-ordered word independence and its exact finite dimension
pass to the polynomial spaces used by the signed-weight filtration.
-/
set_option maxHeartbeats 0
namespace Dixmier.Weyl
open Polynomial

noncomputable def weylSymbolLinearMap : A1 ℂ →ₗ[ℂ] MvPolynomial (Fin 2) ℂ where
  toFun := fun T => symbol T.val
  map_add' := symbol_add
  map_smul' := symbol_smul

 theorem weylSymbolLinearMap_injective : Function.Injective weylSymbolLinearMap := by
  intro P Q h
  exact symbol_injective h

noncomputable def weylOperatorLinearMap : A1 ℂ →ₗ[ℂ] Module.End ℂ ℂ[X] where
  toFun := fun T => T.val
  map_add' := by intro P Q; rfl
  map_smul' := by
    intro c T
    apply LinearMap.ext
    intro f
    rfl

 theorem exact_pair_rectangular_word_symbols_linearIndependent
    (P Q : A1 ℂ) (hp : Q*P-P*Q=1) (N M : ℕ) :
    LinearIndependent ℂ (fun p : Fin N × Fin M =>
      symbol ((P^p.1.val*Q^p.2.val : A1 ℂ).val)) := by
  have hw : LinearIndependent ℂ (fun p : Fin N × Fin M => P^p.1.val*Q^p.2.val) := by
    apply LinearIndependent.of_comp weylOperatorLinearMap
    change LinearIndependent ℂ (fun p : Fin N × Fin M =>
      ((P^p.1.val*Q^p.2.val : A1 ℂ).val))
    simpa only [Subalgebra.coe_mul,Subalgebra.coe_pow] using
      exact_pair_rectangular_words_linearIndependent P Q hp N M
  apply linearIndependent_iff'.mpr
  intro s c hsum i hi
  have hzero : (∑ k ∈ s, c k • (P^k.1.val*Q^k.2.val : A1 ℂ))=0 := by
    apply weylSymbolLinearMap_injective
    rw [map_sum,map_zero]
    simp only [map_smul]
    exact hsum
  have hcoeff : ∀ t : Finset (Fin N × Fin M), ∀ a : (Fin N × Fin M) → ℂ,
      (∑ k ∈ t, a k • (P^k.1.val*Q^k.2.val : A1 ℂ))=0 →
      ∀ k ∈ t, a k=0 :=
    (linearIndependent_iff' (R := ℂ)
      (v := fun k : Fin N × Fin M => (P^k.1.val*Q^k.2.val : A1 ℂ))).mp hw
  exact hcoeff s c hzero i hi

 theorem exact_pair_rectangular_word_symbols_finrank
    (P Q : A1 ℂ) (hp : Q*P-P*Q=1) (N M : ℕ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun p : Fin N × Fin M =>
      symbol ((P^p.1.val*Q^p.2.val : A1 ℂ).val))))=N*M := by
  simpa using finrank_span_eq_card
    (exact_pair_rectangular_word_symbols_linearIndependent P Q hp N M)

 theorem normal_ordered_word_mem_adjoin (P Q : A1 ℂ) (i j : ℕ) :
    P^i*Q^j ∈ Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ)) := by
  have hP : P ∈ Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ)) :=
    Algebra.subset_adjoin (by simp)
  have hQ : Q ∈ Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ)) :=
    Algebra.subset_adjoin (by simp)
  exact (Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ))).mul_mem
    ((Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ))).pow_mem hP i)
    ((Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ))).pow_mem hQ j)

end Dixmier.Weyl
