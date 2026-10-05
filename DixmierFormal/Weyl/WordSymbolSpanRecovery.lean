module

public import DixmierFormal.Weyl.WordSymbolGrowth

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Recovery of generated operators from finite word-symbol spans

Linear combinations of normal-ordered word symbols are symbols of operators
in the generated algebra. This supplies the source membership needed by the
filtered leading-face bridge.
-/
set_option maxHeartbeats 0
namespace Dixmier.Weyl
open Polynomial

 theorem rectangular_word_symbol_span_recovery
    (P Q : A1 ℂ) (N M : ℕ) (p : MvPolynomial (Fin 2) ℂ)
    (hp : p ∈ Submodule.span ℂ (Set.range (fun k : Fin N × Fin M =>
      symbol ((P^k.1.val*Q^k.2.val : A1 ℂ).val)))) :
    ∃ T : A1 ℂ, T ∈ Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ)) ∧ symbol T.val=p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨k,rfl⟩ := hp
    exact ⟨P^k.1.val*Q^k.2.val,normal_ordered_word_mem_adjoin P Q _ _,rfl⟩
  | zero =>
    refine ⟨0,(Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ))).zero_mem,?_⟩
    exact weylSymbolLinearMap.map_zero
  | add p q hp hq ihp ihq =>
    obtain ⟨T,hT,hsT⟩ := ihp
    obtain ⟨U,hU,hsU⟩ := ihq
    refine ⟨T+U,(Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ))).add_mem hT hU,?_⟩
    rw [symbol_add,hsT,hsU]
  | smul c p hp ih =>
    obtain ⟨T,hT,hsT⟩ := ih
    refine ⟨c • T,(Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ))).smul_mem hT c,?_⟩
    rw [symbol_smul,hsT]

end Dixmier.Weyl
