module

public import DixmierFormal.Weyl.ExactPairWordEvaluation
public import Mathlib.LinearAlgebra.Dimension.Constructions

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Finite-dimensional growth of normal-ordered words

An exact Weyl pair has independent normal-ordered words. Rectangular finite
families therefore span spaces whose dimension is the product of their sides.
-/
namespace Dixmier.Weyl
open Polynomial

 theorem exact_pair_words_linearIndependent (P Q : A1 ℂ) (hp : Q*P-P*Q=1) :
    LinearIndependent ℂ (fun e : Fin 2 →₀ ℕ => P.1^(e 0)*Q.1^(e 1)) := by
  apply linearIndependent_iff_injective_finsuppLinearCombination.mpr
  intro u v huv
  let E : MvPolynomial (Fin 2) ℂ ≃ₗ[ℂ] ((Fin 2 →₀ ℕ) →₀ ℂ) :=
    AddMonoidAlgebra.coeffLinearEquiv ℂ
  have h := wordEvaluation_injective P Q hp
    (show wordEvaluation P Q (E.symm u)=wordEvaluation P Q (E.symm v) by
      simpa [wordEvaluation,E] using huv)
  exact E.symm.injective h

 theorem exact_pair_rectangular_words_linearIndependent (P Q : A1 ℂ)
    (hp : Q*P-P*Q=1) (N M : ℕ) :
    LinearIndependent ℂ (fun p : Fin N × Fin M => P.1^p.1.val*Q.1^p.2.val) := by
  have h := (exact_pair_words_linearIndependent P Q hp).comp
    (fun p : Fin N × Fin M => expo p.1.val p.2.val) (by
      intro a b hab
      have he := expo_injective (a₁ := (a.1.val,a.2.val)) (a₂ := (b.1.val,b.2.val)) hab
      apply Prod.ext
      · exact Fin.ext (congrArg Prod.fst he)
      · exact Fin.ext (congrArg Prod.snd he))
  change LinearIndependent ℂ (fun p : Fin N × Fin M =>
    P.1^((expo p.1.val p.2.val) 0)*Q.1^((expo p.1.val p.2.val) 1)) at h
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simpa only [Function.comp_apply,expo,Finsupp.add_apply,Finsupp.single_apply,h01,h10,
    ite_true,ite_false,add_zero,zero_add] using h

 theorem exact_pair_rectangular_words_finrank (P Q : A1 ℂ)
    (hp : Q*P-P*Q=1) (N M : ℕ) :
    Module.finrank ℂ (Submodule.span ℂ
      (Set.range (fun p : Fin N × Fin M => P.1^p.1.val*Q.1^p.2.val)))=N*M := by
  simpa using finrank_span_eq_card
    (exact_pair_rectangular_words_linearIndependent P Q hp N M)

end Dixmier.Weyl
