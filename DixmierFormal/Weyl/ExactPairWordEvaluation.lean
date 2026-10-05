module

public import DixmierFormal.Weyl.ExactPairWordDerivatives
public import DixmierFormal.Weyl.DerivativeStableKernel
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.MonoidAlgebra.Module

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Normal-ordered evaluation at an exact Weyl pair

Bivariate polynomials are evaluated linearly in the words P^i Q^j. This is
not commutative algebra evaluation. Exact commutators intertwine its two
partial derivatives and force injectivity.
-/
set_option maxHeartbeats 0
namespace Dixmier.Weyl
open MvPolynomial Polynomial

noncomputable def wordEvaluation (P Q : A1 ℂ) :
    MvPolynomial (Fin 2) ℂ →ₗ[ℂ] Module.End ℂ ℂ[X] :=
  (Finsupp.linearCombination ℂ (fun e : Fin 2 →₀ ℕ => P.1^(e 0)*Q.1^(e 1))).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] theorem wordEvaluation_monomial (P Q : A1 ℂ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    wordEvaluation P Q (MvPolynomial.monomial e c)=c • (P.1^(e 0)*Q.1^(e 1)) :=
  by simp [wordEvaluation,MvPolynomial.monomial]

@[simp] theorem wordEvaluation_C (P Q : A1 ℂ) (c : ℂ) :
    wordEvaluation P Q (MvPolynomial.C c)=c • (1 : Module.End ℂ ℂ[X]) := by
  change wordEvaluation P Q (MvPolynomial.monomial 0 c)=_
  rw [wordEvaluation_monomial]
  simp only [Finsupp.zero_apply,pow_zero,one_mul]

private theorem expo_pderiv_x (i j : ℕ) : expo i j-Finsupp.single 0 1=expo (i-1) j := by
  ext k; fin_cases k <;> simp [expo]
private theorem expo_pderiv_y (i j : ℕ) : expo i j-Finsupp.single 1 1=expo i (j-1) := by
  ext k; fin_cases k <;> simp [expo]

private theorem wordEvaluation_derivative_x_monomial
    (P Q : A1 ℂ) (hp : Q*P-P*Q=1) (i j : ℕ) (c : ℂ) :
    wordEvaluation P Q (pderiv 0 (MvPolynomial.monomial (expo i j) c)) =
      Q.1*wordEvaluation P Q (MvPolynomial.monomial (expo i j) c)-
        wordEvaluation P Q (MvPolynomial.monomial (expo i j) c)*Q.1 := by
  simp only [pderiv_monomial,expo_pderiv_x,wordEvaluation_monomial]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [expo,Finsupp.add_apply,Finsupp.single_apply,h01,h10,ite_true,ite_false,add_zero,zero_add]
  cases i with
  | zero =>
    simp only [Nat.cast_zero,mul_zero,zero_smul,pow_zero,one_mul]
    have hc : Q.1*Q.1^j=Q.1^j*Q.1 := (Commute.refl Q.1).pow_right j
    rw [mul_smul_comm,smul_mul_assoc,hc,sub_self]
  | succ i =>
    have hd := congrArg (fun T : Module.End ℂ ℂ[X] => c • T)
      (exact_pair_commutator_Q_word P Q hp i j)
    simp only [smul_sub,smul_smul] at hd
    simpa only [mul_smul_comm,smul_mul_assoc,Nat.succ_sub_one,Nat.cast_add,Nat.cast_one] using hd.symm

private theorem wordEvaluation_derivative_y_monomial
    (P Q : A1 ℂ) (hp : Q*P-P*Q=1) (i j : ℕ) (c : ℂ) :
    wordEvaluation P Q (pderiv 1 (MvPolynomial.monomial (expo i j) c)) =
      -(P.1*wordEvaluation P Q (MvPolynomial.monomial (expo i j) c)-
        wordEvaluation P Q (MvPolynomial.monomial (expo i j) c)*P.1) := by
  simp only [pderiv_monomial,expo_pderiv_y,wordEvaluation_monomial]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [expo,Finsupp.add_apply,Finsupp.single_apply,h01,h10,ite_true,ite_false,add_zero,zero_add]
  cases j with
  | zero =>
    simp only [Nat.cast_zero,mul_zero,zero_smul,pow_zero,mul_one]
    have hc : P.1*P.1^i=P.1^i*P.1 := (Commute.refl P.1).pow_right i
    rw [mul_smul_comm,smul_mul_assoc,hc,sub_self,neg_zero]
  | succ j =>
    have hd := congrArg (fun T : Module.End ℂ ℂ[X] => -(c • T))
      (exact_pair_commutator_P_word P Q hp i j)
    simp only [smul_sub,smul_smul,mul_neg,neg_smul,neg_neg] at hd
    simpa only [mul_smul_comm,smul_mul_assoc,Nat.succ_sub_one,Nat.cast_add,Nat.cast_one] using hd.symm

/-- Exact commutator transport for the first partial derivative. -/
theorem wordEvaluation_pderiv_x (P Q : A1 ℂ) (hp : Q*P-P*Q=1)
    (f : MvPolynomial (Fin 2) ℂ) :
    wordEvaluation P Q (pderiv 0 f)=Q.1*wordEvaluation P Q f-wordEvaluation P Q f*Q.1 := by
  induction f using MvPolynomial.induction_on' with
  | monomial e c =>
    obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective e
    exact wordEvaluation_derivative_x_monomial P Q hp i j c
  | add f g hf hg =>
    simp only [map_add,hf,hg,mul_add,add_mul]
    abel

/-- Exact commutator transport for the second partial derivative. -/
theorem wordEvaluation_pderiv_y (P Q : A1 ℂ) (hp : Q*P-P*Q=1)
    (f : MvPolynomial (Fin 2) ℂ) :
    wordEvaluation P Q (pderiv 1 f)=-(P.1*wordEvaluation P Q f-wordEvaluation P Q f*P.1) := by
  induction f using MvPolynomial.induction_on' with
  | monomial e c =>
    obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective e
    exact wordEvaluation_derivative_y_monomial P Q hp i j c
  | add f g hf hg =>
    simp only [map_add,hf,hg,mul_add,add_mul]
    abel

/-- Normal-ordered word evaluation at any exact Weyl pair is injective. -/
theorem wordEvaluation_injective (P Q : A1 ℂ) (hp : Q*P-P*Q=1) :
    Function.Injective (wordEvaluation P Q) := by
  apply bivariate_linearMap_injective_of_derivative_stable_kernel
  · intro f hf i
    fin_cases i
    · change wordEvaluation P Q (pderiv 0 f)=0
      rw [wordEvaluation_pderiv_x P Q hp,hf,mul_zero,zero_mul,sub_self]
    · change wordEvaluation P Q (pderiv 1 f)=0
      rw [wordEvaluation_pderiv_y P Q hp,hf,mul_zero,zero_mul,sub_self,neg_zero]
  · intro c hc
    rw [wordEvaluation_C] at hc
    have he := congrArg (fun T : Module.End ℂ ℂ[X] => T 1) hc
    simpa using he

end Dixmier.Weyl
