module

public import DixmierFormal.Weyl.JosephLocalNilpotence

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Exact commutator differentiation of generated Weyl words

The Weyl relation differentiates normal-ordered words in either generator.
All exponents are unrestricted. These identities provide coefficient
extraction for the generated-word independence argument.
-/
namespace Dixmier.Weyl
open Polynomial

private theorem commutator_mul_leibniz {A : Type*} [Ring A] (U V W : A) :
    U*(V*W)-(V*W)*U=(U*V-V*U)*W+V*(U*W-W*U) := by
  noncomm_ring

/-- A central commutator one differentiates every positive power. -/
theorem commutator_one_power_succ {A : Type*} [Ring A] [Algebra ℂ A]
    (U V : A) (h : U*V-V*U=1) (n : ℕ) :
    U*V^(n+1)-V^(n+1)*U=(n+1 : ℂ) • V^n := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ,commutator_mul_leibniz,ih,h]
    simp only [smul_mul_assoc,mul_one,← pow_succ]
    calc
      (n+1 : ℂ) • V^(n+1)+V^(n+1) = ((n+1 : ℂ)+1) • V^(n+1) := by
        simp only [add_smul,one_smul]
      _ = (↑(n+1)+1 : ℂ) • V^(n+1) := by simp only [Nat.cast_add,Nat.cast_one]

/-- The signed version needed when the commutator is minus one. -/
theorem commutator_neg_one_power_succ {A : Type*} [Ring A] [Algebra ℂ A]
    (U V : A) (h : U*V-V*U = -1) (n : ℕ) :
    U*V^(n+1)-V^(n+1)*U=-(n+1 : ℂ) • V^n := by
  have hneg : (-U)*V-V*(-U)=1 := by
    calc
      (-U)*V-V*(-U)=-(U*V-V*U) := by noncomm_ring
      _ = 1 := by rw [h]; simp
  have hh := commutator_one_power_succ (-U) V hneg n
  have hl : (-U)*V^(n+1)-V^(n+1)*(-U)=-(U*V^(n+1)-V^(n+1)*U) := by
    noncomm_ring
  rw [hl] at hh
  have := congrArg Neg.neg hh
  simpa only [neg_neg,neg_smul] using this

/-- Commutation with Q differentiates the P-power in a normal-ordered word. -/
theorem exact_pair_commutator_Q_word (P Q : A1 ℂ) (h : Q*P-P*Q=1) (i j : ℕ) :
    Q.1*(P.1^(i+1)*Q.1^j)-(P.1^(i+1)*Q.1^j)*Q.1 =
      (i+1 : ℂ) • (P.1^i*Q.1^j) := by
  have hh : Q.1*P.1-P.1*Q.1=1 := congrArg Subtype.val h
  have hc : Q.1*Q.1^j-Q.1^j*Q.1=0 := sub_eq_zero.mpr ((Commute.refl Q.1).pow_right j)
  rw [commutator_mul_leibniz,commutator_one_power_succ Q.1 P.1 hh i,hc]
  simp only [mul_zero,add_zero,smul_mul_assoc]

/-- Commutation with P differentiates the Q-power with the negative sign. -/
theorem exact_pair_commutator_P_word (P Q : A1 ℂ) (h : Q*P-P*Q=1) (i j : ℕ) :
    P.1*(P.1^i*Q.1^(j+1))-(P.1^i*Q.1^(j+1))*P.1 =
      -(j+1 : ℂ) • (P.1^i*Q.1^j) := by
  have hh : P.1*Q.1-Q.1*P.1 = -1 := by
    have hp : Q.1*P.1-P.1*Q.1=1 := congrArg Subtype.val h
    calc
      P.1*Q.1-Q.1*P.1=-(Q.1*P.1-P.1*Q.1) := by abel
      _ = -1 := by rw [hp]
  have hc : P.1*P.1^i-P.1^i*P.1=0 := sub_eq_zero.mpr ((Commute.refl P.1).pow_right i)
  rw [commutator_mul_leibniz,hc,commutator_neg_one_power_succ P.1 Q.1 hh j]
  simp only [zero_mul,zero_add,mul_smul_comm]

end Dixmier.Weyl
