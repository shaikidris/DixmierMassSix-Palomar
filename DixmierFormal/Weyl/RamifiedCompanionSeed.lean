/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedGradeCountercontrol

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Exact seeds for the homogeneous-companion construction

An exact Weyl pair supplies an operator `R` satisfying `[P,R]=P`.
Adding a polynomial in `P` does not change this equation. The remaining
G13/Joseph step is to control the weight of a suitable representative.
-/

namespace Dixmier.Weyl

theorem ramified_companion_seed
    (l : ℕ) (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q * P - P * Q = 1) :
    (Q * P) * P - P * (Q * P) = P := by
  calc
    (Q * P) * P - P * (Q * P) =
        (Q * P - P * Q) * P := by
          calc
            (Q * P) * P - P * (Q * P) =
                (Q * P) * P - (P * Q) * P := by rw [mul_assoc P Q P]
            _ = (Q * P - P * Q) * P := (sub_mul (Q * P) (P * Q) P).symm
    _ = P := by rw [hcomm, one_mul]

theorem ramified_companion_seed_adjust
    (l : ℕ) (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q * P - P * Q = 1) (c : ℂ) (k : ℕ) :
    (Q * P + algebraMap ℂ (ramifiedOperatorAlgebra l) c * P^k) * P -
      P * (Q * P + algebraMap ℂ (ramifiedOperatorAlgebra l) c * P^k) = P := by
  have hseed := ramified_companion_seed l P Q hcomm
  have hcenter : P * (algebraMap ℂ (ramifiedOperatorAlgebra l) c * P^k) =
      (algebraMap ℂ (ramifiedOperatorAlgebra l) c * P^k) * P := by
    have hc : P * algebraMap ℂ (ramifiedOperatorAlgebra l) c =
        algebraMap ℂ (ramifiedOperatorAlgebra l) c * P :=
      (Algebra.commutes c P).symm
    calc
      P * (algebraMap ℂ (ramifiedOperatorAlgebra l) c * P^k) =
          algebraMap ℂ (ramifiedOperatorAlgebra l) c * (P * P^k) := by
            rw [← mul_assoc, hc, mul_assoc]
      _ = algebraMap ℂ (ramifiedOperatorAlgebra l) c * (P^k * P) := by
            rw [show P * P^k = P^(k+1) by rw [← pow_succ'], pow_succ]
      _ = (algebraMap ℂ (ramifiedOperatorAlgebra l) c * P^k) * P := by
            rw [mul_assoc]
  calc
    (Q * P + algebraMap ℂ (ramifiedOperatorAlgebra l) c * P^k) * P -
        P * (Q * P + algebraMap ℂ (ramifiedOperatorAlgebra l) c * P^k) =
        (Q * P) * P - P * (Q * P) := by rw [mul_add, add_mul, hcenter]; abel
    _ = P := hseed

end Dixmier.Weyl
