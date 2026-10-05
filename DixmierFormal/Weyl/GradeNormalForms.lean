/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.ShiftIntertwining

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Normal forms for Weyl grades

Every element supported on a negative grade `-k` is a polynomial in `YX`
followed by `Y^k`; the grade `-1` statement is retained as a named wrapper.
The positive-grade normal forms are developed in
`PositiveGradeNormalForms.lean`. These proofs use finite PBW support and
explicit shifted polynomial bases.
-/

namespace Dixmier.Weyl
open Polynomial
variable {K : Type*} [Field K]

noncomputable def lowerShiftPoly : ℕ → K[X]
  | 0 => 1
  | i+1 => lowerShiftPoly i * (X - C ((i+1 : ℕ) : K))

noncomputable def upperShiftPoly : ℕ → K[X]
  | 0 => 1
  | i+1 => upperShiftPoly i * (X - C ((i+2 : ℕ) : K))

private theorem xPowApply (n : ℕ) : ∀ p : K[X], (xOp K ^ n) p = X ^ n * p := by
  induction n with
  | zero => intro p; simp [xOp]
  | succ n ih =>
      intro p
      rw [pow_succ, Module.End.mul_apply, ih]
      simp [xOp, LinearMap.mulLeft_apply, pow_succ, mul_assoc]

private theorem y_mul_xpow_succ (i : ℕ) :
    yOp K * xOp K ^ (i+1) = xOp K ^ (i+1) * yOp K + ((i+1 : K) • xOp K ^ i) := by
  refine LinearMap.ext fun p => ?_
  change yOp K ((xOp K ^ (i+1)) p) =
    (xOp K ^ (i+1)) (yOp K p) + ((i+1 : K) • ((xOp K ^ i) p))
  rw [xPowApply (K := K) (i+1) p, xPowApply (K := K) (i+1) (yOp K p),
    xPowApply (K := K) i p]
  change derivative (X ^ (i+1) * p) =
    X ^ (i+1) * derivative p + ((i+1 : K) • (X ^ i * p))
  rw [derivative_mul, derivative_X_pow_succ]
  simp [Polynomial.smul_eq_C_mul, mul_assoc]
  ring

private theorem mul_pow_commute (A : Module.End K K[X]) (n : ℕ) :
    A * A ^ n = A ^ n * A := by
  calc
    A * A ^ n = A ^ (n+1) := by rw [← pow_succ']
    _ = A ^ n * A := by rw [pow_succ]

private theorem poly_eval_commute (S : Module.End K K[X]) (p : K[X]) :
    aeval S p * S = S * aeval S p := by
  calc
    aeval S p * S = aeval S p * aeval S X := by rw [aeval_X]
    _ = aeval S (p * X) := (map_mul _ _ _).symm
    _ = aeval S (X * p) := by rw [mul_comm p X]
    _ = aeval S X * aeval S p := map_mul _ _ _
    _ = S * aeval S p := by rw [aeval_X]

private theorem lowerShift_basis (i k : ℕ) :
    aeval (yOp K * xOp K) (lowerShiftPoly (K := K) i) * yOp K ^ k =
      xOp K ^ i * yOp K ^ (i+k) := by
  induction i with
  | zero => simp [lowerShiftPoly]
  | succ i ih =>
      let N : Module.End K K[X] := yOp K * xOp K
      change aeval N (lowerShiftPoly (K := K) i * (X-C ((i+1:ℕ):K))) * yOp K ^ k = _
      rw [map_mul]
      have heval : aeval N (X - C ((i+1:ℕ):K)) =
          N - algebraMap K (Module.End K K[X]) ((i+1:ℕ):K) := by simp
      rw [heval]
      have hN : N = yOp K * xOp K := rfl
      rw [hN] at *
      let A := aeval (yOp K * xOp K) (lowerShiftPoly (K := K) i)
      let c := algebraMap K (Module.End K K[X]) ((i+1:ℕ):K)
      have hAN : A * (yOp K * xOp K) = (yOp K * xOp K) * A :=
        poly_eval_commute _ _
      have hAc : c * A = A * c := Algebra.commutes _ _
      calc
        (A * ((yOp K * xOp K) - c)) * yOp K ^ k =
          ((yOp K * xOp K) - c) * (A * yOp K ^ k) := by
            calc
              _ = ((A * (yOp K * xOp K)) * yOp K ^ k) - ((A*c)*yOp K ^ k) := by simp [mul_sub, sub_mul, mul_assoc]
              _ = (((yOp K * xOp K) * A) * yOp K ^ k) - ((c*A)*yOp K ^ k) := by rw [hAN, hAc.symm]
              _ = _ := by simp [sub_mul, mul_assoc]
        _ = (yOp K * xOp K - algebraMap K (Module.End K K[X]) ((i+1:ℕ):K)) *
            (xOp K ^ i * yOp K ^ (i+k)) := by rw [ih]
        _ = xOp K ^ (i+1) * yOp K ^ (i+k+1) := by
          have hmul := y_mul_xpow_succ (K := K) i
          have hprod : (yOp K * xOp K) * (xOp K ^ i * yOp K ^ (i+k)) =
              xOp K ^ (i+1) * yOp K ^ (i+k+1) + ((i+1:K) • (xOp K ^ i * yOp K ^ (i+k))) := by
            calc
              _ = (yOp K * (xOp K * xOp K ^ i)) * yOp K ^ (i+k) := by simp [mul_assoc]
              _ = (yOp K * xOp K ^ (i+1)) * yOp K ^ (i+k) := by
                rw [← pow_succ' (xOp K) i]
              _ = (xOp K ^ (i+1) * yOp K + ((i+1:K) • xOp K ^ i)) * yOp K ^ (i+k) := by rw [hmul]
              _ = _ := by
                rw [add_mul, smul_mul_assoc]
                rw [mul_assoc, ← pow_succ' (yOp K) (i+k)]
          rw [sub_mul, hprod]
          have hscalar : c * (xOp K ^ i * yOp K ^ (i+k)) =
              ((i+1:K) • (xOp K ^ i * yOp K ^ (i+k))) := by
            dsimp [c]
            rw [Algebra.algebraMap_eq_smul_one]
            simp
          rw [hscalar]
          simp
        _ = xOp K ^ (i+1) * yOp K ^ (i+1+k) := by
          congr 2
          all_goals omega


private theorem grade_expo (i j : ℕ) : grade (expo i j) = (i : ℤ) - j := by
  simp [grade, expo]

private theorem pbw_support_grade_neg [CharZero K] (T : A1 K) (k : ℕ)
    (hgrade : ∀ d ∈ (symbol (T : Module.End K K[X])).support,
      grade d = -(k : ℤ))
    (c : (ℕ × ℕ) →₀ K)
    (hc : c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
      (T : Module.End K K[X])) :
    ∀ p ∈ c.support, p.2 = p.1 + k := by
  intro p hp
  obtain ⟨i, j⟩ := p
  have hcoeff : pbwCoeff (T : Module.End K K[X]) i j = c (i,j) := by
    rw [← hc]
    exact pbwCoeff_finsuppNormalOrderedSum c i j
  have hnonzero : pbwCoeff (T : Module.End K K[X]) i j ≠ 0 := by
    rw [hcoeff]
    exact Finsupp.mem_support_iff.mp hp
  have hs : expo i j ∈ (symbol (T : Module.End K K[X])).support := by
    rw [MvPolynomial.mem_support_iff, symbol_coeff_pbwCoeff]
    exact hnonzero
  have h := hgrade (expo i j) hs
  rw [grade_expo] at h
  omega

private theorem lowerShift_form_sum (c : (ℕ × ℕ) →₀ K) (k : ℕ) :
    aeval (yOp K * xOp K)
      (c.sum (fun p a => a • lowerShiftPoly (K := K) p.1)) * yOp K ^ k =
      c.sum (fun p a => a •
        (aeval (yOp K * xOp K) (lowerShiftPoly (K := K) p.1) * yOp K ^ k)) := by
  classical
  rw [Finsupp.sum, map_sum]
  simp only [map_smul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [smul_mul_assoc]

theorem grade_neg_representation [CharZero K] (T : A1 K) (k : ℕ)
    (hgrade : ∀ d ∈ (symbol (T : Module.End K K[X])).support,
      grade d = -(k : ℤ)) :
    ∃ f : K[X], (T : Module.End K K[X]) =
      aeval (yOp K * xOp K) f * yOp K ^ k := by
  classical
  obtain ⟨c, hc⟩ := A1_exists_finiteNormalOrderedExpansion T
  refine ⟨c.sum (fun p a => a • lowerShiftPoly (K := K) p.1), ?_⟩
  rw [lowerShift_form_sum c k]
  rw [Finsupp.sum] at hc ⊢
  rw [← hc]
  apply Finset.sum_congr rfl
  intro p hp
  have hrel := pbw_support_grade_neg (T := T) k hgrade c hc p hp
  change c p • (xOp K ^ p.1 * yOp K ^ p.2) =
    c p • (aeval (yOp K * xOp K) (lowerShiftPoly (K := K) p.1) * yOp K ^ k)
  rw [hrel, ← lowerShift_basis]

theorem grade_minus_one_representation [CharZero K] (T : A1 K)
    (hgrade : ∀ d ∈ (symbol (T : Module.End K K[X])).support, grade d = -1) :
    ∃ f : K[X], (T : Module.End K K[X]) =
      aeval (yOp K * xOp K) f * yOp K := by
  obtain ⟨f, hf⟩ := grade_neg_representation (T := T) 1 (by simpa using hgrade)
  exact ⟨f, by simpa using hf⟩

private theorem upperShift_basis (i : ℕ) :
    aeval (yOp K * xOp K) (upperShiftPoly (K := K) i) * xOp K =
      xOp K ^ (i+1) * yOp K ^ i := by
  induction i with
  | zero => simp [upperShiftPoly]
  | succ i ih =>
      let N : Module.End K K[X] := yOp K * xOp K
      change aeval N (upperShiftPoly (K := K) i * (X-C ((i+2:ℕ):K))) * xOp K = _
      rw [map_mul]
      have heval : aeval N (X - C ((i+2:ℕ):K)) =
          N - algebraMap K (Module.End K K[X]) ((i+2:ℕ):K) := by simp
      rw [heval]
      have hN : N = yOp K * xOp K := rfl
      rw [hN] at *
      let A := aeval (yOp K * xOp K) (upperShiftPoly (K := K) i)
      let c := algebraMap K (Module.End K K[X]) ((i+2:ℕ):K)
      have hAN : A * (yOp K * xOp K) = (yOp K * xOp K) * A :=
        poly_eval_commute _ _
      have hAc : c * A = A * c := Algebra.commutes _ _
      calc
        (A * ((yOp K * xOp K) - c)) * xOp K =
          ((yOp K * xOp K) - c) * (A * xOp K) := by
            calc
              _ = ((A * (yOp K * xOp K)) * xOp K) - ((A*c)*xOp K) := by simp [mul_sub, sub_mul, mul_assoc]
              _ = (((yOp K * xOp K) * A) * xOp K) - ((c*A)*xOp K) := by rw [hAN, hAc.symm]
              _ = _ := by simp [sub_mul, mul_assoc]
        _ = (yOp K * xOp K - algebraMap K (Module.End K K[X]) ((i+2:ℕ):K)) *
            (xOp K ^ (i+1) * yOp K ^ i) := by rw [ih]
        _ = xOp K ^ (i+2) * yOp K ^ (i+1) := by
          have hmul := y_mul_xpow_succ (K := K) (i+1)
          have hmul' : yOp K * xOp K ^ (i+2) =
              xOp K ^ (i+2) * yOp K +
                (((i:K) + 2) • xOp K ^ (i+1)) := by
            have hcast : ((i+1:ℕ):K) + 1 = (i:K) + 2 := by push_cast; ring
            calc
              yOp K * xOp K ^ (i+2) = yOp K * xOp K ^ (i+1+1) := by
                congr 2
              _ = xOp K ^ (i+1+1) * yOp K + (((i+1:ℕ):K) + 1) • xOp K ^ (i+1) := hmul
              _ = xOp K ^ (i+2) * yOp K + ((i:K)+2) • xOp K ^ (i+1) := by
                rw [hcast]
          have hxp : xOp K * xOp K ^ (i+1) = xOp K ^ (i+2) := by
            calc
              xOp K * xOp K ^ (i+1) = xOp K ^ (i+1) * xOp K :=
                mul_pow_commute (xOp K) (i+1)
              _ = xOp K ^ ((i+1)+1) := (pow_succ (xOp K) (i+1)).symm
              _ = xOp K ^ (i+2) := congrArg (fun n : ℕ => xOp K ^ n) (by omega)
          have hprod : (yOp K * xOp K) * (xOp K ^ (i+1) * yOp K ^ i) =
              xOp K ^ (i+2) * yOp K ^ (i+1) +
                ((i+2:K) • (xOp K ^ (i+1) * yOp K ^ i)) := by
            calc
              _ = (yOp K * xOp K ^ (i+2)) * yOp K ^ i := by
                calc
                  (yOp K * xOp K) * (xOp K ^ (i+1) * yOp K ^ i) =
                      yOp K * (xOp K * xOp K ^ (i+1)) * yOp K ^ i := by simp only [mul_assoc]
                  _ = (yOp K * xOp K ^ (i+2)) * yOp K ^ i := by rw [hxp]
              _ = (xOp K ^ (i+2) * yOp K + (((i:K)+2) • xOp K ^ (i+1))) * yOp K ^ i := by
                rw [hmul']
              _ = _ := by
                rw [add_mul, smul_mul_assoc]
                rw [mul_assoc]
                rw [← pow_succ' (yOp K) i]
          rw [sub_mul, hprod]
          have hscalar : c * (xOp K ^ (i+1) * yOp K ^ i) =
              ((i+2:K) • (xOp K ^ (i+1) * yOp K ^ i)) := by
            dsimp [c]
            rw [Algebra.algebraMap_eq_smul_one]
            simp
          rw [hscalar]
          simp

private theorem upperShift_form_sum (c : (ℕ × ℕ) →₀ K) :
    aeval (yOp K * xOp K)
      (c.sum (fun p a => a • upperShiftPoly (K := K) p.2)) * xOp K =
      c.sum (fun p a => a •
        (aeval (yOp K * xOp K) (upperShiftPoly (K := K) p.2) * xOp K)) := by
  classical
  rw [Finsupp.sum, map_sum]
  simp only [map_smul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [smul_mul_assoc]

private theorem pbw_support_grade_plus_one [CharZero K] (T : A1 K)
    (hgrade : ∀ d ∈ (symbol (T : Module.End K K[X])).support, grade d = 1)
    (c : (ℕ × ℕ) →₀ K)
    (hc : c.sum (fun p a => a • normalOrderedMonomial (K := K) p.1 p.2) =
      (T : Module.End K K[X])) :
    ∀ p ∈ c.support, p.1 = p.2 + 1 := by
  intro p hp
  obtain ⟨i, j⟩ := p
  have hcoeff : pbwCoeff (T : Module.End K K[X]) i j = c (i,j) := by
    rw [← hc]
    exact pbwCoeff_finsuppNormalOrderedSum c i j
  have hnonzero : pbwCoeff (T : Module.End K K[X]) i j ≠ 0 := by
    rw [hcoeff]
    exact Finsupp.mem_support_iff.mp hp
  have hs : expo i j ∈ (symbol (T : Module.End K K[X])).support := by
    rw [MvPolynomial.mem_support_iff, symbol_coeff_pbwCoeff]
    exact hnonzero
  have h := hgrade (expo i j) hs
  rw [grade_expo] at h
  omega

theorem grade_plus_one_representation [CharZero K] (T : A1 K)
    (hgrade : ∀ d ∈ (symbol (T : Module.End K K[X])).support, grade d = 1) :
    ∃ g : K[X], (T : Module.End K K[X]) =
      aeval (yOp K * xOp K) g * xOp K := by
  classical
  obtain ⟨c, hc⟩ := A1_exists_finiteNormalOrderedExpansion T
  refine ⟨c.sum (fun p a => a • upperShiftPoly (K := K) p.2), ?_⟩
  rw [upperShift_form_sum]
  rw [Finsupp.sum] at hc ⊢
  rw [← hc]
  apply Finset.sum_congr rfl
  intro p hp
  have hrel := pbw_support_grade_plus_one (T := T) hgrade c hc p hp
  change c p • (xOp K ^ p.1 * yOp K ^ p.2) =
    c p • (aeval (yOp K * xOp K) (upperShiftPoly (K := K) p.2) * xOp K)
  rw [hrel, ← upperShift_basis]

private theorem adjacent_normal_forms_source_order_forces_constant [CharZero K]
    (f g : K[X])
    (hcomm : (aeval (yOp K * xOp K) f * yOp K) *
      (aeval (yOp K * xOp K) g * xOp K) -
      (aeval (yOp K * xOp K) g * xOp K) *
      (aeval (yOp K * xOp K) f * yOp K) = 1) :
    f.natDegree = 0 ∧ g.natDegree = 0 := by
  let A : Module.End K K[X] := aeval (yOp K * xOp K) f * yOp K
  let B : Module.End K K[X] := aeval (yOp K * xOp K) g * xOp K
  have hAB : A * B - B * A = 1 := by simpa [A, B] using hcomm
  have hminus : aeval (yOp K * xOp K) (-f) * yOp K = -A := by
    dsimp [A]
    rw [map_neg]
    exact neg_mul (aeval (yOp K * xOp K) f) (yOp K)
  have h1 : B * (-A) = -(B * A) := mul_neg B A
  have h2 : (-A) * B = -(A * B) := neg_mul A B
  have hrel : (aeval (yOp K * xOp K) g * xOp K) *
      (aeval (yOp K * xOp K) (-f) * yOp K) -
      (aeval (yOp K * xOp K) (-f) * yOp K) *
      (aeval (yOp K * xOp K) g * xOp K) = 1 := by
    rw [hminus]
    calc
      B * (-A) - (-A) * B = -(B * A) - -(A * B) := by rw [h1, h2]
      _ = A * B - B * A := by abel
      _ = 1 := hAB
  have hconst := yx_normal_forms_exact_relation_forces_factors_constant (-f) g hrel
  constructor
  · simpa using hconst.1
  · exact hconst.2

/-- An exact adjacent-grade pair with the source bracket order forces both shifted
polynomial factors to be constant. This is the algebraic core of Han–Tan case `(a.2)`;
the theorem does not itself perform the Newton-grade extraction. -/
theorem adjacent_grade_exact_pair_forces_constant [CharZero K]
    (P Q : A1 K)
    (hPgrade : ∀ d ∈ (symbol (P : Module.End K K[X])).support, grade d = -1)
    (hQgrade : ∀ d ∈ (symbol (Q : Module.End K K[X])).support, grade d = 1)
    (hcomm : (P : Module.End K K[X]) * (Q : Module.End K K[X]) -
      (Q : Module.End K K[X]) * (P : Module.End K K[X]) = 1) :
    ∃ f g : K[X],
      (P : Module.End K K[X]) = aeval (yOp K * xOp K) f * yOp K ∧
      (Q : Module.End K K[X]) = aeval (yOp K * xOp K) g * xOp K ∧
      f.natDegree = 0 ∧ g.natDegree = 0 := by
  obtain ⟨f, hf⟩ := grade_minus_one_representation P hPgrade
  obtain ⟨g, hg⟩ := grade_plus_one_representation Q hQgrade
  have hnormal : (aeval (yOp K * xOp K) f * yOp K) *
      (aeval (yOp K * xOp K) g * xOp K) -
      (aeval (yOp K * xOp K) g * xOp K) *
      (aeval (yOp K * xOp K) f * yOp K) = 1 := by
    rw [← hf, ← hg]
    exact hcomm
  have hconst := adjacent_normal_forms_source_order_forces_constant f g hnormal
  exact ⟨f, g, hf, hg, hconst.1, hconst.2⟩

/-- The PBW symbol of differentiation is the single monomial `y`. -/
theorem symbol_yOp [CharZero K] : symbol (yOp K) = MvPolynomial.X 1 := by
  have hcoeff (i j : ℕ) :
      pbwCoeff (yOp K) i j = if i = 0 ∧ j = 1 then 1 else 0 := by
    simpa [normalOrderedMonomial] using
      (pbwCoeff_normalOrdered_monomial (K := K) 0 1 i j)
  unfold symbol
  rw [finsum_eq_single _ (0, 1)]
  · simp [hcoeff, expo, MvPolynomial.X]
  · rintro ⟨i, j⟩ hne
    rw [hcoeff, if_neg]
    · simp
    · rintro ⟨rfl, rfl⟩
      exact hne rfl

/-- In the adjacent-grade exact pair, the remaining `j = 1` branch of the
source argument is impossible when the first component is nonmonomial. Constant
shifted factors force that component to be a scalar multiple of `Y`, whose PBW
symbol has only one support point. -/
theorem adjacent_grade_exact_pair_nonmonomial_impossible [CharZero K]
    (P Q : A1 K)
    (hPgrade : ∀ d ∈ (symbol (P : Module.End K K[X])).support, grade d = -1)
    (hQgrade : ∀ d ∈ (symbol (Q : Module.End K K[X])).support, grade d = 1)
    (hcomm : (P : Module.End K K[X]) * (Q : Module.End K K[X]) -
      (Q : Module.End K K[X]) * (P : Module.End K K[X]) = 1)
    (hPnonmonomial : 1 < (symbol (P : Module.End K K[X])).support.card) : False := by
  obtain ⟨f, g, hf, hg, hfdeg, _hgdeg⟩ :=
    adjacent_grade_exact_pair_forces_constant P Q hPgrade hQgrade hcomm
  have hfc : f = C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hfdeg
  let yA : A1 K := ⟨yOp K, yOp_mem_A1⟩
  have hPscalar : P = (f.coeff 0) • yA := by
    apply Subtype.ext
    rw [hf, hfc]
    simp [yA, Algebra.algebraMap_eq_smul_one]
  have hsymbol :
      symbol (P : Module.End K K[X]) = (f.coeff 0) • MvPolynomial.X 1 := by
    rw [hPscalar, symbol_smul, symbol_yOp]
  have hcard : (symbol (P : Module.End K K[X])).support.card ≤ 1 := by
    rw [hsymbol]
    calc
      ((f.coeff 0) • (MvPolynomial.X 1 : MvPolynomial (Fin 2) K)).support.card ≤
          (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).support.card :=
        Finset.card_le_card (MvPolynomial.support_smul)
      _ = 1 := by simp [MvPolynomial.support_X]
  omega

end Dixmier.Weyl
