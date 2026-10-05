/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PositiveGradeNormalForms
public import DixmierFormal.Scalar.FiniteDifference

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Exact commutator for arbitrary opposite homogeneous grades

This file derives the scalar finite-difference identity from the exact Weyl
relation for arbitrary pure grades, rather than from its leading Poisson term.
-/

namespace Dixmier.Weyl

open Polynomial

variable {K : Type*} [Field K]

noncomputable def risingFactorialPoly (k : ℕ) : K[X] :=
  ∏ i ∈ Finset.range k, (X + C (i : K))

private theorem risingFactorialPoly_succ (k : ℕ) :
    risingFactorialPoly (K := K) (k+1) =
      (X + C (k : K)) * risingFactorialPoly (K := K) k := by
  simp [risingFactorialPoly, Finset.prod_range_succ, mul_comm]

private theorem falling_comp_add_eq_rising (k : ℕ) :
    (Dixmier.fallingFactorialPoly (K := K) k).comp (X + C (k : K)) =
      risingFactorialPoly (K := K) k := by
  calc
    (Dixmier.fallingFactorialPoly (K := K) k).comp (X + C (k:K)) =
        ∏ i ∈ Finset.range k,
          (X - C ((i+1:ℕ):K)).comp (X + C (k:K)) := by
            rw [Dixmier.fallingFactorialPoly, Polynomial.prod_comp]
    _ =
        ∏ i ∈ Finset.range k, (X + C (k:K) - C ((i+1:ℕ):K)) := by
          simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    _ = ∏ i ∈ Finset.range k, (X + C ((k-1-i:ℕ):K)) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      have hnat : k - (i+1) = k-1-i := by omega
      have hcast : ((k-(i+1):ℕ):K) = ((k-1-i:ℕ):K) :=
        congrArg (fun n : ℕ => (n : K)) hnat
      have hcoeff : (k : K) - ((i+1:ℕ):K) = ((k-1-i:ℕ):K) := by
        rw [← Nat.cast_sub (by omega : i+1 ≤ k)]
        exact hcast
      have hC : C (k : K) - C ((i+1:ℕ):K) = C ((k-1-i:ℕ):K) := by
        rw [← map_sub]
        exact congrArg C hcoeff
      calc
        X + C (k:K) - C ((i+1:ℕ):K) = X +
            (C (k:K) - C ((i+1:ℕ):K)) := by abel
        _ = X + C ((k-1-i:ℕ):K) := by rw [hC]
    _ = risingFactorialPoly (K := K) k := by
      simpa [risingFactorialPoly] using
        (Finset.prod_range_reflect (fun i : ℕ => X + C (i:K)) k)

private theorem ypow_yx_shift (k : ℕ) :
    yOp K ^ k * (yOp K * xOp K) =
      (yOp K * xOp K) * yOp K ^ k + (k : K) • yOp K ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hYS : yOp K * (yOp K * xOp K) =
          (yOp K * xOp K + 1) * yOp K :=
        by simpa only [aeval_X] using (yOp_aeval_yx_shift (K := K) X)
      rw [pow_succ]
      calc
        (yOp K ^ k * yOp K) * (yOp K * xOp K) =
            yOp K ^ k * (yOp K * (yOp K * xOp K)) := by simp [mul_assoc]
        _ = yOp K ^ k * ((yOp K * xOp K + 1) * yOp K) := by rw [hYS]
        _ = (yOp K ^ k * (yOp K * xOp K + 1)) * yOp K := by simp [mul_assoc]
        _ = (yOp K ^ k * (yOp K * xOp K) + yOp K ^ k) * yOp K := by
          rw [mul_add]
          simp
        _ = ((yOp K * xOp K) * yOp K ^ k + (k : K) • yOp K ^ k +
              yOp K ^ k) * yOp K := by rw [ih]
        _ = (yOp K * xOp K) * yOp K ^ (k+1) + ((k+1 : ℕ) : K) • yOp K ^ (k+1) := by
          rw [pow_succ]
          rw [Nat.cast_succ, add_smul]
          simp [add_mul, mul_assoc]
          abel

private theorem xpow_yx_shift (k : ℕ) :
    xOp K ^ k * (yOp K * xOp K) =
      (yOp K * xOp K) * xOp K ^ k - (k : K) • xOp K ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hXS : xOp K * (yOp K * xOp K) =
          (yOp K * xOp K - 1) * xOp K :=
        by simpa only [aeval_X] using (xOp_aeval_yx_shift (K := K) X)
      rw [pow_succ]
      calc
        (xOp K ^ k * xOp K) * (yOp K * xOp K) =
            xOp K ^ k * (xOp K * (yOp K * xOp K)) := by simp [mul_assoc]
        _ = xOp K ^ k * ((yOp K * xOp K - 1) * xOp K) := by rw [hXS]
        _ = (xOp K ^ k * (yOp K * xOp K - 1)) * xOp K := by simp [mul_assoc]
        _ = (xOp K ^ k * (yOp K * xOp K) - xOp K ^ k) * xOp K := by
          rw [mul_sub]
          simp
        _ = ((yOp K * xOp K) * xOp K ^ k - (k : K) • xOp K ^ k -
              xOp K ^ k) * xOp K := by rw [ih]
        _ = (yOp K * xOp K) * xOp K ^ (k+1) - ((k+1 : ℕ) : K) • xOp K ^ (k+1) := by
          rw [pow_succ]
          rw [Nat.cast_succ, add_smul]
          simp [sub_mul, mul_assoc]
          abel

private theorem ypow_yx_shift_map (k : ℕ) :
    yOp K ^ k * (yOp K * xOp K) =
      (yOp K * xOp K + algebraMap K (Module.End K K[X]) (k : K)) * yOp K ^ k := by
  rw [ypow_yx_shift]
  rw [Algebra.algebraMap_eq_smul_one]
  simp [add_mul, mul_assoc]

private theorem xpow_yx_shift_map (k : ℕ) :
    xOp K ^ k * (yOp K * xOp K) =
      (yOp K * xOp K - algebraMap K (Module.End K K[X]) (k : K)) * xOp K ^ k := by
  rw [xpow_yx_shift]
  rw [Algebra.algebraMap_eq_smul_one]
  simp [sub_mul, mul_assoc]

private theorem aeval_yx_comp_add_nat (k : ℕ) (p : K[X]) :
    aeval (yOp K * xOp K) (p.comp (X + C (k : K))) =
      aeval (yOp K * xOp K + algebraMap K (Module.End K K[X]) (k : K)) p := by
  rw [aeval_comp]
  simp [aeval_X]

private theorem aeval_yx_comp_sub_nat (k : ℕ) (p : K[X]) :
    aeval (yOp K * xOp K) (p.comp (X - C (k : K))) =
      aeval (yOp K * xOp K - algebraMap K (Module.End K K[X]) (k : K)) p := by
  rw [aeval_comp]
  simp [aeval_X]

private theorem ypow_aeval_yx_shift (k : ℕ) (p : K[X]) :
    yOp K ^ k * aeval (yOp K * xOp K) p =
      aeval (yOp K * xOp K) (p.comp (X + C (k : K))) * yOp K ^ k := by
  have h := polynomial_aeval_intertwining (K := K) (R := Module.End K K[X])
    (yOp K * xOp K) (yOp K ^ k)
    (algebraMap K (Module.End K K[X]) (k : K)) (ypow_yx_shift_map k) p
  rw [← aeval_yx_comp_add_nat] at h
  exact h

private theorem xpow_aeval_yx_shift (k : ℕ) (p : K[X]) :
    xOp K ^ k * aeval (yOp K * xOp K) p =
      aeval (yOp K * xOp K) (p.comp (X - C (k : K))) * xOp K ^ k := by
  have h := polynomial_aeval_intertwining (K := K) (R := Module.End K K[X])
    (yOp K * xOp K) (xOp K ^ k)
    (-algebraMap K (Module.End K K[X]) (k : K)) (by
      rw [xpow_yx_shift_map]
      congr 1) p
  have hcomp : aeval (yOp K * xOp K)
      (p.comp (X - C (k : K))) =
    aeval (yOp K * xOp K + -algebraMap K (Module.End K K[X]) (k : K)) p := by
    rw [aeval_yx_comp_sub_nat]
    congr 1
  rw [← hcomp] at h
  exact h

private theorem fallingFactorialPoly_succ (k : ℕ) :
    Dixmier.fallingFactorialPoly (K := K) (k+1) =
      (X - C ((k+1:ℕ):K)) * Dixmier.fallingFactorialPoly (K := K) k := by
  simp [Dixmier.fallingFactorialPoly, Finset.prod_range_succ, mul_comm]

private theorem ypow_xpow_eq_rising (k : ℕ) :
    yOp K ^ k * xOp K ^ k =
      aeval (yOp K * xOp K) (risingFactorialPoly (K := K) k) := by
  induction k with
  | zero => simp [risingFactorialPoly]
  | succ k ih =>
      have hS : yOp K * xOp K + algebraMap K (Module.End K K[X]) (k : K) =
          aeval (yOp K * xOp K) (X + C (k : K)) := by simp [aeval_X]
      calc
        yOp K ^ (k+1) * xOp K ^ (k+1) =
            (yOp K ^ k * (yOp K * xOp K)) * xOp K ^ k := by
              rw [pow_succ, pow_succ']
              simp [mul_assoc]
        _ = ((yOp K * xOp K + algebraMap K (Module.End K K[X]) (k : K)) *
              yOp K ^ k) * xOp K ^ k := by rw [ypow_yx_shift_map]
        _ = (yOp K * xOp K + algebraMap K (Module.End K K[X]) (k : K)) *
              (yOp K ^ k * xOp K ^ k) := by simp [mul_assoc]
        _ = aeval (yOp K * xOp K) (X + C (k : K)) *
              aeval (yOp K * xOp K) (risingFactorialPoly (K := K) k) := by
                rw [hS, ih]
        _ = aeval (yOp K * xOp K)
              ((X + C (k : K)) * risingFactorialPoly (K := K) k) :=
                (map_mul _ _ _).symm
        _ = aeval (yOp K * xOp K) (risingFactorialPoly (K := K) (k+1)) := by
              rw [risingFactorialPoly_succ]

private theorem xpow_xy_factor (k : ℕ) :
    xOp K ^ k * (xOp K * yOp K) =
      (yOp K * xOp K -
        algebraMap K (Module.End K K[X]) ((k+1:ℕ):K)) * xOp K ^ k := by
  have hcomm : yOp K * xOp K - xOp K * yOp K = 1 :=
    yOp_mul_xOp_sub_xOp_mul_yOp (K := K)
  calc
    xOp K ^ k * (xOp K * yOp K) = xOp K ^ k * (yOp K * xOp K - 1) := by
      congr 1
      calc
        xOp K * yOp K = yOp K * xOp K - (yOp K * xOp K - xOp K * yOp K) := by abel
        _ = yOp K * xOp K - 1 := by rw [hcomm]
    _ = xOp K ^ k * (yOp K * xOp K) - xOp K ^ k := by simp [mul_sub]
    _ = (yOp K * xOp K - algebraMap K (Module.End K K[X]) (k : K)) *
          xOp K ^ k - xOp K ^ k := by rw [xpow_yx_shift_map]
    _ = (yOp K * xOp K -
          algebraMap K (Module.End K K[X]) ((k+1:ℕ):K)) * xOp K ^ k := by
      have hcast : algebraMap K (Module.End K K[X]) ((k+1:ℕ):K) =
          algebraMap K (Module.End K K[X]) (k:K) + 1 := by simp [Nat.cast_succ]
      rw [hcast]
      simp [sub_mul, add_mul, mul_assoc]
      abel

private theorem xpow_ypow_eq_falling (k : ℕ) :
    xOp K ^ k * yOp K ^ k =
      aeval (yOp K * xOp K) (Dixmier.fallingFactorialPoly (K := K) k) := by
  induction k with
  | zero => simp [Dixmier.fallingFactorialPoly]
  | succ k ih =>
      have hS : yOp K * xOp K - algebraMap K (Module.End K K[X]) ((k+1:ℕ):K) =
          aeval (yOp K * xOp K) (X - C ((k+1:ℕ):K)) := by simp [aeval_X]
      calc
        xOp K ^ (k+1) * yOp K ^ (k+1) =
            (xOp K ^ k * (xOp K * yOp K)) * yOp K ^ k := by
              rw [pow_succ, pow_succ']
              simp [mul_assoc]
        _ = ((yOp K * xOp K -
              algebraMap K (Module.End K K[X]) ((k+1:ℕ):K)) * xOp K ^ k) * yOp K ^ k :=
                by rw [xpow_xy_factor]
        _ = (yOp K * xOp K -
              algebraMap K (Module.End K K[X]) ((k+1:ℕ):K)) *
              (xOp K ^ k * yOp K ^ k) := by simp [mul_assoc]
        _ = aeval (yOp K * xOp K) (X - C ((k+1:ℕ):K)) *
              aeval (yOp K * xOp K) (Dixmier.fallingFactorialPoly (K := K) k) := by
                rw [hS, ih]
        _ = aeval (yOp K * xOp K)
              ((X - C ((k+1:ℕ):K)) * Dixmier.fallingFactorialPoly (K := K) k) :=
                (map_mul _ _ _).symm
        _ = aeval (yOp K * xOp K)
              (Dixmier.fallingFactorialPoly (K := K) (k+1)) := by
                rw [fallingFactorialPoly_succ]

/-- Exact multiplication formula for the two arbitrary opposite-grade normal forms.
The middle factor is the falling factorial of degree `k`; composing it with the
step-`k` translation gives the rising factor in the reverse product. -/
theorem opposite_grade_normal_form_commutator (f g : K[X]) (k : ℕ) :
    ((aeval (yOp K * xOp K) g * xOp K ^ k) *
        (aeval (yOp K * xOp K) f * yOp K ^ k) -
      (aeval (yOp K * xOp K) f * yOp K ^ k) *
        (aeval (yOp K * xOp K) g * xOp K ^ k)) =
      aeval (yOp K * xOp K)
        (g * f.comp (X - C (k : K)) * Dixmier.fallingFactorialPoly (K := K) k -
          f * g.comp (X + C (k : K)) * risingFactorialPoly (K := K) k) := by
  have hQP : (aeval (yOp K * xOp K) g * xOp K ^ k) *
        (aeval (yOp K * xOp K) f * yOp K ^ k) =
      aeval (yOp K * xOp K)
        (g * f.comp (X - C (k : K)) * Dixmier.fallingFactorialPoly (K := K) k) := by
    calc
      _ = aeval (yOp K * xOp K) g *
            (xOp K ^ k * aeval (yOp K * xOp K) f) * yOp K ^ k := by
              simp [mul_assoc]
      _ = aeval (yOp K * xOp K) g *
            (aeval (yOp K * xOp K) (f.comp (X - C (k:K))) * xOp K ^ k) *
            yOp K ^ k := by rw [xpow_aeval_yx_shift]
      _ = aeval (yOp K * xOp K) g *
            aeval (yOp K * xOp K) (f.comp (X - C (k:K))) *
            (xOp K ^ k * yOp K ^ k) := by simp [mul_assoc]
      _ = aeval (yOp K * xOp K)
            (g * f.comp (X - C (k:K)) * Dixmier.fallingFactorialPoly (K := K) k) := by
              rw [xpow_ypow_eq_falling]
              simp only [map_mul]
  have hPQ : (aeval (yOp K * xOp K) f * yOp K ^ k) *
        (aeval (yOp K * xOp K) g * xOp K ^ k) =
      aeval (yOp K * xOp K)
        (f * g.comp (X + C (k : K)) * risingFactorialPoly (K := K) k) := by
    calc
      _ = aeval (yOp K * xOp K) f *
            (yOp K ^ k * aeval (yOp K * xOp K) g) * xOp K ^ k := by
              simp [mul_assoc]
      _ = aeval (yOp K * xOp K) f *
            (aeval (yOp K * xOp K) (g.comp (X + C (k:K))) * yOp K ^ k) *
            xOp K ^ k := by rw [ypow_aeval_yx_shift]
      _ = aeval (yOp K * xOp K) f *
            aeval (yOp K * xOp K) (g.comp (X + C (k:K))) *
            (yOp K ^ k * xOp K ^ k) := by simp [mul_assoc]
      _ = aeval (yOp K * xOp K)
            (f * g.comp (X + C (k:K)) * risingFactorialPoly (K := K) k) := by
              rw [ypow_xpow_eq_rising]
              simp only [map_mul]
  calc
    _ = aeval (yOp K * xOp K)
          (g * f.comp (X - C (k:K)) * Dixmier.fallingFactorialPoly (K := K) k) -
        aeval (yOp K * xOp K)
          (f * g.comp (X + C (k:K)) * risingFactorialPoly (K := K) k) := by
            rw [hQP, hPQ]
    _ = _ := (map_sub _ _ _).symm

private theorem falling_product_comp_add (f g : K[X]) (k : ℕ) :
    (g * f.comp (X - C (k : K)) * Dixmier.fallingFactorialPoly (K := K) k).comp
        (X + C (k : K)) =
      f * g.comp (X + C (k : K)) * risingFactorialPoly (K := K) k := by
  rw [Polynomial.mul_comp, Polynomial.mul_comp, Polynomial.comp_assoc,
    falling_comp_add_eq_rising]
  have hcancel : (X - C (k:K)).comp (X + C (k:K)) = X := by
    simp [Polynomial.sub_comp, Polynomial.X_comp]
  rw [hcancel]
  simp only [Polynomial.comp_X]
  ring

/-- For the exact relation in arbitrary opposite grades, evaluation injectivity turns the
operator commutator into the step-`k` scalar difference used by the terminal degree lemma. -/
theorem opposite_grade_normal_forms_commutator_eq_scalar [CharZero K]
    (f g : K[X]) (k : ℕ)
    (h : (aeval (yOp K * xOp K) g * xOp K ^ k) *
          (aeval (yOp K * xOp K) f * yOp K ^ k) -
        (aeval (yOp K * xOp K) f * yOp K ^ k) *
          (aeval (yOp K * xOp K) g * xOp K ^ k) = 1) :
    g * f.comp (X - C (k : K)) * Dixmier.fallingFactorialPoly (K := K) k -
      (g * f.comp (X - C (k : K)) * Dixmier.fallingFactorialPoly (K := K) k).comp
        (X + C (k : K)) = 1 := by
  have hop := opposite_grade_normal_form_commutator (K := K) f g k
  have heval : aeval (yOp K * xOp K)
      (g * f.comp (X - C (k:K)) * Dixmier.fallingFactorialPoly (K := K) k -
        (g * f.comp (X - C (k:K)) * Dixmier.fallingFactorialPoly (K := K) k).comp
          (X + C (k:K))) = 1 := by
    rw [opposite_grade_normal_form_commutator] at h
    rw [← falling_product_comp_add] at h
    exact h
  have hEvalOne : aeval (yOp K * xOp K)
      (g * f.comp (X - C (k:K)) * Dixmier.fallingFactorialPoly (K := K) k -
        (g * f.comp (X - C (k:K)) * Dixmier.fallingFactorialPoly (K := K) k).comp
          (X + C (k:K))) = aeval (yOp K * xOp K) (1 : K[X]) := by
    simpa using heval
  simpa using (aeval_yx_injective (K := K) hEvalOne)

/-- An exact Weyl pair supported in opposite pure grades must have grades `-1` and `+1`;
the polynomial factors in both Euler-operator normal forms are constant. This is the
full-operator homogeneous-pair terminal step, with no Poisson truncation. -/
theorem opposite_grade_exact_pair_forces_generator_forms [CharZero K]
    (P Q : A1 K) (k : ℕ) (hk : 0 < k)
    (hPgrade : ∀ d ∈ (symbol (P : Module.End K K[X])).support, grade d = -(k : ℤ))
    (hQgrade : ∀ d ∈ (symbol (Q : Module.End K K[X])).support, grade d = (k : ℤ))
    (hcomm : Q * P - P * Q = 1) :
    ∃ f g : K[X],
      (P : Module.End K K[X]) = aeval (yOp K * xOp K) f * yOp K ^ k ∧
      (Q : Module.End K K[X]) = aeval (yOp K * xOp K) g * xOp K ^ k ∧
      k = 1 ∧ f.natDegree = 0 ∧ g.natDegree = 0 := by
  obtain ⟨f, hf⟩ := grade_neg_representation P k hPgrade
  obtain ⟨g, hg⟩ := grade_nat_representation Q k hQgrade
  have hcommOp : (Q : Module.End K K[X]) * (P : Module.End K K[X]) -
      (P : Module.End K K[X]) * (Q : Module.End K K[X]) = 1 := by
    have hh := congrArg (fun z : A1 K => (z : Module.End K K[X])) hcomm
    simpa using hh
  have hcommNF : (aeval (yOp K * xOp K) g * xOp K ^ k) *
        (aeval (yOp K * xOp K) f * yOp K ^ k) -
      (aeval (yOp K * xOp K) f * yOp K ^ k) *
        (aeval (yOp K * xOp K) g * xOp K ^ k) = 1 := by
    rw [← hg, ← hf]
    exact hcommOp
  have hdiff := opposite_grade_normal_forms_commutator_eq_scalar f g k hcommNF
  have hfactor : g * f.comp (X - C (k : K)) *
        Dixmier.fallingFactorialPoly (K := K) k =
      g * Dixmier.fallingFactorialPoly (K := K) k * f.comp (X - C (k : K)) := by
    ring
  rw [hfactor] at hdiff
  have hg0 : g ≠ 0 := by
    intro hzero
    simp [hzero] at hdiff
  have hfshift0 : f.comp (X - C (k : K)) ≠ 0 := by
    intro hzero
    rw [hzero] at hdiff
    simp at hdiff
  have hrigid := Dixmier.fallingFactorial_shift_difference_forces_generator_case
    g (f.comp (X - C (k : K))) k hk hg0 hfshift0 hdiff
  have hfdeg : f.natDegree = 0 := by
    have hdegree : (f.comp (X - C (k : K))).natDegree = f.natDegree := by
      rw [natDegree_comp, natDegree_X_sub_C, Nat.mul_one]
    omega
  exact ⟨f, g, hf, hg, hrigid.2.1, hfdeg, hrigid.1⟩

end Dixmier.Weyl
