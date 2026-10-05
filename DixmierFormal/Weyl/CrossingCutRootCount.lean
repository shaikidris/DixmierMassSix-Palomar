/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CrossingTermCount
public import DixmierFormal.Weyl.CrossingScalarBridge
public import DixmierFormal.Scalar.GeneralRootDegree
public import DixmierFormal.Weyl.RamifiedCutSetup
public import DixmierFormal.Weyl.CrossingGeneralFaceWeight

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Root count of an actual strict-crossing cut polynomial

Specializing the normalized homogeneous face at `x=1` identifies the
operator's `cutPoly` with the powered scalar face. The scalar companion
equation then bounds its distinct roots without a degree or mass cutoff.
-/

namespace Dixmier.Weyl
open Polynomial MvPolynomial

/-- For an explicitly normalized strict-crossing face, the scalar
companion degree equation supplies G13's endpoint identity using the
*actual* cut polynomial. The leading-weight formula follows from the
same nonzero powered face. -/
theorem crossing_power_face_cutPoly_companion_degree_identity
    (P : A1 ℂ) (ρ s a b k : ℕ) (μ : ℂ) (r f : ℂ[X])
    (hsρ : s < ρ) (hab : b < a) (hμ : μ ≠ 0)
    (hr0 : r.coeff 0 = 1) (hr : 0 < r.natDegree)
    (hface : leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
        r.eval₂ MvPolynomial.C
          (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) ^ k)
    (hcutNonzero : cutPoly ρ (-(s : ℤ)) P.1 ≠ 0)
    (hscalar : Polynomial.C ((ρ : ℂ) - s) * Polynomial.X * f * r.derivative -
      ((Polynomial.C ((a : ℂ) - b) * f +
          Polynomial.C ((ρ : ℂ) * a - (s : ℂ) * b) * Polynomial.X *
          f.derivative + 1) * r) = 0) :
    vDeg ρ (-(s : ℤ)) P.1 * ((1+ρ*f.natDegree : ℕ) : ℤ) =
      ((ρ : ℤ) + ramifiedCutExponent ρ ρ (-(s : ℤ))) *
        ((cutPoly ρ (-(s : ℤ)) P.1).natDegree : ℤ) := by
  have hdeg := (crossing_general_scalar_facts ρ s a b r f
    hsρ hab hr0 hr hscalar).2.2.1
  have hnum := crossing_scalar_degree_cut_endpoint_identity
    ρ s a b r.natDegree f.natDegree hsρ hab hdeg
  have hcut := crossingFace_general_cutPoly_natDegree
    μ a b s ρ k r P hμ (by omega) hr0 hface
  have hPweight := crossingFace_general_weight P μ a b s ρ k r
    hsρ hab hcutNonzero hface
  have hk : ramifiedCutExponent ρ ρ (-(s : ℤ)) = -(s : ℤ) := by
    have hρZ : (0 : ℤ) < ρ := by exact_mod_cast (by omega : 0 < ρ)
    have hself : ((ρ : ℤ) / ρ) = 1 := by
      apply mul_left_cancel₀ (ne_of_gt hρZ)
      simpa only [mul_one] using
        (Int.mul_ediv_cancel' (dvd_refl (ρ : ℤ)))
    simp [ramifiedCutExponent, hself]
  rw [hPweight, hcut, hk]
  have hnumZ : (((ρ*a-s*b)*(1+ρ*f.natDegree) : ℕ) : ℤ) =
      (((ρ-s)*(b+ρ*r.natDegree) : ℕ) : ℤ) := by exact_mod_cast hnum
  have hsub : ((ρ-s : ℕ) : ℤ) = (ρ : ℤ) - s := by
    exact Nat.cast_sub hsρ.le
  simp only [Nat.cast_mul, Nat.cast_add] at hnumZ ⊢
  rw [hsub] at hnumZ
  nlinarith [congrArg (fun z : ℤ => (k : ℤ)*z) hnumZ]

private theorem homogeneous_specialization_coeff_sum
    (F : MvPolynomial (Fin 2) ℂ) (j : ℕ) :
    (MvPolynomial.eval₂ Polynomial.C
      (fun i : Fin 2 => if i = 0 then 1 else Polynomial.X) F).coeff j =
      ∑ d ∈ F.support,
        if d 1 = j then MvPolynomial.coeff d F else 0 := by
  rw [MvPolynomial.eval₂_eq']
  simp_rw [show ∀ d : Fin 2 →₀ ℕ,
      (∏ i : Fin 2, (if i = 0 then (1 : ℂ[X]) else Polynomial.X) ^ d i) =
        (Polynomial.X : ℂ[X]) ^ d 1 from by intro d; simp [Fin.prod_univ_two]]
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : d 1 = j
  · simp [h]
  · have hj : j ≠ d 1 := Ne.symm h
    simp [h, hj]

/-- Homogeneity and positive `ρ` prevent cancellation when `x=1`:
the coefficient at a face point's `Y` exponent survives unchanged. -/
theorem homogeneous_specialization_coeff_at_support
    (F : MvPolynomial (Fin 2) ℂ) (ρ σ degree : ℤ)
    (hρ : 0 < ρ)
    (hhom : F.IsWeightedHomogeneous (wt ρ σ) degree)
    (i j : ℕ)
    (hw : (i : ℤ) * ρ + (j : ℤ) * σ = degree) :
    (MvPolynomial.eval₂ Polynomial.C
      (fun t : Fin 2 => if t = 0 then 1 else Polynomial.X) F).coeff j =
      MvPolynomial.coeff (expo i j) F := by
  rw [homogeneous_specialization_coeff_sum]
  calc
    (∑ d ∈ F.support,
      if d 1 = j then MvPolynomial.coeff d F else 0) =
        if (expo i j) 1 = j then MvPolynomial.coeff (expo i j) F else 0 := by
      apply Finset.sum_eq_single (expo i j)
      · intro d hd hne
        have hdj : d 1 ≠ j := by
          intro he
          obtain ⟨⟨a,b⟩,rfl⟩ := expo_surjective d
          have hb : b = j := by simpa [expo] using he
          have hweight := hhom (MvPolynomial.mem_support_iff.mp hd)
          rw [expo_weight] at hweight
          change (a : ℤ) * ρ + (b : ℤ) * σ = degree at hweight
          have ha : a = i := by
            have hmul : (a : ℤ) * ρ = (i : ℤ) * ρ := by
              rw [hb] at hweight
              omega
            have hcast : (a : ℤ) = (i : ℤ) :=
              (mul_right_cancel₀ (ne_of_gt hρ)) hmul
            exact_mod_cast hcast
          exact hne (by subst a; subst b; rfl)
        simp [hdj]
      · intro hnot
        have hz : MvPolynomial.coeff (expo i j) F = 0 :=
          MvPolynomial.notMem_support_iff.mp hnot
        simp [hz]
    _ = _ := by simp [expo]

/-- On a positive-`ρ` homogeneous face, specializing `x=1` preserves
the maximum `Y` exponent exactly. -/
theorem homogeneous_specialization_natDegree_eq_degreeOf_Y
    (F : MvPolynomial (Fin 2) ℂ) (ρ σ degree : ℤ)
    (hρ : 0 < ρ)
    (hhom : F.IsWeightedHomogeneous (wt ρ σ) degree) :
    (MvPolynomial.eval₂ Polynomial.C
      (fun t : Fin 2 => if t = 0 then 1 else Polynomial.X) F).natDegree =
        F.degreeOf 1 := by
  let G : ℂ[X] := MvPolynomial.eval₂ Polynomial.C
    (fun t : Fin 2 => if t = 0 then 1 else Polynomial.X) F
  apply Nat.le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    change (MvPolynomial.eval₂ Polynomial.C
      (fun t : Fin 2 => if t = 0 then 1 else Polynomial.X) F).coeff j = 0
    rw [homogeneous_specialization_coeff_sum]
    apply Finset.sum_eq_zero
    intro d hd
    have hd1 : d 1 ≤ F.degreeOf 1 :=
      MvPolynomial.le_degreeOf_of_mem_support 1 hd
    simp [show d 1 ≠ j by omega]
  · rw [MvPolynomial.degreeOf_eq_sup]
    apply Finset.sup_le
    intro d hd
    obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective d
    have hw := hhom (MvPolynomial.mem_support_iff.mp hd)
    rw [expo_weight] at hw
    change (i : ℤ) * ρ + (j : ℤ) * σ = degree at hw
    have hcoeff := homogeneous_specialization_coeff_at_support
      F ρ σ degree hρ hhom i j hw
    have hj : j ∈ G.support := by
      apply Polynomial.mem_support_iff.mpr
      change (MvPolynomial.eval₂ Polynomial.C
        (fun t : Fin 2 => if t = 0 then 1 else Polynomial.X) F).coeff j ≠ 0
      rw [hcoeff]
      exact MvPolynomial.mem_support_iff.mp hd
    simpa [expo] using Polynomial.le_natDegree_of_mem_supp j hj

/-- The numerical root budget is the exact degree of the specialized
homogeneous companion `X f(X^ρ)` when its constant coefficient is nonzero. -/
theorem crossing_companion_specialization_degree
    (f : ℂ[X]) (ρ : ℕ) (hρ : 0 < ρ) (hf0 : f.eval 0 ≠ 0) :
    (Polynomial.X * f.comp (Polynomial.X ^ ρ)).natDegree =
      1 + ρ * f.natDegree := by
  have hcomp : f.comp (Polynomial.X ^ ρ) ≠ 0 := by
    intro hz
    have heval := congrArg (Polynomial.eval 0) hz
    simp [Polynomial.eval_comp, hρ.ne'] at heval
    exact hf0 heval
  rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hcomp,
    Polynomial.natDegree_X, Polynomial.natDegree_comp,
    Polynomial.natDegree_X_pow]
  rw [Nat.mul_comm f.natDegree ρ]

/-- The same number is the derivative-order degree of the actual
homogeneous companion after specializing its `x` variable to one. -/
theorem crossing_homogeneous_companion_specialization_degree
    (F : MvPolynomial (Fin 2) ℂ) (f : ℂ[X]) (ρ s : ℕ)
    (hρ : 0 < ρ) (hf0 : f.eval 0 ≠ 0)
    (hF : F = (MvPolynomial.X 0 * MvPolynomial.X 1) *
      f.eval₂ MvPolynomial.C
        (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) :
    (MvPolynomial.eval₂ Polynomial.C
      (fun i : Fin 2 => if i = 0 then 1 else Polynomial.X) F).natDegree =
        1 + ρ * f.natDegree := by
  rw [hF, MvPolynomial.eval₂_mul, crossing_substitution_eval]
  simpa using crossing_companion_specialization_degree f ρ hρ hf0

/-- Under the source's homogeneous-companion weight, the root budget
`1+ρ deg f` is its actual maximal `Y` endpoint coordinate. -/
theorem crossing_homogeneous_companion_degreeOf_Y
    (F : MvPolynomial (Fin 2) ℂ) (f : ℂ[X]) (ρ s : ℕ)
    (hρ : 0 < ρ) (hf0 : f.eval 0 ≠ 0)
    (hhom : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) ((ρ : ℤ) - s))
    (hF : F = (MvPolynomial.X 0 * MvPolynomial.X 1) *
      f.eval₂ MvPolynomial.C
        (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) :
    F.degreeOf 1 = 1 + ρ * f.natDegree := by
  rw [← homogeneous_specialization_natDegree_eq_degreeOf_Y F ρ
    (-(s : ℤ)) ((ρ : ℤ) - s) (by exact_mod_cast hρ) hhom]
  exact crossing_homogeneous_companion_specialization_degree
    F f ρ s hρ hf0 hF

theorem crossing_power_face_cutPoly
    (P : A1 ℂ) (ρ s a b k : ℕ) (μ : ℂ) (r : ℂ[X])
    (hface : leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
        r.eval₂ MvPolynomial.C
          (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) ^ k) :
    cutPoly ρ (-(s : ℤ)) P.1 =
      Polynomial.C μ * Polynomial.X ^ (b * k) *
        (r.comp (Polynomial.X ^ ρ)) ^ k := by
  rw [crossingFace_general_cutPoly μ a b s ρ k r P hface,
    Polynomial.expand_eq_comp_X_pow, Polynomial.pow_comp]

theorem crossing_power_face_cutPoly_root_count
    (P : A1 ℂ) (ρ s a b k : ℕ) (μ : ℂ) (r f : ℂ[X])
    (hsρ : s < ρ) (hab : b < a) (hr0 : r.coeff 0 = 1)
    (hcut : cutPoly ρ (-(s : ℤ)) P.1 ≠ 0)
    (hface : leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
        r.eval₂ MvPolynomial.C
          (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) ^ k)
    (hscalar : Polynomial.C ((ρ : ℂ) - s) * Polynomial.X * f * r.derivative -
      ((Polynomial.C ((a : ℂ) - b) * f +
          Polynomial.C ((ρ : ℂ) * a - (s : ℂ) * b) * Polynomial.X *
          f.derivative + 1) * r) = 0) :
    (cutPoly ρ (-(s : ℤ)) P.1).roots.toFinset.card ≤
      1 + ρ * f.natDegree := by
  have hg := crossing_scalar_to_GenComp ρ s a b r f hsρ hab hscalar
  have hr0eval : r.eval 0 = 1 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hr0
  have hf : f ≠ 0 := by
    intro hzero
    have hconst := hg.constant_relation hr0eval
    simp [hzero] at hconst
  have hshape := crossing_power_face_cutPoly P ρ s a b k μ r hface
  exact hg.powered_face_root_count (Nat.sub_pos_of_lt hsρ)
    hr0eval hf ρ (b * k) k (by omega) μ hcut hshape

/-- Source-shaped G13 root budget: the distinct roots of the actual
operator cut polynomial are bounded by the ending derivative order of
the homogeneous companion, represented here by its `x=1` degree. -/
theorem crossing_power_face_cutPoly_roots_le_companion_degree
    (P : A1 ℂ) (F : MvPolynomial (Fin 2) ℂ)
    (ρ s a b k : ℕ) (μ : ℂ) (r f : ℂ[X])
    (hsρ : s < ρ) (hab : b < a) (hr0 : r.coeff 0 = 1)
    (hcut : cutPoly ρ (-(s : ℤ)) P.1 ≠ 0)
    (hface : leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
        r.eval₂ MvPolynomial.C
          (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) ^ k)
    (hF : F = (MvPolynomial.X 0 * MvPolynomial.X 1) *
      f.eval₂ MvPolynomial.C
        (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ))
    (hscalar : Polynomial.C ((ρ : ℂ) - s) * Polynomial.X * f * r.derivative -
      ((Polynomial.C ((a : ℂ) - b) * f +
          Polynomial.C ((ρ : ℂ) * a - (s : ℂ) * b) * Polynomial.X *
          f.derivative + 1) * r) = 0) :
    (cutPoly ρ (-(s : ℤ)) P.1).roots.toFinset.card ≤
      (MvPolynomial.eval₂ Polynomial.C
        (fun i : Fin 2 => if i = 0 then 1 else Polynomial.X) F).natDegree := by
  have hg := crossing_scalar_to_GenComp ρ s a b r f hsρ hab hscalar
  have hr0eval : r.eval 0 = 1 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hr0
  have hf0 : f.eval 0 ≠ 0 := by
    intro hz
    have hconst := hg.constant_relation hr0eval
    rw [hz] at hconst
    norm_num at hconst
  rw [crossing_homogeneous_companion_specialization_degree F f ρ s
    (by omega) hf0 hF]
  exact crossing_power_face_cutPoly_root_count P ρ s a b k μ r f
    hsρ hab hr0 hcut hface hscalar

/-- The G13 companion root count stated directly against the actual
maximal `Y` coordinate of its homogeneous support. -/
theorem crossing_power_face_cutPoly_roots_le_companion_endpoint_Y
    (P : A1 ℂ) (F : MvPolynomial (Fin 2) ℂ)
    (ρ s a b k : ℕ) (μ : ℂ) (r f : ℂ[X])
    (hsρ : s < ρ) (hab : b < a) (hr0 : r.coeff 0 = 1)
    (hcut : cutPoly ρ (-(s : ℤ)) P.1 ≠ 0)
    (hface : leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
        r.eval₂ MvPolynomial.C
          (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) ^ k)
    (hhom : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) ((ρ : ℤ) - s))
    (hF : F = (MvPolynomial.X 0 * MvPolynomial.X 1) *
      f.eval₂ MvPolynomial.C
        (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ))
    (hscalar : Polynomial.C ((ρ : ℂ) - s) * Polynomial.X * f * r.derivative -
      ((Polynomial.C ((a : ℂ) - b) * f +
          Polynomial.C ((ρ : ℂ) * a - (s : ℂ) * b) * Polynomial.X *
          f.derivative + 1) * r) = 0) :
    (cutPoly ρ (-(s : ℤ)) P.1).roots.toFinset.card ≤ F.degreeOf 1 := by
  have hg := crossing_scalar_to_GenComp ρ s a b r f hsρ hab hscalar
  have hr0eval : r.eval 0 = 1 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hr0
  have hf0 : f.eval 0 ≠ 0 := by
    intro hz
    have hconst := hg.constant_relation hr0eval
    rw [hz] at hconst
    norm_num at hconst
  rw [crossing_homogeneous_companion_degreeOf_Y F f ρ s
    (by omega) hf0 hhom hF]
  exact crossing_power_face_cutPoly_root_count P ρ s a b k μ r f
    hsρ hab hr0 hcut hface hscalar

end Dixmier.Weyl
