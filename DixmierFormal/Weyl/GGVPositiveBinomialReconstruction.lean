/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVDiagonalCutFactorization
public import DixmierFormal.Weyl.GGVPositiveCutRootBudget
public import DixmierFormal.Weyl.HomogeneousCutReconstruction

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # One-root factorization and weighted binomial reconstruction

The full complex root product classifies a one-root cut. Weighted
homogeneity reconstructs its binomial with the axis factor retained.
-/
namespace Dixmier.Weyl
open Polynomial

/-- A nonzero complex polynomial with at most one distinct root is a
constant or a power of one linear factor. -/
theorem complex_polynomial_one_root_factorization
    (p : ℂ[X]) (hp : p ≠ 0) (hcard : p.roots.toFinset.card ≤ 1) :
    (∃ lam : ℂ, lam ≠ 0 ∧ p = C lam) ∨
    (∃ (lam α : ℂ) (k : ℕ), lam ≠ 0 ∧ 1 ≤ k ∧ p = C lam * (X-C α)^k) := by
  classical
  have hlam : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hprod := (IsAlgClosed.splits p).eq_prod_roots
  rw [prod_multiset_root_eq_finset_root] at hprod
  by_cases hz : p.roots.toFinset.card = 0
  · exact Or.inl ⟨p.leadingCoeff, hlam,
      by simpa [Finset.card_eq_zero.mp hz] using hprod⟩
  · have hone : p.roots.toFinset.card = 1 := by omega
    obtain ⟨α, hset⟩ := Finset.card_eq_one.mp hone
    have hmem : α ∈ p.roots := Multiset.mem_toFinset.mp (by rw [hset]; simp)
    have hk : 1 ≤ rootMultiplicity α p := by
      have hpos : 0 < rootMultiplicity α p := by
        rw [← count_roots]
        exact Multiset.count_pos.mpr hmem
      omega
    exact Or.inr ⟨p.leadingCoeff, α, rootMultiplicity α p, hlam, hk,
      by simpa [hset] using hprod⟩

set_option maxHeartbeats 800000 in
/-- Weighted reconstruction retains the first-axis power lost by cutting. -/
theorem positive_face_eq_of_linear_power_cut
    (P : A1 ℂ) (lam α : ℂ) (σ a k : ℕ)
    (hdegree : vDeg 1 (σ : ℤ) P.1 = ((a + σ*k : ℕ) : ℤ))
    (hcut : cutPoly 1 (σ : ℤ) P.1 = C lam * (X-C α)^k) :
    leadingForm 1 (σ : ℤ) P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ a *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0 ^ σ)^k := by
  have hX : MvPolynomial.IsWeightedHomogeneous (wt 1 (σ : ℤ))
      (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℂ) (σ : ℤ) := by
    simpa [wt] using MvPolynomial.isWeightedHomogeneous_X ℂ (wt 1 (σ : ℤ)) (1 : Fin 2)
  have hY : MvPolynomial.IsWeightedHomogeneous (wt 1 (σ : ℤ))
      (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) 1 := by
    simpa [wt] using MvPolynomial.isWeightedHomogeneous_X ℂ (wt 1 (σ : ℤ)) (0 : Fin 2)
  have hYσ : MvPolynomial.IsWeightedHomogeneous (wt 1 (σ : ℤ))
      (MvPolynomial.X (0 : Fin 2) ^ σ : MvPolynomial (Fin 2) ℂ) (σ : ℤ) := by
    simpa [nsmul_eq_mul] using hY.pow σ
  apply homogeneous_eq_of_specialization_eq _ _ 1 (σ : ℤ)
    (vDeg 1 (σ : ℤ) P.1) (by norm_num)
  · exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt 1 (σ : ℤ)) (n := vDeg 1 (σ : ℤ) P.1)
  · rw [hdegree]
    simpa only [nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_mul, mul_assoc,
      mul_comm (k : ℤ) (σ : ℤ)] using
      ((hY.pow a).mul ((hX.sub (hYσ.C_mul α)).pow k)).C_mul lam
  · change cutPoly 1 (σ : ℤ) P.1 = _
    rw [hcut]
    let φ := MvPolynomial.eval₂Hom Polynomial.C
      (fun i : Fin 2 => if i = 0 then (1 : ℂ[X]) else Polynomial.X)
    change _ = φ _
    simp only [map_mul, map_pow, map_sub]
    dsimp [φ]
    simp only [MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
    norm_num

/-- The actual positive cut is nonzero and has the full one-root factorization. -/
theorem preliminary_positive_cut_factorization
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ : ℕ) (hσ : 1 < σ) :
    (∃ lam : ℂ, lam ≠ 0 ∧ cutPoly 1 (σ : ℤ) P.1 = C lam) ∨
    (∃ (lam α : ℂ) (k : ℕ), lam ≠ 0 ∧ 1 ≤ k ∧
      cutPoly 1 (σ : ℤ) P.1 = C lam * (X-C α)^k) := by
  have hdir : IsDirection 1 (σ : ℤ) := ⟨by simp, by positivity⟩
  have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 (σ : ℤ) hdir
  have hne : cutPoly 1 (σ : ℤ) P.1 ≠ 0 := by
    obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr
      (leadingForm_ne_zero_of_vDeg_pos P 1 (σ : ℤ) hp)
    obtain ⟨⟨i,j⟩, rfl⟩ := expo_surjective e
    have hw := (polynomialFace_point_source_data P 1 (σ : ℤ) i j he).2
    have hc := cutPoly_coeff_at_face_point P 1 (σ : ℤ) i j (by norm_num)
      (by simpa using hw)
    intro hz
    have hm := MvPolynomial.mem_support_iff.mp he
    rw [← hc, hz] at hm
    exact hm (by simp)
  exact complex_polynomial_one_root_factorization _ hne
    (preliminary_positive_cut_distinct_roots_le_one hsource P Q hpair σ hσ)

/-- The highest nonzero cut coefficient recovers its nonnegative axis exponent. -/
theorem positive_cut_degree_axis_exponent
    (P : A1 ℂ) (σ : ℕ) (hne : cutPoly 1 (σ : ℤ) P.1 ≠ 0) :
    ∃ a : ℕ, vDeg 1 (σ : ℤ) P.1 =
      ((a + σ * (cutPoly 1 (σ : ℤ) P.1).natDegree : ℕ) : ℤ) := by
  classical
  have hm := Polynomial.natDegree_mem_support_of_nonzero hne
  have hs := cutPolynomial_support_subset_y_exponents
    (leadingForm 1 (σ : ℤ) P.1) hm
  obtain ⟨d, hd, he⟩ := Finset.mem_image.mp hs
  obtain ⟨⟨i,j⟩,rfl⟩ := expo_surjective d
  have hw := (polynomialFace_point_source_data P 1 (σ : ℤ) i j hd).2
  have hj : j = (cutPoly 1 (σ : ℤ) P.1).natDegree := by simpa [expo] using he
  refine ⟨i, ?_⟩
  rw [← hj]
  norm_num at hw ⊢
  nlinarith [hw]

/-- Every actual nontrivial positive face has the binomial shape with
nonzero root and its full residual axis exponent. -/
theorem preliminary_positive_face_binomial
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ : ℕ) (hσ : 1 < σ) (hfaceDir : InDir 1 (σ : ℤ) P.1) :
    ∃ (lam α : ℂ) (a k : ℕ), lam ≠ 0 ∧ α ≠ 0 ∧ 1 ≤ k ∧
      vDeg 1 (σ : ℤ) P.1 = ((a + σ*k : ℕ) : ℤ) ∧
      leadingForm 1 (σ : ℤ) P.1 = MvPolynomial.C lam * MvPolynomial.X 0 ^ a *
        (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0 ^ σ)^k := by
  classical
  rcases preliminary_positive_cut_factorization hsource P Q hpair σ hσ with
    ⟨lam, hlam, hc⟩ | ⟨lam, α, k, hlam, hk, hc⟩
  · have hne : cutPoly 1 (σ : ℤ) P.1 ≠ 0 := by
      rw [hc]; exact C_ne_zero.mpr hlam
    obtain ⟨a, ha⟩ := positive_cut_degree_axis_exponent P σ hne
    have hd : vDeg 1 (σ : ℤ) P.1 = ((a + σ*0 : ℕ) : ℤ) := by
      simpa [hc] using ha
    have hf := positive_face_eq_of_linear_power_cut P lam 0 σ a 0 hd
      (by simpa using hc)
    have hm : leadingForm 1 (σ : ℤ) P.1 =
        MvPolynomial.monomial (Finsupp.single 0 a) lam := by
      simpa [MvPolynomial.C_mul_X_pow_eq_monomial] using hf
    have hbad : (leadingForm 1 (σ : ℤ) P.1).support.card = 1 := by
      rw [hm, MvPolynomial.support_monomial]; simp [hlam]
    change 1 < (leadingForm 1 (σ : ℤ) P.1).support.card at hfaceDir
    omega
  · have hne : cutPoly 1 (σ : ℤ) P.1 ≠ 0 := by
      rw [hc]
      exact mul_ne_zero (C_ne_zero.mpr hlam) (pow_ne_zero k (X_sub_C_ne_zero α))
    obtain ⟨a, ha⟩ := positive_cut_degree_axis_exponent P σ hne
    have hd : vDeg 1 (σ : ℤ) P.1 = ((a + σ*k : ℕ) : ℤ) := by
      simpa [hc, natDegree_C_mul hlam, natDegree_pow, natDegree_X_sub_C] using ha
    have hf := positive_face_eq_of_linear_power_cut P lam α σ a k hd hc
    have hα : α ≠ 0 := by
      intro hz
      have hm : leadingForm 1 (σ : ℤ) P.1 = MvPolynomial.monomial (expo a k) lam := by
        rw [hf, hz]
        simp only [map_zero, zero_mul, sub_zero]
        rw [MvPolynomial.C_mul_X_pow_eq_monomial,
          ← MvPolynomial.monomial_add_single]
        rfl
      have hbad : (leadingForm 1 (σ : ℤ) P.1).support.card = 1 := by
        rw [hm, MvPolynomial.support_monomial]; simp [hlam]
      change 1 < (leadingForm 1 (σ : ℤ) P.1).support.card at hfaceDir
      omega
    exact ⟨lam, α, a, k, hlam, hα, hk, hd, hf⟩

end Dixmier.Weyl
