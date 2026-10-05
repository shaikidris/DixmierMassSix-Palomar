/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.DiagonalCaseReduction
public import DixmierFormal.Weyl.DiagonalTwoRootDegree

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Universal diagonal case map

The companion exhausts the diagonal weight in the two-root branch.
Homogeneous reconstruction removes the residual axis factor; a zero root
uses the one-root dispatcher and two nonzero roots give the final alternative.
-/
namespace Dixmier.Weyl
open Polynomial

/-- Reconstruct the native two-root face with no residual axis factor. -/
theorem preliminary_two_root_cut_face
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (lam α β : ℂ) (u v : ℕ) (hlam : lam ≠ 0) (hab : α ≠ β)
    (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hc : cutPoly 1 1 P.1 = C lam * (X-C α)^u * (X-C β)^v) :
    leadingForm 1 1 P.1 = MvPolynomial.C lam *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0)^u *
      (MvPolynomial.X 1 - MvPolynomial.C β * MvPolynomial.X 0)^v := by
  classical
  have hne : cutPoly 1 1 P.1 ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hlam) (pow_ne_zero u (X_sub_C_ne_zero α)))
      (pow_ne_zero v (X_sub_C_ne_zero β))
  have ha : α ∈ (cutPoly 1 1 P.1).roots.toFinset := by
    rw [Multiset.mem_toFinset,mem_roots hne]
    simp [IsRoot,hc,show u ≠ 0 by omega]
  have hb : β ∈ (cutPoly 1 1 P.1).roots.toFinset := by
    rw [Multiset.mem_toFinset,mem_roots hne]
    simp [IsRoot,hc,show v ≠ 0 by omega]
  have hcard : 2 ≤ (cutPoly 1 1 P.1).roots.toFinset.card := by
    have hlt := Finset.one_lt_card_iff.mpr ⟨α,β,ha,hb,hab⟩
    omega
  have hw := preliminary_diagonal_two_roots_exhaust_weight hsource P Q hpair hcard
  have hd : (cutPoly 1 1 P.1).natDegree = u+v := by
    rw [hc,natDegree_mul
      (mul_ne_zero (C_ne_zero.mpr hlam) (pow_ne_zero u (X_sub_C_ne_zero α)))
      (pow_ne_zero v (X_sub_C_ne_zero β)),natDegree_C_mul hlam,
      natDegree_pow,natDegree_pow,natDegree_X_sub_C,natDegree_X_sub_C]
    simp
  have hf := diagonal_face_eq_of_factored_cut P lam α β 0 u v
    (by simpa [hd] using hw) hc
  simpa using hf

/-- Every polynomial counterexample obeys the frozen case map, relative only
to the preliminary companion and the uniform degree lower bound. -/
theorem preliminary_universal_caseSplit
    (hsource : GGVPreliminaryCompanionInput)
    (hdegree : ∀ R S : A1 ℂ, IsCounterexamplePair R S → 16 ≤ totalDeg R.1)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) :
    CaseAlternative P.1 ∨ CaseAlternative (fourier P.1) := by
  rcases preliminary_diagonal_cut_factorization hsource P Q hpair with
    ⟨lam,hlam,hc⟩ | ⟨lam,α,k,hlam,hk,hc⟩ | ⟨lam,α,β,u,v,hlam,hab,hu,hv,hc⟩
  · have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 1
      (by norm_num [IsDirection])
    let n := (vDeg 1 1 P.1).toNat
    have hn : vDeg 1 1 P.1 = (n : ℤ) := by
      dsimp [n]; exact (Int.toNat_of_nonneg (le_of_lt hp)).symm
    have hf := diagonal_face_eq_of_constant_cut P lam n hn hc
    exact preliminary_diagonal_monomial_complete_caseSplit hsource hdegree P Q hpair
      lam n 0 hlam (by simpa using hf)
  · have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 1
      (by norm_num [IsDirection])
    let n := (vDeg 1 1 P.1).toNat
    have hn : vDeg 1 1 P.1 = (n : ℤ) := by
      dsimp [n]; exact (Int.toNat_of_nonneg (le_of_lt hp)).symm
    have hbound := diagonal_cut_natDegree_le P n hn
    have hkn : k ≤ n := by
      rw [hc,natDegree_C_mul hlam,natDegree_pow,natDegree_X_sub_C] at hbound
      simpa using hbound
    have hf := diagonal_face_eq_of_factored_cut P lam α 0 (n-k) k 0
      (by rw [hn]; congr 1; omega) (by simpa using hc)
    exact preliminary_diagonal_single_factor_complete_caseSplit hsource hdegree P Q hpair
      (n-k) k hk lam α hlam (by simpa using hf)
  · have hf := preliminary_two_root_cut_face hsource P Q hpair lam α β u v hlam hab hu hv hc
    by_cases ha : α=0
    · subst α
      exact Or.inl (preliminary_diagonal_y_factor_complete_caseAlternative hsource hdegree
        P Q hpair u v hv lam β hlam (by simpa using hab.symm) (by simpa using hf))
    · by_cases hb : β=0
      · subst β
        have hf' : leadingForm 1 1 P.1 = MvPolynomial.C lam * MvPolynomial.X 1^v *
            (MvPolynomial.X 1-MvPolynomial.C α*MvPolynomial.X 0)^u := by
          rw [hf]; simp only [map_zero,zero_mul,sub_zero]; ring
        exact Or.inl (preliminary_diagonal_y_factor_complete_caseAlternative hsource hdegree
          P Q hpair v u hu lam α hlam ha hf')
      · exact Or.inl (Or.inr (Or.inr ⟨lam,α,β,u,v,hlam,ha,hb,hab,hu,hv,hf⟩))

end Dixmier.Weyl
