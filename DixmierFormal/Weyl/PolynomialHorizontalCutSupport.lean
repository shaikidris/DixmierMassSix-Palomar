/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PolynomialConstantCutRecovery

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Polynomial support of a recovered horizontal cut

The faithful lift transfers the horizontal half-plane bound and the selected
maximum-root start back to polynomial PBW support. The mate remains unrestricted.
-/
namespace Dixmier.Weyl

/-- Recovery of the horizontal cut preserves the first-coordinate bound. -/
theorem polynomial_horizontal_cut_first_coordinate_bound
    (P R : A1 ℂ) (c : ℂ) (a : ℕ)
    (hbound : ∀ e ∈ (symbol P.1).support, e 0 ≤ a)
    (hrecover : polynomialRamifiedLift 1 R =
      ramifiedCutAut 1 (by norm_num) 1 0 c (polynomialRamifiedLift 1 P)) :
    ∀ e ∈ (symbol R.1).support, e 0 ≤ a := by
  have hupper : ∀ i : ℤ, ∀ j : ℕ,
      (i,j) ∈ ramifiedPBWSupport 1 (by norm_num) (polynomialRamifiedLift 1 P) →
      ramifiedWeight 1 1 0 (i,j) ≤ 1 * (a : ℤ) := by
    intro i j hij
    obtain ⟨n, hn, hs⟩ :=
      (polynomialRamifiedLift_support_iff_symbol 1 (by norm_num) P i j).mp hij
    have hb := hbound (expo n j) hs
    simp [expo] at hb
    simp [ramifiedWeight, hn]
    exact_mod_cast hb
  have hcut := ramifiedCutAut_weight_upper 1 (by norm_num) 1 0 (a : ℤ)
    (by norm_num) (by norm_num) (by norm_num) c (polynomialRamifiedLift 1 P) hupper
  intro e he
  have hexpo : expo (e 0) (e 1) = e := by
    ext i
    fin_cases i <;> simp [expo]
  have hs : ((e 0 : ℤ), e 1) ∈ ramifiedPBWSupport 1 (by norm_num)
      (polynomialRamifiedLift 1 R) :=
    (polynomialRamifiedLift_support_iff_symbol 1 (by norm_num) R _ _).mpr
      ⟨e 0, by simp, hexpo.symm ▸ he⟩
  rw [hrecover] at hs
  have hb := hcut _ _ hs
  simp [ramifiedWeight] at hb
  exact_mod_cast hb

/-- The maximum-root cut is an actual polynomial counterexample pair with
an occupied negative-grade horizontal start and a preserved horizontal bound. -/
theorem preliminary_horizontal_cut_polynomial_support
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b : ℕ) (hrect : IsSubrectangularAt P a b)
    (hab : a < b) (hface : InDir 1 0 P.1) :
    let M := maxRootMult (cutPoly 1 0 P.1)
    ∃ c : ℂ, ∃ R S : A1 ℂ, IsCounterexamplePair R S ∧
      (cutPoly 1 0 P.1).IsRoot c ∧
      (cutPoly 1 0 P.1).rootMultiplicity c = M ∧
      expo a M ∈ (symbol R.1).support ∧
      (∀ e ∈ (symbol R.1).support, e 0 ≤ a) ∧
      (∀ e ∈ (symbol R.1).support, e 0 = a → M ≤ e 1 ∧ grade e < 0) := by
  dsimp only
  obtain ⟨c, hc, hm, hp, hext, _⟩ :=
    preliminary_horizontal_cut_negative_old_face_exact_pair hsource P Q hpair a b hrect hab hface
  obtain ⟨R, S, hrs, hR, _⟩ := horizontal_cut_recovers_polynomial_counterexample c P Q hpair
  refine ⟨c, R, S, hrs, hc, hm, ?_, ?_, ?_⟩
  · rw [← hR] at hp
    obtain ⟨n, hn, hs⟩ :=
      (polynomialRamifiedLift_support_iff_symbol 1 (by norm_num) R _ _).mp hp
    have hna : n = a := by simpa using hn.symm
    simpa [hna] using hs
  · exact polynomial_horizontal_cut_first_coordinate_bound P R c a
      (fun e he => (hrect.2 e he).1) hR
  · intro e he hea
    have hexpo : expo (e 0) (e 1) = e := by
      ext i
      fin_cases i <;> simp [expo]
    have hs : ((e 0 : ℤ), e 1) ∈ ramifiedPBWSupport 1 (by norm_num)
        (polynomialRamifiedLift 1 R) :=
      (polynomialRamifiedLift_support_iff_symbol 1 (by norm_num) R _ _).mpr
        ⟨e 0, by simp, hexpo.symm ▸ he⟩
    rw [hR] at hs
    have hw : ramifiedWeight 1 1 0 ((e 0 : ℤ), e 1) = (a : ℤ) := by
      simp [ramifiedWeight, hea]
    obtain ⟨hmin, hneg⟩ := hext _ _ hs hw
    exact ⟨hmin, by simpa [grade] using hneg⟩

end Dixmier.Weyl
