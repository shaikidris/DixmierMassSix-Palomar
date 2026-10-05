/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVOrderedNonzeroSharedVertices
public import DixmierFormal.Weyl.GGVNegativeDiagonalBoundary
public import DixmierFormal.Weyl.GGVNegativeHorizontalBoundary

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Selecting a strict crossing from the actual ordered negative faces

The terminal horizontal grade sign is a premise here: G13 obtains it
from standard minimality, not from the exact Weyl relation alone.
The nonzero intermediate-grade assertion is conditional on the
preliminary companion input.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- Two occupied points on a positive-first-coordinate face with the
same derivative exponent coincide. -/
theorem leadingFace_same_y_eq
    (P : A1 ℂ) (ρ σ : ℤ) (hρ : 0 < ρ)
    {a b : Fin 2 →₀ ℕ}
    (ha : a ∈ (leadingForm ρ σ P.1).support)
    (hb : b ∈ (leadingForm ρ σ P.1).support)
    (hy : a 1 = b 1) : a = b := by
  have haR := (leadingForm_mem_iff_rational_slope P ρ σ hρ a).mp ha
  have hbR := (leadingForm_mem_iff_rational_slope P ρ σ hρ b).mp hb
  have hab := haR.2 b hbR.1
  have hba := hbR.2 a haR.1
  dsimp [rationalNewtonWeight] at hab hba
  have hx : a 0 = b 0 := by
    have hxy : (a 0 : ℚ) = b 0 := by
      rw [hy] at hab hba
      linarith
    exact_mod_cast hxy
  ext i
  fin_cases i
  · exact hx
  · exact hy

/-- Every occupied diagonal-leading point of a counterexample member
has strictly positive grade. -/
theorem counterexample_diagonal_face_grade_pos
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a : Fin 2 →₀ ℕ)
    (ha : a ∈ (leadingForm 1 (-1) P.1).support) : 0 < grade a := by
  obtain ⟨d, hd, hdpos⟩ := (ggv_grades_opposite_proved P Q hpair).1
  have haR := (leadingForm_mem_iff_rational_slope P 1 (-1)
    (by norm_num) a).mp ha
  have hle := haR.2 d hd
  have hq : (grade d : ℚ) ≤ grade a := by
    dsimp [rationalNewtonWeight] at hle
    norm_num at hle
    have hq' : (d 0 : ℚ) - d 1 ≤ (a 0 : ℚ) - a 1 := by linarith
    simpa only [grade, Int.cast_sub, Int.cast_natCast] using hq'
  have hz : (0 : ℚ) < grade a := lt_of_lt_of_le (by exact_mod_cast hdpos) hq
  exact_mod_cast hz

/-- On the horizontal leading face, the minimum-`Y` occupied point has
the largest grade. Thus a negative starting grade makes every point of
that face negative-grade. -/
theorem horizontal_min_y_negative_all
    (P : A1 ℂ) (a : Fin 2 →₀ ℕ)
    (ha : a ∈ (leadingForm 1 0 P.1).support)
    (haMin : ∀ e ∈ (leadingForm 1 0 P.1).support, a 1 ≤ e 1)
    (haNeg : grade a < 0) :
    ∀ e ∈ (leadingForm 1 0 P.1).support, grade e < 0 := by
  intro e he
  have haR := (leadingForm_mem_iff_rational_slope P 1 0 (by norm_num) a).mp ha
  have heR := (leadingForm_mem_iff_rational_slope P 1 0 (by norm_num) e).mp he
  have hae := haR.2 e heR.1
  have hea := heR.2 a haR.1
  have hx : a 0 = e 0 := by
    dsimp [rationalNewtonWeight] at hae hea
    norm_num at hae hea
    omega
  have hy := haMin e he
  dsimp [grade] at haNeg ⊢
  omega

/-- A negative horizontal face and the exact pair's positive diagonal
grade force an actual face strictly between the diagonal and horizontal.
No companion or nonempty direction-list assumption is required. -/
theorem counterexample_negative_face_slopes_nonempty_of_horizontal_terminal
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (hterminal : ∀ e ∈ (leadingForm 1 0 P.1).support, grade e < 0) :
    0 < (ggvOrderedNegativeFaceSlopes P).length := by
  classical
  obtain ⟨d, hd, -⟩ := (ggv_grades_opposite_proved P Q hpair).1
  obtain ⟨c₀, hc₀, hc₀Max⟩ := Finset.exists_max_image
    (symbol P.1).support grade ⟨d, hd⟩
  have hc₀Diag : c₀ ∈ (leadingForm 1 (-1) P.1).support := by
    apply (leadingForm_mem_iff_rational_slope P 1 (-1) (by norm_num) c₀).mpr
    refine ⟨hc₀, ?_⟩
    intro e he
    have h := hc₀Max e he
    dsimp [rationalNewtonWeight, grade] at h ⊢
    have hq : (e 0 : ℚ) - e 1 ≤ (c₀ 0 : ℚ) - c₀ 1 := by exact_mod_cast h
    norm_num at *
    linarith
  obtain ⟨a, ha, haMax⟩ := Finset.exists_max_image
    (leadingForm 1 (-1) P.1).support (fun e => e 1)
      ⟨c₀, hc₀Diag⟩
  have haPos := counterexample_diagonal_face_grade_pos P Q hpair a ha
  have hhorizontalPos := counterexample_vDeg_pos_all_directions
    P Q hpair 1 0 (by constructor <;> norm_num)
  obtain ⟨b, hb⟩ := MvPolynomial.support_nonempty.mpr
    (leadingForm_ne_zero_of_vDeg_pos P 1 0 hhorizontalPos)
  have hbNeg := hterminal b hb
  have habNe : a ≠ b := by
    intro h
    rw [h] at haPos
    omega
  obtain ⟨habLe, habEq⟩ := leadingFace_points_ordered_by_slope
    P 1 (-1) 1 0 (by norm_num) (by norm_num) (by norm_num) ha hb
  have hab : a 1 < b 1 := lt_of_le_of_ne habLe (fun h => habNe (habEq h))
  have haData := (leadingForm_mem_iff_rational_slope P 1 (-1) (by norm_num) a).mp ha
  have hbData := (leadingForm_mem_iff_rational_slope P 1 0 (by norm_num) b).mp hb
  obtain ⟨t, ht, hmax, c, hc, hca, hct⟩ :=
    leadingFace_exists_first_upward_tilt P 1 (-1) (by norm_num)
      a ha haMax ⟨b, hbData.1, hab⟩
  have htLeft : -1 < t := by simpa using ht
  have htRight : t < 0 := by
    have hbx := hbData.2 a haData.1
    have hstrict : a 0 < b 0 := by
      have hle : a 0 ≤ b 0 := by
        simpa [rationalNewtonWeight] using hbx
      by_contra h
      have heq : a 0 = b 0 := by omega
      have haHorizontal : a ∈ (leadingForm 1 0 P.1).support := by
        apply (leadingForm_mem_iff_rational_slope P 1 0 (by norm_num) a).mpr
        refine ⟨haData.1, ?_⟩
        intro e he
        simpa [rationalNewtonWeight, heq] using hbData.2 e he
      have := hterminal a haHorizontal
      omega
    have hfirst := hmax b hbData.1
    have hx : (a 0 : ℚ) < b 0 := by exact_mod_cast hstrict
    have hy : (a 1 : ℚ) < b 1 := by exact_mod_cast hab
    dsimp [rationalNewtonWeight] at hfirst
    by_contra h
    have htNonneg : 0 ≤ t := le_of_not_gt h
    nlinarith [mul_nonneg htNonneg (le_of_lt (sub_pos.mpr hy))]
  have hac : a ≠ c := by
    intro h
    rw [← h] at hca
    omega
  obtain ⟨-, -, hmem⟩ := rationalSlope_two_maximizers_mem_ordered_negative_slopes
    P t htLeft htRight a c haData.1 hc hmax hct hac
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem hmem)

/-- Select the first negative-ending actual face. Its starting grade
must be positive: at the first face this follows from the diagonal
boundary; at later faces a nonpositive nonzero start would make the
preceding face already negative-ending. The horizontal sign is kept
as an explicit standard-pair premise. -/
theorem counterexample_ordered_strict_crossing_of_terminal
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (hterminal : ∀ e ∈ (leadingForm 1 0 P.1).support, grade e < 0) :
    ∃ (j : ℕ) (hj : j < (ggvOrderedNegativeFaceSlopes P).length)
      (ρ s : ℕ) (a b : Fin 2 →₀ ℕ),
      0 < ρ ∧ 0 < s ∧ IsDirection (ρ : ℤ) (-(s : ℤ)) ∧
      (ggvOrderedNegativeFaceSlopes P)[j]'hj = (-(s : ℤ) : ℚ) / ρ ∧
      InDir (ρ : ℤ) (-(s : ℤ)) P.1 ∧
      InDir (ρ : ℤ) (-(s : ℤ)) Q.1 ∧
      a ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support ∧
      b ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support ∧
      (∀ e ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support,
        a 1 ≤ e 1) ∧
      (∀ e ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support,
        e 1 ≤ b 1) ∧ 0 < grade a ∧ grade b < 0 := by
  classical
  have hzero := counterexample_negative_face_slopes_nonempty_of_horizontal_terminal
    P Q hpair hterminal
  let L := ggvOrderedNegativeFaceSlopes P
  let bad : ℕ → Prop := fun i =>
    ∃ (hi : i < L.length) (ρ s : ℕ) (b : Fin 2 →₀ ℕ),
      0 < ρ ∧ 0 < s ∧ IsDirection (ρ : ℤ) (-(s : ℤ)) ∧
      L[i]'hi = (-(s : ℤ) : ℚ) / ρ ∧
      InDir (ρ : ℤ) (-(s : ℤ)) P.1 ∧
      b ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support ∧
      (∀ e ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support,
        e 1 ≤ b 1) ∧ grade b < 0
  have hex : ∃ i, bad i := by
    let i := L.length - 1
    have hz : 0 < L.length := by simpa only [L] using hzero
    have hi : i < L.length := by dsimp [i]; omega
    have hilast : i + 1 = L.length := by dsimp [i]; omega
    have htmem : L[i] ∈ L := List.getElem_mem hi
    obtain ⟨ρ, s, hρ, hs, hdir, hface, hentry, _, _⟩ :=
      ggv_ordered_negative_entry_nat_face P L[i] htmem
    obtain ⟨b, hbN, hbH, hbMax⟩ :=
      counterexample_last_negative_face_meets_horizontal
        P Q hpair ρ s hρ hs hdir i hilast hentry hface
    exact ⟨i, hi, ρ, s, b, hρ, hs, hdir, hentry,
      hface, hbN, hbMax, hterminal b hbH⟩
  let j := Nat.find hex
  obtain ⟨hj, ρ, s, b, hρ, hs, hdir, hentry,
    hface, hb, hbMax, hbNeg⟩ := Nat.find_spec hex
  have hfaceQ : InDir (ρ : ℤ) (-(s : ℤ)) Q.1 :=
    (counterexample_strict_negative_InDir_iff P Q hpair
      ρ (-(s : ℤ)) hdir (by omega)).mp hface
  by_cases hjzero : j = 0
  · have hentry0 : L[0] = (-(s : ℤ) : ℚ) / ρ := by
      simpa only [j, hjzero] using hentry
    obtain ⟨d, hd, _⟩ := (ggv_grades_opposite_proved P Q hpair).1
    obtain ⟨c, hcSymbol, hcMax⟩ :=
      Finset.exists_max_image (symbol P.1).support grade ⟨d, hd⟩
    have hcDiag : c ∈ (leadingForm 1 (-1) P.1).support :=
      (leadingForm_mem_iff_rational_slope P 1 (-1)
        (by norm_num) c).mpr ⟨hcSymbol, by
          intro e he
          have h := hcMax e he
          dsimp [rationalNewtonWeight, grade] at h ⊢
          have hq : (e 0 : ℚ) - e 1 ≤ (c 0 : ℚ) - c 1 := by
            exact_mod_cast h
          norm_num at *
          linarith⟩
    obtain ⟨a, ha, haDiag, haMin⟩ :=
      first_negative_face_meets_diagonal
        P ρ s hρ hs (by simpa only [L] using hzero)
          hentry0 hface c hcDiag
    have haPos := counterexample_diagonal_face_grade_pos P Q hpair a haDiag
    exact ⟨j, hj, ρ, s, a, b, hρ, hs, hdir, hentry,
      hface, hfaceQ, ha, hb, haMin, hbMax, haPos, hbNeg⟩
  · let k := j - 1
    have hkj : k + 1 = j := by dsimp [k]; omega
    have hk : k < L.length := by omega
    have htk : L[k] ∈ L := List.getElem_mem hk
    obtain ⟨ρ₀, s₀, hρ₀, hs₀, hdir₀, hface₀, hentry₀, _, _⟩ :=
      ggv_ordered_negative_entry_nat_face P L[k] htk
    have hleft : -1 < (-(s₀ : ℤ) : ℚ) / ρ₀ := by
      rw [← hentry₀]
      exact (ggv_ordered_negative_slope_bounds P L[k] htk).1
    have hright : (-(s : ℤ) : ℚ) / ρ < 0 := by
      rw [← hentry]
      exact (ggv_ordered_negative_slope_bounds P L[j]
        (List.getElem_mem hj)).2
    have hnext : k + 1 < L.length := by omega
    have hsecond : L[k+1] = (-(s : ℤ) : ℚ) / ρ := by
      simpa only [hkj] using hentry
    obtain ⟨a, haPrev, ha, haMaxPrev, haMin⟩ :=
      leadingFace_successor_shared_endpoint
        P (ρ₀ : ℤ) (-(s₀ : ℤ)) (ρ : ℤ) (-(s : ℤ))
        (by exact_mod_cast hρ₀) (by exact_mod_cast hρ)
        hleft hright k hnext hentry₀ hsecond hface₀ hface
    have haNe := ggv_preliminary_negative_face_min_y_grade_ne_zero
      hsource P Q hpair ρ s hρ hs hdir a ha haMin
    have haPos : 0 < grade a := by
      by_contra hbad
      have haNeg : grade a < 0 := by omega
      have hbadk : bad k :=
        ⟨hk, ρ₀, s₀, a, hρ₀, hs₀,
          hdir₀,
          hentry₀, hface₀, haPrev, haMaxPrev, haNeg⟩
      exact (Nat.find_min hex (by omega)) hbadk
    exact ⟨j, hj, ρ, s, a, b, hρ, hs, hdir, hentry,
      hface, hfaceQ, ha, hb, haMin, hbMax, haPos, hbNeg⟩

/-- Source-shaped version: G13's standard minimal pair supplies a
negative-grade starting point of the horizontal face. Its existence,
and the preliminary companion, remain separate source obligations. -/
theorem counterexample_ordered_strict_crossing_of_horizontal_start
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (hterminal : ∃ a ∈ (leadingForm 1 0 P.1).support,
      (∀ e ∈ (leadingForm 1 0 P.1).support, a 1 ≤ e 1) ∧ grade a < 0) :
    ∃ (j : ℕ) (hj : j < (ggvOrderedNegativeFaceSlopes P).length)
      (ρ s : ℕ) (a b : Fin 2 →₀ ℕ),
      0 < ρ ∧ 0 < s ∧ IsDirection (ρ : ℤ) (-(s : ℤ)) ∧
      (ggvOrderedNegativeFaceSlopes P)[j]'hj = (-(s : ℤ) : ℚ) / ρ ∧
      InDir (ρ : ℤ) (-(s : ℤ)) P.1 ∧
      InDir (ρ : ℤ) (-(s : ℤ)) Q.1 ∧
      a ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support ∧
      b ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support ∧
      (∀ e ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support,
        a 1 ≤ e 1) ∧
      (∀ e ∈ (leadingForm (ρ : ℤ) (-(s : ℤ)) P.1).support,
        e 1 ≤ b 1) ∧ 0 < grade a ∧ grade b < 0 := by
  obtain ⟨a, ha, haMin, haNeg⟩ := hterminal
  exact counterexample_ordered_strict_crossing_of_terminal
    hsource P Q hpair (horizontal_min_y_negative_all P a ha haMin haNeg)

end Dixmier.Weyl
