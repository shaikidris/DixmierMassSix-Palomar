/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVRationalFace

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# First downward tilt from a finite exposed face

This is the lower-slope counterpart of the first upward tilt. It is
needed to connect the first strict-negative face to the diagonal
boundary without assuming that the diagonal face has two points.
-/

namespace Dixmier.Weyl

/-- If `m` is the smallest derivative order on a maximal `w`-face
and the support has a lower-order point, the first positive downward
tilt retains the old point and ties a lower-order point. -/
theorem finiteSupport_exists_first_downward_tilt
    {α : Type*} (S : Finset α) (y : α → ℕ) (w : α → ℚ)
    (V : ℚ) (m : ℕ)
    (htop : ∀ p ∈ S, w p ≤ V)
    (hstart : ∀ p ∈ S, w p = V → m ≤ y p)
    (hbelow : ∃ p ∈ S, y p < m) :
    ∃ δ : ℚ, 0 < δ ∧
      (∀ p ∈ S, w p - δ * (y p : ℚ) ≤ V - δ * (m : ℚ)) ∧
      (∃ b ∈ S, y b < m ∧
        w b - δ * (y b : ℚ) = V - δ * (m : ℚ)) := by
  classical
  let L : Finset α := S.filter (fun p => y p < m)
  let gap : α → ℚ := fun p => (V - w p) / ((m - y p : ℕ) : ℚ)
  have hL : L.Nonempty := by
    obtain ⟨p, hp, hpm⟩ := hbelow
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpm⟩⟩
  have hgapPos (p : α) (hp : p ∈ L) : 0 < gap p := by
    obtain ⟨hpS, hpm⟩ := Finset.mem_filter.mp hp
    have hstrict : w p < V := by
      have hle := htop p hpS
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · exact False.elim (Nat.not_le.mpr hpm (hstart p hpS heq))
    have hnum : 0 < V - w p := sub_pos.mpr hstrict
    have hden : (0 : ℚ) < ((m - y p : ℕ) : ℚ) := by
      have hnat : 0 < m - y p := by omega
      exact_mod_cast hnat
    exact div_pos hnum hden
  let values : Finset ℚ := L.image gap
  have hvalues : values.Nonempty := hL.image gap
  let δ : ℚ := values.min' hvalues
  obtain ⟨b, hbL, hbδ⟩ := Finset.mem_image.mp (Finset.min'_mem values hvalues)
  have hδpos : 0 < δ := by
    change 0 < values.min' hvalues
    rw [← hbδ]
    exact hgapPos b hbL
  refine ⟨δ, hδpos, ?_, ?_⟩
  · intro p hpS
    by_cases hpm : y p < m
    · have hpL : p ∈ L := Finset.mem_filter.mpr ⟨hpS, hpm⟩
      have hmin : δ ≤ gap p :=
        Finset.min'_le values (gap p) (Finset.mem_image.mpr ⟨p, hpL, rfl⟩)
      have hden : (0 : ℚ) < ((m - y p : ℕ) : ℚ) := by
        have hnat : 0 < m - y p := by omega
        exact_mod_cast hnat
      have hcast : ((m - y p : ℕ) : ℚ) = (m : ℚ) - (y p : ℚ) := by
        rw [Nat.cast_sub (Nat.le_of_lt hpm)]
      dsimp [gap] at hmin
      rw [le_div_iff₀ hden] at hmin
      rw [hcast] at hmin
      nlinarith [hmin]
    · have hmp : m ≤ y p := Nat.le_of_not_gt hpm
      have hw : w p ≤ V := htop p hpS
      have hn : (m : ℚ) ≤ (y p : ℚ) := by exact_mod_cast hmp
      nlinarith [mul_nonneg (le_of_lt hδpos) (sub_nonneg.mpr hn)]
  · have hbS : b ∈ S := (Finset.mem_filter.mp hbL).1
    have hbm : y b < m := (Finset.mem_filter.mp hbL).2
    refine ⟨b, hbS, hbm, ?_⟩
    have hcast : ((m - y b : ℕ) : ℚ) = (m : ℚ) - (y b : ℚ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hbm)]
    have hden : (0 : ℚ) < ((m - y b : ℕ) : ℚ) := by
      have hnat : 0 < m - y b := by omega
      exact_mod_cast hnat
    change gap b = δ at hbδ
    dsimp [gap] at hbδ
    rw [div_eq_iff (ne_of_gt hden), hcast] at hbδ
    nlinarith [hbδ]

/-- The same first downward tilt for an actual PBW leading face. -/
theorem leadingFace_exists_first_downward_tilt
    (P : A1 ℂ) (ρ σ : ℤ) (hρ : 0 < ρ)
    (a : Fin 2 →₀ ℕ)
    (ha : a ∈ (leadingForm ρ σ P.1).support)
    (hfirst : ∀ p ∈ (leadingForm ρ σ P.1).support,
      a 1 ≤ p 1)
    (hbelow : ∃ p ∈ (symbol P.1).support, p 1 < a 1) :
    ∃ t : ℚ, t < (σ : ℚ) / ρ ∧
      (∀ p ∈ (symbol P.1).support,
        rationalNewtonWeight t p ≤ rationalNewtonWeight t a) ∧
      (∃ b ∈ (symbol P.1).support, b 1 < a 1 ∧
        rationalNewtonWeight t b = rationalNewtonWeight t a) := by
  let t₀ : ℚ := (σ : ℚ) / ρ
  let w : (Fin 2 →₀ ℕ) → ℚ := rationalNewtonWeight t₀
  have ha' := (leadingForm_mem_iff_rational_slope P ρ σ hρ a).mp ha
  have htop : ∀ p ∈ (symbol P.1).support, w p ≤ w a := by
    intro p hp
    exact ha'.2 p hp
  have hstart : ∀ p ∈ (symbol P.1).support,
      w p = w a → a 1 ≤ p 1 := by
    intro p hp heq
    apply hfirst p
    apply (leadingForm_mem_iff_rational_slope P ρ σ hρ p).mpr
    refine ⟨hp, ?_⟩
    intro b hb
    exact (htop b hb).trans_eq heq.symm
  obtain ⟨δ, hδ, hbound, b, hb, hlower, htie⟩ :=
    finiteSupport_exists_first_downward_tilt
      (symbol P.1).support (fun p => p 1) w (w a) (a 1)
      htop hstart hbelow
  refine ⟨t₀ - δ, ?_, ?_, b, hb, hlower, ?_⟩
  · dsimp [t₀]
    linarith
  · intro p hp
    have h := hbound p hp
    dsimp [w] at h
    dsimp [rationalNewtonWeight] at h ⊢
    nlinarith [h]
  · dsimp [w] at htie
    dsimp [rationalNewtonWeight] at htie ⊢
    nlinarith [htie]

end Dixmier.Weyl
