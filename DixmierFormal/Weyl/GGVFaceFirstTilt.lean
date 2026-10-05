/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVFaceOrderGeometry

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# First upward tilt from a finite exposed face

This is the finite-support transition needed to connect consecutive
negative Newton directions. It makes no assertion that the resulting
face is the next face of a particular Weyl operator.
-/

namespace Dixmier.Weyl

/-- If `M` is the largest derivative order on a maximal `w`-face and
there is a support point of larger order, the first positive upward
tilt produces a new maximal face through order `M` and at least one
strictly larger order. -/
theorem finiteSupport_exists_first_upward_tilt
    {α : Type*} (S : Finset α) (y : α → ℕ) (w : α → ℚ)
    (V : ℚ) (M : ℕ)
    (htop : ∀ p ∈ S, w p ≤ V)
    (hend : ∀ p ∈ S, w p = V → y p ≤ M)
    (habove : ∃ p ∈ S, M < y p) :
    ∃ t : ℚ, 0 < t ∧
      (∀ p ∈ S, w p + t * (y p : ℚ) ≤ V + t * (M : ℚ)) ∧
      (∃ B ∈ S, M < y B ∧
        w B + t * (y B : ℚ) = V + t * (M : ℚ)) := by
  classical
  let L : Finset α := S.filter (fun p => M < y p)
  let gap : α → ℚ := fun p =>
    (V - w p) / ((y p - M : ℕ) : ℚ)
  have hL : L.Nonempty := by
    obtain ⟨p,hp,hpm⟩ := habove
    exact ⟨p, Finset.mem_filter.mpr ⟨hp,hpm⟩⟩
  have hgapPos (p : α) (hp : p ∈ L) : 0 < gap p := by
    obtain ⟨hpS,hpm⟩ := Finset.mem_filter.mp hp
    have hstrict : w p < V := by
      have hle := htop p hpS
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · exact False.elim (Nat.not_le.mpr hpm (hend p hpS heq))
    have hnum : 0 < V - w p := sub_pos.mpr hstrict
    have hden : (0 : ℚ) < ((y p - M : ℕ) : ℚ) := by
      have hnat : 0 < y p - M := by omega
      exact_mod_cast hnat
    exact div_pos hnum hden
  let values : Finset ℚ := L.image gap
  have hvalues : values.Nonempty := hL.image gap
  let t : ℚ := values.min' hvalues
  obtain ⟨B,hBL,hBt⟩ := Finset.mem_image.mp (Finset.min'_mem values hvalues)
  have htpos : 0 < t := by
    change 0 < values.min' hvalues
    rw [← hBt]
    exact hgapPos B hBL
  refine ⟨t,htpos,?_,?_⟩
  · intro p hpS
    by_cases hpm : M < y p
    · have hpL : p ∈ L := Finset.mem_filter.mpr ⟨hpS,hpm⟩
      have hmin : t ≤ gap p :=
        Finset.min'_le values (gap p) (Finset.mem_image.mpr ⟨p,hpL,rfl⟩)
      have hden : (0 : ℚ) < ((y p - M : ℕ) : ℚ) := by
        have hnat : 0 < y p - M := by omega
        exact_mod_cast hnat
      have hcast : ((y p - M : ℕ) : ℚ) = (y p : ℚ) - (M : ℚ) := by
        rw [Nat.cast_sub (Nat.le_of_lt hpm)]
      dsimp [gap] at hmin
      rw [le_div_iff₀ hden] at hmin
      rw [hcast] at hmin
      nlinarith [hmin]
    · have hmn : y p ≤ M := Nat.le_of_not_gt hpm
      have hw : w p ≤ V := htop p hpS
      have hn : (y p : ℚ) ≤ (M : ℚ) := by exact_mod_cast hmn
      nlinarith [mul_nonneg (le_of_lt htpos) (sub_nonneg.mpr hn)]
  · have hBS : B ∈ S := (Finset.mem_filter.mp hBL).1
    have hBM : M < y B := (Finset.mem_filter.mp hBL).2
    refine ⟨B,hBS,hBM,?_⟩
    have hcast : ((y B - M : ℕ) : ℚ) = (y B : ℚ) - (M : ℚ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hBM)]
    have hden : (0 : ℚ) < ((y B - M : ℕ) : ℚ) := by
      have hnat : 0 < y B - M := by omega
      exact_mod_cast hnat
    change gap B = t at hBt
    dsimp [gap] at hBt
    rw [div_eq_iff (ne_of_gt hden), hcast] at hBt
    nlinarith [hBt]

/-- Before a positive upward tilt first ties a higher-order point,
any support point still tied with the old endpoint has exactly the
old order and old weight. -/
theorem finiteSupport_before_upward_tilt_old_endpoint
    {α : Type*} (S : Finset α) (y : α → ℕ) (w : α → ℚ)
    (V : ℚ) (M : ℕ) (u tFirst : ℚ)
    (hu : 0 < u) (hbefore : u < tFirst)
    (htop : ∀ p ∈ S, w p ≤ V)
    (hfirst : ∀ p ∈ S,
      w p + tFirst * (y p : ℚ) ≤ V + tFirst * (M : ℚ))
    (p : α) (hp : p ∈ S)
    (htie : w p + u * (y p : ℚ) = V + u * (M : ℚ)) :
    y p = M ∧ w p = V := by
  have hw := htop p hp
  have hf := hfirst p hp
  have hyge : M ≤ y p := by
    by_contra hbad
    have hlt : (y p : ℚ) < M := by
      exact_mod_cast Nat.lt_of_not_ge hbad
    nlinarith [mul_pos hu (sub_pos.mpr hlt)]
  have hyle : y p ≤ M := by
    by_contra hbad
    have hgt : (M : ℚ) < y p := by
      exact_mod_cast Nat.lt_of_not_ge hbad
    have hprod : 0 < (tFirst - u) * ((y p : ℚ) - M) :=
      mul_pos (sub_pos.mpr hbefore) (sub_pos.mpr hgt)
    nlinarith [hf, htie, hprod]
  have hyeq : y p = M := Nat.le_antisymm hyle hyge
  constructor
  · exact hyeq
  · rw [hyeq] at htie
    linarith

/-- If a higher-order support point matches or beats the old endpoint
at a later tilt, a supporting first tilt cannot occur after it. -/
theorem finiteSupport_first_upward_tilt_le_later
    {α : Type*} (S : Finset α) (y : α → ℕ) (w : α → ℚ)
    (V : ℚ) (M : ℕ) (tFirst tLater : ℚ)
    (hfirst : ∀ p ∈ S,
      w p + tFirst * (y p : ℚ) ≤ V + tFirst * (M : ℚ))
    (b : α) (hb : b ∈ S) (hhigher : M < y b)
    (hlater : V + tLater * (M : ℚ) ≤
      w b + tLater * (y b : ℚ)) :
    tFirst ≤ tLater := by
  by_contra hbad
  have hlt : tLater < tFirst := lt_of_not_ge hbad
  have hy : (M : ℚ) < y b := by exact_mod_cast hhigher
  have hprod : 0 < (tFirst - tLater) * ((y b : ℚ) - M) :=
    mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hy)
  nlinarith [hfirst b hb, hlater, hprod]

end Dixmier.Weyl
