/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Scalar.HorizontalCompanion

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Square factorization in the horizontal companion equation

These lemmas prepare the constant-Wronskian step of the horizontal-crossing
argument. They are statements about polynomials, independent of a Weyl mate.
-/

namespace Dixmier.Horizontal

open Polynomial Finset

theorem square_factor_of_all_roots_double (g : ℂ[X])
    (hg : g ≠ 0)
    (hall : ∀ β : ℂ, g.IsRoot β → rootMultiplicity β g = 2) :
    ∃ h : ℂ[X], h = (∏ β ∈ g.roots.toFinset, (X - C β)) ∧
      g = C g.leadingCoeff * h ^ 2 ∧ h.Monic := by
  classical
  let S := g.roots.toFinset
  let h : ℂ[X] := ∏ β ∈ S, (X - C β)
  have hprod : (∏ β ∈ S, (X - C β) ^ rootMultiplicity β g) = h ^ 2 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro β hβ
    rw [hall β ((mem_roots hg).mp (Multiset.mem_toFinset.mp hβ))]
  refine ⟨h, rfl, ?_, ?_⟩
  · calc
      g = C g.leadingCoeff * (g.roots.map fun β => X - C β).prod :=
        (C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree).symm
      _ = C g.leadingCoeff * (∏ β ∈ S, (X - C β) ^ rootMultiplicity β g) := by
        rw [prod_multiset_root_eq_finset_root]
      _ = C g.leadingCoeff * h ^ 2 := by rw [hprod]
  · exact monic_prod_X_sub_C id S

theorem root_product_dvd_companion (g f : ℂ[X])
    (hg : g ≠ 0) (hroot : ∀ β : ℂ, g.IsRoot β → f.IsRoot β) :
    (∏ β ∈ g.roots.toFinset, (X - C β)) ∣ f := by
  classical
  apply Finset.prod_dvd_of_coprime
  · intro β _ γ _ hne
    exact pairwise_coprime_X_sub_C (fun _ _ h => h) hne
  · intro β hβ
    exact (dvd_iff_isRoot).mpr
      (hroot β ((mem_roots hg).mp (Multiset.mem_toFinset.mp hβ)))

theorem HorizComp.square_reduces_wronskian {g f h κ : ℂ[X]} {c : ℂ}
    (hcomp : HorizComp 1 g f) (hc : c ≠ 0) (hh : h ≠ 0)
    (hg : g = C c * h ^ 2) (hf : f = h * κ) :
    κ * derivative h - h * derivative κ = 1 := by
  have hpre : (C c * h ^ 2) * (κ * derivative h - h * derivative κ) =
      C c * h ^ 2 := by
    calc
      (C c * h ^ 2) * (κ * derivative h - h * derivative κ) =
          (h * κ) * derivative (C c * h ^ 2) -
            derivative (h * κ) * (C c * h ^ 2) := by
              simp only [pow_two, derivative_mul, derivative_C, zero_mul, zero_add]
              ring
      _ = C c * h ^ 2 := by
        have he := hcomp
        unfold HorizComp at he
        rw [hg, hf] at he
        simpa using he
  exact mul_left_cancel₀
    (mul_ne_zero (C_ne_zero.mpr hc) (pow_ne_zero 2 hh))
    (by simpa only [mul_one] using hpre)

private theorem wronskian_coeff_top (h κ : ℂ[X]) (he : 0 < h.natDegree) :
    (κ * derivative h - h * derivative κ).coeff
        ((h.natDegree - 1) + κ.natDegree) =
      ((h.natDegree : ℂ) - (κ.natDegree : ℂ)) *
        κ.leadingCoeff * h.leadingCoeff := by
  set e := h.natDegree
  set L := κ.natDegree
  have hkh : (κ * derivative h).coeff ((e - 1) + L) =
      κ.coeff L * (derivative h).coeff (e - 1) := by
    rw [add_comm]
    exact coeff_mul_of_natDegree_le' (le_refl L) (natDegree_derivative_le h)
  have hdh : (derivative h).coeff (e - 1) = (e : ℂ) * h.coeff e := by
    rw [coeff_derivative, show e - 1 + 1 = e by omega]
    rw [Nat.cast_sub (by omega : 1 ≤ e)]
    ring
  have hce : h.coeff e = h.leadingCoeff := by simp [e, coeff_natDegree]
  have hcL : κ.coeff L = κ.leadingCoeff := by simp [L, coeff_natDegree]
  by_cases hL : L = 0
  · have hdk : derivative κ = 0 := derivative_of_natDegree_zero hL
    rw [coeff_sub, hkh, hdh, hdk, mul_zero, coeff_zero, sub_zero, hcL, hce]
    simp [hL]
    ring
  · have hhk : (h * derivative κ).coeff ((e - 1) + L) =
        h.coeff e * (derivative κ).coeff (L - 1) := by
      rw [show (e - 1) + L = e + (L - 1) by omega]
      exact coeff_mul_of_natDegree_le' (le_refl e) (natDegree_derivative_le κ)
    have hdk : (derivative κ).coeff (L - 1) = (L : ℂ) * κ.coeff L := by
      rw [coeff_derivative, show L - 1 + 1 = L by omega]
      rw [Nat.cast_sub (by omega : 1 ≤ L)]
      ring
    rw [coeff_sub, hkh, hhk, hdh, hdk]
    rw [hcL, hce]
    ring

private theorem equal_degrees_of_constant_wronskian (h κ : ℂ[X])
    (he : 0 < h.natDegree)
    (hN : 0 < (h.natDegree - 1) + κ.natDegree)
    (hw : κ * derivative h - h * derivative κ = 1) :
    h.natDegree = κ.natDegree := by
  have hh : h ≠ 0 := ne_zero_of_natDegree_gt he
  have hκ : κ ≠ 0 := by
    intro hz
    rw [hz] at hw
    simp at hw
  have hc := wronskian_coeff_top h κ he
  rw [hw] at hc
  have hz : ((h.natDegree : ℂ) - (κ.natDegree : ℂ)) *
      κ.leadingCoeff * h.leadingCoeff = 0 := by
    have hzero : (1 : ℂ[X]).coeff ((h.natDegree - 1) + κ.natDegree) = 0 := by
      rw [coeff_one, if_neg (Nat.ne_of_gt hN)]
    exact hc.symm.trans hzero
  have hdiff : (h.natDegree : ℂ) - (κ.natDegree : ℂ) = 0 := by
    have hz' := (mul_eq_zero.mp hz).resolve_right (leadingCoeff_ne_zero.mpr hh)
    exact (mul_eq_zero.mp hz').resolve_right (leadingCoeff_ne_zero.mpr hκ)
  exact_mod_cast sub_eq_zero.mp hdiff

/-- A monic nonconstant polynomial in a constant-Wronskian pair is linear. -/
theorem degree_one_of_constant_wronskian (h κ : ℂ[X])
    (hm : h.Monic) (he : 0 < h.natDegree)
    (hw : κ * derivative h - h * derivative κ = 1) :
    h.natDegree = 1 := by
  by_contra hne
  have he2 : 2 ≤ h.natDegree := by omega
  have hN : 0 < (h.natDegree - 1) + κ.natDegree := by omega
  have heq := equal_degrees_of_constant_wronskian h κ he hN hw
  have hκ : κ ≠ 0 := by
    intro hz
    rw [hz] at hw
    simp at hw
  let κ' := κ - C κ.leadingCoeff * h
  have hdegree : κ.degree = (C κ.leadingCoeff * h).degree := by
    rw [degree_C_mul (leadingCoeff_ne_zero.mpr hκ)]
    exact (degree_eq_natDegree hκ).trans
      ((heq ▸ degree_eq_natDegree hm.ne_zero).symm)
  have hlc : κ.leadingCoeff = (C κ.leadingCoeff * h).leadingCoeff := by
    rw [hm.leadingCoeff_C_mul]
  have hdeglt : κ'.degree < h.degree := by
    have hlt := degree_sub_lt_left hdegree hκ hlc
    simpa only [κ', degree_eq_natDegree hκ, degree_eq_natDegree hm.ne_zero,
      heq] using hlt
  have hnatlt : κ'.natDegree < h.natDegree := by
    by_cases hz : κ' = 0
    · simp [hz, he]
    · exact natDegree_lt_natDegree hz hdeglt
  have hw' : κ' * derivative h - h * derivative κ' = 1 := by
    dsimp [κ']
    simp only [derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add]
    convert hw using 1
    ring
  have hN' : 0 < (h.natDegree - 1) + κ'.natDegree := by omega
  have heq' := equal_degrees_of_constant_wronskian h κ' he hN' hw'
  omega

/-- The six-term horizontal companion equation leaves only a linear root product. -/
theorem HorizComp.mass_six_square_linear {g f : ℂ[X]}
    (hc : HorizComp 1 g f) (hg : 0 < g.natDegree)
    (hord : rootMultiplicity 0 g < 1)
    (ht : Dixmier.termCount (g ^ 2) ≤ 6) :
    ∃ h : ℂ[X], h.Monic ∧ h.natDegree = 1 ∧
      g = C g.leadingCoeff * h ^ 2 := by
  have hg0 : g ≠ 0 := ne_zero_of_natDegree_gt hg
  obtain ⟨h, hdef, hsq, hm⟩ := square_factor_of_all_roots_double g hg0
    (hc.all_roots_double hg hord ht)
  have hroot : ∀ β : ℂ, g.IsRoot β → f.IsRoot β := by
    intro β hβ
    exact (hc.root_slope hg0 hβ).1
  have hdvd : h ∣ f := by
    rw [hdef]
    exact root_product_dvd_companion g f hg0 hroot
  obtain ⟨κ, hκ⟩ := hdvd
  have hhpos : 0 < h.natDegree := by
    by_contra hn
    have hzero : h.natDegree = 0 := by omega
    have hone : h = 1 := eq_one_of_monic_natDegree_zero hm hzero
    have hgd : g.natDegree = 0 := by
      rw [hsq, hone]
      simp
    omega
  have hw := hc.square_reduces_wronskian
    (leadingCoeff_ne_zero.mpr hg0) hm.ne_zero hsq hκ
  exact ⟨h, hm, degree_one_of_constant_wronskian h κ hm hhpos hw, hsq⟩

/-- In particular the horizontal cut polynomial is a shifted quadratic square;
the shift is nonzero because the face crosses the grade-zero axis. -/
theorem HorizComp.mass_six_quadratic {g f : ℂ[X]}
    (hc : HorizComp 1 g f) (hg : 0 < g.natDegree)
    (hord : rootMultiplicity 0 g < 1)
    (ht : Dixmier.termCount (g ^ 2) ≤ 6) :
    ∃ c β : ℂ, c ≠ 0 ∧ β ≠ 0 ∧ g = C c * (X - C β) ^ 2 := by
  obtain ⟨h, hm, hdeg, hsq⟩ := hc.mass_six_square_linear hg hord ht
  let β := -h.coeff 0
  have hshape : h = X - C β := by
    dsimp [β]
    rw [hm.eq_X_add_C hdeg]
    simp
  have hg0 : g ≠ 0 := ne_zero_of_natDegree_gt hg
  have hβ : β ≠ 0 := by
    intro hz
    have hroot0 : g.IsRoot 0 := by
      rw [hsq, hshape, hz]
      simp
    have hpos := (rootMultiplicity_pos hg0).mpr hroot0
    omega
  exact ⟨g.leadingCoeff, β, leadingCoeff_ne_zero.mpr hg0, hβ, by
    rw [hshape] at hsq
    exact hsq⟩

end Dixmier.Horizontal
