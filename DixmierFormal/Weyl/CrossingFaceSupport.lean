/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PrimeTerminal

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Support geometry of a pure-power crossing face

Separating the first variable exposes distinct lowest and highest `x`-degrees.
These give two bivariate support monomials and a genuine Newton direction.
-/
set_option maxHeartbeats 1000000
namespace Dixmier.Weyl
open MvPolynomial Polynomial

/-- Highest `x`-degree of a strict-crossing base power. -/
theorem crossingBase_power_natDegree (α : ℂ) (q ρ s e : ℕ)
    (hα : α ≠ 0) (hs : 0 < s) :
    (((MvPolynomial.finSuccEquiv ℂ 1)
      ((MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ e))).natDegree =
        e + s * (q * e) := by
  let E := MvPolynomial.finSuccEquiv ℂ 1
  let β : MvPolynomial (Fin 1) ℂ :=
    MvPolynomial.C α * MvPolynomial.X 0 ^ ρ
  let G : Polynomial (MvPolynomial (Fin 1) ℂ) :=
    1 + Polynomial.C β * Polynomial.X ^ s
  have hβ : β ≠ 0 := by
    dsimp [β]
    exact mul_ne_zero (by simpa using hα) (pow_ne_zero _ (by simp))
  have hGdeg : G.natDegree = s := by
    dsimp [G]
    rw [add_comm]
    change (Polynomial.C β * Polynomial.X ^ s + Polynomial.C 1).natDegree = s
    rw [Polynomial.natDegree_add_C]
    exact Polynomial.natDegree_C_mul_X_pow s β hβ
  have hG : G ≠ 0 := by
    intro hz
    have hzero : G.natDegree = 0 := by simp [hz]
    omega
  have hX1 : E (MvPolynomial.X 1) =
      Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
    simpa [E] using (MvPolynomial.finSuccEquiv_X_succ (R := ℂ) (n := 1) (j := 0))
  have hX0 : E (MvPolynomial.X 0) = Polynomial.X := by
    simpa [E] using (MvPolynomial.finSuccEquiv_X_zero (R := ℂ) (n := 1))
  have hC : E (MvPolynomial.C α) = Polynomial.C (MvPolynomial.C α) := by
    simp [E, MvPolynomial.finSuccEquiv_apply]
  have hform : E ((MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ e) =
      Polynomial.X ^ e * G ^ (q * e) := by
    simp only [map_pow, map_mul, map_add, map_one, hX0, hX1, hC]
    dsimp [G, β]
    rw [mul_pow, ← pow_mul]
    congr 1
    simp only [map_mul, map_pow]
    ring
  rw [show (MvPolynomial.finSuccEquiv ℂ 1) _ = Polynomial.X ^ e * G ^ (q * e) from hform]
  rw [Polynomial.natDegree_X_pow_mul (n := e) (pow_ne_zero _ hG),
      Polynomial.natDegree_pow, hGdeg]
  ring

private theorem polynomial_support_two_of_order_lt_degree
    {R : Type*} [Semiring R] (f : R[X]) (hf : f ≠ 0)
    (h : f.natTrailingDegree < f.natDegree) :
    1 < f.support.card := by
  exact Finset.one_lt_card.mpr ⟨f.natTrailingDegree,
    Polynomial.natTrailingDegree_mem_support_of_nonzero hf,
    f.natDegree, Polynomial.natDegree_mem_support_of_nonzero hf,
    ne_of_lt h⟩

/-- The explicit binomial face has at least two bivariate support monomials. -/
theorem crossingFace_support_two
    (α ν : ℂ) (q ρ s e : ℕ)
    (hα : α ≠ 0) (hν : ν ≠ 0)
    (hq : 0 < q) (hs : 0 < s) (he : 0 < e)
    (F : MvPolynomial (Fin 2) ℂ)
    (hF : F = MvPolynomial.C ν *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ e) :
    1 < F.support.card := by
  let E := MvPolynomial.finSuccEquiv ℂ 1
  let R : MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.X 0 * (1 + MvPolynomial.C α *
      MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q
  have hRtrail : (E (R ^ e)).natTrailingDegree = e := by
    simpa [E, R] using crossingBase_power_natTrailingDegree α q ρ s e hs
  have hRdeg : (E (R ^ e)).natDegree = e + s * (q * e) := by
    simpa [E, R] using crossingBase_power_natDegree α q ρ s e hα hs
  have hRne : E (R ^ e) ≠ 0 := by
    intro hz
    simp [hz] at hRtrail
    omega
  have hνC : (MvPolynomial.C ν : MvPolynomial (Fin 1) ℂ) ≠ 0 := by
    simpa using hν
  have hmap : E F = Polynomial.C (MvPolynomial.C ν) * E (R ^ e) := by
    rw [hF]
    simp [E, R, MvPolynomial.finSuccEquiv_apply]
  have hEne : E F ≠ 0 := by
    rw [hmap]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hνC) hRne
  have hEtrail : (E F).natTrailingDegree = e := by
    rw [hmap, Polynomial.natTrailingDegree_mul
      (Polynomial.C_ne_zero.mpr hνC) hRne,
      Polynomial.natTrailingDegree_C, hRtrail]
    omega
  have hEdeg : (E F).natDegree = e + s * (q * e) := by
    rw [hmap, Polynomial.natDegree_mul
      (Polynomial.C_ne_zero.mpr hνC) hRne,
      Polynomial.natDegree_C, hRdeg]
    omega
  have hqe : 0 < q * e := Nat.mul_pos hq he
  have hseqe : 0 < s * (q * e) := Nat.mul_pos hs hqe
  have hlt : (E F).natTrailingDegree < (E F).natDegree := by
    rw [hEtrail, hEdeg]
    omega
  have hEcard := polynomial_support_two_of_order_lt_degree (E F) hEne hlt
  have hcard : (E F).support.card ≤ F.support.card := by
    rw [MvPolynomial.support_finSuccEquiv]
    exact Finset.card_image_le
  exact lt_of_lt_of_le hEcard hcard

/-- An operator with this leading face has the common direction required by
the published cut interface. -/
theorem crossingFace_inDir
    (T : A1 ℂ) (α ν : ℂ) (q ρ s e : ℕ)
    (hα : α ≠ 0) (hν : ν ≠ 0)
    (hq : 0 < q) (hs : 0 < s) (he : 0 < e)
    (hface : leadingForm ρ (-(s : ℤ)) T.1 = MvPolynomial.C ν *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ e) :
    InDir ρ (-(s : ℤ)) T.1 := by
  exact crossingFace_support_two α ν q ρ s e hα hν hq hs he _ hface

/-- The two explicit pure-power faces occupy the same genuine Newton
direction, as required before a GGV cut. -/
theorem crossingPair_commonDirection
    (P Q : A1 ℂ) (α μ ν : ℂ) (p q j ρ s : ℕ)
    (hα : α ≠ 0) (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hp : 0 < p) (hq : 0 < q) (hj : 0 < j) (hs : 0 < s)
    (hPface : leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ p)
    (hQface : leadingForm ρ (-(s : ℤ)) Q.1 = MvPolynomial.C ν *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ j) :
    InDir ρ (-(s : ℤ)) P.1 ∧ InDir ρ (-(s : ℤ)) Q.1 := by
  exact ⟨crossingFace_inDir P α μ q ρ s p hα hμ hq hs hp hPface,
    crossingFace_inDir Q α ν q ρ s j hα hν hq hs hj hQface⟩
end Dixmier.Weyl
