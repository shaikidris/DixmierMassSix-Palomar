/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVFourierRectangle

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Exact diagonal symbol under Fourier exchange

Every positive PBW contraction lowers total degree. The top diagonal
component therefore transforms by the commutative substitution x ↦ y,
y ↦ -x, although the complete PBW symbol has additional lower terms.
-/

namespace Dixmier.Weyl
open MvPolynomial
set_option maxHeartbeats 800000

noncomputable def diagonalFourierSymbol :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.aeval (fun i : Fin 2 => if i=0 then MvPolynomial.X 1 else -MvPolynomial.X 0)

theorem diagonalFourierSymbol_monomial (i j : ℕ) (a : ℂ) :
    diagonalFourierSymbol (MvPolynomial.monomial (expo i j) a) =
      (-1 : ℂ)^j • MvPolynomial.monomial (expo j i) a := by
  have hm (u v : ℕ) : MvPolynomial.C a * MvPolynomial.X (0 : Fin 2)^u *
      MvPolynomial.X 1^v = MvPolynomial.monomial (expo u v) a := by
    rw [MvPolynomial.C_mul_X_pow_eq_monomial, ← MvPolynomial.monomial_add_single]
    rfl
  rw [← hm i j, ← hm j i]
  simp only [diagonalFourierSymbol, map_mul, map_pow, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, if_neg (by decide : (1 : Fin 2) ≠ 0),
    MvPolynomial.algebraMap_eq, MvPolynomial.smul_eq_C_mul]
  rw [neg_pow]
  simp only [if_true, map_neg, map_one]
  ring

private theorem diagonal_component_monomial (N i j : ℕ) (a : ℂ) :
    weightedHomogeneousComponent (wt 1 1) (N : ℤ)
      (MvPolynomial.monomial (expo i j) a) =
      if i+j=N then MvPolynomial.monomial (expo i j) a else 0 := by
  classical
  apply MvPolynomial.ext
  intro e
  rw [coeff_weightedHomogeneousComponent]
  have hw : Finsupp.weight (wt 1 1) (expo i j) = ((i+j : ℕ) : ℤ) := by
    rw [expo_weight]
    push_cast
    ring
  by_cases ht : i+j=N
  · rw [if_pos ht]
    by_cases he : expo i j=e
    · subst e
      rw [hw, ht]
      simp
    · simp [he, MvPolynomial.coeff_monomial]
  · rw [if_neg ht]
    by_cases he : expo i j=e
    · subst e
      rw [hw]
      have hcast : ((i+j : ℕ) : ℤ) ≠ (N : ℤ) := by exact_mod_cast ht
      rw [if_neg hcast]
      simp
    · simp [he, MvPolynomial.coeff_monomial]

/-- At any degree bounding an antinormal monomial, only its zero
contraction can contribute to the component of that degree. -/
theorem antinormal_diagonal_component (N i j : ℕ) (hbound : i+j ≤ N) :
    weightedHomogeneousComponent (wt 1 1) (N : ℤ)
      (symbol (((concreteY ℂ)^i * (concreteX ℂ)^j : A1 ℂ).1)) =
      if i+j=N then MvPolynomial.monomial (expo j i) 1 else 0 := by
  classical
  rw [symbol_concreteAntiNormalMonomial, map_sum]
  simp_rw [diagonal_component_monomial]
  calc
    _ = (if j-0+(i-0)=N then
        MvPolynomial.monomial (expo (j-0) (i-0))
          ((i.choose 0 : ℂ) * (j.descFactorial 0 : ℂ)) else 0) := by
      apply Finset.sum_eq_single 0
      · intro k hk hk0
        have hkmin : k ≤ min j i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hki : k ≤ i := hkmin.trans (min_le_right _ _)
        have hkj : k ≤ j := hkmin.trans (min_le_left _ _)
        have hne : (j-k)+(i-k) ≠ N := by omega
        simp [hne]
      · intro hnot
        exact False.elim (hnot (by simp))
    _ = _ := by simp [Nat.add_comm]

/-- The Fourier transform of the entire top diagonal component of a
finite polynomial Weyl operator, with the full normal ordering retained. -/
theorem fourier_diagonal_component (P : A1 ℂ) (N : ℕ)
    (hbound : totalDeg P.1 ≤ N) :
    weightedHomogeneousComponent (wt 1 1) (N : ℤ)
      (symbol (fourierAlgHom ℂ P).1) =
      diagonalFourierSymbol
        (weightedHomogeneousComponent (wt 1 1) (N : ℤ) (symbol P.1)) := by
  classical
  obtain ⟨c,hc,hsupport⟩ := symbol_support_eq_pbwCoefficientImage P
  have hsource : symbol P.1 = ∑ p ∈ c.support,
      c p • MvPolynomial.monomial (expo p.1 p.2) 1 := by
    have hcA : c.sum (fun p a => a • ((concreteX ℂ)^p.1 * (concreteY ℂ)^p.2)) = P := by
      apply Subtype.ext
      simpa [Finsupp.sum,concreteX,concreteY,normalOrderedMonomial] using hc
    have h := congrArg (symbolLinearMap (K := ℂ)) hcA
    rw [Finsupp.sum,map_sum] at h
    simp only [map_smul] at h
    symm at h
    change symbol P.1 = ∑ p ∈ c.support,
      c p • symbol (((concreteX ℂ)^p.1 * (concreteY ℂ)^p.2 : A1 ℂ).1) at h
    simpa only [symbol_concreteNormalMonomial] using h
  rw [symbol_fourierAlgHom_eq_sum P c hc, hsource, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpoint : expo p.1 p.2 ∈ (symbol P.1).support := by
    rw [hsupport]
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hdeg := MvPolynomial.le_totalDegree hpoint
  rw [Finsupp.sum_fintype (expo p.1 p.2) (fun _ n => n) (by simp)] at hdeg
  have hsum : p.1+p.2 ≤ N := by
    have hle : p.1+p.2 ≤ totalDeg P.1 := by
      simpa [expo,Fin.sum_univ_two,totalDeg] using hdeg
    exact hle.trans hbound
  rw [map_smul,map_smul,antinormal_diagonal_component N p.1 p.2 hsum,
    map_smul,diagonal_component_monomial]
  by_cases ht : p.1+p.2=N
  · simp only [if_pos ht,map_smul,diagonalFourierSymbol_monomial]
  · simp [ht]

/-- The actual top face of a counterexample transforms by the diagonal
symbol map; the equality includes all normal-ordering corrections. -/
theorem counterexample_fourier_diagonal_leadingForm (P Q : A1 ℂ)
    (hpair : IsCounterexamplePair P Q) :
    leadingForm 1 1 (fourierAlgHom ℂ P).1 =
      diagonalFourierSymbol (leadingForm 1 1 P.1) := by
  have hd : IsDirection 1 1 := by norm_num [IsDirection]
  have hp := counterexample_vDeg_pos_all_directions P Q hpair 1 1 hd
  have hf := counterexample_vDeg_pos_all_directions
    (fourierAlgHom ℂ P) (fourierAlgHom ℂ Q)
    (isCounterexamplePair_fourier P Q hpair) 1 1 hd
  unfold leadingForm
  rw [← totalDeg_eq_vDeg_one_one P hp,
    ← totalDeg_eq_vDeg_one_one (fourierAlgHom ℂ P) hf, totalDeg_fourier_eq]
  exact fourier_diagonal_component P (totalDeg P.1) le_rfl

end Dixmier.Weyl
