/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.NoProperPowerMate
public import DixmierFormal.Weyl.PureGradeGeneration

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

set_option maxHeartbeats 1000000

/-!
# Degree-one Weyl operators

An operator of PBW total degree one is an affine combination of the two
Weyl generators. This makes the remaining diagonal bracket-one case a
two-by-two scalar determinant calculation.
-/

namespace Dixmier.Weyl

open MvPolynomial

private theorem expo_eq_iff (a b i j : ℕ) :
    expo a b = expo i j ↔ a = i ∧ b = j := by
  constructor
  · intro h
    exact Prod.mk.inj (expo_injective h)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Exact affine reconstruction of a degree-one Weyl operator from its
three possible PBW coefficients. -/
theorem affine_reconstruction_of_totalDeg_one
    (T : A1 ℂ) (hdeg : totalDeg T.1 = 1) :
    T = pbwCoeff T.1 0 0 • (1 : A1 ℂ) +
      pbwCoeff T.1 1 0 • (⟨xOp ℂ, xOp_mem_A1⟩ : A1 ℂ) +
      pbwCoeff T.1 0 1 • (⟨yOp ℂ, yOp_mem_A1⟩ : A1 ℂ) := by
  apply symbol_injective
  simp only [symbol_add, symbol_smul, symbol_one_A1, symbol_xOp, symbol_yOp]
  apply MvPolynomial.ext
  intro e
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective e
  rw [symbol_coeff_pbwCoeff]
  have h0 : (0 : Fin 2 →₀ ℕ) = expo 0 0 := by simp [expo]
  have hx : Finsupp.single (0 : Fin 2) 1 = expo 1 0 := by simp [expo]
  have hy : Finsupp.single (1 : Fin 2) 1 = expo 0 1 := by simp [expo]
  by_cases h00 : i = 0 ∧ j = 0
  · rcases h00 with ⟨rfl, rfl⟩
    simp [MvPolynomial.coeff_add, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_one, MvPolynomial.coeff_X, h0, hx, hy, expo_eq_iff]
  by_cases h10 : i = 1 ∧ j = 0
  · rcases h10 with ⟨rfl, rfl⟩
    simp [MvPolynomial.coeff_add, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_one, MvPolynomial.coeff_X, h0, hx, hy, expo_eq_iff]
  by_cases h01 : i = 0 ∧ j = 1
  · rcases h01 with ⟨rfl, rfl⟩
    simp [MvPolynomial.coeff_add, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_one, MvPolynomial.coeff_X, h0, hx, hy, expo_eq_iff]
  have hij : 2 ≤ i + j := by omega
  rw [pbwCoeff_eq_zero_of_totalDeg_one T hdeg i j hij]
  have hn00 : ¬ (0 = i ∧ 0 = j) := by simpa [eq_comm] using h00
  have hn10 : ¬ (1 = i ∧ 0 = j) := by simpa [eq_comm] using h10
  have hn01 : ¬ (0 = i ∧ 1 = j) := by simpa [eq_comm] using h01
  simp [MvPolynomial.coeff_add, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_one, MvPolynomial.coeff_X,
    h0, hx, hy, expo_eq_iff, hn00, hn10, hn01]

/-- In diagonal weight one, the top face retains both linear PBW
coefficients of the full operator. -/
theorem leadingForm_linear_coeff_of_vDeg_one
    (T : A1 ℂ) (hdeg : vDeg 1 1 T.1 = 1)
    (i j : ℕ) (hij : i + j = 1) :
    MvPolynomial.coeff (expo i j) (leadingForm 1 1 T.1) = pbwCoeff T.1 i j := by
  unfold leadingForm
  rw [hdeg, MvPolynomial.coeff_weightedHomogeneousComponent]
  have hw : Finsupp.weight (wt 1 1) (expo i j) = 1 := by
    rw [expo_weight]
    omega
  simp only [hw, ↓reduceIte]
  exact symbol_coeff_pbwCoeff T i j

/-- A diagonal bracket-one pair of weight one has unit affine
determinant. The equation uses the actual PBW coefficients. -/
theorem affine_determinant_one_of_diagonal_bracket_one
    (P Q : A1 ℂ)
    (hPdeg : vDeg 1 1 P.1 = 1) (hQdeg : vDeg 1 1 Q.1 = 1)
    (hbr : poisson (leadingForm 1 1 Q.1) (leadingForm 1 1 P.1) = 1) :
    pbwCoeff Q.1 0 1 * pbwCoeff P.1 1 0 -
      pbwCoeff Q.1 1 0 * pbwCoeff P.1 0 1 = 1 := by
  have hcoeff := congrArg (MvPolynomial.coeff 0) hbr
  rw [poisson_coeff_zero,
    leadingForm_linear_coeff_of_vDeg_one Q hQdeg 0 1 (by norm_num),
    leadingForm_linear_coeff_of_vDeg_one P hPdeg 1 0 (by norm_num),
    leadingForm_linear_coeff_of_vDeg_one Q hQdeg 1 0 (by norm_num),
    leadingForm_linear_coeff_of_vDeg_one P hPdeg 0 1 (by norm_num)] at hcoeff
  simpa using hcoeff

/-- An affine pair with unit determinant generates the Weyl algebra.
Only linear algebra in the underlying complex module is needed once the
determinant is known. -/
theorem affine_pair_generates_of_unit_determinant
    (P Q : A1 ℂ) (a b c d e f : ℂ)
    (hP : P = c • (1 : A1 ℂ) +
      a • (⟨xOp ℂ, xOp_mem_A1⟩ : A1 ℂ) +
      b • (⟨yOp ℂ, yOp_mem_A1⟩ : A1 ℂ))
    (hQ : Q = f • (1 : A1 ℂ) +
      d • (⟨xOp ℂ, xOp_mem_A1⟩ : A1 ℂ) +
      e • (⟨yOp ℂ, yOp_mem_A1⟩ : A1 ℂ))
    (hdet : e * a - d * b = 1) :
    Algebra.adjoin ℂ ({P, Q} : Set (A1 ℂ)) = ⊤ := by
  let xA : A1 ℂ := ⟨xOp ℂ, xOp_mem_A1⟩
  let yA : A1 ℂ := ⟨yOp ℂ, yOp_mem_A1⟩
  let S := Algebra.adjoin ℂ ({P, Q} : Set (A1 ℂ))
  have hPin : P ∈ S := Algebra.subset_adjoin (by simp)
  have hQin : Q ∈ S := Algebra.subset_adjoin (by simp)
  have hdetX : e * a - b * d = 1 := by simpa [mul_comm b d] using hdet
  have hdetY : a * e - d * b = 1 := by simpa [mul_comm a e] using hdet
  have hxexpr : xA = e • P - b • Q - (e * c - b * f) • (1 : A1 ℂ) := by
    rw [hP, hQ]
    calc
      xA = (e * a - b * d) • xA := by rw [hdetX]; simp
      _ = _ := by module
  have hyexpr : yA = a • Q - d • P - (a * f - d * c) • (1 : A1 ℂ) := by
    rw [hP, hQ]
    calc
      yA = (a * e - d * b) • yA := by rw [hdetY]; simp
      _ = _ := by module
  have hx : xA ∈ S := by
    have hcS : (e * c - b * f) • (1 : A1 ℂ) ∈ S :=
      S.smul_mem S.one_mem (e * c - b * f)
    have hrest' : (e • P + -(b • Q)) +
        -((e * c - b * f) • (1 : A1 ℂ)) ∈ S :=
      S.add_mem
        (S.add_mem (S.smul_mem hPin e)
          (Subalgebra.neg_mem (R := ℂ) (A := A1 ℂ) S (S.smul_mem hQin b)))
        (Subalgebra.neg_mem (R := ℂ) (A := A1 ℂ) S hcS)
    have hEq : (e • P + -(b • Q)) + -((e * c - b * f) • (1 : A1 ℂ)) =
        e • P - b • Q - (e * c - b * f) • (1 : A1 ℂ) := by abel
    have hrest := hEq ▸ hrest'
    exact hxexpr ▸ hrest
  have hy : yA ∈ S := by
    have hcS : (a * f - d * c) • (1 : A1 ℂ) ∈ S :=
      S.smul_mem S.one_mem (a * f - d * c)
    have hrest' : (a • Q + -(d • P)) +
        -((a * f - d * c) • (1 : A1 ℂ)) ∈ S :=
      S.add_mem
        (S.add_mem (S.smul_mem hQin a)
          (Subalgebra.neg_mem (R := ℂ) (A := A1 ℂ) S (S.smul_mem hPin d)))
        (Subalgebra.neg_mem (R := ℂ) (A := A1 ℂ) S hcS)
    have hEq : (a • Q + -(d • P)) + -((a * f - d * c) • (1 : A1 ℂ)) =
        a • Q - d • P - (a * f - d * c) • (1 : A1 ℂ) := by abel
    have hrest := hEq ▸ hrest'
    exact hyexpr ▸ hrest
  exact adjoin_eq_top_of_xy_mem S hx hy

/-- A counterexample pair cannot have leading bracket one in the total-degree
direction. The face calculation gives the determinant, while PBW degree one
recovers the full affine operators before applying generation. -/
theorem bracket_one_diagonal_impossible
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) :
    poisson (leadingForm 1 1 Q.1) (leadingForm 1 1 P.1) ≠ 1 := by
  intro hbr
  obtain ⟨hPdeg, hQdeg⟩ := leading_weights_one_of_bracket_one_sum_two
    P Q 1 1 (by norm_num [IsDirection]) (by norm_num) hpair hbr
  obtain ⟨hPtotal, hQtotal⟩ :=
    bracket_one_diagonal_forces_totalDeg_one P Q hpair hbr
  have hPaff := affine_reconstruction_of_totalDeg_one P hPtotal
  have hQaff := affine_reconstruction_of_totalDeg_one Q hQtotal
  have hdet := affine_determinant_one_of_diagonal_bracket_one
    P Q hPdeg hQdeg hbr
  have hgen := affine_pair_generates_of_unit_determinant P Q
    (pbwCoeff P.1 1 0) (pbwCoeff P.1 0 1) (pbwCoeff P.1 0 0)
    (pbwCoeff Q.1 1 0) (pbwCoeff Q.1 0 1) (pbwCoeff Q.1 0 0)
    hPaff hQaff hdet
  exact hpair.2 hgen

/-- The diagonal is the only primitive nonnegative integer normal whose
coordinate sum is two. -/
theorem nonnegative_primitive_sum_two_is_diagonal
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsum : ρ + σ = 2) :
    ρ = 1 ∧ σ = 1 := by
  have hρle : ρ ≤ 2 := by omega
  interval_cases ρ
  · have hσeq : σ = 2 := by omega
    subst σ
    norm_num [IsDirection] at hdir
  · constructor <;> omega
  · have hσeq : σ = 0 := by omega
    subst σ
    norm_num [IsDirection] at hdir

/-- Any counterexample's bracket-one face in a nonnegative primitive
direction must have coordinate sum at least three. This combines the
positive-weight numerical obstruction with the exact diagonal argument. -/
theorem bracket_one_nonnegative_weight_sum_at_least_three
    (P Q : A1 ℂ) (ρ σ : ℤ)
    (hpair : IsCounterexamplePair P Q) (hdir : IsDirection ρ σ)
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hbr : poisson (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1) = 1) :
    3 ≤ ρ + σ := by
  have hpos := hdir.2
  by_contra hn
  have hsmall : ρ + σ = 1 ∨ ρ + σ = 2 := by omega
  rcases hsmall with hsum | hsum
  · exact bracket_one_impossible_of_unit_weight_sum P Q ρ σ hdir hsum hpair hbr
  · obtain ⟨rfl, rfl⟩ :=
      nonnegative_primitive_sum_two_is_diagonal ρ σ hdir hρ hσ hsum
    exact bracket_one_diagonal_impossible P Q hpair hbr

end Dixmier.Weyl
