/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PureGradeCompanion

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# A crossing Poisson companion cannot be a monomial

The exact coefficient action of `xy` forces a single grade on any polynomial
it accompanies. Opposite grades on a crossing face therefore require at least
two support monomials in the companion.
-/

namespace Dixmier.Weyl

open MvPolynomial

theorem crossing_poisson_companion_nonmonomial
    (R F : MvPolynomial (Fin 2) ℂ)
    (a b : Fin 2 →₀ ℕ)
    (hbase : expo 1 1 ∈ F.support)
    (hbr : poisson R F = R)
    (ha : a ∈ R.support) (hb : b ∈ R.support)
    (hapos : 0 < grade a) (hbneg : grade b < 0) :
    1 < F.support.card := by
  by_contra hn
  have hle : F.support.card ≤ 1 := by omega
  have hsubset : F.support ⊆ {expo 1 1} := by
    intro d hd
    have heq := (Finset.card_le_one_iff.mp hle) hd hbase
    simpa only [Finset.mem_singleton] using heq
  let c := MvPolynomial.coeff (expo 1 1) F
  have hc : c ≠ 0 := MvPolynomial.mem_support_iff.mp hbase
  have hmono : F = monomial (expo 1 1) c :=
    MvPolynomial.eq_monomial_of_support_subset_singleton (by
      intro d hd
      exact Finset.mem_singleton.mp (hsubset hd))
  have hexpo : expo 1 1 = Finsupp.single 0 1 + Finsupp.single 1 1 := by
    ext i
    fin_cases i <;> simp [expo]
  have hFxy : F = C c * X 0 * X 1 := by
    calc
      F = monomial (expo 1 1) c := hmono
      _ = monomial (Finsupp.single 0 1 + Finsupp.single 1 1) c := by rw [hexpo]
      _ = monomial (Finsupp.single 0 1) c * X 1 := by
        rw [monomial_add_single]
        simp
      _ = C c * X 0 * X 1 := by rw [C_mul_X_eq_monomial]
  have hlinear : poisson R (C c * X 0 * X 1) = C c * poisson R (X 0 * X 1) := by
    calc
      poisson R (C c * X 0 * X 1) = poisson R (C c * (X 0 * X 1)) := by
        rw [mul_assoc]
      _ = C c * poisson R (X 0 * X 1) := by
        unfold poisson
        simp only [MvPolynomial.pderiv_C_mul]
        ring
  rw [hFxy, hlinear] at hbr
  have hcoeff (e : Fin 2 →₀ ℕ) (he : e ∈ R.support) :
      c * ((e 1 : ℂ) - (e 0 : ℂ)) = 1 := by
    have heCoeff : MvPolynomial.coeff e R ≠ 0 := MvPolynomial.mem_support_iff.mp he
    have h := congrArg (MvPolynomial.coeff e) hbr
    rw [MvPolynomial.coeff_C_mul, poisson_xy_coeff] at h
    apply mul_right_cancel₀ heCoeff
    calc
      (c * ((e 1 : ℂ) - (e 0 : ℂ))) * MvPolynomial.coeff e R =
          c * (((e 1 : ℂ) - (e 0 : ℂ)) * MvPolynomial.coeff e R) := by ring
      _ = MvPolynomial.coeff e R := h
      _ = 1 * MvPolynomial.coeff e R := by ring
  have hca := hcoeff a ha
  have hcb := hcoeff b hb
  have hcomplex : (a 1 : ℂ) - (a 0 : ℂ) = (b 1 : ℂ) - (b 0 : ℂ) :=
    mul_left_cancel₀ hc (hca.trans hcb.symm)
  have hint : (a 1 : ℤ) - (a 0 : ℤ) = (b 1 : ℤ) - (b 0 : ℤ) := by
    exact_mod_cast hcomplex
  have hgradeA : grade a = (a 0 : ℤ) - a 1 := rfl
  have hgradeB : grade b = (b 0 : ℤ) - b 1 := rfl
  omega

end Dixmier.Weyl
