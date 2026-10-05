/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.HorizontalCorner
public import DixmierFormal.Weyl.Statements

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Prime pure-power face exclusion, conditional on published GGV inputs

The strict and horizontal branches meet the frozen Theorem 1.3 statement.
`GGVInputs` remains an explicit parameter until its six source statements
are independently formalized.
-/

namespace Dixmier.Weyl

open MvPolynomial
set_option maxHeartbeats 1000000

/-- Paper Theorem 1.3 in its frozen exact face form, relative to the
published GGV structural inputs. No mass, mate-degree, or mate-order
bound is present. -/
theorem purePowerFaceExclusion_of_GGV (H : GGVInputs) :
    Statement.PurePowerFaceExclusion := by
  intro q s ρ p α μ hq hparam hp hα hμ P Q hpair hface
  let B : MvPolynomial (Fin 2) ℂ :=
    1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ
  have hpow : B ^ (p * q) = (B ^ q) ^ p := by
    rw [← pow_mul, mul_comm]
  have hface' : leadingForm ρ (-(s : ℤ)) P.1 =
      MvPolynomial.C μ *
        (MvPolynomial.X 0 *
          (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ s *
            MvPolynomial.X 1 ^ ρ) ^ q) ^ p := by
    rw [hface]
    change MvPolynomial.C μ * MvPolynomial.X 0 ^ p * B ^ (p * q) =
      MvPolynomial.C μ * (MvPolynomial.X 0 * B ^ q) ^ p
    rw [hpow, mul_pow]
    ring
  by_cases hs : s = 0
  · subst s
    obtain ⟨hq2, hρ1⟩ := purePower_horizontal_parameters hq (by simpa using hparam)
    subst q
    subst ρ
    exact horizontalFace_exclusion H P Q α μ p hα hμ hp
      (by simpa using hface') hpair
  · have hspos : 0 < s := Nat.pos_of_ne_zero hs
    exact crossingFace_strict_exclusion H P Q α μ p q ρ s
      hα hμ hp hq hspos hparam hface' hpair

end Dixmier.Weyl
