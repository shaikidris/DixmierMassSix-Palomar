/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.HorizontalEndpoint

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Horizontal corner obstruction

The exact terminal mate has reduced ratio denominator `p`. The actual
ending point of the original horizontal face is `(p,2p)`, contradicting
the published GGV forbidden-corner input. That input remains explicit.
-/

namespace Dixmier.Weyl

open MvPolynomial Polynomial
set_option maxHeartbeats 1000000

/-- The horizontal terminal pair violates the GGV corner condition. -/
theorem horizontalPair_corner_contradiction
    (H : GGVInputs) (P Q : A1 ℂ) (α μ ν : ℂ)
    (p j : ℕ) (hα : α ≠ 0) (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hp : p.Prime) (hj : 1 < j) (hcoprime : Nat.Coprime j p)
    (hPface : leadingForm 1 0 P.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 *
        (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
          MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) ^ p)
    (hQweight : vDeg 1 0 Q.1 = j)
    (hQface : leadingForm 1 0 Q.1 = MvPolynomial.C ν *
      (MvPolynomial.X 0 *
        (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
          MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) ^ j)
    (hpair : IsCounterexamplePair P Q) : False := by
  have hPweight : vDeg 1 0 P.1 = (p : ℤ) := by
    simpa using crossingFace_weight_any_s P α μ 2 1 0 p hμ (by decide) hPface
  have hPweight' : vDeg 1 0 P.1 = (p : ℤ) * 1 := by
    simpa using hPweight
  have hQweight' : vDeg 1 0 Q.1 = (1 * j : ℕ) := by
    simpa using hQweight
  have hdir : IsDirection 1 0 := by
    simpa using (purePower_isDirection (q := 2) (s := 0) (ρ := 1)
      (by decide) (by decide))
  have hPdir : InDir 1 0 P.1 :=
    horizontalFace_support_two α μ p hα hμ hp.pos _ hPface
  have hQdir : InDir 1 0 Q.1 :=
    horizontalFace_support_two α ν j hα hν (by omega) _ hQface
  have hPpos : 0 < vDeg 1 0 P.1 := by
    rw [hPweight]
    exact_mod_cast hp.pos
  have hQpos : 0 < vDeg 1 0 Q.1 := by
    rw [hQweight]
    exact_mod_cast (show 0 < j by omega)
  obtain ⟨hdivP, hdivQ, hratio, _⟩ :=
    primeMate_terminal_signed_ratio P Q p j 1 0 hp hj (by decide)
      hcoprime hPweight' hQweight'
  obtain ⟨hEnd, hMin⟩ :=
    horizontalFace_ending_endpoint α μ p hα hμ hp.pos _ hPface
  have hforbidden := GGVInputs.corner H P Q 1 0 p (2 * p) j p 2
    hpair hdir (by decide) hPdir hQdir hPpos hQpos
    hdivP hdivQ hEnd hMin hratio hj hp.two_le hcoprime (by decide)
  apply hforbidden
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  constructor
  · push_cast
    field_simp [hpq]
    norm_num
  · push_cast
    field_simp [hpq]

/-- A horizontal prime pure-power face is impossible for an exact
counterexample pair, conditional on the explicit GGV structural inputs. -/
theorem horizontalFace_exclusion
    (H : GGVInputs) (P Q : A1 ℂ) (α μ : ℂ) (p : ℕ)
    (hα : α ≠ 0) (hμ : μ ≠ 0) (hp : p.Prime)
    (hPface : leadingForm 1 0 P.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 *
        (1 + MvPolynomial.C α * MvPolynomial.X 0 ^ 0 *
          MvPolynomial.X 1 ^ (1 : ℕ)) ^ (2 : ℕ)) ^ p)
    (hpair : IsCounterexamplePair P Q) : False := by
  obtain ⟨Q', j, ν, hpair', hj, hcoprime, hν, hQweight, hQface⟩ :=
    horizontal_prime_terminal H P Q μ α p hμ hp hPface hpair
  exact horizontalPair_corner_contradiction H P Q' α μ ν p j
    hα hμ hν hp hj hcoprime hPface hQweight hQface hpair'

end Dixmier.Weyl
