/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CrossingFaceWeight

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The first native cut excludes the terminal strict-crossing pair

All geometric, arithmetic and exact-pair premises of the imported cut/corner
interface are assembled explicitly. The conclusion remains conditional on
`GGVInputs.cutCorner`; this module does not prove that published input.
-/
set_option maxHeartbeats 1000000
namespace Dixmier.Weyl
open MvPolynomial Polynomial

/-- Source-conditional contradiction for an exact terminal pair with the
specified strict-crossing faces and reduced prime denominator. -/
theorem crossingPair_cutCorner_contradiction
    (H : GGVInputs) (P Q : A1 ℂ) (α μ ν : ℂ)
    (p q j ρ s : ℕ)
    (hα : α ≠ 0) (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hp : p.Prime) (hq : 2 ≤ q) (hj : 1 < j) (hs : 0 < s)
    (hparam : (q - 1) * ρ = q * s + 1)
    (hcoprime : Nat.Coprime j p)
    (hPweight : vDeg ρ (-(s : ℤ)) P.1 = (p : ℤ) * ρ)
    (hQweight : vDeg ρ (-(s : ℤ)) Q.1 = (ρ * j : ℕ))
    (hPface : leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ p)
    (hQface : leadingForm ρ (-(s : ℤ)) Q.1 = MvPolynomial.C ν *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ j)
    (hpair : IsCounterexamplePair P Q) : False := by
  have hρ : 0 < ρ := purePower_rho_pos hq hparam
  have hsρ : s < ρ := purePower_s_lt_rho hq hparam
  have hdir := purePower_isDirection hq hparam
  have hpositiveP : 0 < vDeg ρ (-(s : ℤ)) P.1 := by
    rw [hPweight]
    exact mul_pos (by exact_mod_cast hp.pos) (by exact_mod_cast hρ)
  have hpositiveQ : 0 < vDeg ρ (-(s : ℤ)) Q.1 := by
    rw [hQweight]
    exact_mod_cast Nat.mul_pos hρ (by omega : 0 < j)
  have hsmall : (ρ : ℤ) + (-(s : ℤ)) <
      vDeg ρ (-(s : ℤ)) P.1 + vDeg ρ (-(s : ℤ)) Q.1 := by
    rw [hPweight, hQweight]
    have hρz : 0 < (ρ : ℤ) := by exact_mod_cast hρ
    have hsz : 0 ≤ (s : ℤ) := by exact_mod_cast Nat.zero_le s
    have hpz : 2 ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    have hjz : 2 ≤ (j : ℤ) := by exact_mod_cast hj
    push_cast
    nlinarith
  obtain ⟨hdivP, hdivQ, hratio, _⟩ :=
    primeMate_terminal_signed_ratio P Q p j ρ s hp hj hρ hcoprime hPweight hQweight
  obtain ⟨hPdir, hQdir⟩ :=
    crossingPair_commonDirection P Q α μ ν p q j ρ s
      hα hμ hν hp.pos (by omega) (by omega) hs hPface hQface
  obtain ⟨hPend, hQend⟩ :=
    crossingPair_ending_grades_negative P Q α μ ν p q j ρ s
      hα hμ hν hp.pos hq (by omega) hs hparam hPface hQface
  obtain ⟨hstart, hstartmax⟩ :=
    crossingFace_starting_point P α μ q ρ s p hμ hs hsρ hp.pos hPface
  have hroot : maxRootMult (cutPoly ρ (-(s : ℤ)) P.1) = q * p :=
    crossingFace_cutPoly_maxRootMult α μ q ρ s p P
      hα hμ (by omega) hρ hp.pos hPface
  have hforbidden := GGVInputs.cutCorner H P Q ρ (-(s : ℤ))
    p 0 j p q hpair hdir (by exact_mod_cast hρ) (by omega)
    hPdir hQdir hpositiveP hpositiveQ hsmall hdivP hdivQ
    hPend hQend hstart hstartmax hratio hj hp.two_le hcoprime hq
  apply hforbidden
  rw [hroot]
  constructor
  · have hnorm := purePower_normalized_corner hq hparam
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hρq : (ρ : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hρ)
    push_cast
    field_simp [hpq, hρq] at hnorm ⊢
    nlinarith [hnorm]
  · have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    push_cast
    field_simp [hpq]

/-- A strict (`s>0`) pure-power face is excluded after exact mate descent,
conditional on the published GGV structural and cut/corner inputs. No bound
is placed on the mate or on the mass of `P`. -/
theorem crossingFace_strict_exclusion
    (H : GGVInputs) (P Q : A1 ℂ) (α μ : ℂ)
    (p q ρ s : ℕ)
    (hα : α ≠ 0) (hμ : μ ≠ 0) (hp : p.Prime)
    (hq : 2 ≤ q) (hs : 0 < s)
    (hparam : (q - 1) * ρ = q * s + 1)
    (hPface : leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ *
      (MvPolynomial.X 0 * (1 + MvPolynomial.C α *
        MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ q) ^ p)
    (hpair : IsCounterexamplePair P Q) : False := by
  have hsρ : s < ρ := purePower_s_lt_rho hq hparam
  have hdir : IsDirection ρ (-(s : ℤ)) := purePower_isDirection hq hparam
  have hPweight : vDeg ρ (-(s : ℤ)) P.1 = (p : ℤ) * ρ :=
    crossingFace_weight P α μ q ρ s p hμ hs hsρ hp.pos hPface
  obtain ⟨Q', j, ν, hpair', hj, hcoprime, hν, hQweight, hQface⟩ :=
    crossingFace_prime_terminal H P Q μ α p q ρ s hμ hp hs hsρ
      hdir hPweight hPface hpair
  exact crossingPair_cutCorner_contradiction H P Q' α μ ν p q j ρ s
    hα hμ hν hp hq hj hs hparam hcoprime
    hPweight hQweight hPface hQface hpair'

end Dixmier.Weyl
