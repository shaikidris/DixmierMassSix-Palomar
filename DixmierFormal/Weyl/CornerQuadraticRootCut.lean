/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCutRootEndpoint
public import DixmierFormal.Scalar.Section6Roots

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Root multiplicity of a quadratic corner face

In the height-two branch of G13 Proposition 5.6 the root polynomial
has degree two. Its `m`-th power has maximum root order `m` or `2m`.
This is only the polynomial root dichotomy; identifying the actual
operator face with such a power and excluding the first alternative
are separate obligations.
-/

namespace Dixmier.Weyl

open Polynomial

theorem maxRootMult_C_mul (p : ℂ[X]) (ν : ℂ) (hν : ν ≠ 0) :
    maxRootMult (C ν * p) = maxRootMult p := by
  classical
  unfold maxRootMult
  rw [roots_C_mul p hν]
  congr 1
  funext z
  rw [← count_roots, roots_C_mul p hν, count_roots]

theorem quadratic_power_maxRootMult_dichotomy
    (r : ℂ[X]) (m : ℕ) (hm : 0 < m) (hdeg : r.natDegree = 2) :
    maxRootMult (r ^ m) = m ∨ maxRootMult (r ^ m) = 2 * m := by
  have hrne : r ≠ 0 := ne_zero_of_natDegree_gt (hdeg ▸ (by omega : 0 < 2))
  have hpowdeg : 0 < (r ^ m).natDegree := by
    rw [natDegree_pow,hdeg]
    omega
  obtain ⟨c,hroot,hmax⟩ :=
    exists_rootMultiplicity_eq_maxRootMult (r ^ m) hpowdeg
  let q := rootMultiplicity c r
  have hqpos : 0 < q := by
    have hpowpos : 0 < rootMultiplicity c (r ^ m) :=
      (rootMultiplicity_pos (pow_ne_zero m hrne)).mpr hroot
    rw [Dixmier.section6_rootMultiplicity_pow] at hpowpos
    by_contra hnot
    have hz : rootMultiplicity c r = 0 := by omega
    simp [hz] at hpowpos
  have hqle : q ≤ 2 := by
    have hle := natDegree_le_of_dvd (pow_rootMultiplicity_dvd r c) hrne
    rw [natDegree_pow,natDegree_X_sub_C,hdeg] at hle
    simpa [q] using hle
  have hq : q = 1 ∨ q = 2 := by omega
  rw [← hmax,Dixmier.section6_rootMultiplicity_pow]
  rcases hq with hq | hq
  · left
    simp [q, hq]
  · right
    simp [q, hq, Nat.mul_comm]

/-- Transfer the dichotomy to the actual face polynomial once its
quadratic-power identity has been established. -/
theorem quadratic_corner_cutPoly_maxRootMult_dichotomy
    (P : A1 ℂ) (ρ σ : ℤ) (r : ℂ[X]) (ν : ℂ) (m : ℕ)
    (hν : ν ≠ 0) (hm : 0 < m) (hdeg : r.natDegree = 2)
    (hface : cutPoly ρ σ P.1 = C ν * r ^ m) :
    maxRootMult (cutPoly ρ σ P.1) = m ∨
      maxRootMult (cutPoly ρ σ P.1) = 2 * m := by
  rw [hface,maxRootMult_C_mul _ _ hν]
  exact quadratic_power_maxRootMult_dichotomy r m hm hdeg

/-- Evaluation of an explicit horizontal power face is exactly the
univariate cut polynomial used by the maximum-root construction. -/
theorem horizontal_power_face_cutPoly
    (P : A1 ℂ) (ν : ℂ) (r : ℂ[X]) (m : ℕ)
    (hface : leadingForm 1 0 P.1 = MvPolynomial.C ν *
      (MvPolynomial.X 0 *
        r.eval₂ MvPolynomial.C (MvPolynomial.X 1)) ^ m) :
    cutPoly 1 0 P.1 = C ν * r ^ m := by
  have hspec (s : ℂ[X]) :
      MvPolynomial.eval₂ Polynomial.C
        (fun i : Fin 2 => if i = 0 then 1 else Polynomial.X)
        (s.eval₂ MvPolynomial.C (MvPolynomial.X 1)) = s := by
    induction s using Polynomial.induction_on' with
    | add p q hp hq => simpa [Polynomial.eval₂_add, MvPolynomial.eval₂_add] using congrArg₂ (· + ·) hp hq
    | monomial n c =>
        simp [Polynomial.eval₂_monomial, MvPolynomial.eval₂_mul,
          Polynomial.C_mul_X_pow_eq_monomial]
  rw [cutPoly,hface]
  simp [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, hspec]

/-- For a horizontal quadratic-power face, the actual maximum-root cut
can only return the normalized corner once its selected endpoint is
known to have strictly negative grade. -/
theorem horizontal_quadratic_face_negative_cut_preserves_corner
    (P : A1 ℂ) (ν : ℂ) (r : ℂ[X]) (m : ℕ)
    (hν : ν ≠ 0) (hm : 0 < m) (hdeg : r.natDegree = 2)
    (hface : leadingForm 1 0 P.1 = MvPolynomial.C ν *
      (MvPolynomial.X 0 *
        r.eval₂ MvPolynomial.C (MvPolynomial.X 1)) ^ m)
    (hgrade : (m : ℤ) -
      (maxRootMult (cutPoly 1 0 P.1) : ℤ) < 0) :
    maxRootMult (cutPoly 1 0 P.1) = 2 * m := by
  have hpoly := horizontal_power_face_cutPoly P ν r m hface
  have hcases := quadratic_corner_cutPoly_maxRootMult_dichotomy
    P 1 0 r ν m hν hm hdeg hpoly
  rcases hcases with hfirst | hsecond
  · rw [hfirst] at hgrade
    omega
  · exact hsecond

/-- Once the normalized height-two face has starting ramified exponent
`(d,0)` and the direction satisfies `ρ=l`, `ρ+σ=1`, the two possible
root orders give either a grade-zero cut endpoint or the same
normalized corner. -/
theorem quadratic_corner_cut_endpoint_dichotomy
    (l d M : ℕ) (hM : M = d ∨ M = 2 * d) :
    let E : ℤ × ℕ :=
      ((d : ℤ) + ((l : ℤ) - 1) * (M : ℤ), M)
    E.1 - (l : ℤ) * (E.2 : ℤ) = 0 ∨
      (E.1 = (d : ℤ) * ((l : ℤ) * 2 - 1) ∧ E.2 = 2 * d) := by
  dsimp
  rcases hM with h | h
  · left
    rw [h]
    ring
  · right
    rw [h]
    constructor
    · push_cast
      ring
    · rfl

/-- A strict negative-grade selected endpoint rules out the
single-root-order branch and keeps the normalized corner. -/
theorem quadratic_corner_cut_negative_preserves_corner
    (l d M : ℕ) (hM : M = d ∨ M = 2 * d)
    (hgrade : (d : ℤ) + ((l : ℤ) - 1) * (M : ℤ) -
      (l : ℤ) * (M : ℤ) < 0) :
    M = 2 * d ∧
      (d : ℤ) + ((l : ℤ) - 1) * (M : ℤ) =
        (d : ℤ) * ((l : ℤ) * 2 - 1) := by
  have hcases := quadratic_corner_cut_endpoint_dichotomy l d M hM
  dsimp at hcases
  rcases hcases with hzero | ⟨hfirst,hsecond⟩
  · omega
  · exact ⟨hsecond,hfirst⟩

/-- The height-two preservation calculation on the actual finite
ramified operator. The face-power identity and negative selected grade
are explicit source hypotheses; the conclusion is an occupied point of
the sheared operator, rather than only a scalar root count. -/
theorem ramified_quadratic_corner_cut_preserves_endpoint
    (l d : ℕ) (hl : 0 < l) (hd : 0 < d)
    (ρ σ : ℤ) (hρ : 0 < ρ)
    (hρl : ρ = (l : ℤ)) (hsum : ρ + σ = 1)
    (T : ramifiedOperatorAlgebra l) (ν : ℂ) (r : ℂ[X])
    (hν : ν ≠ 0) (hdeg : r.natDegree = 2)
    (hface : ramifiedFacePolynomial l hl T (d : ℤ)
      (ramifiedCutExponent l ρ σ) = C ν * r ^ d)
    (hpoint : ((d : ℤ),0) ∈ ramifiedPBWSupport l hl T)
    (hupper : ∀ u : ℤ, ∀ j : ℕ,
      (u,j) ∈ ramifiedPBWSupport l hl T →
        ramifiedWeight l ρ σ (u,j) ≤ ρ*(d : ℤ))
    (hgrade : (d : ℤ) - ramifiedCutExponent l ρ σ *
      (maxRootMult (ramifiedFacePolynomial l hl T (d : ℤ)
        (ramifiedCutExponent l ρ σ)) : ℤ) -
      (l : ℤ) * (maxRootMult (ramifiedFacePolynomial l hl T (d : ℤ)
        (ramifiedCutExponent l ρ σ)) : ℤ) < 0) :
    ∃ c : ℂ,
      (ramifiedFacePolynomial l hl T (d : ℤ)
        (ramifiedCutExponent l ρ σ)).IsRoot c ∧
      (((d : ℤ)*((l : ℤ)*2-1),2*d) ∈
        ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c T)) := by
  have hdiv : ρ ∣ (l : ℤ) := by rw [hρl]
  have hpos : 0 < ρ + σ := by omega
  have htop : ramifiedWeight l ρ σ ((d : ℤ),0) = ρ*(d : ℤ) := by
    simp [ramifiedWeight]
  have hpowdeg : 0 < (ramifiedFacePolynomial l hl T (d : ℤ)
      (ramifiedCutExponent l ρ σ)).natDegree := by
    rw [hface, Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr hν)
      (pow_ne_zero _ (ne_zero_of_natDegree_gt (hdeg ▸ (by omega : 0 < 2))))]
    simp [hdeg, hd]
  obtain ⟨c,hroot,_,hcut⟩ :=
    ramifiedCutAut_exists_maxRoot_start l hl ρ σ (d : ℤ) (d : ℤ) 0
      hρ hdiv hpos T hpoint htop hupper hpowdeg
  let M := maxRootMult (ramifiedFacePolynomial l hl T (d : ℤ)
    (ramifiedCutExponent l ρ σ))
  have hM : M = d ∨ M = 2*d := by
    dsimp [M]
    rw [hface, maxRootMult_C_mul _ _ hν]
    exact quadratic_power_maxRootMult_dichotomy r d hd hdeg
  have hk : ramifiedCutExponent l ρ σ = 1 - (l : ℤ) := by
    have hself : ((l : ℤ) / ρ) = 1 := by
      rw [hρl]
      exact Int.ediv_self (ne_of_gt (by simpa [hρl] using hρ))
    unfold ramifiedCutExponent
    rw [hself]
    omega
  have hgrade' : (d : ℤ) + ((l : ℤ)-1)*(M : ℤ) -
      (l : ℤ)*(M : ℤ) < 0 := by
    dsimp [M]
    rw [hk] at hgrade
    rw [hk]
    nlinarith [hgrade]
  obtain ⟨hMfull,hcoord⟩ :=
    quadratic_corner_cut_negative_preserves_corner l d M hM hgrade'
  refine ⟨c,hroot,?_⟩
  change ((d : ℤ) - ramifiedCutExponent l ρ σ*(M : ℤ),M) ∈
    ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c T) at hcut
  have hfirst : (d : ℤ) - ramifiedCutExponent l ρ σ*(M : ℤ) =
      (d : ℤ)*((l : ℤ)*2-1) := by
    rw [hk,hMfull]
    push_cast
    ring
  have hpair : ((d : ℤ)*((l : ℤ)*2-1),2*d) =
      ((d : ℤ) - ramifiedCutExponent l ρ σ*(M : ℤ),M) := by
    exact Prod.ext hfirst.symm hMfull.symm
  rw [hpair]
  exact hcut

end Dixmier.Weyl
