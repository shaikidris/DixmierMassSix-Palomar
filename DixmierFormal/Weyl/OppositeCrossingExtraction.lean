/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.OppositeCrossingFaces
public import DixmierFormal.Weyl.CrossingBaseShape

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Extracting generator monomials from an exact crossing bracket

The constant coefficient of a Poisson bracket is controlled by the two linear
monomials. A face homogeneous in a strict crossing direction cannot contain
the position monomial; if its bracket with a mate face is one, the mate must
contain that position monomial.
-/

namespace Dixmier.Weyl

open Polynomial MvPolynomial

private theorem coeff_sub_local (d : Fin 2 →₀ ℕ) (p q : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.coeff d (p - q) = MvPolynomial.coeff d p - MvPolynomial.coeff d q := by
  simpa only [MvPolynomial.coeffAddMonoidHom_apply] using
    (MvPolynomial.coeffAddMonoidHom d).map_sub p q

private theorem coeff_mul_zero (p q : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.coeff 0 (p * q) = MvPolynomial.coeff 0 p * MvPolynomial.coeff 0 q := by
  rw [MvPolynomial.coeff_mul]
  simp

/-- The constant coefficient of a Poisson bracket is determined by its two
linear-monomial pairs. -/
theorem poisson_coeff_zero (p q : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.coeff 0 (poisson p q) =
      MvPolynomial.coeff (expo 0 1) p * MvPolynomial.coeff (expo 1 0) q -
        MvPolynomial.coeff (expo 1 0) p * MvPolynomial.coeff (expo 0 1) q := by
  unfold poisson
  rw [coeff_sub_local, coeff_mul_zero, coeff_mul_zero]
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv,
    MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv]
  simp [expo]

/-- If the first homogeneous face has degree `-d` in a direction `(ell,-d)`
with `ell>0`, an exact bracket of one forces the mate face to contain the
opposite generator monomial `X`. -/
theorem poisson_eq_one_forces_mate_position_term
    (p q : MvPolynomial (Fin 2) ℂ) (d ell : ℕ) (hell : 0 < ell)
    (hp : p.IsWeightedHomogeneous (wt ell (-(d : ℤ))) (-(d : ℤ)))
    (hbr : poisson p q = 1) : expo 1 0 ∈ q.support := by
  have hpXnot : expo 1 0 ∉ p.support := by
    intro hmem
    have hweight := hp (MvPolynomial.mem_support_iff.mp hmem)
    rw [expo_weight] at hweight
    have hellZ : 0 < (ell : ℤ) := by exact_mod_cast hell
    omega
  have hpXcoeff : MvPolynomial.coeff (expo 1 0) p = 0 := by
    by_contra hne
    exact hpXnot (MvPolynomial.mem_support_iff.mpr hne)
  have hcoeff := congrArg (MvPolynomial.coeff 0) hbr
  rw [poisson_coeff_zero, hpXcoeff] at hcoeff
  have hqcoeff : MvPolynomial.coeff (expo 1 0) q ≠ 0 := by
    intro hzero
    rw [hzero] at hcoeff
    simp at hcoeff
  exact MvPolynomial.mem_support_iff.mpr hqcoeff

/-- In a strict crossing direction, a bracket-one pair has both generator
monomials in its respective faces. -/
theorem poisson_eq_one_forces_opposite_generator_terms
    (p q : MvPolynomial (Fin 2) ℂ) (d ell : ℕ) (hell : 0 < ell)
    (hp : p.IsWeightedHomogeneous (wt ell (-(d : ℤ))) (-(d : ℤ)))
    (hbr : poisson p q = 1) :
    expo 0 1 ∈ p.support ∧ expo 1 0 ∈ q.support := by
  have hpXnot : expo 1 0 ∉ p.support := by
    intro hmem
    have hweight := hp (MvPolynomial.mem_support_iff.mp hmem)
    rw [expo_weight] at hweight
    have hellZ : 0 < (ell : ℤ) := by exact_mod_cast hell
    omega
  have hpXcoeff : MvPolynomial.coeff (expo 1 0) p = 0 := by
    by_contra hne
    exact hpXnot (MvPolynomial.mem_support_iff.mpr hne)
  have hcoeff := congrArg (MvPolynomial.coeff 0) hbr
  rw [poisson_coeff_zero, hpXcoeff] at hcoeff
  have hpYcoeff : MvPolynomial.coeff (expo 0 1) p ≠ 0 := by
    intro hzero
    rw [hzero] at hcoeff
    simp at hcoeff
  have hqcoeff : MvPolynomial.coeff (expo 1 0) q ≠ 0 := by
    intro hzero
    rw [hzero] at hcoeff
    simp at hcoeff
  exact ⟨MvPolynomial.mem_support_iff.mpr hpYcoeff,
    MvPolynomial.mem_support_iff.mpr hqcoeff⟩

/-- For a strict primitive crossing direction, the two homogeneous faces
have normalized base representations beginning at the derivative and
position generators. This extracts the shapes needed by I115. -/
theorem strict_crossing_opposite_generator_face_shapes
    (R F : MvPolynomial (Fin 2) ℂ) (d ell : ℕ)
    (hd : 0 < d) (hde : d < ell) (hc : Nat.Coprime ell d)
    (hR : R.IsWeightedHomogeneous (wt ell (-(d : ℤ))) (-(d : ℤ)))
    (hF : F.IsWeightedHomogeneous (wt ell (-(d : ℤ))) (ell : ℤ))
    (hbr : poisson R F = 1) :
    ∃ (c e : ℂ) (A B : ℂ[X]),
      c ≠ 0 ∧ e ≠ 0 ∧ Polynomial.coeff A 0 = 1 ∧ Polynomial.coeff B 0 = 1 ∧
      R = MvPolynomial.C c * (MvPolynomial.X 1 *
        A.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ d * MvPolynomial.X 1 ^ ell)) ∧
      F = MvPolynomial.C e * (MvPolynomial.X 0 *
        B.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ d * MvPolynomial.X 1 ^ ell)) := by
  obtain ⟨hRbase, hFbase⟩ :=
    poisson_eq_one_forces_opposite_generator_terms R F d ell (by omega) hR hbr
  have hRne : R ≠ 0 := by
    intro hzero
    rw [hzero] at hRbase
    simp at hRbase
  have hFne : F ≠ 0 := by
    intro hzero
    rw [hzero] at hFbase
    simp at hFbase
  obtain ⟨a, b, c, A, hcne, hA0, hRray, hRshape⟩ :=
    crossing_base_normalized_shape R ell d (-(d : ℤ)) hd hde hc hRne hR
  obtain ⟨a', b', e, B, hene, hB0, hFray, hFshape⟩ :=
    crossing_base_normalized_shape F ell d (ell : ℤ) hd hde hc hFne hF
  obtain ⟨t, htexp⟩ := hRray (expo 0 1) hRbase
  have hx : 0 = a + d * t := by
    have h := congrArg (fun z : Fin 2 →₀ ℕ => z 0) htexp
    simpa [expo] using h
  have hy : 1 = b + ell * t := by
    have h := congrArg (fun z : Fin 2 →₀ ℕ => z 1) htexp
    simpa [expo] using h
  have ht : t = 0 := by
    have hdt : d * t = 0 := by omega
    rcases Nat.mul_eq_zero.mp hdt with hd0 | ht0
    · omega
    · exact ht0
  have ha : a = 0 := by simpa [ht] using hx.symm
  have hb : b = 1 := by simpa [ht] using hy.symm
  obtain ⟨t', htexp'⟩ := hFray (expo 1 0) hFbase
  have hx' : 1 = a' + d * t' := by
    have h := congrArg (fun z : Fin 2 →₀ ℕ => z 0) htexp'
    simpa [expo] using h
  have hy' : 0 = b' + ell * t' := by
    have h := congrArg (fun z : Fin 2 →₀ ℕ => z 1) htexp'
    simpa [expo] using h
  have ht' : t' = 0 := by
    have hprod : ell * t' = 0 := by omega
    rcases Nat.mul_eq_zero.mp hprod with hell0 | ht0
    · omega
    · exact ht0
  have ha' : a' = 1 := by simpa [ht'] using hx'.symm
  have hb' : b' = 0 := by simpa [ht'] using hy'.symm
  refine ⟨c, e, A, B, hcne, hene, hA0, hB0, ?_, ?_⟩
  · simpa [ha, hb] using hRshape
  · simpa [ha', hb'] using hFshape

/-- After absorbing the two nonzero normalization scalars into the univariate
factors, I115 applies to the extracted faces. Thus exact bracket one forces
both factors in a strict crossing pair to be constant. -/
theorem strict_crossing_bracket_one_forces_constant_factors
    (R F : MvPolynomial (Fin 2) ℂ) (d ell : ℕ)
    (hd : 0 < d) (hde : d < ell) (hc : Nat.Coprime ell d)
    (hR : R.IsWeightedHomogeneous (wt ell (-(d : ℤ))) (-(d : ℤ)))
    (hF : F.IsWeightedHomogeneous (wt ell (-(d : ℤ))) (ell : ℤ))
    (hbr : poisson R F = 1) :
    ∃ (A B : ℂ[X]),
      A ≠ 0 ∧ B ≠ 0 ∧
      R = MvPolynomial.X 1 *
        A.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ d * MvPolynomial.X 1 ^ ell) ∧
      F = MvPolynomial.X 0 *
        B.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ d * MvPolynomial.X 1 ^ ell) ∧
      A.natDegree = 0 ∧ B.natDegree = 0 := by
  obtain ⟨c, e, A, B, hcne, hene, hA0, hB0, hRshape, hFshape⟩ :=
    strict_crossing_opposite_generator_face_shapes R F d ell hd hde hc hR hF hbr
  have hAne : A ≠ 0 := by
    intro hz
    rw [hz] at hA0
    simp at hA0
  have hBne : B ≠ 0 := by
    intro hz
    rw [hz] at hB0
    simp at hB0
  let A' : ℂ[X] := Polynomial.C c * A
  let B' : ℂ[X] := Polynomial.C e * B
  have hA'ne : A' ≠ 0 := by
    dsimp [A']
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hcne) hAne
  have hB'ne : B' ≠ 0 := by
    dsimp [B']
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hene) hBne
  have hR' : R = MvPolynomial.X 1 *
      A'.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ d * MvPolynomial.X 1 ^ ell) := by
    rw [hRshape]
    simp only [A', Polynomial.eval₂_mul, Polynomial.eval₂_C]
    ring
  have hF' : F = MvPolynomial.X 0 *
      B'.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ d * MvPolynomial.X 1 ^ ell) := by
    rw [hFshape]
    simp only [B', Polynomial.eval₂_mul, Polynomial.eval₂_C]
    ring
  have hbr' := hbr
  rw [hR', hF'] at hbr'
  obtain ⟨hAdeg, hBdeg⟩ :=
    poisson_opposite_crossing_bases_eq_one_forces_degree_zero
      A' B' d ell (by omega) hA'ne hB'ne hbr'
  exact ⟨A', B', hA'ne, hB'ne, hR', hF', hAdeg, hBdeg⟩

/-- The nonmonomial strict-crossing face in Han--Tan case (a.1) cannot have
bracket one with its opposite face. The constant-factor conclusion would
leave the first face supported only at the distinguished generator. -/
theorem strict_crossing_nonmonomial_face_excludes_bracket_one
    (R F : MvPolynomial (Fin 2) ℂ) (d ell : ℕ)
    (hd : 0 < d) (hde : d < ell) (hc : Nat.Coprime ell d)
    (hR : R.IsWeightedHomogeneous (wt ell (-(d : ℤ))) (-(d : ℤ)))
    (hF : F.IsWeightedHomogeneous (wt ell (-(d : ℤ))) (ell : ℤ))
    (hRnonmono : 1 < R.support.card) : poisson R F ≠ 1 := by
  intro hbr
  obtain ⟨A, B, hAne, hBne, hRshape, hFshape, hAdeg, hBdeg⟩ :=
    strict_crossing_bracket_one_forces_constant_factors
      R F d ell hd hde hc hR hF hbr
  have hAconst : A = Polynomial.C (Polynomial.coeff A 0) :=
    eq_C_of_natDegree_eq_zero hAdeg
  have hcoeffAne : Polynomial.coeff A 0 ≠ 0 := by
    intro hz
    apply hAne
    rw [hAconst, hz]
    simp
  have hRsingle : R = MvPolynomial.C (Polynomial.coeff A 0) * MvPolynomial.X 1 := by
    calc
      R = MvPolynomial.X 1 *
          A.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ d * MvPolynomial.X 1 ^ ell) := hRshape
      _ = MvPolynomial.X 1 * MvPolynomial.C (Polynomial.coeff A 0) := by
        rw [hAconst]
        simp
      _ = MvPolynomial.C (Polynomial.coeff A 0) * MvPolynomial.X 1 := by ring
  have hRsupport : R.support = {expo 0 1} := by
    rw [hRsingle, MvPolynomial.C_mul', MvPolynomial.support_smul_eq hcoeffAne,
      MvPolynomial.support_X]
    simp [expo]
  rw [hRsupport] at hRnonmono
  simp at hRnonmono

end Dixmier.Weyl
