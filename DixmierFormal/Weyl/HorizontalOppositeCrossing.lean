/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.OppositeCrossingExtraction
public import DixmierFormal.Weyl.HorizontalNativeShape

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Horizontal boundary of the opposite-crossing case

The primitive horizontal face has degree zero and the mate has degree one.
The scalar-free condition factors the first face through the derivative
variable, reducing bracket one to the opposite-face rigidity theorem.
-/
namespace Dixmier.Weyl
open Polynomial MvPolynomial

private theorem horizontal_scalarfree_face_shape
    (R : MvPolynomial (Fin 2) ℂ)
    (hRne : R ≠ 0) (hRone : R.IsWeightedHomogeneous (wt 1 0) 0)
    (hRscalarFree : MvPolynomial.coeff (expo 0 0) R = 0) :
    ∃ (A' : ℂ[X]), A' ≠ 0 ∧
      R = MvPolynomial.X 1 * A'.eval₂ MvPolynomial.C (MvPolynomial.X 1) := by
  obtain ⟨a, U, hadeg, hUne, hRraw⟩ :=
    horizontal_nonzero_homogeneous_shape R 0 hRne hRone
  have ha : a = 0 := by omega
  have hRrename : R = MvPolynomial.rename Fin.succ U := by
    simpa [ha] using hRraw
  let A : ℂ[X] := MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) U
  have hRpoly : R = A.eval₂ MvPolynomial.C (MvPolynomial.X 1) := by
    rw [hRrename]
    simpa [A] using horizontal_rename_eq_eval U
  have hexpo0 : expo 0 0 = 0 := by
    ext i
    fin_cases i <;> simp [expo]
  have hU0 : MvPolynomial.coeff 0 U = 0 := by
    have h := hRscalarFree
    rw [hRrename, hexpo0] at h
    have hcoeff0 : MvPolynomial.coeff 0 (MvPolynomial.rename Fin.succ U) =
        MvPolynomial.coeff 0 U := by
      simpa using (MvPolynomial.coeff_rename_mapDomain Fin.succ
        (Fin.succ_injective 1) U (0 : Fin 1 →₀ ℕ))
    rw [hcoeff0] at h
    exact h
  have hA0 : A.coeff 0 = 0 := by
    simpa only [A, MvPolynomial.coeff_uniqueAlgEquiv, Finsupp.single_zero] using hU0
  have hXdvd : Polynomial.X ∣ A := by rwa [Polynomial.X_dvd_iff]
  obtain ⟨A', hAdiv⟩ := hXdvd
  have hRbase : R = MvPolynomial.X 1 *
      A'.eval₂ MvPolynomial.C (MvPolynomial.X 1) := by
    calc
      R = A.eval₂ MvPolynomial.C (MvPolynomial.X 1) := hRpoly
      _ = (Polynomial.X * A').eval₂ MvPolynomial.C (MvPolynomial.X 1) := by
        rw [hAdiv]
      _ = MvPolynomial.X 1 * A'.eval₂ MvPolynomial.C (MvPolynomial.X 1) := by simp
  have hA'ne : A' ≠ 0 := by
    intro hz
    rw [hz] at hRbase
    simp at hRbase
    exact hRne hRbase
  exact ⟨A', hA'ne, hRbase⟩

private theorem horizontal_mate_face_shape
    (F : MvPolynomial (Fin 2) ℂ)
    (hFne : F ≠ 0) (hFone : F.IsWeightedHomogeneous (wt 1 0) 1) :
    ∃ (B : ℂ[X]), B ≠ 0 ∧
      F = MvPolynomial.X 0 * B.eval₂ MvPolynomial.C (MvPolynomial.X 1) := by
  obtain ⟨b, V, hbdeg, hVne, hFraw⟩ :=
    horizontal_nonzero_homogeneous_shape F 1 hFne hFone
  have hb : b = 1 := by omega
  have hFrename : F = MvPolynomial.X 0 * MvPolynomial.rename Fin.succ V := by
    simpa [hb] using hFraw
  let B : ℂ[X] := MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) V
  have hFbase : F = MvPolynomial.X 0 *
      B.eval₂ MvPolynomial.C (MvPolynomial.X 1) := by
    rw [hFrename, horizontal_rename_eq_eval V]
  have hBne : B ≠ 0 := by
    intro hz
    rw [hz] at hFbase
    simp at hFbase
    exact hFne hFbase
  exact ⟨B, hBne, hFbase⟩

private theorem horizontal_bracket_one_forces_nonzero
    (R F : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous (wt 1 0) 0)
    (hbr : poisson R F = 1) : R ≠ 0 ∧ F ≠ 0 := by
  obtain ⟨hRgen, hFgen⟩ :=
    poisson_eq_one_forces_opposite_generator_terms R F 0 1 (by norm_num) hR hbr
  constructor
  · intro hz
    rw [hz] at hRgen
    simp at hRgen
  · intro hz
    rw [hz] at hFgen
    simp at hFgen

private theorem horizontal_constant_factor_support
    (R : MvPolynomial (Fin 2) ℂ) (A : ℂ[X])
    (hAne : A ≠ 0)
    (hRbase : R = MvPolynomial.X 1 *
      A.eval₂ MvPolynomial.C (MvPolynomial.X 1))
    (hAdeg : A.natDegree = 0) :
    R.support = {expo 0 1} := by
  have hAconst : A = Polynomial.C (Polynomial.coeff A 0) :=
    eq_C_of_natDegree_eq_zero hAdeg
  have hcoeffAne : Polynomial.coeff A 0 ≠ 0 := by
    intro hz
    apply hAne
    rw [hAconst, hz]
    simp
  have hRsingle : R = MvPolynomial.C (Polynomial.coeff A 0) * MvPolynomial.X 1 := by
    calc
      R = MvPolynomial.X 1 * A.eval₂ MvPolynomial.C (MvPolynomial.X 1) := hRbase
      _ = MvPolynomial.X 1 * MvPolynomial.C (Polynomial.coeff A 0) := by
        rw [hAconst]
        simp
      _ = MvPolynomial.C (Polynomial.coeff A 0) * MvPolynomial.X 1 := by ring
  rw [hRsingle, MvPolynomial.C_mul', MvPolynomial.support_smul_eq hcoeffAne,
    MvPolynomial.support_X]
  simp [expo]

private theorem horizontal_transfer_bracket
    (R F : MvPolynomial (Fin 2) ℂ) (A B : ℂ[X])
    (hRbase : R = MvPolynomial.X 1 *
      A.eval₂ MvPolynomial.C (MvPolynomial.X 1))
    (hFbase : F = MvPolynomial.X 0 *
      B.eval₂ MvPolynomial.C (MvPolynomial.X 1))
    (hbr : poisson R F = 1) :
    poisson (MvPolynomial.X 1 * A.eval₂ MvPolynomial.C (MvPolynomial.X 1))
      (MvPolynomial.X 0 * B.eval₂ MvPolynomial.C (MvPolynomial.X 1)) = 1 := by
  rw [← hRbase, ← hFbase]
  exact hbr

private theorem horizontal_pair_degrees
    (A B : ℂ[X]) (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hbr : poisson
      (MvPolynomial.X 1 * A.eval₂ MvPolynomial.C (MvPolynomial.X 1))
      (MvPolynomial.X 0 * B.eval₂ MvPolynomial.C (MvPolynomial.X 1)) = 1) :
    A.natDegree = 0 ∧ B.natDegree = 0 := by
  have hbr' : poisson
      (MvPolynomial.X 1 * A.eval₂ MvPolynomial.C
        (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 1))
      (MvPolynomial.X 0 * B.eval₂ MvPolynomial.C
        (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 1)) = 1 := by
    simpa only [pow_zero, pow_one, one_mul] using hbr
  exact poisson_opposite_crossing_bases_eq_one_forces_degree_zero
    A B 0 1 (by norm_num) hAne hBne hbr'

/-- In the primitive horizontal boundary, a scalar-free nonmonomial first
face cannot have bracket one with its opposite homogeneous face. -/
theorem horizontal_nonmonomial_face_excludes_bracket_one
    (R F : MvPolynomial (Fin 2) ℂ) (ell : ℕ)
    (_hell : 0 < ell) (hc : Nat.Coprime ell 0)
    (hR : R.IsWeightedHomogeneous (wt ell 0) 0)
    (hF : F.IsWeightedHomogeneous (wt ell 0) (ell : ℤ))
    (hRscalarFree : MvPolynomial.coeff (expo 0 0) R = 0)
    (hRnonmono : 1 < R.support.card) : poisson R F ≠ 1 := by
  have hell1 : ell = 1 := by simpa [Nat.Coprime] using hc
  have hRone : R.IsWeightedHomogeneous (wt 1 0) 0 := by
    simpa [hell1, wt] using hR
  have hFone : F.IsWeightedHomogeneous (wt 1 0) 1 := by
    simpa [hell1, wt] using hF
  intro hbr
  obtain ⟨hRne, hFne⟩ := horizontal_bracket_one_forces_nonzero R F hRone hbr
  obtain ⟨A, hAne, hRbase⟩ := horizontal_scalarfree_face_shape R hRne hRone hRscalarFree
  obtain ⟨B, hBne, hFbase⟩ := horizontal_mate_face_shape F hFne hFone
  have hbrbase := horizontal_transfer_bracket R F A B hRbase hFbase hbr
  obtain ⟨hAdeg, hBdeg⟩ := horizontal_pair_degrees A B hAne hBne hbrbase
  have hRsupport := horizontal_constant_factor_support R A hAne hRbase hAdeg
  rw [hRsupport] at hRnonmono
  simp at hRnonmono

end Dixmier.Weyl
