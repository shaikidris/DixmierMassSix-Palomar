module

public import DixmierFormal.Weyl.RamifiedDiagonalCompanionFullRoot
public import DixmierFormal.Weyl.CornerAdjacentDivisibility

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Index divisibility from an actual pure-power face

A second occupied canonical face order makes the pure-power root nonzero.
Its penultimate coefficient then supplies adjacent actual PBW face orders,
whose equal weights force the primitive direction to divide the index.
-/

namespace Dixmier.Weyl
open Polynomial

theorem ramified_pure_power_face_root_ne_zero
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (P : ramifiedOperatorAlgebra l)
    (c : ℂ) (j : ℕ)
    (hj : j ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support)
    (hne : j ≠ (ramifiedTopFacePolynomial l hl ρ σ P).natDegree)
    (hshape : ramifiedTopFacePolynomial l hl ρ σ P=
      C (ramifiedTopFacePolynomial l hl ρ σ P).leadingCoeff *
        (X-C c)^(ramifiedTopFacePolynomial l hl ρ σ P).natDegree) : c ≠ 0 := by
  intro hc
  have hcoef := Polynomial.mem_support_iff.mp hj
  rw [hshape,hc] at hcoef
  simp [hne] at hcoef

theorem ramified_pure_power_face_rho_dvd_index
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (P : ramifiedOperatorAlgebra l) (c : ℂ) (hc : c ≠ 0)
    (hpositive : 0 < (ramifiedTopFacePolynomial l hl ρ σ P).natDegree)
    (hshape : ramifiedTopFacePolynomial l hl ρ σ P=
      C (ramifiedTopFacePolynomial l hl ρ σ P).leadingCoeff *
        (X-C c)^(ramifiedTopFacePolynomial l hl ρ σ P).natDegree) :
    ρ ∣ (l:ℤ) := by
  let p := ramifiedTopFacePolynomial l hl ρ σ P
  have hp : p ≠ 0 := ne_zero_of_natDegree_gt hpositive
  have hlead : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hnext : p.nextCoeff= -(p.natDegree:ℂ)*c*p.leadingCoeff := by
    change (ramifiedTopFacePolynomial l hl ρ σ P).nextCoeff = _
    conv_lhs => rw [hshape]
    rw [nextCoeff_C_mul,(monic_X_sub_C c).nextCoeff_pow,nextCoeff_X_sub_C]
    simp [nsmul_eq_mul]
    ring
  have hnextne : p.nextCoeff ≠ 0 := by
    rw [hnext]
    exact mul_ne_zero
      (mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpositive))) hc)
      hlead
  have hcoeff : p.coeff (p.natDegree-1) ≠ 0 := by
    rw [← nextCoeff_of_natDegree_pos hpositive]
    exact hnextne
  have hlow := (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P
    (p.natDegree-1)).mp (Polynomial.mem_support_iff.mpr hcoeff)
  have hhigh := (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P
    p.natDegree).mp (Polynomial.natDegree_mem_support_of_nonzero hp)
  apply ramified_adjacent_face_first_coordinate_dvd_index
    l ρ σ (ramifiedPBWTopLaurent l hl P (p.natDegree-1))
      (ramifiedPBWTopLaurent l hl P p.natDegree) (p.natDegree-1) hdir
  have hpdegree : 0 < p.natDegree := hpositive
  have hsucc : p.natDegree-1+1=p.natDegree := by omega
  rw [hsucc]
  exact hlow.2.trans hhigh.2.symm

end Dixmier.Weyl
