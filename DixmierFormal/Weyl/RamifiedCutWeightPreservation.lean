module

public import DixmierFormal.Weyl.RamifiedMateFullRootAlignment
public import DixmierFormal.Weyl.RamifiedShearTopFace

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Exact cut preserves every nonzero operator's old face weight

The canonical endpoint supplies an integral affine face index once the
primitive direction divides the coefficient index. Thus the exact shear
weight theorem applies without an assumed weight quotient.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 800000

theorem ramifiedCutAut_weightDeg_eq
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (hdiv : ρ ∣ (l:ℤ)) (hsum : 0 < ρ+σ)
    (c : ℂ) (P : ramifiedOperatorAlgebra l) (hP : P ≠ 0) :
    ramifiedWeightDeg l hl ρ σ (ramifiedCutAut l hl ρ σ c P)=
      ramifiedWeightDeg l hl ρ σ P := by
  let N := (ramifiedTopFacePolynomial l hl ρ σ P).natDegree
  let i := ramifiedPBWTopLaurent l hl P N
  let k := ramifiedCutExponent l ρ σ
  let r := i+k*(N:ℤ)
  have hpface := ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ P hP
  have hend := (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P N).mp
    (Polynomial.natDegree_mem_support_of_nonzero hpface)
  have hk := ramifiedCutExponent_weight l ρ σ hdiv
  have hw : ramifiedWeightDeg l hl ρ σ P=ρ*r := by
    dsimp [r,k,i] at *
    nlinarith [congrArg (fun z : ℤ => z*(N:ℤ)) hk]
  exact (ramifiedCutAut_topFace_eq_translate_of_weight
    l hl ρ σ r hρ hdiv hsum c P hP hw).1.trans hw.symm

end Dixmier.Weyl
