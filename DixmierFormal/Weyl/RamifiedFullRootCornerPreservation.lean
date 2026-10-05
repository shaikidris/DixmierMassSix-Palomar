module

public import DixmierFormal.Weyl.RamifiedDiagonalCompanionAdmissibility
public import DixmierFormal.Weyl.RamifiedCornerGradeBarrier

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # A full-degree root preserves the old ending point under the exact cut

The root-selected minimum-order point on the sheared old face is exactly
the canonical maximum-order point of the original face when the chosen
root consumes its full degree. This uses the actual ramified shear.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 800000

theorem ramified_full_degree_root_cut_preserves_canonical_endpoint
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (hdiv : ρ ∣ (l:ℤ)) (hsum : 0 < ρ+σ)
    (P : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (c : ℂ)
    (hmult : (ramifiedTopFacePolynomial l hl ρ σ P).rootMultiplicity c=
      (ramifiedTopFacePolynomial l hl ρ σ P).natDegree) :
    let N := (ramifiedTopFacePolynomial l hl ρ σ P).natDegree
    let i := ramifiedPBWTopLaurent l hl P N
    (i,N) ∈ ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c P) ∧
    ramifiedWeight l ρ σ (i,N)=ramifiedWeightDeg l hl ρ σ P ∧
    ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c P) →
      ramifiedWeight l ρ σ (u,n)=ramifiedWeightDeg l hl ρ σ P → N ≤ n := by
  dsimp only
  let N := (ramifiedTopFacePolynomial l hl ρ σ P).natDegree
  let i := ramifiedPBWTopLaurent l hl P N
  let k := ramifiedCutExponent l ρ σ
  let r := i+k*(N:ℤ)
  have hpface := ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ P hP
  have hend := (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P N).mp
    (Polynomial.natDegree_mem_support_of_nonzero hpface)
  have hmem : (i,N) ∈ ramifiedPBWSupport l hl P := by
    apply (ramifiedPBWSupport_mem_iff l hl P i N).mpr
    exact Finsupp.mem_support_iff.mp (ramifiedPBWTopLaurent_mem l hl P N hend.1)
  have hwend : ramifiedWeight l ρ σ (i,N)=ramifiedWeightDeg l hl ρ σ P := hend.2
  have hk := ramifiedCutExponent_weight l ρ σ hdiv
  have hw : ramifiedWeightDeg l hl ρ σ P=ρ*r := by
    dsimp [ramifiedWeight,r,k] at *
    nlinarith [congrArg (fun z : ℤ => z*(N:ℤ)) hk]
  have hupper : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p ≤ ramifiedWeightDeg l hl ρ σ P := by
    intro p hp
    exact ramifiedWeight_le_weightDeg_of_mem l hl ρ σ P p hp
  have hpol := ramifiedTopFacePolynomial_eq_cutFace
    l hl ρ σ hρ hdiv P r hw hupper
  have hm : (ramifiedFacePolynomial l hl P r k).rootMultiplicity c=N := by
    rw [← hpol]
    exact hmult
  have hstart := ramifiedCutAut_root_start_on_old_face l hl ρ σ r i N
    hρ hdiv hsum c P hmem (hwend.trans hw)
    (by intro u n hp; exact (hupper (u,n) hp).trans_eq hw)
  dsimp only at hstart
  change ((r-k*((ramifiedFacePolynomial l hl P r k).rootMultiplicity c:ℤ),
      (ramifiedFacePolynomial l hl P r k).rootMultiplicity c) ∈ _ ∧ _) ∧ _ at hstart
  rw [hm] at hstart
  have hi : r-k*(N:ℤ)=i := by dsimp [r]; ring
  rw [hi] at hstart
  exact ⟨hstart.1.1,hwend,by intro u n hp ht; exact hstart.2 u n hp (ht.trans hw)⟩

end Dixmier.Weyl
