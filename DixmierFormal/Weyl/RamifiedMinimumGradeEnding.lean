module

public import DixmierFormal.Weyl.RamifiedLowerFaceEndingPoint

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Minimum-grade top points are actual canonical ending points

In a positive-sum direction with positive horizontal coefficient, grade
increases as derivative order decreases along a supporting line.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

theorem ramified_min_grade_top_canonical_ending
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P : ramifiedOperatorAlgebra l) (E : ℤ × ℕ)
    (hE : E ∈ ramifiedPBWSupport l hl P)
    (hEtop : ramifiedWeight l ρ σ E=ramifiedWeightDeg l hl ρ σ P)
    (hmin : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p=ramifiedWeightDeg l hl ρ σ P →
      E.1-(l:ℤ)*(E.2:ℤ) ≤ p.1-(l:ℤ)*(p.2:ℤ)) :
    (ramifiedTopFacePolynomial l hl ρ σ P).natDegree=E.2 ∧
      ramifiedPBWTopLaurent l hl P E.2=E.1 := by
  have hu : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p ≤ ramifiedWeightDeg l hl ρ σ P := by
    intro p hp; exact ramifiedWeight_le_weightDeg_of_mem l hl ρ σ P p hp
  obtain ⟨hord,hcoord,hweight⟩ := ramified_face_point_topLaurent_at_order
    l hl ρ σ hρ P E hE hEtop hu
  refine ⟨ramifiedTopFacePolynomial_natDegree_of_endpoint l hl ρ σ P E.2 hord hweight ?_,hcoord⟩
  intro j hj hjtop
  let p : ℤ × ℕ := (ramifiedPBWTopLaurent l hl P j,j)
  have hp : p ∈ ramifiedPBWSupport l hl P := ramifiedPBWTopLaurent_support l hl P j hj
  have hptop : ramifiedWeight l ρ σ p=ramifiedWeightDeg l hl ρ σ P := hjtop
  have hgrade := hmin p hp hptop
  have hface := hptop.trans hEtop.symm
  have hid : (l:ℤ)*(ρ+σ)*((E.2:ℤ)-(p.2:ℤ))=
      ρ*((p.1-(l:ℤ)*(p.2:ℤ))-(E.1-(l:ℤ)*(E.2:ℤ))) := by
    unfold ramifiedWeight at hface
    nlinarith only [hface]
  have hnonneg := mul_nonneg (le_of_lt hρ) (sub_nonneg.mpr hgrade)
  rw [← hid] at hnonneg
  have hfactor : 0 < (l:ℤ)*(ρ+σ) := mul_pos (by exact_mod_cast hl) hsum
  have hle : (p.2:ℤ) ≤ (E.2:ℤ) := by nlinarith only [hnonneg,hfactor]
  exact_mod_cast hle

end Dixmier.Weyl
