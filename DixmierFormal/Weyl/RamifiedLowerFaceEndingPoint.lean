module

public import DixmierFormal.Weyl.RamifiedNormalizedCornerGeometry

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # The preserved point is the ending point of the strictly lower face

The old support bound and strict direction decrease bound every new-face
derivative order by the preserved point's order. This identifies its
minimum grade and its actual canonical face degree.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

theorem ramified_strict_lower_face_order_le_preserved_point
    (l : ℕ) (hl : 0 < l) (ρ σ r s : ℤ) (hr : 0 < r)
    (hstrict : ρ*s < r*σ) (E p : ℤ × ℕ)
    (hold : ramifiedWeight l ρ σ p ≤ ramifiedWeight l ρ σ E)
    (htie : ramifiedWeight l r s p=ramifiedWeight l r s E) :
    p.2 ≤ E.2 := by
  have hid : r*(ramifiedWeight l ρ σ p-ramifiedWeight l ρ σ E)=
      (l:ℤ)*(r*σ-ρ*s)*((p.2:ℤ)-(E.2:ℤ)) := by
    unfold ramifiedWeight at htie ⊢
    linear_combination ρ*htie
  have hfactor : (0:ℤ) < (l:ℤ)*(r*σ-ρ*s) :=
    mul_pos (by exact_mod_cast hl) (sub_pos.mpr hstrict)
  have hprod : r*(ramifiedWeight l ρ σ p-ramifiedWeight l ρ σ E) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hr) (sub_nonpos.mpr hold)
  rw [hid] at hprod
  have horder : (p.2:ℤ) ≤ (E.2:ℤ) := by nlinarith only [hfactor,hprod]
  exact_mod_cast horder

theorem ramified_strict_lower_face_preserved_point_min_grade
    (l : ℕ) (hl : 0 < l) (ρ σ r s : ℤ) (hr : 0 < r) (hsum : 0 < r+s)
    (hstrict : ρ*s < r*σ) (E p : ℤ × ℕ)
    (hold : ramifiedWeight l ρ σ p ≤ ramifiedWeight l ρ σ E)
    (htie : ramifiedWeight l r s p=ramifiedWeight l r s E) :
    E.1-(l:ℤ)*(E.2:ℤ) ≤ p.1-(l:ℤ)*(p.2:ℤ) := by
  exact ramified_face_grade_min_of_order_max l hl r s hr hsum E p htie
    (ramified_strict_lower_face_order_le_preserved_point
      l hl ρ σ r s hr hstrict E p hold htie)

theorem ramified_strict_lower_face_canonical_degree_at_preserved_point
    (l : ℕ) (hl : 0 < l) (ρ σ r s : ℤ) (hr : 0 < r)
    (hstrict : ρ*s < r*σ) (P : ramifiedOperatorAlgebra l) (E : ℤ × ℕ)
    (hE : E ∈ ramifiedPBWSupport l hl P)
    (htop : ramifiedWeight l r s E=ramifiedWeightDeg l hl r s P)
    (hold : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p ≤ ramifiedWeight l ρ σ E) :
    (ramifiedTopFacePolynomial l hl r s P).natDegree=E.2 ∧
      ramifiedPBWTopLaurent l hl P E.2=E.1 := by
  have hu : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l r s p ≤ ramifiedWeightDeg l hl r s P := by
    intro p hp
    exact ramifiedWeight_le_weightDeg_of_mem l hl r s P p hp
  obtain ⟨horder,hcoord,hEtop⟩ :=
    ramified_face_point_topLaurent_at_order l hl r s hr P E hE htop hu
  refine ⟨ramifiedTopFacePolynomial_natDegree_of_endpoint
    l hl r s P E.2 horder hEtop ?_,hcoord⟩
  intro j hj hweight
  have hmem : (ramifiedPBWTopLaurent l hl P j,j) ∈ ramifiedPBWSupport l hl P := by
    apply (ramifiedPBWSupport_mem_iff l hl P _ _).mpr
    exact Finsupp.mem_support_iff.mp (ramifiedPBWTopLaurent_mem l hl P j hj)
  exact ramified_strict_lower_face_order_le_preserved_point l hl ρ σ r s hr hstrict
    E (ramifiedPBWTopLaurent l hl P j,j) (hold _ hmem) (hweight.trans htop.symm)

theorem ramified_normalized_corner_new_face_weight_ratio
    (l d n h : ℕ) (r s : ℤ) (P Q : ramifiedOperatorAlgebra l) (hl : 0 < l)
    (hPtop : ramifiedWeight l r s ((d:ℤ)*((l:ℤ)*(h:ℤ)-1),d*h)=
      ramifiedWeightDeg l hl r s P)
    (hQtop : ramifiedWeight l r s ((n:ℤ)*((l:ℤ)*(h:ℤ)-1),n*h)=
      ramifiedWeightDeg l hl r s Q) :
    ramifiedWeightDeg l hl r s Q*(d:ℤ)=
      ramifiedWeightDeg l hl r s P*(n:ℤ) := by
  rw [← hPtop,← hQtop]
  simp only [ramifiedWeight,Prod.fst,Prod.snd,Nat.cast_mul]
  ring

end Dixmier.Weyl
