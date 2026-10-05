module

public import DixmierFormal.Weyl.RamifiedFullRootCutCommonSlope

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Strict decrease from an actual lower-order tying point

A point below the old face's minimum derivative order has strictly
smaller old weight. If it ties the preserved endpoint in a new direction
with positive horizontal coordinate, the new slope is strictly smaller.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

theorem ramified_lower_order_tie_direction_strict_decrease
    (l : ℕ) (hl : 0 < l) (ρ σ r s : ℤ) (hr : 0 < r)
    (E B : ℤ × ℕ) (horder : B.2 < E.2)
    (hold : ramifiedWeight l ρ σ B < ramifiedWeight l ρ σ E)
    (hnew : ramifiedWeight l r s B = ramifiedWeight l r s E) :
    ρ*s < r*σ := by
  have hid : r*(ramifiedWeight l ρ σ E-ramifiedWeight l ρ σ B)=
      (l:ℤ)*((E.2:ℤ)-(B.2:ℤ))*(r*σ-ρ*s) := by
    unfold ramifiedWeight at hnew ⊢
    linear_combination -ρ*hnew
  have hdelta : (0:ℤ) < (E.2:ℤ)-(B.2:ℤ) := by omega
  have hfactor : (0:ℤ) < (l:ℤ)*((E.2:ℤ)-(B.2:ℤ)) :=
    mul_pos (by exact_mod_cast hl) hdelta
  have hprod : 0 < r*(ramifiedWeight l ρ σ E-ramifiedWeight l ρ σ B) :=
    mul_pos hr (sub_pos.mpr hold)
  rw [hid] at hprod
  have hpositive : 0 < r*σ-ρ*s := by nlinarith only [hfactor,hprod]
  linarith

theorem ramified_old_face_min_order_new_tie_strict_decrease
    (l : ℕ) (hl : 0 < l) (ρ σ r s : ℤ) (hr : 0 < r)
    (P : ramifiedOperatorAlgebra l) (E B : ℤ × ℕ)
    (hB : B ∈ ramifiedPBWSupport l hl P)
    (htop : ramifiedWeight l ρ σ E=ramifiedWeightDeg l hl ρ σ P)
    (hstart : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p=ramifiedWeightDeg l hl ρ σ P → E.2 ≤ p.2)
    (horder : B.2 < E.2)
    (hnew : ramifiedWeight l r s B=ramifiedWeight l r s E) :
    ρ*s < r*σ := by
  have hle := ramifiedWeight_le_weightDeg_of_mem l hl ρ σ P B hB
  have hlt : ramifiedWeight l ρ σ B < ramifiedWeightDeg l hl ρ σ P := by
    apply lt_of_le_of_ne hle
    intro heq
    have hmin := hstart B hB heq
    omega
  exact ramified_lower_order_tie_direction_strict_decrease
    l hl ρ σ r s hr E B horder (hlt.trans_eq htop.symm) hnew

theorem ramified_full_root_cut_exists_strict_lower_common_face
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (hdiv : ρ ∣ (l:ℤ)) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hcomm : Q*P-P*Q=1) (c : ℂ)
    (hrootP : (ramifiedTopFacePolynomial l hl ρ σ P).rootMultiplicity c=
      (ramifiedTopFacePolynomial l hl ρ σ P).natDegree)
    (hrootQ : (ramifiedTopFacePolynomial l hl ρ σ Q).rootMultiplicity c=
      (ramifiedTopFacePolynomial l hl ρ σ Q).natDegree)
    (E F : ℤ × ℕ)
    (hE : E=(ramifiedPBWTopLaurent l hl P
      (ramifiedTopFacePolynomial l hl ρ σ P).natDegree,
      (ramifiedTopFacePolynomial l hl ρ σ P).natDegree))
    (hF : F=(ramifiedPBWTopLaurent l hl Q
      (ramifiedTopFacePolynomial l hl ρ σ Q).natDegree,
      (ramifiedTopFacePolynomial l hl ρ σ Q).natDegree))
    (hEgrade : E.1-(l:ℤ)*(E.2:ℤ)<0)
    (hFgrade : F.1-(l:ℤ)*(F.2:ℤ)<0)
    (hEorder : 2 ≤ E.2) (hForder : 2 ≤ F.2)
    (hparallel : (E.2:ℤ)*F.1=(F.2:ℤ)*E.1) :
    ∃ r s : ℤ, IsDirection r s ∧ 0 < r ∧ ρ*s < r*σ ∧
      ramifiedWeight l r s E=
        ramifiedWeightDeg l hl r s (ramifiedCutAut l hl ρ σ c P) ∧
      ramifiedWeight l r s F=
        ramifiedWeightDeg l hl r s (ramifiedCutAut l hl ρ σ c Q) ∧
      (∃ BP ∈ ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c P),
        BP.2<E.2 ∧ ramifiedWeight l r s BP=
          ramifiedWeightDeg l hl r s (ramifiedCutAut l hl ρ σ c P)) ∧
      (∃ BQ ∈ ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c Q),
        BQ.2<F.2 ∧ ramifiedWeight l r s BQ=
          ramifiedWeightDeg l hl r s (ramifiedCutAut l hl ρ σ c Q)) := by
  obtain ⟨r,s,hdir,hr,hEtop,hFtop,⟨BP,hBP,hBPlow,hBPtop⟩,hBQ⟩ :=
    ramified_full_root_cut_exists_primitive_common_face
      l hl ρ σ hρ hdiv hsum P Q hP hQ hcomm c hrootP hrootQ
      E F hE hF hEgrade hFgrade hEorder hForder hparallel
  have hPs := ramified_full_degree_root_cut_preserves_canonical_endpoint
    l hl ρ σ hρ hdiv hsum P hP c hrootP
  dsimp only at hPs
  rw [← hE] at hPs
  have hPc := ramifiedCutAut_weightDeg_eq l hl ρ σ hρ hdiv hsum c P hP
  have hstart : ∀ p ∈ ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c P),
      ramifiedWeight l ρ σ p=
        ramifiedWeightDeg l hl ρ σ (ramifiedCutAut l hl ρ σ c P) → E.2 ≤ p.2 := by
    intro p hp ht
    rw [hPc] at ht
    simpa only [hE,Prod.snd] using hPs.2.2 p.1 p.2 hp ht
  have hstrict := ramified_old_face_min_order_new_tie_strict_decrease
    l hl ρ σ r s hr (ramifiedCutAut l hl ρ σ c P) E BP hBP
    (hPs.2.1.trans hPc.symm) hstart hBPlow (hBPtop.trans hEtop.symm)
  exact ⟨r,s,hdir,hr,hstrict,hEtop,hFtop,⟨BP,hBP,hBPlow,hBPtop⟩,hBQ⟩

end Dixmier.Weyl
