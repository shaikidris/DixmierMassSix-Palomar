module

public import DixmierFormal.Weyl.RamifiedCutWeightPreservation
public import DixmierFormal.Weyl.RamifiedCommonAdjacentDirection
public import DixmierFormal.Weyl.RamifiedCommonIntegralFace

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # A common early adjacent slope after the full-root cut

The exact cut transports the commutator, preserves both old weights,
and turns both canonical ending points into old-face starting points.
Parallel negative-grade endpoints of order at least two therefore have
a common early adjacent slope after the cut.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

theorem ramified_full_root_cut_exists_common_early_slope
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
    ∃ t : ℚ, 0 < t ∧ t < (l:ℚ)*((ρ+σ:ℤ):ℚ) ∧
      (∀ p ∈ ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c P),
        (ramifiedWeight l ρ σ p:ℚ)-t*(p.2:ℚ) ≤
          (ramifiedWeightDeg l hl ρ σ P:ℚ)-t*(E.2:ℚ)) ∧
      (∀ q ∈ ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c Q),
        (ramifiedWeight l ρ σ q:ℚ)-t*(q.2:ℚ) ≤
          (ramifiedWeightDeg l hl ρ σ Q:ℚ)-t*(F.2:ℚ)) ∧
      (∃ BP ∈ ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c P),
        BP.2<E.2 ∧ (ramifiedWeight l ρ σ BP:ℚ)-t*(BP.2:ℚ)=
          (ramifiedWeightDeg l hl ρ σ P:ℚ)-t*(E.2:ℚ)) ∧
      (∃ BQ ∈ ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c Q),
        BQ.2<F.2 ∧ (ramifiedWeight l ρ σ BQ:ℚ)-t*(BQ.2:ℚ)=
          (ramifiedWeightDeg l hl ρ σ Q:ℚ)-t*(F.2:ℚ)) := by
  have hPs := ramified_full_degree_root_cut_preserves_canonical_endpoint
    l hl ρ σ hρ hdiv hsum P hP c hrootP
  have hQs := ramified_full_degree_root_cut_preserves_canonical_endpoint
    l hl ρ σ hρ hdiv hsum Q hQ c hrootQ
  dsimp only at hPs hQs
  rw [← hE] at hPs
  rw [← hF] at hQs
  have hPc := ramifiedCutAut_weightDeg_eq l hl ρ σ hρ hdiv hsum c P hP
  have hQc := ramifiedCutAut_weightDeg_eq l hl ρ σ hρ hdiv hsum c Q hQ
  have hcutcomm := ramifiedCutAut_exact_pair l hl ρ σ c P Q hcomm
  exact ramified_exact_pair_exists_common_early_adjacent_face
    l hl ρ σ hρ hsum (ramifiedCutAut l hl ρ σ c P)
    (ramifiedCutAut l hl ρ σ c Q) hcutcomm
    (ramifiedWeightDeg l hl ρ σ P) (ramifiedWeightDeg l hl ρ σ Q) E F
    hPs.1 hQs.1 hPs.2.1 hQs.2.1 hEgrade hFgrade hEorder hForder hparallel
    (by intro p hp; exact
      (ramifiedWeight_le_weightDeg_of_mem l hl ρ σ _ p hp).trans_eq hPc)
    (by intro q hq; exact
      (ramifiedWeight_le_weightDeg_of_mem l hl ρ σ _ q hq).trans_eq hQc)
    (by intro p hp ht; simpa only [hE,Prod.snd] using hPs.2.2 p.1 p.2 hp ht)
    (by intro q hq ht; simpa only [hF,Prod.snd] using hQs.2.2 q.1 q.2 hq ht)

theorem ramified_full_root_cut_exists_primitive_common_face
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
    ∃ r s : ℤ, IsDirection r s ∧ 0 < r ∧
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
  obtain ⟨t,_,hearly,hPfirst,hQfirst,⟨BP,hBP,hBPlow,hBPtie⟩,
      ⟨BQ,hBQ,hBQlow,hBQtie⟩⟩ :=
    ramified_full_root_cut_exists_common_early_slope
      l hl ρ σ hρ hdiv hsum P Q hP hQ hcomm c hrootP hrootQ
      E F hE hF hEgrade hFgrade hEorder hForder hparallel
  have hPs := ramified_full_degree_root_cut_preserves_canonical_endpoint
    l hl ρ σ hρ hdiv hsum P hP c hrootP
  have hQs := ramified_full_degree_root_cut_preserves_canonical_endpoint
    l hl ρ σ hρ hdiv hsum Q hQ c hrootQ
  dsimp only at hPs hQs
  rw [← hE] at hPs
  rw [← hF] at hQs
  obtain ⟨r,s,hdir,hr,hEtop,hFtop,hBPtop,hBQtop⟩ :=
    ramified_common_rational_tilt_primitive_face
      l hl ρ σ hρ (ramifiedCutAut l hl ρ σ c P)
      (ramifiedCutAut l hl ρ σ c Q)
      (ramifiedWeightDeg l hl ρ σ P) (ramifiedWeightDeg l hl ρ σ Q)
      E F BP BQ t hearly hPs.1 hQs.1 hBP hBQ hPs.2.1 hQs.2.1
      hPfirst hQfirst hBPtie hBQtie
  exact ⟨r,s,hdir,hr,hEtop,hFtop,⟨BP,hBP,hBPlow,hBPtop⟩,
    ⟨BQ,hBQ,hBQlow,hBQtop⟩⟩

end Dixmier.Weyl
