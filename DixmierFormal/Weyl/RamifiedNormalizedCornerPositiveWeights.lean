module

public import DixmierFormal.Weyl.RamifiedLowerFaceEndingPoint
public import DixmierFormal.Weyl.RamifiedCommonFaceRatio

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Positive successor weights from the retained normalized corners

The exact commutator bounds the sum of top weights below by the positive
first-contraction step. Parallel normalized top corners then force both
weights positive and preserve the original ratio integers.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

theorem ramified_exact_pair_normalized_top_corners_positive_ratio
    (l : ℕ) (hl : 0 < l) (r s : ℤ) (hr : 0 < r) (hsum : 0 < r+s)
    (P Q : ramifiedOperatorAlgebra l) (hcomm : Q*P-P*Q=1)
    (d n h : ℕ) (hd : 0 < d) (hn : 0 < n) (hh : 0 < h)
    (hPtop : ramifiedWeight l r s ((d:ℤ)*((l:ℤ)*(h:ℤ)-1),d*h)=
      ramifiedWeightDeg l hl r s P)
    (hQtop : ramifiedWeight l r s ((n:ℤ)*((l:ℤ)*(h:ℤ)-1),n*h)=
      ramifiedWeightDeg l hl r s Q) :
    0 < ramifiedWeightDeg l hl r s P ∧
    0 < ramifiedWeightDeg l hl r s Q ∧
    ramifiedWeightDeg l hl r s Q*(d:ℤ)=
      ramifiedWeightDeg l hl r s P*(n:ℤ) := by
  apply ramified_exact_pair_parallel_top_weights_positive_ratio
    l hl r s hr hsum P Q hcomm
    ((d:ℤ)*((l:ℤ)*(h:ℤ)-1),d*h)
    ((n:ℤ)*((l:ℤ)*(h:ℤ)-1),n*h)
    (by exact Nat.mul_pos hd hh) _ hPtop hQtop d n hd hn
  · simp only [Prod.fst,Prod.snd,Nat.cast_mul]
    ring
  · simp only [Prod.snd,Nat.cast_mul]
    ring

theorem ramified_normalized_corner_full_root_cut_positive_lower_face
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
    (n d h : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n) (hh : 2 ≤ h)
    (hA : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hD : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hthreshold : 0 < ramifiedWeightDeg l hl ρ σ P+
      ramifiedWeightDeg l hl ρ σ Q-(l:ℤ)*(ρ+σ))
    (hratio : ramifiedWeightDeg l hl ρ σ Q*(d:ℤ)=
      ramifiedWeightDeg l hl ρ σ P*(n:ℤ))
    (hcorner : E=((d:ℤ)*((l:ℤ)*(h:ℤ)-1),d*h)) :
    ∃ r s : ℤ, IsDirection r s ∧ 0 < r ∧ ρ*s < r*σ ∧
      0 < ramifiedWeightDeg l hl r s (ramifiedCutAut l hl ρ σ c P) ∧
      0 < ramifiedWeightDeg l hl r s (ramifiedCutAut l hl ρ σ c Q) ∧
      ramifiedWeightDeg l hl r s (ramifiedCutAut l hl ρ σ c Q)*(d:ℤ)=
        ramifiedWeightDeg l hl r s (ramifiedCutAut l hl ρ σ c P)*(n:ℤ) ∧
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
  obtain ⟨r,s,hdir,hr,hstrict,hEtop,hFtop,hBP,hBQ⟩ :=
    ramified_normalized_corner_full_root_cut_lower_face
      l hl ρ σ hρ hdiv hsum P Q hP hQ hcomm c hrootP hrootQ
      E F hE hF n d h hd hn hh hA hD hthreshold hratio hcorner
  have hprop := ramified_exact_pair_canonical_ends_proportional
    l hl ρ σ hρ hsum P Q hP hQ hcomm hA hD hthreshold n d hratio
  have hx : (n:ℤ)*E.1=(d:ℤ)*F.1 := by
    simpa only [hE,hF,Prod.fst] using hprop.1
  have hy : n*E.2=d*F.2 := by
    simpa only [hE,hF,Prod.snd] using hprop.2
  have hmate := ramified_normalized_corner_proportion_mate_coordinates
    l d n h (by omega) E.1 F.1 E.2 F.2 hx hy
    (by rw [hcorner]) (by rw [hcorner])
  have hFcorner : F=((n:ℤ)*((l:ℤ)*(h:ℤ)-1),n*h) :=
    Prod.ext hmate.1 hmate.2
  have hpos := ramified_exact_pair_normalized_top_corners_positive_ratio
    l hl r s hr hdir.2 (ramifiedCutAut l hl ρ σ c P)
    (ramifiedCutAut l hl ρ σ c Q)
    (ramifiedCutAut_exact_pair l hl ρ σ c P Q hcomm)
    d n h (by omega) (by omega) (by omega)
    (by simpa only [hcorner] using hEtop)
    (by simpa only [hFcorner] using hFtop)
  exact ⟨r,s,hdir,hr,hstrict,hpos.1,hpos.2.1,hpos.2.2,hEtop,hFtop,hBP,hBQ⟩

end Dixmier.Weyl
