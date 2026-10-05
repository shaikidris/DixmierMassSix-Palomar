module

public import DixmierFormal.Weyl.RamifiedCanonicalEndProportion

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Geometry of the normalized corner and its mate

The endpoints d*(lh-1,h) and n*(lh-1,h) have negative grades,
orders at least two and parallel rays when d,n,h are at least two.
These are the numerical hypotheses consumed by the full-root successor.
-/

namespace Dixmier.Weyl

theorem ramified_normalized_corner_pair_geometry
    (l d n h : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n) (hh : 2 ≤ h)
    (E F : ℤ × ℕ)
    (hE : E=((d:ℤ)*((l:ℤ)*(h:ℤ)-1),d*h))
    (hF : F=((n:ℤ)*((l:ℤ)*(h:ℤ)-1),n*h)) :
    E.1-(l:ℤ)*(E.2:ℤ)<0 ∧ F.1-(l:ℤ)*(F.2:ℤ)<0 ∧
    2 ≤ E.2 ∧ 2 ≤ F.2 ∧ (E.2:ℤ)*F.1=(F.2:ℤ)*E.1 := by
  subst E
  subst F
  simp only [Prod.fst,Prod.snd,Nat.cast_mul]
  have hdZ : (0:ℤ) < (d:ℤ) := by omega
  have hnZ : (0:ℤ) < (n:ℤ) := by omega
  have hegrade : (d:ℤ)*((l:ℤ)*(h:ℤ)-1)-(l:ℤ)*((d:ℤ)*(h:ℤ))=-(d:ℤ) := by ring
  have hfgrade : (n:ℤ)*((l:ℤ)*(h:ℤ)-1)-(l:ℤ)*((n:ℤ)*(h:ℤ))=-(n:ℤ) := by ring
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hegrade]; omega
  · rw [hfgrade]; omega
  · nlinarith
  · nlinarith
  · ring

theorem ramified_normalized_corner_full_root_cut_lower_face
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
  obtain ⟨hEg,hFg,hEo,hFo,hpar⟩ :=
    ramified_normalized_corner_pair_geometry l d n h hd hn hh E F hcorner hFcorner
  exact ramified_full_root_cut_exists_strict_lower_common_face
    l hl ρ σ hρ hdiv hsum P Q hP hQ hcomm c hrootP hrootQ
    E F hE hF hEg hFg hEo hFo hpar

end Dixmier.Weyl
