module

public import DixmierFormal.Weyl.RamifiedDiagonalCutCertificate

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Lower normalized-corner successor from an actual diagonal companion

The exact companion certificate supplies the admissible full-root cut. The
successor has a strictly lower primitive common direction, positive weights,
and the retained normalized corner and ratio. Next-cut admissibility is a
separate condition.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

theorem ramified_diagonal_companion_normalized_corner_lower_successor
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (hdir : IsDirection ρ σ)
    (P Q G : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0) (hG : G ≠ 0)
    (hcomm : Q*P-P*Q=1)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P*G-G*P)=ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P*G-G*P)=
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hGweight : ramifiedWeightDeg l hl ρ σ G=(l:ℤ)*(ρ+σ))
    (hlinear : (ramifiedTopFacePolynomial l hl ρ σ (-G)).natDegree=1)
    (hPdegree : 2 ≤ (ramifiedTopFacePolynomial l hl ρ σ P).natDegree)
    (j : ℕ) (hj : j ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support)
    (hne : j ≠ (ramifiedTopFacePolynomial l hl ρ σ P).natDegree)
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
    (hratio : ramifiedWeightDeg l hl ρ σ Q*(d:ℤ)=
      ramifiedWeightDeg l hl ρ σ P*(n:ℤ))
    (hcorner : E=((d:ℤ)*((l:ℤ)*(h:ℤ)-1),d*h)) :
    ∃ c : ℂ, c ≠ 0 ∧ ρ ∣ (l:ℤ) ∧ ∃ r s : ℤ, IsDirection r s ∧ 0 < r ∧ ρ*s < r*σ ∧
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
          ramifiedWeightDeg l hl r s (ramifiedCutAut l hl ρ σ c Q)) ∧
      ((ramifiedTopFacePolynomial l hl r s (ramifiedCutAut l hl ρ σ c P)).natDegree=E.2 ∧
        ramifiedPBWTopLaurent l hl (ramifiedCutAut l hl ρ σ c P) E.2=E.1) ∧
      ((ramifiedTopFacePolynomial l hl r s (ramifiedCutAut l hl ρ σ c Q)).natDegree=F.2 ∧
        ramifiedPBWTopLaurent l hl (ramifiedCutAut l hl ρ σ c Q) F.2=F.1) := by
  obtain ⟨hdiv,ht,c,hc,_,hrootP,hrootQ⟩ :=
    ramified_diagonal_companion_exact_pair_cut_certificate
      l hl ρ σ hρ hdir P Q G hP hQ hG hcomm hA hD
      hdegree hface hGweight hlinear hPdegree j hj hne
  obtain ⟨r,s,hrs,hr,hstrict,hposP,hposQ,hrat,hEtop,hFtop,hBP,hBQ⟩ :=
    ramified_normalized_corner_full_root_cut_positive_lower_face
      l hl ρ σ hρ hdiv hdir.2 P Q hP hQ hcomm c hrootP hrootQ
      E F hE hF n d h hd hn hh hA hD ht hratio hcorner
  have hpresP := ramified_full_degree_root_cut_preserves_canonical_endpoint
    l hl ρ σ hρ hdiv hdir.2 P hP c hrootP
  have hpresQ := ramified_full_degree_root_cut_preserves_canonical_endpoint
    l hl ρ σ hρ hdiv hdir.2 Q hQ c hrootQ
  have hEP : E ∈ ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c P) := by
    simpa only [hE] using hpresP.1
  have hFQ : F ∈ ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c Q) := by
    simpa only [hF] using hpresQ.1
  have hEPold : ramifiedWeight l ρ σ E=ramifiedWeightDeg l hl ρ σ P := by
    simpa only [hE] using hpresP.2.1
  have hFQold : ramifiedWeight l ρ σ F=ramifiedWeightDeg l hl ρ σ Q := by
    simpa only [hF] using hpresQ.2.1
  have hendingP := ramified_strict_lower_face_canonical_degree_at_preserved_point
    l hl ρ σ r s hr hstrict (ramifiedCutAut l hl ρ σ c P) E hEP hEtop
    (by
      intro p hp
      have hu := ramifiedWeight_le_weightDeg_of_mem l hl ρ σ
        (ramifiedCutAut l hl ρ σ c P) p hp
      rw [ramifiedCutAut_weightDeg_eq l hl ρ σ hρ hdiv hdir.2 c P hP] at hu
      exact hu.trans_eq hEPold.symm)
  have hendingQ := ramified_strict_lower_face_canonical_degree_at_preserved_point
    l hl ρ σ r s hr hstrict (ramifiedCutAut l hl ρ σ c Q) F hFQ hFtop
    (by
      intro p hp
      have hu := ramifiedWeight_le_weightDeg_of_mem l hl ρ σ
        (ramifiedCutAut l hl ρ σ c Q) p hp
      rw [ramifiedCutAut_weightDeg_eq l hl ρ σ hρ hdiv hdir.2 c Q hQ] at hu
      exact hu.trans_eq hFQold.symm)
  exact ⟨c,hc,hdiv,r,s,hrs,hr,hstrict,hposP,hposQ,hrat,hEtop,hFtop,
    hBP,hBQ,hendingP,hendingQ⟩

end Dixmier.Weyl
