module

public import DixmierFormal.Weyl.RamifiedParallelCompanionFullRoot

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # A full-root cut certificate from either actual companion branch

Normalized corner data and a genuine source face supply a nonzero
full-degree root shared by the exact pair. The companion is not assumed
linear: its actual endpoint-case theorem handles both branches.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 800000

theorem ramified_normalized_corner_source_companion_full_root_certificate
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hdir : IsDirection ρ σ)
    (P Q F : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0) (hF : F ≠ 0)
    (hcomm : Q*P-P*Q=1)
    (hA : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hD : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P*F-F*P)=ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P*F-F*P)=
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F=(l:ℤ)*(ρ+σ))
    (n d h : ℕ) (hd : 0 < d) (hn : 0 < n) (hh : 2 ≤ h) (hcop : Nat.Coprime d n)
    (hratio : ramifiedWeightDeg l hl ρ σ Q*(d:ℤ)=
      ramifiedWeightDeg l hl ρ σ P*(n:ℤ))
    (hPdegree : (ramifiedTopFacePolynomial l hl ρ σ P).natDegree=d*h)
    (hPcoord : ramifiedPBWTopLaurent l hl P (d*h)=(d:ℤ)*((l:ℤ)*(h:ℤ)-1))
    (hQtop : ramifiedWeight l ρ σ ((n:ℤ)*((l:ℤ)*(h:ℤ)-1),n*h)=
      ramifiedWeightDeg l hl ρ σ Q)
    (j : ℕ) (hj : j ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support)
    (hne : j ≠ (ramifiedTopFacePolynomial l hl ρ σ P).natDegree) :
    ρ ∣ (l:ℤ) ∧
    0 < ramifiedWeightDeg l hl ρ σ P+
      ramifiedWeightDeg l hl ρ σ Q-(l:ℤ)*(ρ+σ) ∧
    ∃ c : ℂ, c ≠ 0 ∧
      (ramifiedTopFacePolynomial l hl ρ σ P).IsRoot c ∧
      (ramifiedTopFacePolynomial l hl ρ σ P).rootMultiplicity c=
        (ramifiedTopFacePolynomial l hl ρ σ P).natDegree ∧
      (ramifiedTopFacePolynomial l hl ρ σ Q).rootMultiplicity c=
        (ramifiedTopFacePolynomial l hl ρ σ Q).natDegree := by
  have hf := ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ P hP
  have hend := (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P
    (ramifiedTopFacePolynomial l hl ρ σ P).natDegree).mp
    (natDegree_mem_support_of_nonzero hf) |>.2
  have hPtop : ramifiedWeight l ρ σ ((d:ℤ)*((l:ℤ)*(h:ℤ)-1),d*h)=
      ramifiedWeightDeg l hl ρ σ P := by
    simpa only [ramifiedWeight,hPdegree,hPcoord] using hend
  have ht := ramified_exact_pair_normalized_corners_positive_threshold
    l hl ρ σ hρ hdir.2 P Q hP hQ hcomm d n h hd hn hh hA hD hPtop hQtop
  obtain hlinear | ⟨_,_,h2,hρl,hσ,hzero,hcoord⟩ :=
    ramified_normalized_corner_source_companion_endpoint_cases
      l hl ρ σ hρ hdir P Q F hP hQ hF hcomm hA hD hdegree hface hFweight
      n d h hd hn hh hcop hratio hPdegree hPcoord hQtop j hj hne
  · have hdeg : 2 ≤ (ramifiedTopFacePolynomial l hl ρ σ P).natDegree := by
      rw [hPdegree]
      nlinarith only [hd,hh]
    exact ramified_diagonal_companion_exact_pair_cut_certificate
      l hl ρ σ hρ hdir P Q F hP hQ hF hcomm hA hD hdegree hface hFweight
      hlinear.1 hdeg j hj hne
  · obtain ⟨c,hc,hroot,hrootP,hrootQ⟩ := ramified_parallel_corner_companion_full_root
      l hl ρ σ hρ hρl (by omega) P Q F hP hQ hF hcomm hA hD
      hdegree hface hFweight n d hd hcop hratio
      (by simpa only [h2,Nat.mul_comm] using hPdegree) hzero hcoord
    exact ⟨by rw [hρl],ht,c,hc,hroot,hrootP,hrootQ⟩

end Dixmier.Weyl
