module

public import DixmierFormal.Weyl.RamifiedCompanionPositiveThreshold

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # The diagonal companion supplies an exact-pair full-root cut certificate

A degree-one companion on a genuine source face supplies index divisibility
and a nonzero full-degree root. Its strict degree gap gives positive
commutator threshold, so that root transfers to the unrestricted mate.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

theorem ramified_exact_pair_full_degree_root_mate_of_reverse_commutator
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hcomm : Q*P-P*Q=1)
    (hA : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hD : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hthreshold : 0 < ramifiedWeightDeg l hl ρ σ P+
      ramifiedWeightDeg l hl ρ σ Q-(l:ℤ)*(ρ+σ))
    (c : ℂ)
    (hmult : (ramifiedTopFacePolynomial l hl ρ σ P).rootMultiplicity c=
      (ramifiedTopFacePolynomial l hl ρ σ P).natDegree) :
    (ramifiedTopFacePolynomial l hl ρ σ Q).rootMultiplicity c=
      (ramifiedTopFacePolynomial l hl ρ σ Q).natDegree := by
  have ht : 0 < ramifiedWeightDeg l hl ρ σ Q+
      ramifiedWeightDeg l hl ρ σ P-(l:ℤ)*(ρ+σ) := by simpa [add_comm] using hthreshold
  have hr := ramified_exact_pair_top_face_rootMultiplicity_ratio
    l hl ρ σ hρ hsum Q P hQ hP hcomm hD hA ht c
  have hd := ramified_exact_pair_top_face_degree_ratio
    l hl ρ σ hρ hsum Q P hQ hP hcomm hD hA ht
  rw [hmult] at hr
  have hpos : 0 < (ramifiedWeightDeg l hl ρ σ P).toNat := by omega
  exact Nat.eq_of_mul_eq_mul_left hpos (hr.trans hd.symm)

theorem ramified_diagonal_companion_exact_pair_cut_certificate
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hdir : IsDirection ρ σ)
    (P Q F : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0) (hF : F ≠ 0)
    (hcomm : Q*P-P*Q=1)
    (hA : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hD : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P*F-F*P)=ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P*F-F*P)=
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F=(l:ℤ)*(ρ+σ))
    (hlinear : (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree=1)
    (hPdegree : 2 ≤ (ramifiedTopFacePolynomial l hl ρ σ P).natDegree)
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
  have ht := ramified_exact_pair_positive_threshold_of_source_companion_degree_gap
    l hl ρ σ hρ hdir.2 P Q F hP hQ hF hcomm hA hD hdegree hface hFweight
    (by rw [hlinear]; omega)
  obtain ⟨hdiv,c,hc,hroot,hmult,_⟩ :=
    ramified_linear_source_companion_admissible_full_root
      l hl ρ σ hρ hdir P F hP hF hdegree hface hFweight hlinear j hj hne
  exact ⟨hdiv,ht,c,hc,hroot,hmult,
    ramified_exact_pair_full_degree_root_mate_of_reverse_commutator
      l hl ρ σ hρ hdir.2 P Q hP hQ hcomm hA hD ht c hmult⟩

end Dixmier.Weyl
