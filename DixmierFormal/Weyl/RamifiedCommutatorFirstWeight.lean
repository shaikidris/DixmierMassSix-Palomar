module

public import DixmierFormal.Weyl.RamifiedNoncentralizingFirstFace
public import DixmierFormal.Weyl.RamifiedGradeFiltration
public import DixmierFormal.Weyl.RamifiedGradeExactPair

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # The exact first weight and face of a noncentralizing commutator

The canonical PBW first-contraction sum has no coefficients above the sum of
the input weights minus the contraction weight. A nonzero scalar face bracket
attains that bound, so it is the actual canonical face of the full commutator.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 800000

theorem LaurentUpper_first_derivative_bracket
    (l : ℕ) (f g : LaurentPolynomial ℂ) (B C : ℤ) (n m : ℕ)
    (hf : LaurentUpper f B) (hg : LaurentUpper g C) :
    LaurentUpper (f*((n:ℂ) • ramifiedDerivative l g) -
      g*((m:ℂ) • ramifiedDerivative l f)) (B+C-(l:ℤ)) := by
  apply LaurentUpper_sub_local
  · have h := LaurentUpper_mul f ((n:ℂ) • ramifiedDerivative l g) B (C-(l:ℤ))
      hf (LaurentUpper_smul_local _ _ _ (LaurentUpper_derivative l g C hg))
    convert h using 1 <;> ring
  · have h := LaurentUpper_mul g ((m:ℂ) • ramifiedDerivative l f) C (B-(l:ℤ))
      hg (LaurentUpper_smul_local _ _ _ (LaurentUpper_derivative l f B hf))
    convert h using 1 <;> ring

theorem ramified_commutator_support_first_weight_upper
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (p : ℤ × ℕ) (hp : p ∈ ramifiedPBWSupport l hl (P*Q-Q*P)) :
    ramifiedWeight l ρ σ p ≤
      ramifiedWeightDeg l hl ρ σ P + ramifiedWeightDeg l hl ρ σ Q -
        (l:ℤ)*(ρ+σ) := by
  classical
  by_contra hbad
  have hgt := lt_of_not_ge hbad
  have hc := (ramifiedPBWSupport_mem_iff l hl (P*Q-Q*P) p.1 p.2).mp hp
  change ((ramifiedPBWCoeffs l hl (P*Q-Q*P)) p.2).coeff p.1 ≠ 0 at hc
  rw [ramifiedPBWCoeffs_commutator_first_face_canonical
    l hl ρ σ hρ hsum P Q hP hQ p.2 p.1 (le_of_lt hgt)] at hc
  obtain ⟨n,hn,hns⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  obtain ⟨m,hm,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hns
  split_ifs at hterm with ht
  · have hu := LaurentUpper_first_derivative_bracket l
      ((ramifiedPBWCoeffs l hl P) n) ((ramifiedPBWCoeffs l hl Q) m)
      (ramifiedPBWTopLaurent l hl P n) (ramifiedPBWTopLaurent l hl Q m) n m
      (ramifiedPBWTopLaurent_upper l hl P n) (ramifiedPBWTopLaurent_upper l hl Q m)
    have hv := hu p.1 (Finsupp.mem_support_iff.mpr hterm)
    have hfirstZ : (n:ℤ)+(m:ℤ)=(p.2:ℤ)+1 := by exact_mod_cast ht.1
    have hs := congrArg (fun z : ℤ => (l:ℤ)*σ*z) hfirstZ
    have hup : ramifiedWeight l ρ σ p ≤
        ramifiedWeightDeg l hl ρ σ P + ramifiedWeightDeg l hl ρ σ Q -
          (l:ℤ)*(ρ+σ) := by
      dsimp [ramifiedWeight]
      nlinarith [ht.2.1, ht.2.2]
    exact (not_le_of_gt hgt) hup
  · exact (hterm rfl).elim

theorem ramified_noncentralizing_commutator_weight
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hc : ramifiedFaceCentralization l hl ρ σ P Q ≠ 0) :
    ramifiedWeightDeg l hl ρ σ (P*Q-Q*P) =
      ramifiedWeightDeg l hl ρ σ P + ramifiedWeightDeg l hl ρ σ Q -
        (l:ℤ)*(ρ+σ) := by
  apply ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ _ (P*Q-Q*P)
  · exact ramified_noncentralizing_first_face_exists l hl ρ σ hρ hsum P Q hP hQ hc
  · intro p hp
    exact ramified_commutator_support_first_weight_upper l hl ρ σ hρ hsum P Q hP hQ p hp

theorem ramified_noncentralizing_commutator_top_face
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hc : ramifiedFaceCentralization l hl ρ σ P Q ≠ 0) :
    ramifiedTopFacePolynomial l hl ρ σ (P*Q-Q*P) =
      -ramifiedFaceCentralization l hl ρ σ P Q := by
  rw [← ramifiedWeightComponent_at_degree l hl ρ σ hρ (P*Q-Q*P),
    ramified_noncentralizing_commutator_weight l hl ρ σ hρ hsum P Q hP hQ hc]
  exact ramified_first_weight_component_eq_neg_centralization l hl ρ σ hρ hsum P Q hP hQ

theorem ramifiedTopFacePolynomial_zero_first_weight
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) :
    ramifiedTopFacePolynomial l hl ρ σ (0 : ramifiedOperatorAlgebra l) = 0 := by
  rw [← ramifiedWeightComponent_at_degree l hl ρ σ hρ, map_zero]

theorem ramifiedFaceCentralization_zero_right
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (P : ramifiedOperatorAlgebra l) :
    ramifiedFaceCentralization l hl ρ σ P 0 = 0 := by
  unfold ramifiedFaceCentralization
  rw [ramifiedTopFacePolynomial_zero_first_weight l hl ρ σ hρ]
  simp

end Dixmier.Weyl
