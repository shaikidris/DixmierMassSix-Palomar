module

public import DixmierFormal.Weyl.RamifiedLeadingPoissonConstant
public import DixmierFormal.Weyl.RamifiedNormalizedCornerPositiveWeights

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # A normalized corner excludes the constant commutator threshold

At threshold zero, one top face has an order-zero term. Its positive weight
is at least rho because its Laurent coordinate is integral. The normalized
corners of height at least two force both weights strictly below rho at
that threshold, which is impossible. No companion degree bound is used.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

theorem ramified_positive_order_zero_face_weight_ge_rho
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (P : ramifiedOperatorAlgebra l)
    (hpos : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hzero : 0 ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support) :
    ρ ≤ ramifiedWeightDeg l hl ρ σ P := by
  have he := (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P 0).mp hzero |>.2
  simp only [Nat.cast_zero,mul_zero,add_zero] at he
  have hi : 1 ≤ ramifiedPBWTopLaurent l hl P 0 := by
    by_contra hn
    have hprod := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hρ)
      (by omega : ramifiedPBWTopLaurent l hl P 0 ≤ 0)
    omega
  have hm := mul_le_mul_of_nonneg_left hi (le_of_lt hρ)
  simpa only [mul_one,he] using hm

theorem ramified_exact_pair_normalized_corners_positive_threshold
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hcomm : Q*P-P*Q=1)
    (d n h : ℕ) (hd : 0 < d) (hn : 0 < n) (hh : 2 ≤ h)
    (hA : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hD : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hPtop : ramifiedWeight l ρ σ ((d:ℤ)*((l:ℤ)*(h:ℤ)-1),d*h)=
      ramifiedWeightDeg l hl ρ σ P)
    (hQtop : ramifiedWeight l ρ σ ((n:ℤ)*((l:ℤ)*(h:ℤ)-1),n*h)=
      ramifiedWeightDeg l hl ρ σ Q) :
    0 < ramifiedWeightDeg l hl ρ σ P+
      ramifiedWeightDeg l hl ρ σ Q-(l:ℤ)*(ρ+σ) := by
  let A := ramifiedWeightDeg l hl ρ σ P
  let D := ramifiedWeightDeg l hl ρ σ Q
  let w := (l:ℤ)*(h:ℤ)*(ρ+σ)-ρ
  have hAw : A=(d:ℤ)*w := by
    dsimp [A,w]
    unfold ramifiedWeight at hPtop
    push_cast at hPtop
    nlinarith only [hPtop]
  have hDw : D=(n:ℤ)*w := by
    dsimp [D,w]
    unfold ramifiedWeight at hQtop
    push_cast at hQtop
    nlinarith only [hQtop]
  have hdZ : 1 ≤ (d:ℤ) := by exact_mod_cast hd
  have hnZ : 1 ≤ (n:ℤ) := by exact_mod_cast hn
  have hhZ : 2 ≤ (h:ℤ) := by exact_mod_cast hh
  have hwpos : 0 < w := by
    have hdpos : 0 < (d:ℤ) := by exact_mod_cast hd
    change 0 < A at hA
    nlinarith only [hdpos,hAw,hA]
  have hwA : w ≤ A := by nlinarith only [hdZ,hwpos,hAw]
  have hwD : w ≤ D := by nlinarith only [hnZ,hwpos,hDw]
  have hlower := ramified_exact_pair_weightDeg_sum_lower l hl ρ σ hρ hsum Q P hcomm
  by_contra hbad
  have hz : D+A-(l:ℤ)*(ρ+σ)=0 := by
    dsimp [A,D] at *
    omega
  have hρeq : ρ=(h:ℤ)*(A+D)-w := by
    dsimp [w]
    nlinarith only [hz]
  have hAD : 0 < A+D := by dsimp [A,D]; omega
  have hhAD := mul_le_mul_of_nonneg_right hhZ (le_of_lt hAD)
  have hApos : 0 < A := hA
  have hDpos : 0 < D := hD
  have hρA : A < ρ := by
    change 0 < D at hD
    nlinarith only [hρeq,hhAD,hwD,hD,hApos]
  have hρD : D < ρ := by
    change 0 < A at hA
    nlinarith only [hρeq,hhAD,hwA,hA,hDpos]
  obtain hzeroQ | hzeroP := ramified_exact_pair_threshold_zero_has_top_order_zero
    l hl ρ σ hρ hsum Q P hQ hP hcomm hz
  · have hge := ramified_positive_order_zero_face_weight_ge_rho l hl ρ σ hρ Q hD hzeroQ
    change ρ ≤ D at hge
    omega
  · have hge := ramified_positive_order_zero_face_weight_ge_rho l hl ρ σ hρ P hA hzeroP
    change ρ ≤ A at hge
    omega

end Dixmier.Weyl
