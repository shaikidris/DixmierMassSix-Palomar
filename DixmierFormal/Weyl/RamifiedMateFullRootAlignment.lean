module

public import DixmierFormal.Weyl.RamifiedFullRootCornerPreservation
public import DixmierFormal.Weyl.RamifiedFacePowerRatio

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Full-degree roots align across an exact ramified pair

The exact face power ratio gives the degree ratio as well as the root
multiplicity ratio. A root consuming the first face degree therefore
consumes the mate face degree, without a mate order bound.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 800000

theorem ramified_exact_pair_top_face_degree_ratio
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hcomm : P*Q-Q*P=1)
    (hA : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hD : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hthreshold : 0 < ramifiedWeightDeg l hl ρ σ P+
      ramifiedWeightDeg l hl ρ σ Q-(l:ℤ)*(ρ+σ)) :
    (ramifiedWeightDeg l hl ρ σ Q).toNat *
        (ramifiedTopFacePolynomial l hl ρ σ P).natDegree=
      (ramifiedWeightDeg l hl ρ σ P).toNat *
        (ramifiedTopFacePolynomial l hl ρ σ Q).natDegree := by
  obtain ⟨a,ha,hpow⟩ := ramified_exact_pair_top_face_power_ratio
    l hl ρ σ hρ hsum P Q hP hQ hcomm hA hD hthreshold
  have hdeg := congrArg Polynomial.natDegree hpow
  rw [natDegree_pow,natDegree_mul (C_ne_zero.mpr ha)
    (pow_ne_zero _ (ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ Q hQ)),
    natDegree_C,natDegree_pow,zero_add] at hdeg
  simpa only [mul_comm] using hdeg

theorem ramified_exact_pair_full_degree_root_mate
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hcomm : P*Q-Q*P=1)
    (hA : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hD : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hthreshold : 0 < ramifiedWeightDeg l hl ρ σ P+
      ramifiedWeightDeg l hl ρ σ Q-(l:ℤ)*(ρ+σ))
    (c : ℂ)
    (hmult : (ramifiedTopFacePolynomial l hl ρ σ P).rootMultiplicity c=
      (ramifiedTopFacePolynomial l hl ρ σ P).natDegree) :
    (ramifiedTopFacePolynomial l hl ρ σ Q).rootMultiplicity c=
      (ramifiedTopFacePolynomial l hl ρ σ Q).natDegree := by
  have hr := ramified_exact_pair_top_face_rootMultiplicity_ratio
    l hl ρ σ hρ hsum P Q hP hQ hcomm hA hD hthreshold c
  have hd := ramified_exact_pair_top_face_degree_ratio
    l hl ρ σ hρ hsum P Q hP hQ hcomm hA hD hthreshold
  rw [hmult] at hr
  have hpos : 0 < (ramifiedWeightDeg l hl ρ σ P).toNat := by omega
  exact Nat.eq_of_mul_eq_mul_left hpos (hr.symm.trans hd)

end Dixmier.Weyl
