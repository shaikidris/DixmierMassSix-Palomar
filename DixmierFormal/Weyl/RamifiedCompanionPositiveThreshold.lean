module

public import DixmierFormal.Weyl.RamifiedNormalizedCornerPositiveWeights
public import DixmierFormal.Weyl.RamifiedLeadingPoissonConstant

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # A source companion excludes the constant-threshold boundary

A constant derivative bracket forces simple roots. Root containment in
the source companion contradicts the constant threshold whenever its
face degree is strictly smaller than the source face degree.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 800000

theorem constant_derivative_bracket_maxRoot_le_one
    (f g : ℂ[X]) (A B : ℂ) (hg : g ≠ 0)
    (hbr : C A*(f.derivative*g)-C B*(f*g.derivative)=1) :
    maxRootMult g ≤ 1 := by
  classical
  unfold maxRootMult
  apply Finset.sup_le
  intro c _
  by_contra hbad
  have hm : 1 < g.rootMultiplicity c := by omega
  obtain ⟨hroot,hder⟩ := (one_lt_rootMultiplicity_iff_isRoot hg).mp hm
  change g.eval c=0 at hroot
  change g.derivative.eval c=0 at hder
  have he := congrArg (eval c) hbr
  simp only [eval_sub,eval_mul,eval_C,hroot,hder,mul_zero,zero_mul,sub_zero,eval_one] at he
  exact zero_ne_one he

theorem ramified_exact_pair_positive_threshold_of_source_companion_degree_gap
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q F : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0) (hF : F ≠ 0)
    (hcomm : Q*P-P*Q=1)
    (hA : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hD : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P*F-F*P)=ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P*F-F*P)=
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F=(l:ℤ)*(ρ+σ))
    (hdegreeGap : (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree <
      (ramifiedTopFacePolynomial l hl ρ σ P).natDegree) :
    0 < ramifiedWeightDeg l hl ρ σ P+
      ramifiedWeightDeg l hl ρ σ Q-(l:ℤ)*(ρ+σ) := by
  have hlower := ramified_exact_pair_weightDeg_sum_lower l hl ρ σ hρ hsum Q P hcomm
  by_contra hbad
  have hz : ramifiedWeightDeg l hl ρ σ Q+
      ramifiedWeightDeg l hl ρ σ P-(l:ℤ)*(ρ+σ)=0 := by omega
  have hbr := ramified_exact_pair_top_face_bracket_eq_one_of_threshold_zero
    l hl ρ σ hρ hsum Q P hQ hP hcomm hz
  have hm := constant_derivative_bracket_maxRoot_le_one _ _ _ _
    (ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ P hP) hbr
  have hc := ramified_source_companion_top_face_root_count
    l hl ρ σ hρ hsum P F hP hF hdegree hface hFweight
  have he := complex_polynomial_companion_root_budget _ _ hc
  have hdegreeLe : (ramifiedTopFacePolynomial l hl ρ σ P).natDegree ≤
      (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree := by
    have hmul := Nat.mul_le_mul_left
      (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree hm
    simpa only [Nat.mul_one] using he.trans hmul
  omega

end Dixmier.Weyl
