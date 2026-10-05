/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCornerGradeBarrier
public import DixmierFormal.Weyl.RamifiedGradeExactPair

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Removing the PBW origin from an exact ramified pair

If the origin is the only nonnegative-grade support point of each
operator, subtract its scalar coefficient from each member. The exact
commutator survives, while both resulting supports have strictly
negative grade, contradicting the exact-pair grade theorem.
-/

namespace Dixmier.Weyl

noncomputable def ramifiedWithoutOrigin
    (l : ℕ) (hl : 0 < l) (T : ramifiedOperatorAlgebra l) :
    ramifiedOperatorAlgebra l :=
  T - (ramifiedPBWCoeff l hl T 0 0) • 1

theorem ramifiedWithoutOrigin_coeff
    (l : ℕ) (hl : 0 < l) (T : ramifiedOperatorAlgebra l)
    (p : ℤ × ℕ) :
    ramifiedPBWCoeff l hl (ramifiedWithoutOrigin l hl T) p.1 p.2 =
      ramifiedPBWCoeff l hl T p.1 p.2 -
        ramifiedPBWCoeff l hl T 0 0 *
          ramifiedPBWCoeff l hl (1 : ramifiedOperatorAlgebra l) p.1 p.2 := by
  simp only [ramifiedWithoutOrigin, ramifiedPBWCoeff,
    ramifiedPBWCoeffs_sub, ramifiedPBWCoeffs_smul,
    Finsupp.sub_apply, Finsupp.smul_apply]
  rfl

theorem ramifiedWithoutOrigin_coeff_origin
    (l : ℕ) (hl : 0 < l) (T : ramifiedOperatorAlgebra l) :
    ramifiedPBWCoeff l hl (ramifiedWithoutOrigin l hl T) 0 0 = 0 := by
  have h := ramifiedWithoutOrigin_coeff l hl T (0,0)
  have hone : ramifiedPBWCoeff l hl
      (1 : ramifiedOperatorAlgebra l) 0 0 = 1 :=
    ramifiedPBWCoeffs_one_coeff_at_origin l hl
  rw [hone] at h
  simpa using h

theorem ramifiedWithoutOrigin_coeff_ne_origin
    (l : ℕ) (hl : 0 < l) (T : ramifiedOperatorAlgebra l)
    (p : ℤ × ℕ) (hp : p ≠ (0,0)) :
    ramifiedPBWCoeff l hl (ramifiedWithoutOrigin l hl T) p.1 p.2 =
      ramifiedPBWCoeff l hl T p.1 p.2 := by
  rw [ramifiedWithoutOrigin_coeff]
  have hone : ramifiedPBWCoeff l hl
      (1 : ramifiedOperatorAlgebra l) p.1 p.2 = 0 := by
    by_contra hne
    have hmem : p.1 ∈
        ((ramifiedPBWCoeffs l hl (1 : ramifiedOperatorAlgebra l)) p.2).coeff.support :=
      Finsupp.mem_support_iff.mpr hne
    obtain ⟨hj,hi⟩ := ramifiedPBWCoeffs_one_coeff_support
      l hl p.2 p.1 hmem
    exact hp (Prod.ext hi hj)
  rw [hone]
  ring

private theorem commutator_scalar_shift {R : Type*} [Ring R] [Algebra ℂ R]
      (P Q : R) (a b : ℂ) :
      (Q-b•1)*(P-a•1)-(P-a•1)*(Q-b•1)=Q*P-P*Q := by
    simp only [sub_mul Q (b•1) (P-a•1), sub_mul P (a•1) (Q-b•1),
      mul_sub Q P (a•1), mul_sub (b•1) P (a•1),
      mul_sub P Q (b•1), mul_sub (a•1) Q (b•1)]
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    simp only [smul_smul, mul_comm a b]
    abel

theorem ramifiedWithoutOrigin_exact_pair
    (l : ℕ) (hl : 0 < l)
    (P Q : ramifiedOperatorAlgebra l)
    (hQP : Q*P-P*Q=1) :
    ramifiedWithoutOrigin l hl Q *
      ramifiedWithoutOrigin l hl P -
      ramifiedWithoutOrigin l hl P *
        ramifiedWithoutOrigin l hl Q = 1 := by
  rw [ramifiedWithoutOrigin, ramifiedWithoutOrigin,
    commutator_scalar_shift P Q
      (ramifiedPBWCoeff l hl P 0 0) (ramifiedPBWCoeff l hl Q 0 0)]
  exact hQP

theorem ramifiedWithoutOrigin_negative
    (l : ℕ) (hl : 0 < l) (T : ramifiedOperatorAlgebra l)
    (honly : ∀ p ∈ ramifiedPBWSupport l hl T,
      0 ≤ p.1-(l : ℤ)*(p.2 : ℤ) → p = (0,0)) :
    ∀ p ∈ ramifiedPBWSupport l hl (ramifiedWithoutOrigin l hl T),
      p.1-(l : ℤ)*(p.2 : ℤ) < 0 := by
  intro p hp
  have hpne : p ≠ (0,0) := by
    intro heq
    subst p
    have hcoeff := (ramifiedPBWSupport_mem_iff l hl
      (ramifiedWithoutOrigin l hl T) 0 0).mp hp
    exact hcoeff (ramifiedWithoutOrigin_coeff_origin l hl T)
  have hcoeff := (ramifiedPBWSupport_mem_iff l hl
    (ramifiedWithoutOrigin l hl T) p.1 p.2).mp hp
  have horiginal : p ∈ ramifiedPBWSupport l hl T := by
    apply (ramifiedPBWSupport_mem_iff l hl T p.1 p.2).mpr
    rw [← ramifiedWithoutOrigin_coeff_ne_origin l hl T p hpne]
    exact hcoeff
  by_contra hbad
  exact hpne (honly p horiginal (by omega))

/-- An exact pair cannot have the PBW origin as its only possible
nonnegative-grade point in both members. -/
theorem ramified_exact_pair_has_nonorigin_nonnegative_grade_point
    (l : ℕ) (hl : 0 < l)
    (P Q : ramifiedOperatorAlgebra l)
    (hQP : Q*P-P*Q=1) :
    (∃ p ∈ ramifiedPBWSupport l hl P,
      p ≠ (0,0) ∧ 0 ≤ p.1-(l : ℤ)*(p.2 : ℤ)) ∨
    (∃ q ∈ ramifiedPBWSupport l hl Q,
      q ≠ (0,0) ∧ 0 ≤ q.1-(l : ℤ)*(q.2 : ℤ)) := by
  by_contra hnone
  push Not at hnone
  have hPonly : ∀ p ∈ ramifiedPBWSupport l hl P,
      0 ≤ p.1-(l : ℤ)*(p.2 : ℤ) → p = (0,0) := by
    intro p hp hgrade
    by_contra hne
    exact (not_lt_of_ge hgrade) (hnone.1 p hp hne)
  have hQonly : ∀ q ∈ ramifiedPBWSupport l hl Q,
      0 ≤ q.1-(l : ℤ)*(q.2 : ℤ) → q = (0,0) := by
    intro q hq hgrade
    by_contra hne
    exact (not_lt_of_ge hgrade) (hnone.2 q hq hne)
  rcases ramified_exact_pair_has_nonnegative_grade_point l hl
      (ramifiedWithoutOrigin l hl P)
      (ramifiedWithoutOrigin l hl Q)
      (ramifiedWithoutOrigin_exact_pair l hl P Q hQP) with
    ⟨p,hp,hgrade⟩ | ⟨q,hq,hgrade⟩
  · have hneg := ramifiedWithoutOrigin_negative l hl P hPonly p hp
    omega
  · have hneg := ramifiedWithoutOrigin_negative l hl Q hQonly q hq
    omega

/-- At a normalized corner, the exact commutator cannot occur at the
first contraction weight. This closes the scalar-origin loophole in
the nonnegative-grade support argument. -/
theorem ramified_corner_exact_pair_weight_sum_strict
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (E : ℤ × ℕ)
    (hEtop : ramifiedWeight l ρ σ E =
      ramifiedWeightDeg l hl ρ σ P)
    (d n h : ℕ) (hd : 1 < d) (hn : 1 < n) (hh : 2 ≤ h)
    (hEfirst : E.1 = (d : ℤ)*((h : ℤ)*(l : ℤ)-1))
    (hEsecond : E.2 = d*h)
    (hPpos : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hratio : ramifiedWeightDeg l hl ρ σ Q*(d : ℤ) =
      ramifiedWeightDeg l hl ρ σ P*(n : ℤ))
    (hQP : Q*P-P*Q=1) :
    (l : ℤ)*(ρ+σ) <
      ramifiedWeightDeg l hl ρ σ P + ramifiedWeightDeg l hl ρ σ Q := by
  have hbound := ramified_exact_pair_weightDeg_sum_lower
    l hl ρ σ hρ hsum Q P hQP
  have hnot : ramifiedWeightDeg l hl ρ σ P +
      ramifiedWeightDeg l hl ρ σ Q ≠ (l : ℤ)*(ρ+σ) := by
    intro heq
    obtain ⟨hPonly,hQonly⟩ :=
      ramified_corner_first_step_nonnegative_only_origin
        l hl ρ σ hρ hsum P Q E hEtop d n h hd hn hh
        hEfirst hEsecond hPpos hratio heq
    rcases ramified_exact_pair_has_nonorigin_nonnegative_grade_point
      l hl P Q hQP with ⟨p,hp,hpne,hgrade⟩ | ⟨q,hq,hqne,hgrade⟩
    · exact hpne (hPonly p hp hgrade)
    · exact hqne (hQonly q hq hgrade)
  omega

end Dixmier.Weyl
