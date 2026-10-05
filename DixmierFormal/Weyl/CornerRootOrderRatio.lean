/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PolynomialCutMateAlignment
public import DixmierFormal.Weyl.CornerQuadraticRootCut

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Maximum-root dichotomy from the exact mate ratio

The exact-pair common-root theorem makes the reduced denominator
divide the selected maximum root order. At corner degree `2d`, that
order is `d` or `2d`, without first factoring the leading face as a
quadratic power. The degree hypothesis must still be derived from the
actual normalized ending point.
-/

namespace Dixmier.Weyl

open Polynomial

theorem maxRootMult_le_natDegree (p : ℂ[X]) (hp : p ≠ 0) :
    maxRootMult p ≤ p.natDegree := by
  classical
  unfold maxRootMult
  apply Finset.sup_le
  intro c hc
  have hle := natDegree_le_of_dvd (pow_rootMultiplicity_dvd p c) hp
  rw [natDegree_pow,natDegree_X_sub_C] at hle
  simpa only [Nat.mul_one] using hle

theorem positive_divisor_at_most_twice
    (d M : ℕ) (hd : 0 < d) (hM : 0 < M)
    (hdiv : d ∣ M) (hbound : M ≤ 2 * d) :
    M = d ∨ M = 2 * d := by
  obtain ⟨k,hk⟩ := hdiv
  have hkpos : 0 < k := by
    by_contra hn
    have hz : k = 0 := by omega
    simp [hz] at hk
    omega
  have hkle : k ≤ 2 := by
    by_contra hn
    have hthree : 3 ≤ k := by omega
    have hge := Nat.mul_le_mul_left d hthree
    rw [hk] at hbound
    nlinarith
  have hkcases : k = 1 ∨ k = 2 := by omega
  rcases hkcases with h | h
  · left; simpa [h] using hk
  · right; simpa [h, Nat.mul_comm] using hk

/-- On a positive-sum face, the endpoint of minimal grade has the
largest Y exponent and hence determines the cut polynomial's degree. -/
theorem cutPoly_natDegree_of_min_grade_endpoint
    (P : A1 ℂ) (ρ σ : ℤ) (a b : ℕ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (hend : expo a b ∈ (leadingForm ρ σ P.1).support)
    (hmin : ∀ e ∈ (leadingForm ρ σ P.1).support,
      grade (expo a b) ≤ grade e) :
    (cutPoly ρ σ P.1).natDegree = b := by
  have hw := (polynomialFace_point_source_data P ρ σ a b hend).2
  have hc : (cutPoly ρ σ P.1).coeff b ≠ 0 := by
    rw [cutPoly_coeff_at_face_point P ρ σ a b hρ hw]
    exact MvPolynomial.mem_support_iff.mp hend
  apply Nat.le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    by_contra hne
    obtain ⟨i,hi⟩ := cutPoly_coeff_nonzero_has_face_point P ρ σ j hne
    have hcoeff : MvPolynomial.coeff (expo i j) (leadingForm ρ σ P.1) ≠ 0 := by
      rw [← cutPoly_coeff_at_face_point P ρ σ i j hρ hi]
      exact hne
    have hmem := MvPolynomial.mem_support_iff.mpr hcoeff
    have hg := hmin (expo i j) hmem
    simp [grade, expo] at hg
    have hjZ : (b : ℤ) < (j : ℤ) := by exact_mod_cast hj
    nlinarith [mul_pos hsum (sub_pos.mpr hjZ)]
  · exact Polynomial.le_natDegree_of_ne_zero hc

/-- A maximum root consuming the whole degree forces a pure linear
power, with the scalar fixed by the leading coefficient. -/
theorem polynomial_eq_linear_power_of_maxRootMult_eq_natDegree
    (p : ℂ[X]) (hdeg : 0 < p.natDegree)
    (hmax : maxRootMult p = p.natDegree) :
    ∃ c : ℂ, p.IsRoot c ∧
      p = C p.leadingCoeff * (X - C c) ^ p.natDegree := by
  obtain ⟨c,hroot,hm⟩ :=
    exists_rootMultiplicity_eq_maxRootMult p hdeg
  refine ⟨c,hroot,?_⟩
  have hmonic : ((X - C c) ^ p.natDegree).Monic := by
    exact (monic_X_sub_C c).pow _
  have hdvd : (X - C c) ^ p.natDegree ∣ p := by
    rw [← hmax,← hm]
    exact pow_rootMultiplicity_dvd p c
  exact eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    hmonic hdvd (by rw [natDegree_pow, natDegree_X_sub_C]; omega)

/-- A minimal-grade endpoint `(d,2d)` on the actual horizontal face
determines the full degree of its cut polynomial. -/
theorem horizontal_corner_cutPoly_natDegree
    (P : A1 ℂ) (d : ℕ)
    (hend : expo d (2 * d) ∈ (leadingForm 1 0 P.1).support)
    (hmin : ∀ e ∈ (leadingForm 1 0 P.1).support,
      grade (expo d (2 * d)) ≤ grade e) :
    (cutPoly 1 0 P.1).natDegree = 2 * d := by
  have hw : vDeg 1 0 P.1 = (d : ℤ) := by
    have h := (polynomialFace_point_source_data P 1 0 d (2 * d) hend).2
    simpa using h.symm
  have hc : (cutPoly 1 0 P.1).coeff (2 * d) ≠ 0 := by
    rw [cutPoly_coeff_at_face_point P 1 0 d (2 * d) (by omega)]
    · exact MvPolynomial.mem_support_iff.mp hend
    · simpa [hw]
  apply Nat.le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    by_contra hne
    obtain ⟨i,hi⟩ := cutPoly_coeff_nonzero_has_face_point P 1 0 j hne
    have hid : i = d := by
      rw [hw] at hi
      exact_mod_cast (by simpa using hi : (i : ℤ) = (d : ℤ))
    subst i
    have hcoeff : MvPolynomial.coeff (expo d j) (leadingForm 1 0 P.1) ≠ 0 := by
      rw [← cutPoly_coeff_at_face_point P 1 0 d j (by omega)]
      · exact hne
      · simpa [hw]
    have hmem := MvPolynomial.mem_support_iff.mpr hcoeff
    have hg := hmin (expo d j) hmem
    simp [grade, expo] at hg
    omega
  · exact Polynomial.le_natDegree_of_ne_zero hc

/-- The actual selected maximum root of an exact polynomial Weyl pair
has only the two corner-compatible orders when its face polynomial
has degree twice the reduced denominator. -/
theorem exactPair_corner_maxRoot_order_dichotomy
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hP : 0 < vDeg ρ σ P.1) (hQ : 0 < vDeg ρ σ Q.1)
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hQP : Q * P - P * Q = 1)
    (hsum : ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1)
    (d n : ℕ) (hd : 0 < d)
    (hweight : vDeg ρ σ Q.1 * (d : ℤ) =
      vDeg ρ σ P.1 * (n : ℤ))
    (hcop : Nat.Coprime n d)
    (hdegree : (cutPoly ρ σ P.1).natDegree = 2 * d) :
    maxRootMult (cutPoly ρ σ P.1) = d ∨
      maxRootMult (cutPoly ρ σ P.1) = 2 * d := by
  obtain ⟨c,hrootP,hmP,hrootQ,hratio,_,_,_⟩ :=
    exactPair_maxRoot_cut_mate_oldFace_endpoints
      l hl P Q ρ σ hdir hρ hdiv hP hQ hdirP hdirQ hQP hsum
  have hratioZ := congrArg (fun a : ℕ => (a : ℤ)) hratio
  push_cast at hratioZ
  rw [Int.toNat_of_nonneg (le_of_lt hP),
    Int.toNat_of_nonneg (le_of_lt hQ)] at hratioZ
  have hMdiv : d ∣ maxRootMult (cutPoly ρ σ P.1) :=
    (reduced_ratio_root_orders_divide
      (vDeg ρ σ P.1) (vDeg ρ σ Q.1) d n
      (maxRootMult (cutPoly ρ σ P.1))
      ((cutPoly ρ σ Q.1).rootMultiplicity c)
      hP hweight hratioZ hcop).1
  have hpne : cutPoly ρ σ P.1 ≠ 0 := by
    apply ne_zero_of_natDegree_gt
      (show 0 < (cutPoly ρ σ P.1).natDegree by
        rw [hdegree]
        omega)
  have hMpos : 0 < maxRootMult (cutPoly ρ σ P.1) := by
    rw [← hmP]
    exact (rootMultiplicity_pos hpne).mpr hrootP
  have hMle : maxRootMult (cutPoly ρ σ P.1) ≤ 2 * d := by
    rw [← hdegree]
    exact maxRootMult_le_natDegree _ hpne
  exact positive_divisor_at_most_twice d _ hd hMpos hMdiv hMle

/-- At the normalized height-two endpoint, the actual minimum-grade
face point supplies the degree used in the exact-pair dichotomy. -/
theorem exactPair_heightTwo_corner_maxRoot_order_dichotomy
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hP : 0 < vDeg ρ σ P.1) (hQ : 0 < vDeg ρ σ Q.1)
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hQP : Q * P - P * Q = 1)
    (hsum : ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1)
    (d n : ℕ) (hd : 0 < d)
    (hweight : vDeg ρ σ Q.1 * (d : ℤ) =
      vDeg ρ σ P.1 * (n : ℤ))
    (hcop : Nat.Coprime n d)
    (hend : expo d (2 * d) ∈ (leadingForm ρ σ P.1).support)
    (hmin : ∀ e ∈ (leadingForm ρ σ P.1).support,
      grade (expo d (2 * d)) ≤ grade e) :
    maxRootMult (cutPoly ρ σ P.1) = d ∨
      maxRootMult (cutPoly ρ σ P.1) = 2 * d := by
  apply exactPair_corner_maxRoot_order_dichotomy
    l hl P Q ρ σ hdir hρ hdiv hP hQ hdirP hdirQ
    hQP hsum d n hd hweight hcop
  exact cutPoly_natDegree_of_min_grade_endpoint P ρ σ d (2 * d)
    hρ hdir.2 hend hmin

/-- The second branch of the actual height-two corner dichotomy has
the entire cut polynomial concentrated at one root. -/
theorem exactPair_heightTwo_corner_root_or_linear_power
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hP : 0 < vDeg ρ σ P.1) (hQ : 0 < vDeg ρ σ Q.1)
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hQP : Q * P - P * Q = 1)
    (hsum : ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1)
    (d n : ℕ) (hd : 0 < d)
    (hweight : vDeg ρ σ Q.1 * (d : ℤ) =
      vDeg ρ σ P.1 * (n : ℤ))
    (hcop : Nat.Coprime n d)
    (hend : expo d (2 * d) ∈ (leadingForm ρ σ P.1).support)
    (hmin : ∀ e ∈ (leadingForm ρ σ P.1).support,
      grade (expo d (2 * d)) ≤ grade e) :
    maxRootMult (cutPoly ρ σ P.1) = d ∨
      ∃ c : ℂ, (cutPoly ρ σ P.1).IsRoot c ∧
        cutPoly ρ σ P.1 =
          C (cutPoly ρ σ P.1).leadingCoeff *
            (X - C c) ^ (2 * d) := by
  have hcases := exactPair_heightTwo_corner_maxRoot_order_dichotomy
    l hl P Q ρ σ hdir hρ hdiv hP hQ hdirP hdirQ hQP hsum
    d n hd hweight hcop hend hmin
  rcases hcases with hsmall | hfull
  · exact Or.inl hsmall
  · right
    have hdegree := cutPoly_natDegree_of_min_grade_endpoint
      P ρ σ d (2 * d) hρ hdir.2 hend hmin
    have hdegpos : 0 < (cutPoly ρ σ P.1).natDegree := by
      rw [hdegree]
      omega
    obtain ⟨c,hroot,hshape⟩ :=
      polynomial_eq_linear_power_of_maxRootMult_eq_natDegree
        (cutPoly ρ σ P.1) hdegpos (by rw [hdegree]; exact hfull)
    exact ⟨c,hroot,by simpa [hdegree] using hshape⟩

/-- The root-order dichotomy from an actual minimal-grade horizontal
corner endpoint, with no degree or factorization premise on the face. -/
theorem exactPair_horizontal_corner_maxRoot_order_dichotomy
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (hdir : IsDirection 1 0)
    (hP : 0 < vDeg 1 0 P.1) (hQ : 0 < vDeg 1 0 Q.1)
    (hdirP : InDir 1 0 P.1) (hdirQ : InDir 1 0 Q.1)
    (hQP : Q * P - P * Q = 1)
    (hsum : 1 < vDeg 1 0 P.1 + vDeg 1 0 Q.1)
    (d n : ℕ) (hd : 0 < d)
    (hweight : vDeg 1 0 Q.1 * (d : ℤ) =
      vDeg 1 0 P.1 * (n : ℤ))
    (hcop : Nat.Coprime n d)
    (hend : expo d (2 * d) ∈ (leadingForm 1 0 P.1).support)
    (hmin : ∀ e ∈ (leadingForm 1 0 P.1).support,
      grade (expo d (2 * d)) ≤ grade e) :
    maxRootMult (cutPoly 1 0 P.1) = d ∨
      maxRootMult (cutPoly 1 0 P.1) = 2 * d := by
  apply exactPair_corner_maxRoot_order_dichotomy
    l hl P Q 1 0 hdir (by omega) (by simp) hP hQ hdirP hdirQ
    hQP (by simpa using hsum) d n hd hweight hcop
  exact horizontal_corner_cutPoly_natDegree P d hend hmin

end Dixmier.Weyl
