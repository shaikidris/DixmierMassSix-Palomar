/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PolynomialCommonPower
public import DixmierFormal.Weyl.RamifiedTopFaceSupport
public import DixmierFormal.Weyl.RamifiedTopLaurentFaceLift
public import DixmierFormal.Weyl.RamifiedFacePolynomial
public import DixmierFormal.Weyl.CornerQuadraticRootCut

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Identifying canonical top faces with cut-line polynomials

When a ramified Newton face has known weight `ρ*r`, the canonical polynomial
in derivative order agrees with the affine-lattice polynomial used by the
root-selected shear.
-/

namespace Dixmier.Weyl

/-- The canonical top-face polynomial is the affine cut-face polynomial when
the latter is indexed by the actual maximal weight. -/
theorem ramifiedTopFacePolynomial_eq_cutFace
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (hdiv : ρ ∣ (l : ℤ)) (T : ramifiedOperatorAlgebra l) (r : ℤ)
    (hweight : ramifiedWeightDeg l hl ρ σ T = ρ*r)
    (hupper : ∀ p ∈ ramifiedPBWSupport l hl T,
      ramifiedWeight l ρ σ p ≤ ramifiedWeightDeg l hl ρ σ T) :
    ramifiedTopFacePolynomial l hl ρ σ T =
      ramifiedFacePolynomial l hl T r (ramifiedCutExponent l ρ σ) := by
  apply Polynomial.ext
  intro j
  let k := ramifiedCutExponent l ρ σ
  by_cases hj : j ∈ (ramifiedTopFacePolynomial l hl ρ σ T).support
  · obtain ⟨hjs, htop⟩ :=
      (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ T j).mp hj
    have hwt : ramifiedWeight l ρ σ
        (ramifiedPBWTopLaurent l hl T j,j) = ρ*r := by
      simpa [ramifiedWeight, hweight] using htop
    have hi := ramifiedCutWeight_point_index l ρ σ r
      (ramifiedPBWTopLaurent l hl T j) j hρ hdiv hwt
    rw [ramifiedTopFacePolynomial_coeff_of_mem_support l hl ρ σ T j hj,
      ramifiedFacePolynomial_coeff, ← hi]
    rfl
  · have hzero : (ramifiedTopFacePolynomial l hl ρ σ T).coeff j = 0 := by
      exact Polynomial.notMem_support_iff.mp hj
    rw [hzero, ramifiedFacePolynomial_coeff]
    by_contra hne
    have hmem : (r-k*(j : ℤ),j) ∈ ramifiedPBWSupport l hl T :=
      (ramifiedPBWSupport_mem_iff l hl T _ _).mpr (Ne.symm hne)
    have hwt : ramifiedWeight l ρ σ (r-k*(j : ℤ),j) = ρ*r := by
      have hk := ramifiedCutExponent_weight l ρ σ hdiv
      dsimp [ramifiedWeight, k]
      nlinarith [congrArg (fun z : ℤ => z*(j : ℤ)) hk]
    obtain ⟨hjs, _, htop⟩ := ramified_face_point_topLaurent_at_order
      l hl ρ σ hρ T (r-k*(j : ℤ),j) hmem (by rw [hweight]; exact hwt) hupper
    have htop' : ρ*ramifiedPBWTopLaurent l hl T j +
        (l : ℤ)*σ*(j : ℤ) = ramifiedWeightDeg l hl ρ σ T := by
      simpa [ramifiedWeight] using htop
    exact hj ((ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ T j).mpr
      ⟨hjs, htop'⟩)

/-- For an exact height-two pair, the common-base extraction and canonical
face identification supply the power-shape premise of the actual maximum-root
corner cut. The source's non-diagonal clause rules out grade zero. -/
theorem ramified_exact_pair_quadratic_corner_cut_preserves_endpoint
    (l d : ℕ) (hl : 0 < l) (hd : 0 < d)
    (ρ σ : ℤ) (hρ : 0 < ρ)
    (hρl : ρ = (l : ℤ)) (hsum : ρ + σ = 1)
    (P Q : ramifiedOperatorAlgebra l)
    (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (hcomm : P*Q-Q*P = 1)
    (hA : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hD : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hthreshold : 0 < ramifiedWeightDeg l hl ρ σ P +
      ramifiedWeightDeg l hl ρ σ Q - (l : ℤ)*(ρ+σ))
    (n : ℕ)
    (hratio : (ramifiedWeightDeg l hl ρ σ Q).toNat * d =
      (ramifiedWeightDeg l hl ρ σ P).toNat * n)
    (hcop : Nat.Coprime d n)
    (hpoint : ((d : ℤ),0) ∈ ramifiedPBWSupport l hl P)
    (hupper : ∀ u : ℤ, ∀ j : ℕ,
      (u,j) ∈ ramifiedPBWSupport l hl P →
        ramifiedWeight l ρ σ (u,j) ≤ ρ*(d : ℤ))
    (hdegree : (ramifiedTopFacePolynomial l hl ρ σ P).natDegree = 2*d)
    (hnondiagonal : (d : ℤ) - ramifiedCutExponent l ρ σ *
      (maxRootMult (ramifiedFacePolynomial l hl P (d : ℤ)
        (ramifiedCutExponent l ρ σ)) : ℤ) -
      (l : ℤ) * (maxRootMult (ramifiedFacePolynomial l hl P (d : ℤ)
        (ramifiedCutExponent l ρ σ)) : ℤ) ≠ 0) :
    ∃ c : ℂ,
      (ramifiedFacePolynomial l hl P (d : ℤ)
        (ramifiedCutExponent l ρ σ)).IsRoot c ∧
      (((d : ℤ)*((l : ℤ)*2-1),2*d) ∈
        ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c P)) := by
  have hdiv : ρ ∣ (l : ℤ) := by rw [hρl]
  have hwt : ramifiedWeightDeg l hl ρ σ P = ρ*(d : ℤ) := by
    apply ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ _ P
    · refine ⟨((d : ℤ),0),hpoint,?_⟩
      simp [ramifiedWeight]
    · intro p hp
      exact hupper p.1 p.2 hp
  have hfaceEq := ramifiedTopFacePolynomial_eq_cutFace
    l hl ρ σ hρ hdiv P (d : ℤ) hwt (by
      intro p hp
      rw [hwt]
      exact hupper p.1 p.2 hp)
  obtain ⟨ν, r, hν, hdeg, hface⟩ :=
    ramified_exact_pair_top_face_quadratic_power
      l hl ρ σ hρ (by omega) P Q hPne hQne hcomm hA hD
      hthreshold n d hd hratio hcop hdegree
  let M := maxRootMult (ramifiedFacePolynomial l hl P (d : ℤ)
    (ramifiedCutExponent l ρ σ))
  have hM : M = d ∨ M = 2*d := by
    dsimp [M]
    rw [← hfaceEq, hface, maxRootMult_C_mul _ _ hν]
    exact quadratic_power_maxRootMult_dichotomy r d hd hdeg
  have hk : ramifiedCutExponent l ρ σ = 1 - (l : ℤ) := by
    have hself : ((l : ℤ) / ρ) = 1 := by
      rw [hρl]
      exact Int.ediv_self (ne_of_gt (by simpa [hρl] using hρ))
    unfold ramifiedCutExponent
    rw [hself]
    omega
  have hgrade : (d : ℤ) - ramifiedCutExponent l ρ σ * (M : ℤ) -
      (l : ℤ) * (M : ℤ) < 0 := by
    change (d : ℤ) - ramifiedCutExponent l ρ σ * (M : ℤ) -
      (l : ℤ) * (M : ℤ) ≠ 0 at hnondiagonal
    have hgradeEq : (d : ℤ) - ramifiedCutExponent l ρ σ * (M : ℤ) -
        (l : ℤ) * (M : ℤ) = (d : ℤ) - (M : ℤ) := by
      rw [hk]
      ring
    rw [hgradeEq] at hnondiagonal ⊢
    have hMge : d ≤ M := by rcases hM with hm | hm <;> omega
    have hMgt : d < M := by
      by_contra hnot
      have he : M = d := by omega
      exact hnondiagonal (by rw [he]; ring)
    exact sub_neg.mpr (by exact_mod_cast hMgt)
  apply ramified_quadratic_corner_cut_preserves_endpoint
    l d hl hd ρ σ hρ hρl hsum P ν r hν hdeg
  · rw [← hfaceEq]
    exact hface
  · exact hpoint
  · exact hupper
  · exact hgrade

end Dixmier.Weyl
