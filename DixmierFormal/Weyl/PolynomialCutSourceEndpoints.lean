/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedOneSidedFirstSlope

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Source-selected endpoints for a maximum-root cut

The common-root multiplicity ratio determines the determinant of the
two explicitly occupied sheared old-face points. This is the endpoint
alignment consumed by the first-slope argument.
-/

namespace Dixmier.Weyl

theorem cut_oldFace_endpoints_parallel
    (l : ℕ) (ρ σ wP wQ : ℤ) (M N : ℕ)
    (hP : 0 < wP) (hQ : 0 < wQ)
    (hratio : wQ.toNat * M = wP.toNat * N) :
    let k := ramifiedCutExponent l ρ σ
    let rP := ((l : ℤ) / ρ) * wP
    let rQ := ((l : ℤ) / ρ) * wQ
    (M : ℤ) * (rQ-k*(N : ℤ)) =
      (N : ℤ) * (rP-k*(M : ℤ)) := by
  have hcastP : ((wP.toNat : ℕ) : ℤ) = wP :=
    Int.toNat_of_nonneg (le_of_lt hP)
  have hcastQ : ((wQ.toNat : ℕ) : ℤ) = wQ :=
    Int.toNat_of_nonneg (le_of_lt hQ)
  have hratioZ := congrArg (fun a : ℕ => (a : ℤ)) hratio
  push_cast at hratioZ
  rw [hcastP,hcastQ] at hratioZ
  dsimp
  linear_combination ((l : ℤ) / ρ) * hratioZ

/-- The chosen maximum root simultaneously supplies occupied old-face
points of both exact operators, parallelism of those points, and the
root-order bounds from a reduced nonintegral weight ratio. -/
theorem exactPair_maxRoot_cut_parallel_endpoints_and_orders
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hP : 0 < vDeg ρ σ P.1) (hQ : 0 < vDeg ρ σ Q.1)
    (hdirP : InDir ρ σ P.1) (hdirQ : InDir ρ σ Q.1)
    (hQP : Q * P - P * Q = 1)
    (hsum : ρ + σ < vDeg ρ σ P.1 + vDeg ρ σ Q.1)
    (d n : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n)
    (hweight : vDeg ρ σ Q.1 * (d : ℤ) =
      vDeg ρ σ P.1 * (n : ℤ))
    (hcop : Nat.Coprime n d) :
    let rP := ((l : ℤ) / ρ) * vDeg ρ σ P.1
    let rQ := ((l : ℤ) / ρ) * vDeg ρ σ Q.1
    let k := ramifiedCutExponent l ρ σ
    ∃ c : ℂ, ∃ M N : ℕ,
      (cutPoly ρ σ P.1).IsRoot c ∧
      M = maxRootMult (cutPoly ρ σ P.1) ∧
      M = (cutPoly ρ σ P.1).rootMultiplicity c ∧
      N = (cutPoly ρ σ Q.1).rootMultiplicity c ∧
      2 ≤ M ∧ 2 ≤ N ∧
      (rP-k*(M : ℤ),M) ∈ ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) ∧
      (rQ-k*(N : ℤ),N) ∈ ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q)) ∧
      (M : ℤ) * (rQ-k*(N : ℤ)) =
        (N : ℤ) * (rP-k*(M : ℤ)) ∧
      ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q) *
          ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P) -
        ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P) *
          ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l Q) = 1 := by
  obtain ⟨c,hrootP,hmP,hrootQ,hratio,hpointP,hpointQ,hexact⟩ :=
    exactPair_maxRoot_cut_mate_oldFace_endpoints
      l hl P Q ρ σ hdir hρ hdiv hP hQ hdirP hdirQ hQP hsum
  let M := (cutPoly ρ σ P.1).rootMultiplicity c
  let N := (cutPoly ρ σ Q.1).rootMultiplicity c
  have hpne : cutPoly ρ σ P.1 ≠ 0 :=
    cutPoly_ne_zero_of_InDir P ρ σ hρ hdirP
  have hqne : cutPoly ρ σ Q.1 ≠ 0 :=
    cutPoly_ne_zero_of_InDir Q ρ σ hρ hdirQ
  have hMpos : 0 < M := (Polynomial.rootMultiplicity_pos hpne).mpr hrootP
  have hNpos : 0 < N := (Polynomial.rootMultiplicity_pos hqne).mpr hrootQ
  have hratioM : (vDeg ρ σ Q.1).toNat * M =
      (vDeg ρ σ P.1).toNat * N := by
    simpa [M,N,hmP] using hratio
  have hratioZ : vDeg ρ σ Q.1 * (M : ℤ) =
      vDeg ρ σ P.1 * (N : ℤ) := by
    have h := congrArg (fun a : ℕ => (a : ℤ)) hratioM
    push_cast at h
    simpa [Int.toNat_of_nonneg (le_of_lt hP),
      Int.toNat_of_nonneg (le_of_lt hQ)] using h
  obtain ⟨hdM,hnN⟩ := reduced_ratio_root_orders_ge
    (vDeg ρ σ P.1) (vDeg ρ σ Q.1) d n M N
    hP hweight hratioZ hcop hMpos hNpos
  have hparallel := cut_oldFace_endpoints_parallel l ρ σ
    (vDeg ρ σ P.1) (vDeg ρ σ Q.1) M N hP hQ hratioM
  have hpointPM : (((l : ℤ) / ρ) * vDeg ρ σ P.1 -
        ramifiedCutExponent l ρ σ * (M : ℤ),M) ∈
      ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) := by
    simpa [M,hmP] using hpointP
  exact ⟨c,M,N,hrootP,hmP,rfl,rfl,hd.trans hdM,hn.trans hnN,
    hpointPM,hpointQ,hparallel,hexact⟩

end Dixmier.Weyl
