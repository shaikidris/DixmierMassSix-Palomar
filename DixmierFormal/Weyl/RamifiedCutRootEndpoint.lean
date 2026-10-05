/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedShearPBWSum
public import DixmierFormal.Weyl.Defs
public import DixmierFormal.Scalar.GeneralRootDegree
public import Mathlib.Algebra.Polynomial.RingDivision

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Root multiplicity selects the new starting point

After the exact shear, the smallest derivative exponent on the old
maximal face equals the multiplicity of the chosen root of the original
face polynomial. This is the local endpoint calculation behind G13
Proposition 5.3(6), before constructing its new supporting direction.
-/
namespace Dixmier.Weyl

theorem exists_rootMultiplicity_eq_maxRootMult (p : Polynomial ℂ)
    (hp : 0 < p.natDegree) :
    ∃ c : ℂ, p.IsRoot c ∧
      p.rootMultiplicity c = maxRootMult p := by
  obtain ⟨c,hc,hmax⟩ := Dixmier.General.exists_max_rootMultiplicity p hp
  refine ⟨c,hc,?_⟩
  have hpne : p ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hp
  have hmem : c ∈ p.roots.toFinset := by
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hpne).mpr hc)
  apply le_antisymm
  · exact Finset.le_sup (f := fun z : ℂ => p.rootMultiplicity z) hmem
  · change p.roots.toFinset.sup (fun z => p.rootMultiplicity z) ≤ _
    apply Finset.sup_le
    intro z hz
    exact hmax z ((Polynomial.mem_roots hpne).mp
      (Multiset.mem_toFinset.mp hz))

/-- Two distinct PBW points on one positive-`ρ` face make its scalar
face polynomial nonconstant. This is the ramified support form of the
source direction premise. -/
theorem ramifiedFacePolynomial_natDegree_pos_of_two_points
    (l : ℕ) (hl : 0 < l) (ρ σ r i₁ i₂ : ℤ)
    (j₁ j₂ : ℕ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (T : ramifiedOperatorAlgebra l)
    (h₁ : (i₁,j₁) ∈ ramifiedPBWSupport l hl T)
    (h₂ : (i₂,j₂) ∈ ramifiedPBWSupport l hl T)
    (hw₁ : ramifiedWeight l ρ σ (i₁,j₁) = ρ*r)
    (hw₂ : ramifiedWeight l ρ σ (i₂,j₂) = ρ*r)
    (hdist : (i₁,j₁) ≠ (i₂,j₂)) :
    0 < (ramifiedFacePolynomial l hl T r
      (ramifiedCutExponent l ρ σ)).natDegree := by
  have hi₁ := ramifiedCutWeight_point_index l ρ σ r i₁ j₁ hρ hdiv hw₁
  have hi₂ := ramifiedCutWeight_point_index l ρ σ r i₂ j₂ hρ hdiv hw₂
  have hneq : j₁ ≠ j₂ := by
    intro heq
    apply hdist
    subst j₂
    rw [hi₁, hi₂]
  have hnonzero (i : ℤ) (j : ℕ)
      (hij : (i,j) ∈ ramifiedPBWSupport l hl T)
      (hijw : ramifiedWeight l ρ σ (i,j) = ρ*r) :
      (ramifiedFacePolynomial l hl T r
        (ramifiedCutExponent l ρ σ)).coeff j ≠ 0 := by
    rw [ramifiedFacePolynomial_coeff,
      ← ramifiedCutWeight_point_index l ρ σ r i j hρ hdiv hijw]
    exact (ramifiedPBWSupport_mem_iff l hl T i j).mp hij
  have hdeg₁ := Polynomial.le_natDegree_of_ne_zero
    (hnonzero i₁ j₁ h₁ hw₁)
  have hdeg₂ := Polynomial.le_natDegree_of_ne_zero
    (hnonzero i₂ j₂ h₂ hw₂)
  omega

/-- A chosen root of multiplicity `m` gives the first occupied point
of the sheared old face at derivative exponent `m`. All other points
of that face have derivative exponent at least `m`. -/
theorem ramifiedCutAut_root_start_on_old_face (l : ℕ) (hl : 0 < l)
    (ρ σ r i : ℤ) (j : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (c : ℂ)
    (T : ramifiedOperatorAlgebra l)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl T)
    (htop : ramifiedWeight l ρ σ (i,j) = ρ*r)
    (hweight : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl T →
        ramifiedWeight l ρ σ (u,n) ≤ ρ*r) :
    let k := ramifiedCutExponent l ρ σ
    let m := Polynomial.rootMultiplicity c
      (ramifiedFacePolynomial l hl T r k)
    ((r-k*(m : ℤ),m) ∈ ramifiedPBWSupport l hl
      (ramifiedCutAut l hl ρ σ c T) ∧
      ramifiedWeight l ρ σ (r-k*(m : ℤ),m) = ρ*r) ∧
    (∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c T) →
      ramifiedWeight l ρ σ (u,n) = ρ*r → m ≤ n) := by
  dsimp only
  let k := ramifiedCutExponent l ρ σ
  let p := ramifiedFacePolynomial l hl T r k
  let U := ramifiedCutAut l hl ρ σ c T
  let q := ramifiedFacePolynomial l hl U r k
  let m := Polynomial.rootMultiplicity c p
  have hpne : p ≠ 0 :=
    ramifiedFacePolynomial_ne_zero_of_weight_point l hl T
      ρ σ r i j hρ hdiv hmem htop
  have htrans : q = p.comp (Polynomial.X + Polynomial.C c) :=
    ramifiedCutAut_face_eq_translate_of_weight_upper l hl ρ σ r
      hρ hdiv hpos c T hweight
  have hqne : q ≠ 0 := by
    rw [htrans]
    exact Polynomial.comp_X_add_C_ne_zero_iff.mpr hpne
  have hm : m = q.natTrailingDegree := by
    change p.rootMultiplicity c = q.natTrailingDegree
    rw [Polynomial.rootMultiplicity_eq_natTrailingDegree, htrans]
  have hmin : m ∈ q.support := by
    rw [hm]
    exact Polynomial.natTrailingDegree_mem_support_of_nonzero hqne
  have hk := ramifiedCutExponent_weight l ρ σ hdiv
  constructor
  · constructor
    · apply (ramifiedPBWSupport_mem_iff l hl U _ m).mpr
      have hc : q.coeff m ≠ 0 := Polynomial.mem_support_iff.mp hmin
      simpa [q, ramifiedFacePolynomial_coeff] using hc
    · dsimp [ramifiedWeight]
      nlinarith [congrArg (fun x : ℤ => x * (m : ℤ)) hk]
  · intro u n hun hwn
    have hu : u = r-k*(n : ℤ) :=
      ramifiedCutWeight_point_index l ρ σ r u n hρ hdiv hwn
    have hcn : q.coeff n ≠ 0 := by
      rw [ramifiedFacePolynomial_coeff]
      rw [← hu]
      exact (ramifiedPBWSupport_mem_iff l hl U u n).mp hun
    have hle := Polynomial.natTrailingDegree_le_of_ne_zero hcn
    rw [← hm] at hle
    exact hle

/-- On a positive-weight-sum face, the root-selected point has the
largest scaled grade `i-lj` among all sheared points of that face.
This identifies the source's `st` endpoint in the PBW lattice. -/
theorem ramifiedCutAut_root_start_max_grade (l : ℕ) (hl : 0 < l)
    (ρ σ r i : ℤ) (j : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (c : ℂ)
    (T : ramifiedOperatorAlgebra l)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl T)
    (htop : ramifiedWeight l ρ σ (i,j) = ρ*r)
    (hweight : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl T →
        ramifiedWeight l ρ σ (u,n) ≤ ρ*r)
    (u : ℤ) (n : ℕ)
    (hun : (u,n) ∈ ramifiedPBWSupport l hl
      (ramifiedCutAut l hl ρ σ c T))
    (hwn : ramifiedWeight l ρ σ (u,n) = ρ*r) :
    let k := ramifiedCutExponent l ρ σ
    let m := Polynomial.rootMultiplicity c
      (ramifiedFacePolynomial l hl T r k)
    u - (l : ℤ)*(n : ℤ) ≤
      (r-k*(m : ℤ)) - (l : ℤ)*(m : ℤ) := by
  dsimp only
  let k := ramifiedCutExponent l ρ σ
  let m := Polynomial.rootMultiplicity c
    (ramifiedFacePolynomial l hl T r k)
  have hs := ramifiedCutAut_root_start_on_old_face l hl
    ρ σ r i j hρ hdiv hpos c T hmem htop hweight
  have hmn : m ≤ n := hs.2 u n hun hwn
  have hu : u = r-k*(n : ℤ) :=
    ramifiedCutWeight_point_index l ρ σ r u n hρ hdiv hwn
  have hkl : 0 < k + (l : ℤ) := by
    have hk := ramifiedCutExponent_gt_neg_index l hl ρ σ hρ hdiv hpos
    dsimp [k]
    omega
  rw [hu]
  have hmnz : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
  nlinarith

/-- Choosing a root of maximum multiplicity gives exactly the
source's maximal-root endpoint on the sheared old face. The
nonconstant-face premise is explicit; deriving it from the source's
direction hypotheses belongs to the polynomial-to-ramified adapter. -/
theorem ramifiedCutAut_exists_maxRoot_start (l : ℕ) (hl : 0 < l)
    (ρ σ r i : ℤ) (j : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ)
    (T : ramifiedOperatorAlgebra l)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl T)
    (htop : ramifiedWeight l ρ σ (i,j) = ρ*r)
    (hweight : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl T →
        ramifiedWeight l ρ σ (u,n) ≤ ρ*r)
    (hdegree : 0 < (ramifiedFacePolynomial l hl T r
      (ramifiedCutExponent l ρ σ)).natDegree) :
    ∃ c : ℂ,
      (ramifiedFacePolynomial l hl T r
        (ramifiedCutExponent l ρ σ)).IsRoot c ∧
      (ramifiedFacePolynomial l hl T r
        (ramifiedCutExponent l ρ σ)).rootMultiplicity c =
          maxRootMult (ramifiedFacePolynomial l hl T r
            (ramifiedCutExponent l ρ σ)) ∧
      ((r - ramifiedCutExponent l ρ σ *
          (maxRootMult (ramifiedFacePolynomial l hl T r
            (ramifiedCutExponent l ρ σ)) : ℤ),
         maxRootMult (ramifiedFacePolynomial l hl T r
            (ramifiedCutExponent l ρ σ))) ∈
        ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c T)) := by
  let p := ramifiedFacePolynomial l hl T r
    (ramifiedCutExponent l ρ σ)
  obtain ⟨c,hroot,hm⟩ := exists_rootMultiplicity_eq_maxRootMult p hdegree
  refine ⟨c,hroot,hm,?_⟩
  have hs := (ramifiedCutAut_root_start_on_old_face l hl
    ρ σ r i j hρ hdiv hpos c T hmem htop hweight).1.1
  change (r - ramifiedCutExponent l ρ σ *
      (p.rootMultiplicity c : ℤ),p.rootMultiplicity c) ∈
    ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c T) at hs
  rw [hm] at hs
  exact hs

/-- Maximum-root selection from the two occupied points that define a
genuine face; no separate polynomial-degree premise is required. -/
theorem ramifiedCutAut_exists_maxRoot_start_of_two_points
    (l : ℕ) (hl : 0 < l) (ρ σ r i₁ i₂ : ℤ) (j₁ j₂ : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ)
    (T : ramifiedOperatorAlgebra l)
    (h₁ : (i₁,j₁) ∈ ramifiedPBWSupport l hl T)
    (h₂ : (i₂,j₂) ∈ ramifiedPBWSupport l hl T)
    (hw₁ : ramifiedWeight l ρ σ (i₁,j₁) = ρ*r)
    (hw₂ : ramifiedWeight l ρ σ (i₂,j₂) = ρ*r)
    (hdist : (i₁,j₁) ≠ (i₂,j₂))
    (hweight : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl T →
        ramifiedWeight l ρ σ (u,n) ≤ ρ*r) :
    ∃ c : ℂ,
      (ramifiedFacePolynomial l hl T r
        (ramifiedCutExponent l ρ σ)).IsRoot c ∧
      (ramifiedFacePolynomial l hl T r
        (ramifiedCutExponent l ρ σ)).rootMultiplicity c =
          maxRootMult (ramifiedFacePolynomial l hl T r
            (ramifiedCutExponent l ρ σ)) ∧
      ((r - ramifiedCutExponent l ρ σ *
          (maxRootMult (ramifiedFacePolynomial l hl T r
            (ramifiedCutExponent l ρ σ)) : ℤ),
         maxRootMult (ramifiedFacePolynomial l hl T r
            (ramifiedCutExponent l ρ σ))) ∈
        ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c T)) := by
  have hd := ramifiedFacePolynomial_natDegree_pos_of_two_points
    l hl ρ σ r i₁ i₂ j₁ j₂ hρ hdiv T
    h₁ h₂ hw₁ hw₂ hdist
  exact ramifiedCutAut_exists_maxRoot_start l hl
    ρ σ r i₁ j₁ hρ hdiv hpos T h₁ hw₁ hweight hd

end Dixmier.Weyl
