/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedFacePolynomial

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Exact finite PBW expansion of an arbitrary ramified shear

The transformed coefficients are a finite sum of left coefficient
multiplications against the normal-order recurrence for each shifted
power. This is the operator-level finite-sum adapter for the eventual
leading-face translation theorem.
-/
namespace Dixmier.Weyl

/-- Normal-ordered finite coefficient sequence of a sheared PBW sum. -/
noncomputable def ramifiedShearPBWSum (l : ℕ)
    (h : LaurentPolynomial ℂ) (a : ℕ →₀ LaurentPolynomial ℂ) :
    ℕ →₀ LaurentPolynomial ℂ :=
  a.sum fun n f => ramifiedCoeffLeftLinear f (ramifiedShiftPBWPower l h n)

theorem ramifiedShearPBWSum_eval (l : ℕ)
    (h : LaurentPolynomial ℂ) (a : ℕ →₀ LaurentPolynomial ℂ) :
    ramifiedNormalEval l (ramifiedShearPBWSum l h a) =
      ramifiedShiftEval l h a := by
  classical
  unfold ramifiedShearPBWSum ramifiedShiftEval
  rw [← ramifiedNormalEvalLinear_apply]
  simp only [Finsupp.sum, map_sum]
  simp only [ramifiedNormalEvalLinear_apply,
    ramifiedNormalEval_coeff_left, ramifiedShiftPBWPower_eval]

/-- This formula applies to an arbitrary finite operator, with no bound
on its PBW order, Laurent support, or the number of occupied grades. -/
theorem ramifiedCutAut_pbwCoeffs_sum (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (c : ℂ) (T : ramifiedOperatorAlgebra l) :
    ramifiedPBWCoeffs l hl (ramifiedCutAut l hl ρ σ c T) =
      ramifiedShearPBWSum l (ramifiedCutShift l ρ σ c)
        (ramifiedPBWCoeffs l hl T) := by
  apply ramifiedPBWCoeffs_eq_of_eval
  exact (ramifiedShearPBWSum_eval l _ _).trans rfl

/-- Every transformed PBW coefficient is an explicit finite sum over
the original derivative orders. -/
theorem ramifiedCutAut_pbwCoeff_finset (l : ℕ) (hl : 0 < l)
    (ρ σ : ℤ) (c : ℂ) (T : ramifiedOperatorAlgebra l)
    (i : ℤ) (j : ℕ) :
    ramifiedPBWCoeff l hl (ramifiedCutAut l hl ρ σ c T) i j =
      ∑ n ∈ (ramifiedPBWCoeffs l hl T).support,
        (((ramifiedPBWCoeffs l hl T) n) *
          (ramifiedShiftPBWPower l (ramifiedCutShift l ρ σ c) n j)).coeff i := by
  rw [ramifiedPBWCoeff, ramifiedCutAut_pbwCoeffs_sum]
  simp only [ramifiedShearPBWSum, Finsupp.sum,
    Finsupp.finsetSum_apply, ramifiedCoeffLeftLinear_apply,
    AddMonoidAlgebra.coeff_sum]

/-- At the sum of two upper Laurent exponents, only the two edge
coefficients can contribute to a product. -/
theorem LaurentUpper_mul_edge (f g : LaurentPolynomial ℂ)
    (B C : ℤ) (hf : LaurentUpper f B) (hg : LaurentUpper g C) :
    (f * g).coeff (B+C) = f.coeff B * g.coeff C := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
  have hsingle :
      (∑ u ∈ f.coeff.support, f.coeff u * g.coeff (-u + (B+C))) =
        f.coeff B * g.coeff (-B + (B+C)) := by
    apply Finset.sum_eq_single B
    · intro u hu hne
      have huB := hf u hu
      have hlt : u < B := by omega
      have hzero : g.coeff (-u + (B+C)) = 0 :=
        LaurentUpper_coeff_zero_above g C (-u + (B+C)) hg (by omega)
      simp [hzero]
    · intro hnot
      have hz : f.coeff B = 0 := Finsupp.notMem_support_iff.mp hnot
      simp [hz]
  simpa only [show -B + (B+C) = C by omega] using hsingle

theorem LaurentUpper_mul (f g : LaurentPolynomial ℂ)
    (B C : ℤ) (hf : LaurentUpper f B) (hg : LaurentUpper g C) :
    LaurentUpper (f*g) (B+C) := by
  intro i hi
  have hmul := AddMonoidAlgebra.support_coeff_mul_subset f g hi
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.mem_add.mp hmul
  have huB := hf u hu
  have hvC := hg v hv
  omega

theorem LaurentUpper_finset_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → LaurentPolynomial ℂ) (B : ℤ)
    (hf : ∀ a ∈ s, LaurentUpper (f a) B) :
    LaurentUpper (∑ a ∈ s, f a) B := by
  classical
  induction s using Finset.induction with
  | empty => simpa using LaurentUpper_zero B
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply LaurentUpper_add
      · exact hf a (Finset.mem_insert_self a s)
      · exact ih (by
          intro b hb
          exact hf b (Finset.mem_insert_of_mem hb))

/-- Exact coefficient on a proposed weighted edge of an arbitrary
finite PBW operator after shear. The upper-bound hypothesis is the
support condition that every original monomial has weight at most
`ρr`; no assertion about the transformed maximum is needed here. -/
theorem ramifiedCutAut_edgeCoeff_finset (l : ℕ) (hl : 0 < l)
    (ρ σ r : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (c : ℂ)
    (T : ramifiedOperatorAlgebra l)
    (hupper : ∀ n : ℕ,
      LaurentUpper ((ramifiedPBWCoeffs l hl T) n)
        (r - ramifiedCutExponent l ρ σ * (n : ℤ)))
    (j : ℕ) :
    ramifiedPBWCoeff l hl (ramifiedCutAut l hl ρ σ c T)
      (r - ramifiedCutExponent l ρ σ * (j : ℤ)) j =
      ∑ n ∈ (ramifiedPBWCoeffs l hl T).support,
        ramifiedPBWCoeff l hl T
          (r - ramifiedCutExponent l ρ σ * (n : ℤ)) n *
          ((Nat.choose n j : ℂ) * c^(n-j)) := by
  rw [ramifiedCutAut_pbwCoeff_finset]
  apply Finset.sum_congr rfl
  intro n hn
  let k := ramifiedCutExponent l ρ σ
  have hidx : (r - k * (n : ℤ)) +
      (((n : ℤ) - (j : ℤ)) * k) = r - k * (j : ℤ) := by ring
  rw [← hidx]
  have hmul := LaurentUpper_mul_edge
    ((ramifiedPBWCoeffs l hl T) n)
    (ramifiedShiftPBWPower l (ramifiedCutShift l ρ σ c) n j)
    (r - k * (n : ℤ)) (((n : ℤ) - (j : ℤ)) * k)
    (hupper n)
    (ramifiedCutPower_upper l hl ρ σ hρ hdiv hpos c n j)
  rw [hmul]
  change _ = ramifiedPBWCoeff l hl T (r - k * (n : ℤ)) n *
    ((Nat.choose n j : ℂ) * c^(n-j))
  rw [ramifiedPBWCoeff]
  congr 1
  exact ramifiedCutEdgeCoeff_binomial l hl ρ σ hρ hdiv hpos c n j

/-- Coefficients of polynomial translation in a form matching the
finite PBW edge sum. -/
theorem polynomial_translate_coeff_finset (p : Polynomial ℂ)
    (c : ℂ) (j : ℕ) :
    (p.comp (Polynomial.X + Polynomial.C c)).coeff j =
      ∑ n ∈ p.support, p.coeff n *
        ((Nat.choose n j : ℂ) * c^(n-j)) := by
  rw [Polynomial.comp_eq_sum_left]
  simp only [Polynomial.sum,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem ramifiedFacePolynomial_support_subset (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (r k : ℤ) :
    (ramifiedFacePolynomial l hl T r k).support ⊆
      (ramifiedPBWCoeffs l hl T).support := by
  intro n hn
  by_contra hnot
  have hz : (ramifiedPBWCoeffs l hl T) n = 0 :=
    Finsupp.notMem_support_iff.mp hnot
  have hnz : (ramifiedFacePolynomial l hl T r k).coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hn
  rw [ramifiedFacePolynomial_coeff] at hnz
  simp [ramifiedPBWCoeff, hz] at hnz

/-- The transformed edge of any finite operator is exactly the
commutative translation of its original scalar face, coefficient by
coefficient. This is the arbitrary-operator part of G13 Proposition 5.1
under the stated upper-weight hypothesis. -/
theorem ramifiedCutAut_facePolynomial_eq_translate (l : ℕ)
    (hl : 0 < l) (ρ σ r : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (c : ℂ)
    (T : ramifiedOperatorAlgebra l)
    (hupper : ∀ n : ℕ,
      LaurentUpper ((ramifiedPBWCoeffs l hl T) n)
        (r - ramifiedCutExponent l ρ σ * (n : ℤ))) :
    ramifiedFacePolynomial l hl
      (ramifiedCutAut l hl ρ σ c T) r
      (ramifiedCutExponent l ρ σ) =
        (ramifiedFacePolynomial l hl T r
          (ramifiedCutExponent l ρ σ)).comp
            (Polynomial.X + Polynomial.C c) := by
  apply Polynomial.ext
  intro j
  rw [ramifiedFacePolynomial_coeff,
    ramifiedCutAut_edgeCoeff_finset l hl ρ σ r hρ hdiv hpos c T hupper j,
    polynomial_translate_coeff_finset]
  let p := ramifiedFacePolynomial l hl T r
    (ramifiedCutExponent l ρ σ)
  have hsub : p.support ⊆ (ramifiedPBWCoeffs l hl T).support :=
    ramifiedFacePolynomial_support_subset l hl T r _
  have hsum :
      (∑ n ∈ (ramifiedPBWCoeffs l hl T).support,
        p.coeff n * ((Nat.choose n j : ℂ) * c^(n-j))) =
      ∑ n ∈ p.support,
        p.coeff n * ((Nat.choose n j : ℂ) * c^(n-j)) := by
    symm
    apply Finset.sum_subset hsub
    intro n hn hnnot
    have hz : p.coeff n = 0 := by
      simpa using (Polynomial.mem_support_iff.not).mp hnnot
    simp [hz]
  simpa only [p, ramifiedFacePolynomial_coeff] using hsum

/-- A global Newton half-plane bound supplies exactly the per-order
Laurent bounds used by the finite-sum calculation. -/
theorem ramifiedCut_upper_of_weight_upper (l : ℕ) (hl : 0 < l)
    (ρ σ r : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (T : ramifiedOperatorAlgebra l)
    (hweight : ∀ i : ℤ, ∀ j : ℕ,
      (i,j) ∈ ramifiedPBWSupport l hl T →
        ramifiedWeight l ρ σ (i,j) ≤ ρ*r) :
    ∀ n : ℕ, LaurentUpper ((ramifiedPBWCoeffs l hl T) n)
      (r - ramifiedCutExponent l ρ σ * (n : ℤ)) := by
  intro n i hi
  have hmem : (i,n) ∈ ramifiedPBWSupport l hl T :=
    (ramifiedPBWSupport_mem_iff l hl T i n).mpr
      (Finsupp.mem_support_iff.mp hi)
  have hw := hweight i n hmem
  have hk := ramifiedCutExponent_weight l ρ σ hdiv
  dsimp [ramifiedWeight] at hw
  nlinarith [congrArg (fun x : ℤ => x * (n : ℤ)) hk]

/-- The exact shear preserves the upper half-plane bound at every
derivative order, uniformly over the finite PBW support. -/
theorem ramifiedCutAut_LaurentUpper (l : ℕ) (hl : 0 < l)
    (ρ σ r : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (c : ℂ)
    (T : ramifiedOperatorAlgebra l)
    (hupper : ∀ n : ℕ,
      LaurentUpper ((ramifiedPBWCoeffs l hl T) n)
        (r - ramifiedCutExponent l ρ σ * (n : ℤ))) :
    ∀ j : ℕ,
      LaurentUpper
        ((ramifiedPBWCoeffs l hl
          (ramifiedCutAut l hl ρ σ c T)) j)
        (r - ramifiedCutExponent l ρ σ * (j : ℤ)) := by
  intro j
  rw [ramifiedCutAut_pbwCoeffs_sum]
  change LaurentUpper
    ((∑ n ∈ (ramifiedPBWCoeffs l hl T).support,
      ramifiedCoeffLeftLinear ((ramifiedPBWCoeffs l hl T) n)
        (ramifiedShiftPBWPower l (ramifiedCutShift l ρ σ c) n)) j)
    (r - ramifiedCutExponent l ρ σ * (j : ℤ))
  simp only [Finsupp.finsetSum_apply, ramifiedCoeffLeftLinear_apply]
  apply LaurentUpper_finset_sum
  intro n hn
  have hm := LaurentUpper_mul
    ((ramifiedPBWCoeffs l hl T) n)
    (ramifiedShiftPBWPower l (ramifiedCutShift l ρ σ c) n j)
    (r - ramifiedCutExponent l ρ σ * (n : ℤ))
    (((n : ℤ) - (j : ℤ)) * ramifiedCutExponent l ρ σ)
    (hupper n)
    (ramifiedCutPower_upper l hl ρ σ hρ hdiv hpos c n j)
  convert hm using 1
  ring

theorem ramifiedCutAut_weight_upper (l : ℕ) (hl : 0 < l)
    (ρ σ r : ℤ) (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (c : ℂ)
    (T : ramifiedOperatorAlgebra l)
    (hweight : ∀ i : ℤ, ∀ j : ℕ,
      (i,j) ∈ ramifiedPBWSupport l hl T →
        ramifiedWeight l ρ σ (i,j) ≤ ρ*r) :
    ∀ i : ℤ, ∀ j : ℕ,
      (i,j) ∈ ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c T) →
        ramifiedWeight l ρ σ (i,j) ≤ ρ*r := by
  have hu := ramifiedCutAut_LaurentUpper l hl ρ σ r
    hρ hdiv hpos c T
    (ramifiedCut_upper_of_weight_upper l hl ρ σ r hρ hdiv T hweight)
  intro i j hij
  have hi : i ∈ ((ramifiedPBWCoeffs l hl
      (ramifiedCutAut l hl ρ σ c T)) j).coeff.support :=
    Finsupp.mem_support_iff.mpr
      ((ramifiedPBWSupport_mem_iff l hl _ i j).mp hij)
  have hle := hu j i hi
  have hk := ramifiedCutExponent_weight l ρ σ hdiv
  dsimp [ramifiedWeight]
  nlinarith [congrArg (fun x : ℤ => x * (j : ℤ)) hk]

/-- Exact face translation stated directly in terms of a Newton
half-plane bound on the original operator. -/
theorem ramifiedCutAut_face_eq_translate_of_weight_upper (l : ℕ)
    (hl : 0 < l) (ρ σ r : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (c : ℂ)
    (T : ramifiedOperatorAlgebra l)
    (hweight : ∀ i : ℤ, ∀ j : ℕ,
      (i,j) ∈ ramifiedPBWSupport l hl T →
        ramifiedWeight l ρ σ (i,j) ≤ ρ*r) :
    ramifiedFacePolynomial l hl
      (ramifiedCutAut l hl ρ σ c T) r
      (ramifiedCutExponent l ρ σ) =
        (ramifiedFacePolynomial l hl T r
          (ramifiedCutExponent l ρ σ)).comp
            (Polynomial.X + Polynomial.C c) := by
  exact ramifiedCutAut_facePolynomial_eq_translate l hl ρ σ r
    hρ hdiv hpos c T
    (ramifiedCut_upper_of_weight_upper l hl ρ σ r hρ hdiv T hweight)

/-- A nonempty top face remains nonempty after the shear. This does
not yet assert that no new point lies above it; that support bound is
the remaining half of full weight preservation. -/
theorem ramifiedCutAut_face_nonempty_of_weight_point (l : ℕ)
    (hl : 0 < l) (ρ σ r i : ℤ) (j : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (c : ℂ)
    (T : ramifiedOperatorAlgebra l)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl T)
    (htop : ramifiedWeight l ρ σ (i,j) = ρ*r)
    (hweight : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl T →
        ramifiedWeight l ρ σ (u,n) ≤ ρ*r) :
    ∃ u : ℤ, ∃ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c T) ∧
      ramifiedWeight l ρ σ (u,n) = ρ*r := by
  let U := ramifiedCutAut l hl ρ σ c T
  let k := ramifiedCutExponent l ρ σ
  have hnonzero : ramifiedFacePolynomial l hl U r k ≠ 0 := by
    rw [ramifiedCutAut_face_eq_translate_of_weight_upper l hl ρ σ r
      hρ hdiv hpos c T hweight]
    exact ramifiedCutFace_translate_ne_zero_of_weight_point l hl T
      ρ σ r i j c hρ hdiv hmem htop
  obtain ⟨n,hn⟩ := Polynomial.support_nonempty.mpr hnonzero
  refine ⟨r-k*(n : ℤ), n, ?_, ?_⟩
  · apply (ramifiedPBWSupport_mem_iff l hl U _ n).mpr
    have hcoef : (ramifiedFacePolynomial l hl U r k).coeff n ≠ 0 :=
      Polynomial.mem_support_iff.mp hn
    simpa [ramifiedFacePolynomial_coeff] using hcoef
  · have hk := ramifiedCutExponent_weight l ρ σ hdiv
    dsimp [ramifiedWeight]
    nlinarith [congrArg (fun x : ℤ => x * (n : ℤ)) hk]

/-- Exact maximum-weight preservation for an arbitrary nonzero finite
ramified operator with an occupied face at `ρr`. The face itself is
transformed by `ramifiedCutAut_face_eq_translate_of_weight_upper`. -/
theorem ramifiedCutAut_preserves_max_weight_data (l : ℕ)
    (hl : 0 < l) (ρ σ r i : ℤ) (j : ℕ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l : ℤ))
    (hpos : 0 < ρ + σ) (c : ℂ)
    (T : ramifiedOperatorAlgebra l)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl T)
    (htop : ramifiedWeight l ρ σ (i,j) = ρ*r)
    (hweight : ∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl T →
        ramifiedWeight l ρ σ (u,n) ≤ ρ*r) :
    (∃ u : ℤ, ∃ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c T) ∧
      ramifiedWeight l ρ σ (u,n) = ρ*r) ∧
    (∀ u : ℤ, ∀ n : ℕ,
      (u,n) ∈ ramifiedPBWSupport l hl
        (ramifiedCutAut l hl ρ σ c T) →
      ramifiedWeight l ρ σ (u,n) ≤ ρ*r) := by
  exact ⟨ramifiedCutAut_face_nonempty_of_weight_point l hl
    ρ σ r i j hρ hdiv hpos c T hmem htop hweight,
    ramifiedCutAut_weight_upper l hl ρ σ r
      hρ hdiv hpos c T hweight⟩

end Dixmier.Weyl
