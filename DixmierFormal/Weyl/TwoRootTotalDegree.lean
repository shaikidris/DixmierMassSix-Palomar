/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.TwoRootTotal
public import DixmierFormal.Weyl.CrossingFaceWeight
public import DixmierFormal.Weyl.DescentTermination

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Total-degree equality and the two-root mass contradiction

The weight `(1,1)` agrees with PBW total degree. The nonzero two-root face
therefore has operator degree `u+v`; the GGV gcd bound and the sparse cut
then contradict mass at most six. The GGV input remains explicit.
-/

namespace Dixmier.Weyl
open MvPolynomial Polynomial

theorem weight_one_one_eq_degree (d : Fin 2 →₀ ℕ) :
    Finsupp.weight (wt 1 1) d = (d.sum fun _ e => e : ℕ) := by
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
  have hsum : (expo i j).sum (fun _ e => e) = i + j := by
    rw [Finsupp.sum_fintype (expo i j) (fun _ e => e) (by simp)]
    simp [Fin.sum_univ_two, expo]
  rw [expo_weight]
  rw [hsum]
  norm_num

theorem twoRoot_vDeg_eq_exponent_sum
    (T : A1 ℂ) (lam α β : ℂ) (u v : ℕ)
    (hlam : lam ≠ 0)
    (hface : leadingForm 1 1 T.1 = MvPolynomial.C lam *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0) ^ u *
      (MvPolynomial.X 1 - MvPolynomial.C β * MvPolynomial.X 0) ^ v) :
    vDeg 1 1 T.1 = (u + v : ℕ) := by
  have hX : MvPolynomial.IsWeightedHomogeneous (wt 1 1)
      (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℂ) 1 := by
    simpa [wt] using MvPolynomial.isWeightedHomogeneous_X ℂ (wt 1 1) (1 : Fin 2)
  have hY : MvPolynomial.IsWeightedHomogeneous (wt 1 1)
      (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) 1 := by
    simpa [wt] using MvPolynomial.isWeightedHomogeneous_X ℂ (wt 1 1) (0 : Fin 2)
  have hA := hX.sub (hY.C_mul α)
  have hB := hX.sub (hY.C_mul β)
  have hshape : (leadingForm 1 1 T.1).IsWeightedHomogeneous
      (wt 1 1) ((u + v : ℕ) : ℤ) := by
    rw [hface]
    simpa [nsmul_eq_mul, mul_assoc] using ((hA.pow u).mul (hB.pow v)).C_mul lam
  have hcutne : cutPoly 1 1 T.1 ≠ 0 := by
    rw [twoRoot_cutPoly T lam α β u v hface]
    exact mul_ne_zero
      (mul_ne_zero (Polynomial.C_ne_zero.mpr hlam)
        (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero α)))
      (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero β))
  have hfacene : leadingForm 1 1 T.1 ≠ 0 := by
    intro hz
    apply hcutne
    simp [cutPoly, hz]
  have hlead : (leadingForm 1 1 T.1).IsWeightedHomogeneous (wt 1 1)
      (vDeg 1 1 T.1) := by
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol T.1) (w := wt 1 1) (n := vDeg 1 1 T.1)
  exact (MvPolynomial.IsWeightedHomogeneous.inj_right hfacene hlead hshape)

theorem totalDeg_eq_vDeg_one_one (T : A1 ℂ)
    (hpos : 0 < vDeg 1 1 T.1) :
    (totalDeg T.1 : ℤ) = vDeg 1 1 T.1 := by
  have hweighted := weightedDegree_eq_coe_of_vDeg_pos T 1 1 hpos
  have hfacene := leadingForm_ne_zero_of_vDeg_pos T 1 1 hpos
  have hsymbol : symbol T.1 ≠ 0 := by
    intro hz
    apply hfacene
    simp [leadingForm, hz]
  have hle : (totalDeg T.1 : ℤ) ≤ vDeg 1 1 T.1 := by
    have hpoint : ∀ d ∈ (symbol T.1).support,
        (d.sum fun _ e => e : ℕ) ≤ (vDeg 1 1 T.1).toNat := by
      intro d hd
      have hsup : (Finsupp.weight (wt 1 1) d : WithBot ℤ) ≤
          weightedTotalDegree' (wt 1 1) (symbol T.1) := by
        change (Finsupp.weight (wt 1 1) d : WithBot ℤ) ≤
          (symbol T.1).support.sup
            (fun e => (Finsupp.weight (wt 1 1) e : WithBot ℤ))
        exact Finset.le_sup (α := WithBot ℤ) (f := fun e =>
          (Finsupp.weight (wt 1 1) e : WithBot ℤ)) hd
      rw [hweighted, weight_one_one_eq_degree] at hsup
      have hcast : ((d.sum fun _ e => e : ℕ) : ℤ) ≤ vDeg 1 1 T.1 :=
        WithBot.coe_le_coe.mp hsup
      omega
    have hnat : totalDeg T.1 ≤ (vDeg 1 1 T.1).toNat := by
      exact Finset.sup_le hpoint
    omega
  have hge : vDeg 1 1 T.1 ≤ (totalDeg T.1 : ℤ) := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hfacene
    have hdsource := weightedComponent_support_subset (symbol T.1) 1 1
      (vDeg 1 1 T.1) hd
    have hw := weight_of_mem_leadingForm T 1 1 d hd
    rw [weight_one_one_eq_degree] at hw
    have hdegree := MvPolynomial.le_totalDegree hdsource
    exact hw ▸ (by exact_mod_cast hdegree)
  omega

theorem twoRoot_totalDeg_eq_exponent_sum
    (T : A1 ℂ) (lam α β : ℂ) (u v : ℕ)
    (hlam : lam ≠ 0) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hface : leadingForm 1 1 T.1 = MvPolynomial.C lam *
      (MvPolynomial.X 1 - MvPolynomial.C α * MvPolynomial.X 0) ^ u *
      (MvPolynomial.X 1 - MvPolynomial.C β * MvPolynomial.X 0) ^ v) :
    totalDeg T.1 = u + v := by
  have hweight := twoRoot_vDeg_eq_exponent_sum T lam α β u v hlam hface
  have hpos : 0 < vDeg 1 1 T.1 := by rw [hweight]; exact_mod_cast (show 0 < u + v by omega)
  have heq := totalDeg_eq_vDeg_one_one T hpos
  rw [hweight] at heq
  exact_mod_cast heq

theorem twoRoot_massSix_contradiction_of_GGV
    (H : GGVInputs) (P Q : A1 ℂ)
    (hpair : IsCounterexamplePair P Q)
    (hmass : mass P.1 ≤ 6)
    (htwo : TwoRootTotalSymbol P.1) : False := by
  obtain ⟨lam, α, β, u, v, hlam, hα, hβ, _hab, hu, hv, hface⟩ := htwo
  have hdegree := twoRoot_totalDeg_eq_exponent_sum P lam α β u v hlam hu hv hface
  have hterms := twoRoot_cutPoly_termCount_gt_exponents P lam α β u v
    hlam hα hβ hface
  have hcutmass := cutPoly_termCount_le_mass P 1 1 (by norm_num)
  have hgcd := H.degreeBound P Q hpair
  have hgcdle := Nat.gcd_le_left (totalDeg Q.1)
    (by omega : 0 < totalDeg P.1)
  omega

end Dixmier.Weyl
