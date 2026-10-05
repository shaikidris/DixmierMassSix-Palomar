/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedUnequalFaceExclusion
public import DixmierFormal.Weyl.RamifiedRationalTiltDirection
public import DixmierFormal.Weyl.RamifiedTopLaurentFaceLift

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The first adjacent slopes of an exact pair cannot differ

This theorem consumes actual first-slope witnesses for both finite
PBW supports. It converts the earlier rational tilt to an integral
Newton direction, obtains the changed face and singleton mate face,
and applies the exact full-commutator exclusion.
-/

namespace Dixmier.Weyl

theorem ramified_exact_pair_no_earlier_first_slope
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q*P-P*Q = 1)
    (VP VQ : ℤ) (E F B : ℤ × ℕ) (tP tQ : ℚ)
    (htP : 0 < tP)
    (hearly : tP < (l : ℚ) * ((ρ+σ : ℤ) : ℚ))
    (hlt : tP < tQ)
    (hForder : 2 ≤ F.2)
    (hOld : (E.2 : ℤ)*F.1 = (F.2 : ℤ)*E.1)
    (hEP : E ∈ ramifiedPBWSupport l hl P)
    (hFQ : F ∈ ramifiedPBWSupport l hl Q)
    (hBP : B ∈ ramifiedPBWSupport l hl P)
    (hBlower : B.2 < E.2)
    (hEold : ramifiedWeight l ρ σ E = VP)
    (hFold : ramifiedWeight l ρ σ F = VQ)
    (hPfirst : ∀ p ∈ ramifiedPBWSupport l hl P,
      ((ramifiedWeight l ρ σ p : ℤ) : ℚ) - tP * (p.2 : ℚ) ≤
        (VP : ℚ) - tP * (E.2 : ℚ))
    (hBtie : ((ramifiedWeight l ρ σ B : ℤ) : ℚ) - tP * (B.2 : ℚ) =
      (VP : ℚ) - tP * (E.2 : ℚ))
    (hQoldTop : ∀ q ∈ ramifiedPBWSupport l hl Q,
      ramifiedWeight l ρ σ q ≤ VQ)
    (hQfirst : ∀ q ∈ ramifiedPBWSupport l hl Q,
      ((ramifiedWeight l ρ σ q : ℤ) : ℚ) - tQ * (q.2 : ℚ) ≤
        (VQ : ℚ) - tQ * (F.2 : ℚ)) :
    False := by
  let ρ' := rationalTiltRho l ρ tP
  let σ' := rationalTiltSigma l σ tP
  have hρ' : 0 < ρ' := rationalTilt_rho_pos l hl ρ hρ tP
  have hsum' : 0 < ρ'+σ' := rationalTilt_sum_pos l ρ σ tP hearly
  have hPtilt : ∀ p ∈ ramifiedPBWSupport l hl P,
      ((ramifiedWeight l ρ σ p : ℤ) : ℚ) - tP * (p.2 : ℚ) ≤
        ((ramifiedWeight l ρ σ E : ℤ) : ℚ) - tP * (E.2 : ℚ) := by
    simpa [hEold] using hPfirst
  have hQtilt : ∀ q ∈ ramifiedPBWSupport l hl Q,
      ((ramifiedWeight l ρ σ q : ℤ) : ℚ) - tP * (q.2 : ℚ) ≤
        ((ramifiedWeight l ρ σ F : ℤ) : ℚ) - tP * (F.2 : ℚ) := by
    have h := finiteSupport_before_first_slope_bound
      (ramifiedPBWSupport l hl Q) (ramifiedWeight l ρ σ)
      VQ F.2 tP tQ (le_of_lt htP) (le_of_lt hlt)
      hQoldTop hQfirst
    simpa [hFold] using h
  have hPupper : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ' σ' p ≤ ramifiedWeight l ρ' σ' E :=
    rationalTilt_support_bound l hl ρ σ tP
      (ramifiedPBWSupport l hl P) E hPtilt
  have hQupper : ∀ q ∈ ramifiedPBWSupport l hl Q,
      ramifiedWeight l ρ' σ' q ≤ ramifiedWeight l ρ' σ' F :=
    rationalTilt_support_bound l hl ρ σ tP
      (ramifiedPBWSupport l hl Q) F hQtilt
  have hEtop : ramifiedWeight l ρ' σ' E =
      ramifiedWeightDeg l hl ρ' σ' P := by
    exact (ramifiedWeightDeg_eq_of_attained_upper
      l hl ρ' σ' (ramifiedWeight l ρ' σ' E) P
      ⟨E,hEP,rfl⟩ hPupper).symm
  have hFtop : ramifiedWeight l ρ' σ' F =
      ramifiedWeightDeg l hl ρ' σ' Q := by
    exact (ramifiedWeightDeg_eq_of_attained_upper
      l hl ρ' σ' (ramifiedWeight l ρ' σ' F) Q
      ⟨F,hFQ,rfl⟩ hQupper).symm
  have hBnew : ramifiedWeight l ρ' σ' B =
      ramifiedWeight l ρ' σ' E := by
    have hq : ((ramifiedWeight l ρ' σ' B : ℤ) : ℚ) =
        ((ramifiedWeight l ρ' σ' E : ℤ) : ℚ) := by
      rw [rationalTilt_weight_scale, rationalTilt_weight_scale]
      rw [hEold]
      rw [hBtie]
    exact_mod_cast hq
  have hBtop : ramifiedWeight l ρ' σ' B =
      ramifiedWeightDeg l hl ρ' σ' P := hBnew.trans hEtop
  have hPupperDeg : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ' σ' p ≤
        ramifiedWeightDeg l hl ρ' σ' P := by
    intro p hp
    rw [← hEtop]
    exact hPupper p hp
  obtain ⟨hn,hBcanonical,hNtop⟩ :=
    ramified_face_point_topLaurent_at_order
      l hl ρ' σ' hρ' P B hBP hBtop hPupperDeg
  have hQsingleton : ∀ U ∈ ramifiedPBWSupport l hl Q,
      ramifiedWeight l ρ' σ' U =
        ramifiedWeightDeg l hl ρ' σ' Q → U = F := by
    intro U hU hUtop
    apply rationalTilt_before_first_slope_singleton
      l hl ρ σ hρ (ramifiedPBWSupport l hl Q) VQ F
      tP tQ htP hlt hFold hQoldTop hQfirst U hU
    rw [hUtop, ← hFtop]
  exact ramified_exact_pair_no_unequal_first_face
    l hl ρ' σ' hρ' hsum' P Q hcomm E F B.2
    hForder hOld hEtop hFtop hn hNtop hBlower hQsingleton

end Dixmier.Weyl
