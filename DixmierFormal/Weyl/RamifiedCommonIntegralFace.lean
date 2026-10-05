/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedCommonAdjacentDirection
public import DixmierFormal.Weyl.RamifiedRationalTiltDirection

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The common rational slope as an integral Newton face

The first common rational tilt has an integral representative with
positive horizontal weight and positive coordinate sum. Both old
starts and both lower-order tied points attain the actual top weight
of their respective operators in that representative.
-/

namespace Dixmier.Weyl

theorem ramified_common_rational_tilt_integral_face
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (P Q : ramifiedOperatorAlgebra l)
    (VP VQ : ℤ) (E F BP BQ : ℤ × ℕ) (t : ℚ)
    (hearly : t < (l : ℚ) * ((ρ+σ : ℤ) : ℚ))
    (hEP : E ∈ ramifiedPBWSupport l hl P)
    (hFQ : F ∈ ramifiedPBWSupport l hl Q)
    (hBP : BP ∈ ramifiedPBWSupport l hl P)
    (hBQ : BQ ∈ ramifiedPBWSupport l hl Q)
    (hEweight : ramifiedWeight l ρ σ E = VP)
    (hFweight : ramifiedWeight l ρ σ F = VQ)
    (hPfirst : ∀ p ∈ ramifiedPBWSupport l hl P,
      (ramifiedWeight l ρ σ p : ℚ) - t * (p.2 : ℚ) ≤
        (VP : ℚ) - t * (E.2 : ℚ))
    (hQfirst : ∀ q ∈ ramifiedPBWSupport l hl Q,
      (ramifiedWeight l ρ σ q : ℚ) - t * (q.2 : ℚ) ≤
        (VQ : ℚ) - t * (F.2 : ℚ))
    (hBPtie : (ramifiedWeight l ρ σ BP : ℚ) - t * (BP.2 : ℚ) =
      (VP : ℚ) - t * (E.2 : ℚ))
    (hBQtie : (ramifiedWeight l ρ σ BQ : ℚ) - t * (BQ.2 : ℚ) =
      (VQ : ℚ) - t * (F.2 : ℚ)) :
    ∃ ρ' σ' : ℤ,
      ρ' = rationalTiltRho l ρ t ∧
      σ' = rationalTiltSigma l σ t ∧
      0 < ρ' ∧ 0 < ρ'+σ' ∧
      (∀ p ∈ ramifiedPBWSupport l hl P,
        ramifiedWeight l ρ' σ' p ≤ ramifiedWeight l ρ' σ' E) ∧
      (∀ q ∈ ramifiedPBWSupport l hl Q,
        ramifiedWeight l ρ' σ' q ≤ ramifiedWeight l ρ' σ' F) ∧
      ramifiedWeight l ρ' σ' E = ramifiedWeightDeg l hl ρ' σ' P ∧
      ramifiedWeight l ρ' σ' F = ramifiedWeightDeg l hl ρ' σ' Q ∧
      ramifiedWeight l ρ' σ' BP = ramifiedWeightDeg l hl ρ' σ' P ∧
      ramifiedWeight l ρ' σ' BQ = ramifiedWeightDeg l hl ρ' σ' Q := by
  let ρ' := rationalTiltRho l ρ t
  let σ' := rationalTiltSigma l σ t
  have hρ' : 0 < ρ' := rationalTilt_rho_pos l hl ρ hρ t
  have hsum' : 0 < ρ'+σ' := rationalTilt_sum_pos l ρ σ t hearly
  have hPbound : ∀ p ∈ ramifiedPBWSupport l hl P,
      (ramifiedWeight l ρ σ p : ℚ) - t*(p.2 : ℚ) ≤
        (ramifiedWeight l ρ σ E : ℚ) - t*(E.2 : ℚ) := by
    simpa [hEweight] using hPfirst
  have hQbound : ∀ q ∈ ramifiedPBWSupport l hl Q,
      (ramifiedWeight l ρ σ q : ℚ) - t*(q.2 : ℚ) ≤
        (ramifiedWeight l ρ σ F : ℚ) - t*(F.2 : ℚ) := by
    simpa [hFweight] using hQfirst
  have hPupper := rationalTilt_support_bound l hl ρ σ t
    (ramifiedPBWSupport l hl P) E hPbound
  have hQupper := rationalTilt_support_bound l hl ρ σ t
    (ramifiedPBWSupport l hl Q) F hQbound
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
  have hBPtop : ramifiedWeight l ρ' σ' BP =
      ramifiedWeightDeg l hl ρ' σ' P := by
    have hq : (ramifiedWeight l ρ' σ' BP : ℚ) =
        (ramifiedWeight l ρ' σ' E : ℚ) := by
      rw [rationalTilt_weight_scale, rationalTilt_weight_scale]
      simpa [hEweight] using congrArg
        (fun z : ℚ => (l : ℚ)*(t.den : ℚ)*z) hBPtie
    have hz : ramifiedWeight l ρ' σ' BP =
        ramifiedWeight l ρ' σ' E := by exact_mod_cast hq
    exact hz.trans hEtop
  have hBQtop : ramifiedWeight l ρ' σ' BQ =
      ramifiedWeightDeg l hl ρ' σ' Q := by
    have hq : (ramifiedWeight l ρ' σ' BQ : ℚ) =
        (ramifiedWeight l ρ' σ' F : ℚ) := by
      rw [rationalTilt_weight_scale, rationalTilt_weight_scale]
      simpa [hFweight] using congrArg
        (fun z : ℚ => (l : ℚ)*(t.den : ℚ)*z) hBQtie
    have hz : ramifiedWeight l ρ' σ' BQ =
        ramifiedWeight l ρ' σ' F := by exact_mod_cast hq
    exact hz.trans hFtop
  exact ⟨ρ',σ',rfl,rfl,hρ',hsum',hPupper,hQupper,
    hEtop,hFtop,hBPtop,hBQtop⟩

/-- Dividing a positive-sum integral normal by its gcd preserves both
top faces, including the lower-order tied witnesses. -/
theorem ramified_common_integral_face_primitive
    (l : ℕ) (hl : 0 < l) (R S : ℤ)
    (hR : 0 < R) (hsum : 0 < R+S)
    (P Q : ramifiedOperatorAlgebra l)
    (E F BP BQ : ℤ × ℕ)
    (hEP : E ∈ ramifiedPBWSupport l hl P)
    (hFQ : F ∈ ramifiedPBWSupport l hl Q)
    (hPupper : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l R S p ≤ ramifiedWeight l R S E)
    (hQupper : ∀ q ∈ ramifiedPBWSupport l hl Q,
      ramifiedWeight l R S q ≤ ramifiedWeight l R S F)
    (hPBP : ramifiedWeight l R S BP = ramifiedWeight l R S E)
    (hQBQ : ramifiedWeight l R S BQ = ramifiedWeight l R S F) :
    ∃ r s g : ℤ, 0 < g ∧ R = g*r ∧ S = g*s ∧
      IsDirection r s ∧ 0 < r ∧
      ramifiedWeight l r s E = ramifiedWeightDeg l hl r s P ∧
      ramifiedWeight l r s F = ramifiedWeightDeg l hl r s Q ∧
      ramifiedWeight l r s BP = ramifiedWeightDeg l hl r s P ∧
      ramifiedWeight l r s BQ = ramifiedWeightDeg l hl r s Q := by
  have hgcd : 0 < Int.gcd R S :=
    Int.gcd_pos_of_ne_zero_left S (ne_of_gt hR)
  obtain ⟨g,r,s,hg,hcop,hReq,hSeq⟩ := Int.exists_gcd_one' hgcd
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  have hr : 0 < r := by rw [hReq] at hR; nlinarith
  have hrs : 0 < r+s := by rw [hReq,hSeq] at hsum; nlinarith
  have hscale (p : ℤ × ℕ) :
      ramifiedWeight l R S p = (g : ℤ)*ramifiedWeight l r s p := by
    rw [hReq,hSeq]
    dsimp [ramifiedWeight]
    ring
  have hPupper' : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l r s p ≤ ramifiedWeight l r s E := by
    intro p hp
    have h := hPupper p hp
    rw [hscale p,hscale E] at h
    exact (mul_le_mul_iff_of_pos_left hgZ).mp h
  have hQupper' : ∀ q ∈ ramifiedPBWSupport l hl Q,
      ramifiedWeight l r s q ≤ ramifiedWeight l r s F := by
    intro q hq
    have h := hQupper q hq
    rw [hscale q,hscale F] at h
    exact (mul_le_mul_iff_of_pos_left hgZ).mp h
  have hEtop : ramifiedWeight l r s E =
      ramifiedWeightDeg l hl r s P := by
    exact (ramifiedWeightDeg_eq_of_attained_upper
      l hl r s (ramifiedWeight l r s E) P
      ⟨E,hEP,rfl⟩ hPupper').symm
  have hFtop : ramifiedWeight l r s F =
      ramifiedWeightDeg l hl r s Q := by
    exact (ramifiedWeightDeg_eq_of_attained_upper
      l hl r s (ramifiedWeight l r s F) Q
      ⟨F,hFQ,rfl⟩ hQupper').symm
  have hBP' : ramifiedWeight l r s BP = ramifiedWeight l r s E := by
    rw [hscale BP,hscale E] at hPBP
    exact mul_left_cancel₀ (ne_of_gt hgZ) hPBP
  have hBQ' : ramifiedWeight l r s BQ = ramifiedWeight l r s F := by
    rw [hscale BQ,hscale F] at hQBQ
    exact mul_left_cancel₀ (ne_of_gt hgZ) hQBQ
  exact ⟨r,s,g,hgZ,by simpa [mul_comm] using hReq,
    by simpa [mul_comm] using hSeq,⟨hcop,hrs⟩,hr,hEtop,hFtop,
    hBP'.trans hEtop,hBQ'.trans hFtop⟩

/-- The full rational-to-primitive adapter for a common adjacent face. -/
theorem ramified_common_rational_tilt_primitive_face
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (P Q : ramifiedOperatorAlgebra l)
    (VP VQ : ℤ) (E F BP BQ : ℤ × ℕ) (t : ℚ)
    (hearly : t < (l : ℚ) * ((ρ+σ : ℤ) : ℚ))
    (hEP : E ∈ ramifiedPBWSupport l hl P)
    (hFQ : F ∈ ramifiedPBWSupport l hl Q)
    (hBP : BP ∈ ramifiedPBWSupport l hl P)
    (hBQ : BQ ∈ ramifiedPBWSupport l hl Q)
    (hEweight : ramifiedWeight l ρ σ E = VP)
    (hFweight : ramifiedWeight l ρ σ F = VQ)
    (hPfirst : ∀ p ∈ ramifiedPBWSupport l hl P,
      (ramifiedWeight l ρ σ p : ℚ) - t * (p.2 : ℚ) ≤
        (VP : ℚ) - t * (E.2 : ℚ))
    (hQfirst : ∀ q ∈ ramifiedPBWSupport l hl Q,
      (ramifiedWeight l ρ σ q : ℚ) - t * (q.2 : ℚ) ≤
        (VQ : ℚ) - t * (F.2 : ℚ))
    (hBPtie : (ramifiedWeight l ρ σ BP : ℚ) - t * (BP.2 : ℚ) =
      (VP : ℚ) - t * (E.2 : ℚ))
    (hBQtie : (ramifiedWeight l ρ σ BQ : ℚ) - t * (BQ.2 : ℚ) =
      (VQ : ℚ) - t * (F.2 : ℚ)) :
    ∃ r s : ℤ, IsDirection r s ∧ 0 < r ∧
      ramifiedWeight l r s E = ramifiedWeightDeg l hl r s P ∧
      ramifiedWeight l r s F = ramifiedWeightDeg l hl r s Q ∧
      ramifiedWeight l r s BP = ramifiedWeightDeg l hl r s P ∧
      ramifiedWeight l r s BQ = ramifiedWeightDeg l hl r s Q := by
  obtain ⟨R,S,_,_,hR,hsum,hPupper,hQupper,hEtop,hFtop,hBPtop,hBQtop⟩ :=
    ramified_common_rational_tilt_integral_face
      l hl ρ σ hρ P Q VP VQ E F BP BQ t hearly
      hEP hFQ hBP hBQ hEweight hFweight
      hPfirst hQfirst hBPtie hBQtie
  obtain ⟨r,s,_,_,_,_,hdir,hr,hE,hF,hBP',hBQ'⟩ :=
    ramified_common_integral_face_primitive
    l hl R S hR hsum P Q E F BP BQ hEP hFQ
      hPupper hQupper (hBPtop.trans hEtop.symm)
      (hBQtop.trans hFtop.symm)
  exact ⟨r,s,hdir,hr,hE,hF,hBP',hBQ'⟩

/-- On a positive-sum Newton face with positive horizontal weight,
the point of largest derivative order has the smallest PBW grade. -/
theorem ramified_face_grade_min_of_order_max
    (l : ℕ) (hl : 0 < l) (r s : ℤ)
    (hr : 0 < r) (hsum : 0 < r+s)
    (E p : ℤ × ℕ)
    (hface : ramifiedWeight l r s p = ramifiedWeight l r s E)
    (horder : p.2 ≤ E.2) :
    E.1 - (l : ℤ)*(E.2 : ℤ) ≤
      p.1 - (l : ℤ)*(p.2 : ℤ) := by
  have hlZ : (0 : ℤ) < l := by exact_mod_cast hl
  have horderZ : (p.2 : ℤ) ≤ (E.2 : ℤ) := by exact_mod_cast horder
  have hweight :
      r*((p.1 - (l : ℤ)*(p.2 : ℤ)) -
          (E.1 - (l : ℤ)*(E.2 : ℤ))) =
        ((l : ℤ)*(r+s))*((E.2 : ℤ) - (p.2 : ℤ)) := by
    dsimp [ramifiedWeight] at hface
    nlinarith [hface]
  have hnonneg : 0 ≤ ((l : ℤ)*(r+s))*
      ((E.2 : ℤ) - (p.2 : ℤ)) :=
    mul_nonneg (le_of_lt (mul_pos hlZ hsum)) (by omega)
  have hnonneg' : 0 ≤ r*((p.1 - (l : ℤ)*(p.2 : ℤ)) -
      (E.1 - (l : ℤ)*(E.2 : ℤ))) := hweight.symm ▸ hnonneg
  nlinarith [hnonneg']

/-- A primitive representative of a positive first tilt keeps the old
start as the minimum-grade point of its new top face. -/
theorem ramified_first_tilt_old_start_min_grade
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (T : ramifiedOperatorAlgebra l) (V : ℤ)
    (E : ℤ × ℕ) (t : ℚ) (ht : 0 < t)
    (hEold : ramifiedWeight l ρ σ E = V)
    (hOldTop : ∀ p ∈ ramifiedPBWSupport l hl T,
      ramifiedWeight l ρ σ p ≤ V)
    (r s g : ℤ) (hg : 0 < g)
    (hR : rationalTiltRho l ρ t = g*r)
    (hS : rationalTiltSigma l σ t = g*s)
    (hr : 0 < r) (hsum : 0 < r+s)
    (hEtop : ramifiedWeight l r s E =
      ramifiedWeightDeg l hl r s T) :
    ∀ p ∈ ramifiedPBWSupport l hl T,
      ramifiedWeight l r s p = ramifiedWeightDeg l hl r s T →
      E.1 - (l : ℤ)*(E.2 : ℤ) ≤
        p.1 - (l : ℤ)*(p.2 : ℤ) := by
  intro p hp hptop
  have heq : ramifiedWeight l r s p = ramifiedWeight l r s E :=
    hptop.trans hEtop.symm
  have hscale (q : ℤ × ℕ) :
      ramifiedWeight l (rationalTiltRho l ρ t)
        (rationalTiltSigma l σ t) q =
        g * ramifiedWeight l r s q := by
    rw [hR,hS]
    dsimp [ramifiedWeight]
    ring
  have heqR : ramifiedWeight l (rationalTiltRho l ρ t)
      (rationalTiltSigma l σ t) p =
      ramifiedWeight l (rationalTiltRho l ρ t)
        (rationalTiltSigma l σ t) E := by
    rw [hscale p,hscale E,heq]
  have heqQ := congrArg (fun z : ℤ => (z : ℚ)) heqR
  rw [rationalTilt_weight_scale, rationalTilt_weight_scale] at heqQ
  have hfac : (0 : ℚ) < (l : ℚ)*(t.den : ℚ) :=
    mul_pos (by exact_mod_cast hl) (by exact_mod_cast Rat.den_pos t)
  have htie : (ramifiedWeight l ρ σ p : ℚ) - t*(p.2 : ℚ) =
      (ramifiedWeight l ρ σ E : ℚ) - t*(E.2 : ℚ) :=
    (mul_left_cancel₀ (ne_of_gt hfac)) heqQ
  have horder := finiteSupport_tilted_face_order_le_old_start
    (ramifiedPBWSupport l hl T) (ramifiedWeight l ρ σ)
    V E.2 t ht hOldTop p hp (by simpa [hEold] using htie)
  exact ramified_face_grade_min_of_order_max
    l hl r s hr hsum E p heq horder

end Dixmier.Weyl
