/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVFiniteFaceSlopes
public import DixmierFormal.Weyl.OneSidedFaceDispatch

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Genuine negative face directions transfer to the exact mate

The common homogeneous root supplies occupied extreme endpoints in both
actual leading faces. On a strict negative direction, a nonsingleton
homogeneous face must have distinct first coordinates. The two scaled
endpoints therefore stay distinct for the unrestricted mate.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- Two different support points on a negative homogeneous face have
different first coordinates. -/
theorem negative_face_distinct_x
    (P : A1 ℂ) (ρ s : ℕ) (hs : 0 < s)
    {a b : Fin 2 →₀ ℕ}
    (ha : a ∈ (leadingForm ρ (-(s : ℤ)) P.1).support)
    (hb : b ∈ (leadingForm ρ (-(s : ℤ)) P.1).support)
    (hab : a ≠ b) : a 0 ≠ b 0 := by
  intro hx
  have hwa : Finsupp.weight (wt ρ (-(s : ℤ))) a =
      vDeg ρ (-(s : ℤ)) P.1 := by
    have h := ha
    simp only [leadingForm, MvPolynomial.support_weightedHomogeneousComponent,
      Finset.mem_filter] at h
    exact h.2
  have hwb : Finsupp.weight (wt ρ (-(s : ℤ))) b =
      vDeg ρ (-(s : ℤ)) P.1 := by
    have h := hb
    simp only [leadingForm, MvPolynomial.support_weightedHomogeneousComponent,
      Finset.mem_filter] at h
    exact h.2
  have hsZ : (s : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  have hyZ : (a 1 : ℤ) = b 1 := by
    simp [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two] at hwa hwb
    have hxZ : (a 0 : ℤ) = b 0 := by exact_mod_cast hx
    rw [hxZ] at hwa
    have hm : (s : ℤ) * ((a 1 : ℤ) - b 1) = 0 := by
      nlinarith [hwa,hwb]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hsZ)
  apply hab
  ext i
  fin_cases i
  · exact hx
  · exact_mod_cast hyZ

/-- Every genuine primitive strict-negative face direction of a
counterexample's first member is also a genuine face direction of its
unrestricted exact mate. -/
theorem counterexample_negative_face_direction_of_first
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ s : ℕ) (hs : 0 < s)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ)))
    (hfaceP : InDir ρ (-(s : ℤ)) P.1) :
    InDir ρ (-(s : ℤ)) Q.1 := by
  classical
  obtain ⟨n,d,u,v,r,t,hn,hd,_,hpMax,hqMax,hpMin,hqMin,hpBounds,_⟩ :=
    counterexample_strict_negative_face_proportional_endpoints
      P Q hpair ρ s hs hdir
  obtain ⟨a,b,ha,hb,hab⟩ := Finset.one_lt_card_iff.mp hfaceP
  have hax : a 0 ≠ b 0 := negative_face_distinct_x P ρ s hs ha hb hab
  have har := hpBounds a ha
  have hbr := hpBounds b hb
  have hru : r < u := by
    have hru0 : r ≤ u := by
      have h := hpBounds (expo (d*r) (d*t)) hpMin
      have hmul : d*r ≤ d*u := by simpa [expo] using h.2
      exact (Nat.mul_le_mul_left_iff hd).mp hmul
    rcases lt_or_eq_of_le hru0 with hlt | heq
    · exact hlt
    · rw [heq] at har hbr
      have haX : a 0 = d*r := by omega
      have hbX : b 0 = d*r := by omega
      exact False.elim (hax (haX.trans hbX.symm))
  have hneq : expo (n*r) (n*t) ≠ expo (n*u) (n*v) := by
    intro heq
    have hx := congrArg (fun e : Fin 2 →₀ ℕ => e 0) heq
    have hlt : n*r < n*u := Nat.mul_lt_mul_of_pos_left hru hn
    simp [expo] at hx
    omega
  exact Finset.one_lt_card_iff.mpr ⟨expo (n*r) (n*t), expo (n*u) (n*v),
    hqMin, hqMax, hneq⟩

/-- The source-facing signed-integer formulation; the primitive normal is
converted to the natural coordinates used by the common-root endpoint
theorem, without imposing a mate-order or mass bound. -/
theorem counterexample_strict_negative_InDir_mate
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ) (hσ : σ < 0)
    (hfaceP : InDir ρ σ P.1) : InDir ρ σ Q.1 := by
  have hρ : 0 < ρ := by have := hdir.2; omega
  obtain ⟨ell,s,_,_,_,hr,hs⟩ :=
    primitive_signed_normal_nat ρ σ hdir.1 hρ (le_of_lt hσ) hdir.2
  subst ρ
  subst σ
  have hspos : 0 < s := by omega
  exact counterexample_negative_face_direction_of_first
    P Q hpair ell s hspos hdir hfaceP

/-- Negating an operator changes coefficients but not its exposed PBW face. -/
theorem leadingForm_support_neg_A1
    (P : A1 ℂ) (ρ σ : ℤ) :
    (leadingForm ρ σ (-P).1).support =
      (leadingForm ρ σ P.1).support := by
  have hsym : symbol (-P).1 = -symbol P.1 := by
    have h : (-P : A1 ℂ) = (-1 : ℂ) • P := (neg_one_smul ℂ P).symm
    rw [h, symbol_smul]
    simp
  ext e
  rw [leadingForm_mem_iff_realExposedFace,
    leadingForm_mem_iff_realExposedFace]
  simp only [realExposedFace, hsym, MvPolynomial.support_neg]

/-- The two members of any counterexample pair have exactly the same
genuine primitive strict-negative face directions. -/
theorem counterexample_strict_negative_InDir_iff
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ) (hσ : σ < 0) :
    InDir ρ σ P.1 ↔ InDir ρ σ Q.1 := by
  constructor
  · exact counterexample_strict_negative_InDir_mate P Q hpair ρ σ hdir hσ
  · intro hfaceQ
    have hswap := isCounterexamplePair_swap_neg P Q hpair
    have hfaceNegP :=
      counterexample_strict_negative_InDir_mate Q (-P) hswap
        ρ σ hdir hσ hfaceQ
    simpa only [InDir, leadingForm_support_neg_A1] using hfaceNegP

/-- The finite primitive strict-negative direction carrier can be chosen
identically for both members of a counterexample pair. -/
theorem counterexample_strict_negative_direction_sets_eq
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) :
    {v : ℤ × ℤ | IsDirection v.1 v.2 ∧ 0 < v.1 ∧ v.2 < 0 ∧
      InDir v.1 v.2 P.1} =
    {v : ℤ × ℤ | IsDirection v.1 v.2 ∧ 0 < v.1 ∧ v.2 < 0 ∧
      InDir v.1 v.2 Q.1} := by
  ext v
  constructor
  · rintro ⟨hdir,hρ,hσ,hface⟩
    exact ⟨hdir,hρ,hσ,
      (counterexample_strict_negative_InDir_iff P Q hpair v.1 v.2 hdir hσ).mp hface⟩
  · rintro ⟨hdir,hρ,hσ,hface⟩
    exact ⟨hdir,hρ,hσ,
      (counterexample_strict_negative_InDir_iff P Q hpair v.1 v.2 hdir hσ).mpr hface⟩

end Dixmier.Weyl
