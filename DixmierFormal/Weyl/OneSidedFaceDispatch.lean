/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.OneSidedSupportGeometry
public import DixmierFormal.Weyl.NewtonRealDirection
public import DixmierFormal.Weyl.OppositeCrossingExtraction
public import DixmierFormal.Weyl.HorizontalOppositeCrossing
public import DixmierFormal.Weyl.OneSidedRoofZero
public import DixmierFormal.Weyl.OneSidedDiagonalVertex
public import DixmierFormal.Weyl.PBWGradeSlices

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Transfer of one-sided support geometry to Weyl symbols

The finite coordinate support of a Weyl symbol is identified exactly with the
support used by the rational supporting-line argument. This is the first
adapter toward Han--Tan's one-sided case dispatch.
-/

namespace Dixmier.Weyl

open Polynomial MvPolynomial

/-- Positive scaling of a real Newton normal preserves its exposed support
face. This is the face-level bridge needed to divide an integer normal by its
gcd before applying the primitive crossing lemmas. -/
theorem realExposedFace_pos_scale (c r s : ℝ) (hc : 0 < c)
    (S : Set (Fin 2 →₀ ℕ)) :
    realExposedFace (c * r) (c * s) S = realExposedFace r s S := by
  ext d
  constructor
  · rintro ⟨hd, hmax⟩
    refine ⟨hd, ?_⟩
    intro e he
    have h := hmax e he
    have hscale (a : Fin 2 →₀ ℕ) :
        realNewtonWeight (c * r) (c * s) a =
          c * realNewtonWeight r s a := by
      dsimp [realNewtonWeight]
      ring
    rw [hscale e, hscale d] at h
    exact (mul_le_mul_iff_of_pos_left hc).mp h
  · rintro ⟨hd, hmax⟩
    refine ⟨hd, ?_⟩
    intro e he
    have h := hmax e he
    have hscale (a : Fin 2 →₀ ℕ) :
        realNewtonWeight (c * r) (c * s) a =
          c * realNewtonWeight r s a := by
      dsimp [realNewtonWeight]
      ring
    rw [hscale e, hscale d]
    exact (mul_le_mul_iff_of_pos_left hc).mpr h

/-- Divide an integer Newton normal by its gcd without changing the
leading-form support. The resulting normal is primitive and preserves the
strict/horizontal sign conditions. -/
theorem primitive_normal_same_leading_face (T : Module.End ℂ ℂ[X])
    (ρ σ : ℤ) (hρ : 0 < ρ) (hσ : σ ≤ 0) (hsum : 0 < ρ + σ) :
    ∃ r s : ℤ, Int.gcd r s = 1 ∧ 0 < r ∧ s ≤ 0 ∧ 0 < r + s ∧
      (leadingForm ρ σ T).support = (leadingForm r s T).support := by
  have hgcd : 0 < Int.gcd ρ σ := Int.gcd_pos_of_ne_zero_left σ (ne_of_gt hρ)
  obtain ⟨g, r, s, hg, hcop, hρeq, hσeq⟩ := Int.exists_gcd_one' hgcd
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  have hr : 0 < r := by
    rw [hρeq] at hρ
    nlinarith
  have hs : s ≤ 0 := by
    rw [hσeq] at hσ
    nlinarith
  have hrs : 0 < r + s := by
    rw [hρeq, hσeq] at hsum
    nlinarith
  have hface : realExposedFace (ρ : ℝ) (σ : ℝ)
      ((symbol T).support : Set (Fin 2 →₀ ℕ)) =
      realExposedFace (r : ℝ) (s : ℝ)
        ((symbol T).support : Set (Fin 2 →₀ ℕ)) := by
    rw [hρeq, hσeq]
    push_cast
    convert realExposedFace_pos_scale (g : ℝ) (r : ℝ) (s : ℝ)
      (by exact_mod_cast hg) ((symbol T).support : Set (Fin 2 →₀ ℕ)) using 1 <;>
      ring
  refine ⟨r, s, hcop, hr, hs, hrs, ?_⟩
  ext d
  rw [leadingForm_mem_iff_realExposedFace,
    leadingForm_mem_iff_realExposedFace, hface]

/-- A primitive integer crossing normal has coprime natural coordinates in
the convention used by the crossing-face exclusion lemmas. -/
theorem primitive_signed_normal_nat (r s : ℤ)
    (hcop : Int.gcd r s = 1) (hr : 0 < r) (hs : s ≤ 0)
    (hrs : 0 < r + s) :
    ∃ ell d : ℕ, 0 < ell ∧ d < ell ∧ Nat.Coprime ell d ∧
      r = (ell : ℤ) ∧ s = -(d : ℤ) := by
  refine ⟨r.toNat, (-s).toNat, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · have hrabs : r.natAbs = r.toNat := by omega
    have hsabs : s.natAbs = (-s).toNat := by omega
    simpa [Nat.Coprime, Int.gcd_def, hrabs, hsabs] using hcop
  · omega
  · omega

/-- Native face normalization in the exact parameter form consumed by the
strict and horizontal crossing lemmas. -/
theorem crossing_face_coprime_nat_normal (T : Module.End ℂ ℂ[X])
    (ρ σ : ℤ) (hρ : 0 < ρ) (hσ : σ ≤ 0) (hsum : 0 < ρ + σ) :
    ∃ ell d : ℕ, 0 < ell ∧ d < ell ∧ Nat.Coprime ell d ∧
      (leadingForm ρ σ T).support =
        (leadingForm (ell : ℤ) (-(d : ℤ)) T).support := by
  obtain ⟨r, s, hcop, hr, hs, hrs, hface⟩ :=
    primitive_normal_same_leading_face T ρ σ hρ hσ hsum
  obtain ⟨ell, d, hell, hdell, hcop', hr, hs⟩ :=
    primitive_signed_normal_nat r s hcop hr hs hrs
  refine ⟨ell, d, hell, hdell, hcop', ?_⟩
  simpa [hr, hs] using hface

/-- A single gcd normalization works simultaneously for the two faces of an
exact pair; the second operator is unrestricted. -/
theorem crossing_pair_coprime_nat_normal (P Q : Module.End ℂ ℂ[X])
    (ρ σ : ℤ) (hρ : 0 < ρ) (hσ : σ ≤ 0) (hsum : 0 < ρ + σ) :
    ∃ ell d : ℕ, 0 < ell ∧ d < ell ∧ Nat.Coprime ell d ∧
      (leadingForm ρ σ P).support =
        (leadingForm (ell : ℤ) (-(d : ℤ)) P).support ∧
      (leadingForm ρ σ Q).support =
        (leadingForm (ell : ℤ) (-(d : ℤ)) Q).support := by
  have hgcd : 0 < Int.gcd ρ σ := Int.gcd_pos_of_ne_zero_left σ (ne_of_gt hρ)
  obtain ⟨g, r, s, hg, hcop, hρeq, hσeq⟩ := Int.exists_gcd_one' hgcd
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  have hr : 0 < r := by rw [hρeq] at hρ; nlinarith
  have hs : s ≤ 0 := by rw [hσeq] at hσ; nlinarith
  have hrs : 0 < r + s := by rw [hρeq, hσeq] at hsum; nlinarith
  obtain ⟨ell, d, hell, hdell, hcop', hr', hs'⟩ :=
    primitive_signed_normal_nat r s hcop hr hs hrs
  have hface (T : Module.End ℂ ℂ[X]) :
      (leadingForm ρ σ T).support = (leadingForm r s T).support := by
    have hscale : realExposedFace (ρ : ℝ) (σ : ℝ)
        ((symbol T).support : Set (Fin 2 →₀ ℕ)) =
        realExposedFace (r : ℝ) (s : ℝ)
          ((symbol T).support : Set (Fin 2 →₀ ℕ)) := by
      rw [hρeq, hσeq]
      push_cast
      convert realExposedFace_pos_scale (g : ℝ) (r : ℝ) (s : ℝ)
        (by exact_mod_cast hg) ((symbol T).support : Set (Fin 2 →₀ ℕ)) using 1 <;>
        ring
    ext a
    rw [leadingForm_mem_iff_realExposedFace,
      leadingForm_mem_iff_realExposedFace, hscale]
  refine ⟨ell, d, hell, hdell, hcop', ?_, ?_⟩
  · simpa [hr', hs'] using hface P
  · simpa [hr', hs'] using hface Q

/-- Leading components with the same selected support have the same
coefficients, since both are cut from one PBW symbol. -/
theorem leadingForm_eq_of_support_eq (T : Module.End ℂ ℂ[X])
    (ρ σ r s : ℤ)
    (hface : (leadingForm ρ σ T).support = (leadingForm r s T).support) :
    leadingForm ρ σ T = leadingForm r s T := by
  apply MvPolynomial.ext
  intro a
  by_cases ha : a ∈ (leadingForm ρ σ T).support
  · have ha' : a ∈ (leadingForm r s T).support := by simpa [← hface] using ha
    have hw := (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol T) (w := wt ρ σ) (n := vDeg ρ σ T))
      (MvPolynomial.mem_support_iff.mp ha)
    have hw' := (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol T) (w := wt r s) (n := vDeg r s T))
      (MvPolynomial.mem_support_iff.mp ha')
    simpa only [leadingForm, MvPolynomial.coeff_weightedHomogeneousComponent,
      if_pos hw, if_pos hw']
  · have ha' : a ∉ (leadingForm r s T).support := by simpa [← hface] using ha
    simp only [MvPolynomial.mem_support_iff] at ha ha'
    exact (not_ne_iff.mp ha).trans (not_ne_iff.mp ha').symm

/-- Simultaneous normalization preserves the full leading polynomials,
including coefficients and therefore their Poisson bracket. -/
theorem crossing_pair_coprime_nat_faces (P Q : Module.End ℂ ℂ[X])
    (ρ σ : ℤ) (hρ : 0 < ρ) (hσ : σ ≤ 0) (hsum : 0 < ρ + σ) :
    ∃ ell d : ℕ, 0 < ell ∧ d < ell ∧ Nat.Coprime ell d ∧
      leadingForm ρ σ P = leadingForm (ell : ℤ) (-(d : ℤ)) P ∧
      leadingForm ρ σ Q = leadingForm (ell : ℤ) (-(d : ℤ)) Q := by
  obtain ⟨ell, d, hell, hdell, hcop, hP, hQ⟩ :=
    crossing_pair_coprime_nat_normal P Q ρ σ hρ hσ hsum
  exact ⟨ell, d, hell, hdell, hcop,
    leadingForm_eq_of_support_eq P ρ σ ell (-(d : ℤ)) hP,
    leadingForm_eq_of_support_eq Q ρ σ ell (-(d : ℤ)) hQ⟩

/-- The distinguished derivative term fixes the first face's weighted
degree, independently of all other terms. -/
theorem leadingForm_degree_of_y_term (T : Module.End ℂ ℂ[X])
    (ell d : ℕ)
    (hY : expo 0 1 ∈ (leadingForm (ell : ℤ) (-(d : ℤ)) T).support) :
    vDeg (ell : ℤ) (-(d : ℤ)) T = -(d : ℤ) := by
  have hhom := (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
    (φ := symbol T) (w := wt (ell : ℤ) (-(d : ℤ)))
    (n := vDeg (ell : ℤ) (-(d : ℤ)) T))
    (MvPolynomial.mem_support_iff.mp hY)
  simpa [expo_weight] using hhom.symm

/-- The opposite generator term fixes the mate face's weighted degree. -/
theorem leadingForm_degree_of_x_term (T : Module.End ℂ ℂ[X])
    (ell d : ℕ)
    (hX : expo 1 0 ∈ (leadingForm (ell : ℤ) (-(d : ℤ)) T).support) :
    vDeg (ell : ℤ) (-(d : ℤ)) T = (ell : ℤ) := by
  have hhom := (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
    (φ := symbol T) (w := wt (ell : ℤ) (-(d : ℤ)))
    (n := vDeg (ell : ℤ) (-(d : ℤ)) T))
    (MvPolynomial.mem_support_iff.mp hX)
  simpa [expo_weight] using hhom.symm

/-- The Poisson sign conversion from the exact-pair convention to the
first-face convention used in the local crossing exclusions. -/
theorem poisson_first_neg_second (R F : MvPolynomial (Fin 2) ℂ) :
    poisson R (-F) = poisson F R := by
  unfold poisson
  simp only [map_neg, mul_neg, neg_mul]
  ring

/-- Once the selected face is in primitive crossing coordinates, a
nonmonomial scalar-free first face cannot realize the bracket-one branch.
The mate has no support or order bound. -/
theorem primitive_crossing_face_bracket_one_impossible
    (R F : MvPolynomial (Fin 2) ℂ) (ell d : ℕ)
    (hell : 0 < ell) (hdell : d < ell) (hcop : Nat.Coprime ell d)
    (hR : R.IsWeightedHomogeneous (wt ell (-(d : ℤ))) (-(d : ℤ)))
    (hF : F.IsWeightedHomogeneous (wt ell (-(d : ℤ))) (ell : ℤ))
    (hRscalarFree : MvPolynomial.coeff (expo 0 0) R = 0)
    (hRnonmono : 1 < R.support.card)
    (hbr : poisson F R = 1) : False := by
  have hbr' : poisson R (-F) = 1 := by
    rw [poisson_first_neg_second, hbr]
  have hF' : (-F).IsWeightedHomogeneous (wt ell (-(d : ℤ))) (ell : ℤ) :=
    hF.neg
  by_cases hd : d = 0
  · subst d
    have hR' : R.IsWeightedHomogeneous (wt ell 0) 0 := by simpa using hR
    have hF'' : (-F).IsWeightedHomogeneous (wt ell 0) (ell : ℤ) := by
      simpa using hF'
    exact (horizontal_nonmonomial_face_excludes_bracket_one R (-F) ell hell
      hcop hR' hF'' hRscalarFree hRnonmono) hbr'
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    exact (strict_crossing_nonmonomial_face_excludes_bracket_one
      R (-F) d ell hdpos hdell hcop hR hF' hRnonmono) hbr'

/-- The face weights needed by the local crossing exclusions follow from
the distinguished `Y` term and the bracket-one identity; they are not extra
assumptions on the mate. -/
theorem primitive_leading_pair_bracket_one_impossible
    (P Q : Module.End ℂ ℂ[X]) (ell d : ℕ)
    (hell : 0 < ell) (hdell : d < ell) (hcop : Nat.Coprime ell d)
    (hY : expo 0 1 ∈ (leadingForm ell (-(d : ℤ)) P).support)
    (hRscalarFree : MvPolynomial.coeff (expo 0 0)
      (leadingForm ell (-(d : ℤ)) P) = 0)
    (hRnonmono : 1 < (leadingForm ell (-(d : ℤ)) P).support.card)
    (hbr : poisson (leadingForm ell (-(d : ℤ)) Q)
      (leadingForm ell (-(d : ℤ)) P) = 1) : False := by
  let R := leadingForm ell (-(d : ℤ)) P
  let F := leadingForm ell (-(d : ℤ)) Q
  have hRdeg := leadingForm_degree_of_y_term P ell d hY
  have hRhom : R.IsWeightedHomogeneous (wt ell (-(d : ℤ))) (-(d : ℤ)) := by
    have h := MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P) (w := wt ell (-(d : ℤ)))
      (n := vDeg ell (-(d : ℤ)) P)
    simpa [R, leadingForm, hRdeg] using h
  have hbr' : poisson R (-F) = 1 := by
    rw [poisson_first_neg_second]
    exact hbr
  have hX : expo 1 0 ∈ (-F).support :=
    poisson_eq_one_forces_mate_position_term R (-F) d ell hell hRhom hbr'
  have hFhom0 : (-F).IsWeightedHomogeneous (wt ell (-(d : ℤ)))
      (vDeg ell (-(d : ℤ)) Q) := by
    exact (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol Q) (w := wt ell (-(d : ℤ)))
      (n := vDeg ell (-(d : ℤ)) Q)).neg
  have hFdeg : vDeg ell (-(d : ℤ)) Q = (ell : ℤ) := by
    have hw := hFhom0 (MvPolynomial.mem_support_iff.mp hX)
    simpa [expo_weight] using hw.symm
  have hFhom : F.IsWeightedHomogeneous (wt ell (-(d : ℤ))) (ell : ℤ) := by
    have h := MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol Q) (w := wt ell (-(d : ℤ)))
      (n := vDeg ell (-(d : ℤ)) Q)
    simpa [F, leadingForm, hFdeg] using h
  exact primitive_crossing_face_bracket_one_impossible R F ell d hell hdell hcop
    hRhom hFhom hRscalarFree hRnonmono hbr

/-- The bracket-one branch is excluded directly at any positive-sum
strict/horizontal integer normal, without assuming that the original
normal was primitive. -/
theorem crossing_pair_bracket_one_impossible
    (P Q : Module.End ℂ ℂ[X]) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hσ : σ ≤ 0) (hsum : 0 < ρ + σ)
    (hY : expo 0 1 ∈ (leadingForm ρ σ P).support)
    (hRscalarFree : MvPolynomial.coeff (expo 0 0) (leadingForm ρ σ P) = 0)
    (hRnonmono : 1 < (leadingForm ρ σ P).support.card)
    (hbr : poisson (leadingForm ρ σ Q) (leadingForm ρ σ P) = 1) : False := by
  obtain ⟨ell, d, hell, hdell, hcop, hP, hQ⟩ :=
    crossing_pair_coprime_nat_faces P Q ρ σ hρ hσ hsum
  rw [hP] at hY hRscalarFree hRnonmono
  rw [hP, hQ] at hbr
  exact primitive_leading_pair_bracket_one_impossible P Q ell d hell hdell hcop
    hY hRscalarFree hRnonmono hbr

noncomputable def oneSidedSymbolCoords (T : Module.End ℂ ℂ[X]) : Finset (ℕ × ℕ) :=
  (symbol T).support.image (fun d => (d 0, d 1))

private theorem oneSidedSymbolCoords_mem_iff (T : Module.End ℂ ℂ[X])
    (p : ℕ × ℕ) :
    p ∈ oneSidedSymbolCoords T ↔ expo p.1 p.2 ∈ (symbol T).support := by
  classical
  constructor
  · intro hp
    obtain ⟨d, hd, hdp⟩ := Finset.mem_image.mp hp
    have h0 : d 0 = p.1 := congrArg Prod.fst hdp
    have h1 : d 1 = p.2 := congrArg Prod.snd hdp
    have he : d = expo p.1 p.2 := by
      ext i
      fin_cases i
      · simpa [expo] using h0
      · simpa [expo] using h1
    simpa [← he] using hd
  · intro hp
    apply Finset.mem_image.mpr
    exact ⟨expo p.1 p.2, hp, by simp [expo]⟩

/-- Strictly negative grades of the PBW symbol become the coordinate
inequality needed by the finite supporting-line theorem. -/
theorem oneSidedSymbolCoords_strict (T : Module.End ℂ ℂ[X])
    (hgrade : ∀ d ∈ (symbol T).support, grade d < 0) :
    ∀ p ∈ oneSidedSymbolCoords T, p.1 < p.2 := by
  intro p hp
  have h := hgrade (expo p.1 p.2) ((oneSidedSymbolCoords_mem_iff T p).mp hp)
  simp [grade, expo] at h
  omega

/-- The finite dichotomy applies directly to the PBW symbol of an operator.
The strict branch is still expressed by a rational supporting line; the
Newton-real-direction bridge converts it into an integer leading form. -/
theorem oneSidedSymbol_support_face_dichotomy (T : Module.End ℂ ℂ[X])
    (hgrade : ∀ d ∈ (symbol T).support, grade d < 0)
    (hother : ∃ d ∈ (symbol T).support, d ≠ expo 0 1) :
    (∃ d ∈ (symbol T).support, d ≠ expo 0 1 ∧ d 1 = d 0 + 1) ∨
    (∃ (t : ℚ) (d : Fin 2 →₀ ℕ), d ∈ (symbol T).support ∧ d ≠ expo 0 1 ∧
      0 ≤ t ∧ t < 1 ∧
      (d 0 : ℚ) = t * ((d 1 : ℚ) - 1) ∧
      ∀ e ∈ (symbol T).support, (e 0 : ℚ) ≤ t * ((e 1 : ℚ) - 1)) := by
  have hotherCoords : ∃ p ∈ oneSidedSymbolCoords T, p ≠ (0, 1) := by
    obtain ⟨d, hd, hne⟩ := hother
    refine ⟨(d 0, d 1), Finset.mem_image.mpr ⟨d, hd, rfl⟩, ?_⟩
    intro hp
    apply hne
    ext i
    fin_cases i
    · have h0 : d 0 = 0 := congrArg Prod.fst hp
      simpa [expo] using h0
    · have h1 : d 1 = 1 := congrArg Prod.snd hp
      simpa [expo] using h1
  obtain hcase := oneSidedSupport_face_dichotomy (oneSidedSymbolCoords T)
    (oneSidedSymbolCoords_strict T hgrade) hotherCoords
  rcases hcase with ⟨p, hp, hpg, hboundary⟩ |
    ⟨t, p, hp, hpg, hlo, hhi, heq, hline⟩
  · refine Or.inl ⟨expo p.1 p.2, (oneSidedSymbolCoords_mem_iff T p).mp hp, ?_, ?_⟩
    · intro he
      apply hpg
      have h0 : p.1 = 0 := by simpa [expo] using congrArg (fun d : Fin 2 →₀ ℕ => d 0) he
      have h1 : p.2 = 1 := by simpa [expo] using congrArg (fun d : Fin 2 →₀ ℕ => d 1) he
      exact Prod.ext h0 h1
    · simpa [expo] using hboundary
  · refine Or.inr ⟨t, expo p.1 p.2, (oneSidedSymbolCoords_mem_iff T p).mp hp,
        ?_, hlo, hhi, ?_, ?_⟩
    · intro he
      apply hpg
      have h0 : p.1 = 0 := by simpa [expo] using congrArg (fun d : Fin 2 →₀ ℕ => d 0) he
      have h1 : p.2 = 1 := by simpa [expo] using congrArg (fun d : Fin 2 →₀ ℕ => d 1) he
      exact Prod.ext h0 h1
    · simpa [expo] using heq
    · intro e he
      have hem : (e 0, e 1) ∈ oneSidedSymbolCoords T :=
        Finset.mem_image.mpr ⟨e, he, rfl⟩
      exact hline (e 0, e 1) hem

/-- A rational supporting line with ratio below one exposes the generator
and a second PBW monomial in a genuine positive-sum integer leading form. -/
theorem oneSidedSymbol_strict_line_to_integer_face (T : Module.End ℂ ℂ[X])
    (hgen : expo 0 1 ∈ (symbol T).support)
    (t : ℚ) (d : Fin 2 →₀ ℕ)
    (hd : d ∈ (symbol T).support) (hne : d ≠ expo 0 1)
    (ht : t < 1)
    (hlineD : (d 0 : ℚ) = t * ((d 1 : ℚ) - 1))
    (hline : ∀ e ∈ (symbol T).support,
      (e 0 : ℚ) ≤ t * ((e 1 : ℚ) - 1)) :
    ∃ ρ σ : ℤ, 0 < ρ + σ ∧
      expo 0 1 ∈ (leadingForm ρ σ T).support ∧
      d ∈ (leadingForm ρ σ T).support := by
  let ρ : ℝ := 1
  let σ : ℝ := -(t : ℝ)
  have hsum : 0 < ρ + σ := by
    have htR : (t : ℝ) < 1 := by exact_mod_cast ht
    dsimp [ρ, σ]
    linarith
  have hfaceGen : expo 0 1 ∈
      realExposedFace ρ σ ((symbol T).support : Set (Fin 2 →₀ ℕ)) := by
    constructor
    · exact hgen
    · intro e he
      have hq := hline e he
      have hr : (e 0 : ℝ) ≤ (t : ℝ) * ((e 1 : ℝ) - 1) := by exact_mod_cast hq
      dsimp [realNewtonWeight, ρ, σ]
      simp [expo]
      nlinarith
  have hfaceD : d ∈
      realExposedFace ρ σ ((symbol T).support : Set (Fin 2 →₀ ℕ)) := by
    constructor
    · exact hd
    · intro e he
      have hq := hline e he
      have hr : (e 0 : ℝ) ≤ (t : ℝ) * ((e 1 : ℝ) - 1) := by exact_mod_cast hq
      have hdR : (d 0 : ℝ) = (t : ℝ) * ((d 1 : ℝ) - 1) := by exact_mod_cast hlineD
      dsimp [realNewtonWeight, ρ, σ]
      nlinarith
  obtain ⟨r, s, hrs, hfaceEq⟩ :=
    realExposedFace_eq_leadingForm_support_of_two_points ρ σ T hsum
      hfaceGen hfaceD hne.symm
  refine ⟨r, s, hrs, ?_, ?_⟩
  · change expo 0 1 ∈ ((leadingForm r s T).support : Set (Fin 2 →₀ ℕ))
    rw [← hfaceEq]
    exact hfaceGen
  · change d ∈ ((leadingForm r s T).support : Set (Fin 2 →₀ ℕ))
    rw [← hfaceEq]
    exact hfaceD

/-- A grade-`-1` point is on the `(1,-1)` leading form when every supported
grade is strictly negative. -/
theorem oneSidedSymbol_grade_minus_one_mem_face (T : Module.End ℂ ℂ[X])
    (hgrade : ∀ e ∈ (symbol T).support, grade e < 0)
    (d : Fin 2 →₀ ℕ) (hd : d ∈ (symbol T).support)
    (hdgrade : grade d = -1) :
    d ∈ (leadingForm 1 (-1) T).support := by
  rw [leadingForm_mem_iff_realExposedFace]
  constructor
  · exact hd
  · intro e he
    have hegrade : grade e ≤ -1 := by have h := hgrade e he; omega
    have hle : (e 0 : ℤ) - e 1 ≤ (d 0 : ℤ) - d 1 := by
      simp only [grade] at hegrade hdgrade
      omega
    have hleR : (e 0 : ℝ) - e 1 ≤ (d 0 : ℝ) - d 1 := by exact_mod_cast hle
    dsimp [realNewtonWeight]
    norm_num
    linarith

/-- Source-case dispatch for an actual PBW symbol, conditional only on the
strictly negative-grade support and presence of the derivative generator.
It produces either the grade-boundary face or a positive-sum integer face,
each containing at least two monomials. -/
theorem oneSidedSymbol_face_dispatch (T : Module.End ℂ ℂ[X])
    (hgrade : ∀ d ∈ (symbol T).support, grade d < 0)
    (hgen : expo 0 1 ∈ (symbol T).support)
    (hother : ∃ d ∈ (symbol T).support, d ≠ expo 0 1) :
    (∃ d ∈ (leadingForm 1 (-1) T).support, d ≠ expo 0 1 ∧
      expo 0 1 ∈ (leadingForm 1 (-1) T).support) ∨
    (∃ ρ σ : ℤ, 0 < ρ + σ ∧
      expo 0 1 ∈ (leadingForm ρ σ T).support ∧
      ∃ d ∈ (leadingForm ρ σ T).support, d ≠ expo 0 1) := by
  obtain hcase := oneSidedSymbol_support_face_dichotomy T hgrade hother
  rcases hcase with ⟨d, hd, hne, hboundary⟩ |
    ⟨t, d, hd, hne, _, ht, hlineD, hline⟩
  · have hdgrade : grade d = -1 := by
      simp only [grade]
      omega
    have hgengrade : grade (expo 0 1) = -1 := by simp [grade, expo]
    exact Or.inl ⟨d,
      oneSidedSymbol_grade_minus_one_mem_face T hgrade d hd hdgrade,
      hne, oneSidedSymbol_grade_minus_one_mem_face T hgrade _ hgen hgengrade⟩
  · obtain ⟨ρ, σ, hsum, hgenFace, hdFace⟩ :=
      oneSidedSymbol_strict_line_to_integer_face T hgen t d hd hne ht hlineD hline
    exact Or.inr ⟨ρ, σ, hsum, hgenFace, d, hdFace, hne⟩

/-- A bracket-one leading-face pair with the first operator on the
nonpositive-grade side must contain the derivative generator in that first
face. This is the missing linear-term extraction before the finite dispatch. -/
theorem oneSided_leading_bracket_one_forces_generator (P Q : A1 ℂ)
    (ρ σ : ℤ)
    (hside : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d ≤ 0)
    (hbr : poisson (leadingForm ρ σ (Q : Module.End ℂ ℂ[X]))
      (leadingForm ρ σ (P : Module.End ℂ ℂ[X])) = 1) :
    expo 0 1 ∈ (leadingForm ρ σ (P : Module.End ℂ ℂ[X])).support ∧
    expo 0 1 ∈ (symbol (P : Module.End ℂ ℂ[X])).support := by
  let R := leadingForm ρ σ (P : Module.End ℂ ℂ[X])
  let F := leadingForm ρ σ (Q : Module.End ℂ ℂ[X])
  have hXnot : expo 1 0 ∉ R.support := by
    intro hx
    have hxS := leadingForm_support_subset_symbol_support
      (P : Module.End ℂ ℂ[X]) ρ σ hx
    have h := hside (expo 1 0) hxS
    simp [grade, expo] at h
  have hXcoeff : MvPolynomial.coeff (expo 1 0) R = 0 := by
    by_contra hn
    exact hXnot (MvPolynomial.mem_support_iff.mpr hn)
  have hcoeff := congrArg (MvPolynomial.coeff 0) hbr
  rw [poisson_coeff_zero, hXcoeff] at hcoeff
  have hYcoeff : MvPolynomial.coeff (expo 0 1) R ≠ 0 := by
    intro hz
    rw [hz] at hcoeff
    simp at hcoeff
  have hY : expo 0 1 ∈ R.support := MvPolynomial.mem_support_iff.mpr hYcoeff
  exact ⟨hY, leadingForm_support_subset_symbol_support
    (P : Module.End ℂ ℂ[X]) ρ σ hY⟩

/-- For a scalar-free exact pair with one-sided support, the roof argument
supplies a bracket-one direction and the linear coefficient identity then
forces the derivative generator into the full PBW support. -/
theorem oneSided_exact_pair_has_generator (P Q : A1 ℂ)
    (hPnonconstant : ∃ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, d ≠ 0)
    (hQnonconstant : ∃ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, d ≠ 0)
    (hPscalarFree : (0 : Fin 2 →₀ ℕ) ∉ (symbol (P : Module.End ℂ ℂ[X])).support)
    (hQscalarFree : (0 : Fin 2 →₀ ℕ) ∉ (symbol (Q : Module.End ℂ ℂ[X])).support)
    (hPside : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d ≤ 0)
    (hexact : Q * P - P * Q = 1) :
    expo 0 1 ∈ (symbol (P : Module.End ℂ ℂ[X])).support := by
  obtain ⟨ρ, σ, _, hbr⟩ :=
    exists_integer_positive_direction_leading_bracket_one P Q
      hPnonconstant hQnonconstant hPscalarFree hQscalarFree hPside hexact
  exact (oneSided_leading_bracket_one_forces_generator P Q ρ σ hPside hbr).2

/-- Every integer normal beyond the supplied support bound exposes the
maximal diagonal PBW exponent as a singleton leading form. -/
theorem oneSidedSymbol_maximal_diagonal_singleton_face_of_bound (T : Module.End ℂ ℂ[X])
    (hside : ∀ e ∈ (symbol T).support, grade e ≤ 0)
    (d : Fin 2 →₀ ℕ) (hd : d ∈ (symbol T).support)
    (hdiag : d 0 = d 1)
    (hmax : ∀ e ∈ (symbol T).support, e 0 = e 1 → e 1 ≤ d 1)
    (N : ℕ) (hbound : ∀ e ∈ (symbol T).support, e 1 < N) :
    (leadingForm (N : ℤ) (1 - (N : ℤ)) T).support = {d} := by
  have hcoordSide : ∀ p ∈ oneSidedSymbolCoords T, p.1 ≤ p.2 := by
    intro p hp
    have h := hside (expo p.1 p.2) ((oneSidedSymbolCoords_mem_iff T p).mp hp)
    simp [grade, expo] at h
    omega
  have hdCoord : (d 0, d 1) ∈ oneSidedSymbolCoords T :=
    Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have hcoordMax : ∀ p ∈ oneSidedSymbolCoords T,
      p.1 = p.2 → p.2 ≤ d 1 := by
    intro p hp hpeq
    have he := (oneSidedSymbolCoords_mem_iff T p).mp hp
    have h := hmax (expo p.1 p.2) he (by simpa [expo] using hpeq)
    simpa [expo] using h
  have hcoordBound : ∀ p ∈ oneSidedSymbolCoords T, p.2 < N := by
    intro p hp
    have he := (oneSidedSymbolCoords_mem_iff T p).mp hp
    simpa [expo] using hbound (expo p.1 p.2) he
  have hstrict :=
    oneSided_maximal_diagonal_exposed_of_bound (oneSidedSymbolCoords T) hcoordSide
      (d 0, d 1) hdCoord hdiag hcoordMax N hcoordBound
  have hweight (e : Fin 2 →₀ ℕ) :
      realNewtonWeight (N : ℝ) (1 - (N : ℝ)) e =
        (diagonalVertexWeight N (e 0, e 1) : ℝ) := by
    simp [realNewtonWeight, diagonalVertexWeight]
  have hdFace : d ∈
      realExposedFace (N : ℝ) (1 - (N : ℝ))
        ((symbol T).support : Set (Fin 2 →₀ ℕ)) := by
    constructor
    · exact hd
    · intro e he
      by_cases hed : e = d
      · subst e
        rfl
      · have hcoordNe : (e 0, e 1) ≠ (d 0, d 1) := by
          intro heq
          apply hed
          ext i
          fin_cases i
          · exact congrArg Prod.fst heq
          · exact congrArg Prod.snd heq
        have hem : (e 0, e 1) ∈ oneSidedSymbolCoords T :=
          Finset.mem_image.mpr ⟨e, he, rfl⟩
        have hlt := hstrict (e 0, e 1) hem hcoordNe
        rw [hweight e, hweight d]
        exact_mod_cast hlt.le
  apply Finset.eq_singleton_iff_unique_mem.mpr
  constructor
  · apply (leadingForm_mem_iff_realExposedFace _ _ T d).mpr
    simpa using hdFace
  · intro e he
    have heFace := (leadingForm_mem_iff_realExposedFace _ _ T e).mp he
    by_contra hed
    have hcoordNe : (e 0, e 1) ≠ (d 0, d 1) := by
      intro heq
      apply hed
      ext i
      fin_cases i
      · exact congrArg Prod.fst heq
      · exact congrArg Prod.snd heq
    have hem : (e 0, e 1) ∈ oneSidedSymbolCoords T :=
      Finset.mem_image.mpr ⟨e, heFace.1, rfl⟩
    have hlt := hstrict (e 0, e 1) hem hcoordNe
    have hle := heFace.2 d hd
    have hle' : realNewtonWeight (N : ℝ) (1 - (N : ℝ)) d ≤
        realNewtonWeight (N : ℝ) (1 - (N : ℝ)) e := by simpa using hle
    rw [hweight e, hweight d] at hle'
    exact not_lt_of_ge hle' (by exact_mod_cast hlt)

/-- A maximal diagonal PBW exponent of a one-sided symbol is literally a
singleton integer leading form. -/
theorem oneSidedSymbol_maximal_diagonal_singleton_face (T : Module.End ℂ ℂ[X])
    (hside : ∀ e ∈ (symbol T).support, grade e ≤ 0)
    (d : Fin 2 →₀ ℕ) (hd : d ∈ (symbol T).support)
    (hdiag : d 0 = d 1)
    (hmax : ∀ e ∈ (symbol T).support, e 0 = e 1 → e 1 ≤ d 1) :
    ∃ N : ℕ, 0 < N ∧
      (leadingForm (N : ℤ) (1 - (N : ℤ)) T).support = {d} := by
  let M := (symbol T).support.sup' ⟨d, hd⟩ (fun e => e 1)
  let N := M + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hbound : ∀ e ∈ (symbol T).support, e 1 < N := by
    intro e he
    have hle : e 1 ≤ M := Finset.le_sup' (fun e => e 1) he
    dsimp [N]
    omega
  exact ⟨N, hN,
    oneSidedSymbol_maximal_diagonal_singleton_face_of_bound T hside d hd hdiag hmax N hbound⟩

/-- At a sufficiently steep diagonal perturbation, a mate with positive
grade somewhere has positive grade on its selected leading face. -/
theorem positive_grade_in_diagonal_leading_face (T : Module.End ℂ ℂ[X])
    (N : ℕ)
    (hbound : ∀ e ∈ (symbol T).support, e 1 < N)
    (hpositive : ∃ e ∈ (symbol T).support, 0 < grade e) :
    ∃ d ∈ (leadingForm (N : ℤ) (1 - (N : ℤ)) T).support, 0 < grade d := by
  have hcoordBound : ∀ p ∈ oneSidedSymbolCoords T, p.2 < N := by
    intro p hp
    have he := (oneSidedSymbolCoords_mem_iff T p).mp hp
    simpa [expo] using hbound (expo p.1 p.2) he
  have hcoordPos : ∃ p ∈ oneSidedSymbolCoords T, p.2 < p.1 := by
    obtain ⟨e, he, hgrade⟩ := hpositive
    refine ⟨(e 0, e 1), Finset.mem_image.mpr ⟨e, he, rfl⟩, ?_⟩
    simp [grade] at hgrade
    omega
  obtain ⟨p, hp, hpos, hmax⟩ :=
    positive_grade_at_diagonal_normal_max (oneSidedSymbolCoords T) N
      hcoordBound hcoordPos
  let d := expo p.1 p.2
  have hd : d ∈ (symbol T).support := (oneSidedSymbolCoords_mem_iff T p).mp hp
  have hweight (e : Fin 2 →₀ ℕ) :
      realNewtonWeight (N : ℝ) (1 - (N : ℝ)) e =
        (diagonalVertexWeight N (e 0, e 1) : ℝ) := by
    simp [realNewtonWeight, diagonalVertexWeight]
  have hface : d ∈ realExposedFace (N : ℝ) (1 - (N : ℝ))
      ((symbol T).support : Set (Fin 2 →₀ ℕ)) := by
    constructor
    · exact hd
    · intro e he
      have hem : (e 0, e 1) ∈ oneSidedSymbolCoords T :=
        Finset.mem_image.mpr ⟨e, he, rfl⟩
      have hle := hmax (e 0, e 1) hem
      rw [hweight e, hweight d]
      simpa [d, expo] using (show
        (diagonalVertexWeight N (e 0, e 1) : ℝ) ≤
          (diagonalVertexWeight N p : ℝ) by exact_mod_cast hle)
  refine ⟨d, ?_, ?_⟩
  · apply (leadingForm_mem_iff_realExposedFace _ _ T d).mpr
    simpa using hface
  · simp [d, grade, expo]
    omega

/-- A singleton face supported at a diagonal exponent has no linear `X` or
`Y` coefficient, so its Poisson bracket with any mate cannot equal one. -/
theorem diagonal_singleton_face_poisson_ne_one
    (R F : MvPolynomial (Fin 2) ℂ) (d : Fin 2 →₀ ℕ)
    (hdiag : d 0 = d 1) (hsupp : R.support = {d}) :
    poisson R F ≠ 1 ∧ poisson F R ≠ 1 := by
  have hYnot : expo 0 1 ∉ R.support := by
    rw [hsupp]
    intro h
    have he : expo 0 1 = d := Finset.mem_singleton.mp h
    have h0 : d 0 = 0 := by simpa [expo] using congrArg (fun e : Fin 2 →₀ ℕ => e 0) he.symm
    have h1 : d 1 = 1 := by simpa [expo] using congrArg (fun e : Fin 2 →₀ ℕ => e 1) he.symm
    omega
  have hXnot : expo 1 0 ∉ R.support := by
    rw [hsupp]
    intro h
    have he : expo 1 0 = d := Finset.mem_singleton.mp h
    have h0 : d 0 = 1 := by simpa [expo] using congrArg (fun e : Fin 2 →₀ ℕ => e 0) he.symm
    have h1 : d 1 = 0 := by simpa [expo] using congrArg (fun e : Fin 2 →₀ ℕ => e 1) he.symm
    omega
  have hY : MvPolynomial.coeff (expo 0 1) R = 0 := by
    by_contra hn
    exact hYnot (MvPolynomial.mem_support_iff.mpr hn)
  have hX : MvPolynomial.coeff (expo 1 0) R = 0 := by
    by_contra hn
    exact hXnot (MvPolynomial.mem_support_iff.mpr hn)
  constructor
  · intro hbr
    have hcoeff := congrArg (MvPolynomial.coeff 0) hbr
    rw [poisson_coeff_zero, hY, hX] at hcoeff
    simp at hcoeff
  · intro hbr
    have hcoeff := congrArg (MvPolynomial.coeff 0) hbr
    rw [poisson_coeff_zero, hY, hX] at hcoeff
    simp at hcoeff

/-- The positive-grade mate face rules out the zero-bracket alternative at
the same diagonal perturbation. Together with the preceding singleton
coefficient argument, this excludes an exact pair with such a diagonal point
under a common support bound. -/
theorem no_exact_pair_with_maximal_diagonal_of_bound (P Q : A1 ℂ)
    (hpair : Q * P - P * Q = 1)
    (hPside : ∀ e ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade e ≤ 0)
    (hQpositive : ∃ e ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, 0 < grade e)
    (d : Fin 2 →₀ ℕ)
    (hd : d ∈ (symbol (P : Module.End ℂ ℂ[X])).support)
    (hdiag : d 0 = d 1) (hdpos : 0 < d 0)
    (hmax : ∀ e ∈ (symbol (P : Module.End ℂ ℂ[X])).support,
      e 0 = e 1 → e 1 ≤ d 1)
    (N : ℕ)
    (hPbound : ∀ e ∈ (symbol (P : Module.End ℂ ℂ[X])).support, e 1 < N)
    (hQbound : ∀ e ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, e 1 < N) : False := by
  let ρ : ℤ := N
  let σ : ℤ := 1 - (N : ℤ)
  let R := leadingForm ρ σ (P : Module.End ℂ ℂ[X])
  let F := leadingForm ρ σ (Q : Module.End ℂ ℂ[X])
  have hRsupport : R.support = {d} :=
    oneSidedSymbol_maximal_diagonal_singleton_face_of_bound
      (P : Module.End ℂ ℂ[X]) hPside d hd hdiag hmax N hPbound
  obtain ⟨e, heF, hepos⟩ :=
    positive_grade_in_diagonal_leading_face
      (Q : Module.End ℂ ℂ[X]) N hQbound hQpositive
  have hsum : 0 < ρ + σ := by dsimp [ρ, σ]; omega
  have hbr := exactPair_leadingPoisson_zero_or_one P Q ρ σ hsum hpair
  have hneOne : poisson F R ≠ 1 :=
    (diagonal_singleton_face_poisson_ne_one R F d hdiag hRsupport).2
  have hzero : poisson F R = 0 := hbr.resolve_right hneOne
  have hRnonconst : ∃ a ∈ R.support, a ≠ 0 := by
    refine ⟨d, hRsupport ▸ Finset.mem_singleton_self d, ?_⟩
    intro hz
    have hzero : d 0 = 0 := by rw [hz]; simp
    omega
  have hFnonconst : ∃ a ∈ F.support, a ≠ 0 := by
    refine ⟨e, heF, ?_⟩
    intro hz
    rw [hz] at hepos
    simp [grade] at hepos
  have hRne : R ≠ 0 := by
    intro hz
    have hdR : d ∈ R.support := by rw [hRsupport]; simp
    simp [hz] at hdR
  have hFne : F ≠ 0 := by
    intro hz
    have : e ∈ F.support := heF
    rw [hz] at this
    simp at this
  have hRside : ∀ a ∈ R.support, grade a ≤ 0 := by
    intro a ha
    have ha' : a = d := by rw [hRsupport] at ha; simpa using ha
    rw [ha']
    simp [grade, hdiag]
  have hRhom : R.IsWeightedHomogeneous (wt ρ σ)
      (vDeg ρ σ (P : Module.End ℂ ℂ[X])) := by
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol (P : Module.End ℂ ℂ[X])) (w := wt ρ σ)
      (n := vDeg ρ σ (P : Module.End ℂ ℂ[X]))
  have hFhom : F.IsWeightedHomogeneous (wt ρ σ)
      (vDeg ρ σ (Q : Module.End ℂ ℂ[X])) := by
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol (Q : Module.End ℂ ℂ[X])) (w := wt ρ σ)
      (n := vDeg ρ σ (Q : Module.End ℂ ℂ[X]))
  have hwnz : (wt ρ σ) 0 ≠ 0 ∨ (wt ρ σ) 1 ≠ 0 := by
    left
    have hN : 0 < N := by
      obtain ⟨a, ha, _⟩ := hQpositive
      have hab := hQbound a ha
      omega
    simp [wt, ρ]
    omega
  have hneZero := poisson_ne_zero_of_homogeneous_faces_grade_separated
    (wt ρ σ) (vDeg ρ σ (P : Module.End ℂ ℂ[X]))
    (vDeg ρ σ (Q : Module.End ℂ ℂ[X])) R F hwnz
    (by intro a ha; exact hRhom (MvPolynomial.mem_support_iff.mp ha))
    (by intro a ha; exact hFhom (MvPolynomial.mem_support_iff.mp ha))
    hRnonconst hFnonconst hRne hFne hRside ⟨e, heF, hepos⟩
  apply hneZero
  have hanti : poisson R F = -poisson F R := by unfold poisson; ring
  rw [hanti, hzero]
  simp

/-- The common perturbation bound is obtained from the finite supports of
both operators; the mate is unrestricted in order and mass. -/
theorem no_exact_pair_with_maximal_diagonal (P Q : A1 ℂ)
    (hpair : Q * P - P * Q = 1)
    (hPside : ∀ e ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade e ≤ 0)
    (hQpositive : ∃ e ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, 0 < grade e)
    (d : Fin 2 →₀ ℕ)
    (hd : d ∈ (symbol (P : Module.End ℂ ℂ[X])).support)
    (hdiag : d 0 = d 1) (hdpos : 0 < d 0)
    (hmax : ∀ e ∈ (symbol (P : Module.End ℂ ℂ[X])).support,
      e 0 = e 1 → e 1 ≤ d 1) : False := by
  let SP := (symbol (P : Module.End ℂ ℂ[X])).support
  let SQ := (symbol (Q : Module.End ℂ ℂ[X])).support
  have hQpositive' := hQpositive
  obtain ⟨q, hq, _⟩ := hQpositive
  let MP := SP.sup' ⟨d, hd⟩ (fun e => e 1)
  let MQ := SQ.sup' ⟨q, hq⟩ (fun e => e 1)
  let N := max MP MQ + 1
  have hPbound : ∀ e ∈ SP, e 1 < N := by
    intro e he
    have hle : e 1 ≤ MP := Finset.le_sup' (fun e => e 1) he
    dsimp [N]
    omega
  have hQbound : ∀ e ∈ SQ, e 1 < N := by
    intro e he
    have hle : e 1 ≤ MQ := Finset.le_sup' (fun e => e 1) he
    dsimp [N]
    omega
  exact no_exact_pair_with_maximal_diagonal_of_bound P Q hpair hPside hQpositive'
    d hd hdiag hdpos hmax N hPbound hQbound

/-- No positive diagonal PBW exponent occurs in a one-sided exact member.
The mate has no order or mass bound. -/
theorem oneSided_exact_pair_no_positive_diagonal (P Q : A1 ℂ)
    (hpair : Q * P - P * Q = 1)
    (hPside : ∀ e ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade e ≤ 0)
    (hQpositive : ∃ e ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, 0 < grade e) :
    ¬ ∃ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support,
      d 0 = d 1 ∧ 0 < d 0 := by
  intro hex
  classical
  let S := (symbol (P : Module.End ℂ ℂ[X])).support.filter
    (fun d => d 0 = d 1 ∧ 0 < d 0)
  obtain ⟨d₀, hd₀, hdiag₀, hpos₀⟩ := hex
  have hS : S.Nonempty := by
    refine ⟨d₀, ?_⟩
    exact Finset.mem_filter.mpr ⟨hd₀, hdiag₀, hpos₀⟩
  obtain ⟨d, hdS, hmaxS⟩ := S.exists_max_image (fun e => e 1) hS
  have hdParts : d ∈ (symbol (P : Module.End ℂ ℂ[X])).support ∧
      d 0 = d 1 ∧ 0 < d 0 := by
    simpa [S] using hdS
  obtain ⟨hd, hdiag, hdpos⟩ := hdParts
  have hmax : ∀ e ∈ (symbol (P : Module.End ℂ ℂ[X])).support,
      e 0 = e 1 → e 1 ≤ d 1 := by
    intro e he hediag
    by_cases hpos : 0 < e 0
    · exact hmaxS e (Finset.mem_filter.mpr ⟨he, hediag, hpos⟩)
    · have he0 : e 0 = 0 := by omega
      omega
  exact no_exact_pair_with_maximal_diagonal P Q hpair hPside hQpositive
    d hd hdiag hdpos hmax

/-- After removing the scalar term, nonpositive support of an exact pair is
actually strictly negative. This is the source-case premise used by the
one-sided face dispatch. -/
theorem oneSided_exact_pair_strict_grade (P Q : A1 ℂ)
    (hpair : Q * P - P * Q = 1)
    (hPside : ∀ e ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade e ≤ 0)
    (hPscalarFree : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (P : Module.End ℂ ℂ[X])).support)
    (hQpositive : ∃ e ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, 0 < grade e) :
    ∀ e ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade e < 0 := by
  intro e he
  have hle := hPside e he
  by_contra hn
  have hzero : grade e = 0 := by omega
  have hdiag : e 0 = e 1 := by simp [grade] at hzero; omega
  by_cases hpos : 0 < e 0
  · exact oneSided_exact_pair_no_positive_diagonal P Q hpair hPside hQpositive
      ⟨e, he, hdiag, hpos⟩
  · have h0 : e = 0 := by
      ext i
      fin_cases i
      · have hz : e 0 = 0 := by omega
        simpa using hz
      · have hz : e 1 = 0 := by omega
        simpa using hz
    exact hPscalarFree (h0 ▸ he)

/-- For a scalar-free nonmonomial exact pair, the one-sided hypotheses now
produce the two native nonmonomial face cases directly. The remaining task is
to exclude the selected face using its exact commutator constraints. -/
theorem oneSided_exact_pair_face_dispatch (P Q : A1 ℂ)
    (hpair : Q * P - P * Q = 1)
    (hPside : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d ≤ 0)
    (hPnonconstant : ∃ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, d ≠ 0)
    (hQnonconstant : ∃ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, d ≠ 0)
    (hPscalarFree : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (P : Module.End ℂ ℂ[X])).support)
    (hQscalarFree : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (Q : Module.End ℂ ℂ[X])).support)
    (hPother : ∃ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support,
      d ≠ expo 0 1) :
    (∃ d ∈ (leadingForm 1 (-1) (P : Module.End ℂ ℂ[X])).support,
      d ≠ expo 0 1 ∧
      expo 0 1 ∈ (leadingForm 1 (-1) (P : Module.End ℂ ℂ[X])).support) ∨
    (∃ ρ σ : ℤ, 0 < ρ + σ ∧
      expo 0 1 ∈ (leadingForm ρ σ (P : Module.End ℂ ℂ[X])).support ∧
      ∃ d ∈ (leadingForm ρ σ (P : Module.End ℂ ℂ[X])).support,
        d ≠ expo 0 1) := by
  have hQpositive : ∃ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support,
      0 < grade d := by
    by_contra hn
    have hQside : ∀ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support,
        grade d ≤ 0 := by
      intro d hd
      by_contra hnot
      exact hn ⟨d, hd, lt_of_not_ge hnot⟩
    exact (no_exact_pair_both_nonpositive P Q hPside hQside) hpair
  have hstrict := oneSided_exact_pair_strict_grade P Q hpair hPside
    hPscalarFree hQpositive
  have hgen := oneSided_exact_pair_has_generator P Q hPnonconstant
    hQnonconstant hPscalarFree hQscalarFree hPside hpair
  exact oneSidedSymbol_face_dispatch (P : Module.End ℂ ℂ[X]) hstrict hgen hPother

/-- The grade-boundary alternative of the native dispatch is excluded by
the already formalized Han--Tan case (a.2), with the mate sign adjusted to
the project's `[Q,P]=1` convention. -/
theorem oneSided_exact_pair_grade_boundary_impossible (P Q : A1 ℂ)
    (hpair : Q * P - P * Q = 1)
    (hgen : expo 0 1 ∈
      (leadingForm 1 (-1) (P : Module.End ℂ ℂ[X])).support)
    (hother : ∃ d ∈
      (leadingForm 1 (-1) (P : Module.End ℂ ℂ[X])).support,
      d ≠ expo 0 1) : False := by
  have hpair' : P * (-Q) - (-Q) * P = 1 := by
    have h : P * (-Q) - (-Q) * P = Q * P - P * Q := by
      apply Subtype.ext
      change (P : Module.End ℂ ℂ[X]) * (-(Q : Module.End ℂ ℂ[X])) -
          (-(Q : Module.End ℂ ℂ[X])) * (P : Module.End ℂ ℂ[X]) =
          (Q : Module.End ℂ ℂ[X]) * (P : Module.End ℂ ℂ[X]) -
            (P : Module.End ℂ ℂ[X]) * (Q : Module.End ℂ ℂ[X])
      have h1 : (P : Module.End ℂ ℂ[X]) * (-(Q : Module.End ℂ ℂ[X])) =
          -((P : Module.End ℂ ℂ[X]) * (Q : Module.End ℂ ℂ[X])) := by
        ext f
        simp [Module.End.mul_apply]
      have h2 : (-(Q : Module.End ℂ ℂ[X])) * (P : Module.End ℂ ℂ[X]) =
          -((Q : Module.End ℂ ℂ[X]) * (P : Module.End ℂ ℂ[X])) := by
        ext f
        simp [Module.End.mul_apply]
      rw [h1, h2]
      abel
    rw [h, hpair]
  have hcard : 1 <
      (leadingForm 1 (-1) (P : Module.End ℂ ℂ[X])).support.card := by
    obtain ⟨d, hd, hne⟩ := hother
    have hne' : expo 0 1 ≠ d := Ne.symm hne
    exact Finset.one_lt_card.mpr ⟨expo 0 1, hgen, d, hd, hne'⟩
  exact hanTan_case_a2_face_impossible P (-Q) hpair' hgen hcard

/-- A scalar-free one-sided exact pair with nonmonomial first member must
therefore have a positive-sum integer leading face containing the derivative
generator and another monomial. The remaining strict-face exclusion is the
sole open branch of this source-case dispatch. -/
theorem oneSided_exact_pair_strict_face (P Q : A1 ℂ)
    (hpair : Q * P - P * Q = 1)
    (hPside : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d ≤ 0)
    (hPnonconstant : ∃ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, d ≠ 0)
    (hQnonconstant : ∃ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, d ≠ 0)
    (hPscalarFree : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (P : Module.End ℂ ℂ[X])).support)
    (hQscalarFree : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (Q : Module.End ℂ ℂ[X])).support)
    (hPother : ∃ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support,
      d ≠ expo 0 1) :
    ∃ ρ σ : ℤ, 0 < ρ + σ ∧
      expo 0 1 ∈ (leadingForm ρ σ (P : Module.End ℂ ℂ[X])).support ∧
      ∃ d ∈ (leadingForm ρ σ (P : Module.End ℂ ℂ[X])).support,
        d ≠ expo 0 1 := by
  obtain hcase := oneSided_exact_pair_face_dispatch P Q hpair hPside
    hPnonconstant hQnonconstant hPscalarFree hQscalarFree hPother
  rcases hcase with ⟨d, hd, hne, hgen⟩ | hstrict
  · exact False.elim (oneSided_exact_pair_grade_boundary_impossible P Q
      hpair hgen ⟨d, hd, hne⟩)
  · exact hstrict

/-- A positive-sum two-point face through `Y` in strictly negative support
automatically has the strict/horizontal crossing normal used by the local
bracket-one exclusions. The second exponent is at least two grades below
the diagonal. -/
theorem oneSided_symbol_face_normal_sign (T : Module.End ℂ ℂ[X])
    (hstrict : ∀ e ∈ (symbol T).support, grade e < 0)
    (ρ σ : ℤ) (hsum : 0 < ρ + σ)
    (hgen : expo 0 1 ∈ (leadingForm ρ σ T).support)
    (d : Fin 2 →₀ ℕ) (hd : d ∈ (leadingForm ρ σ T).support)
    (hne : d ≠ expo 0 1) :
    0 < ρ ∧ σ ≤ 0 ∧ d 0 + 1 < d 1 := by
  have hdSymbol := leadingForm_support_subset_symbol_support T ρ σ hd
  have hgrade := hstrict d hdSymbol
  obtain ⟨⟨i,j⟩, hde⟩ := expo_surjective d
  have hpairNe : (i,j) ≠ (0,1) := by
    intro he
    apply hne
    rcases he with ⟨rfl, rfl⟩
    exact hde.symm
  have hpoint : i < j := by
    rw [← hde] at hgrade
    simp [grade, expo] at hgrade
    omega
  have hgenFilter : Finsupp.weight (wt ρ σ) (expo 0 1) = vDeg ρ σ T := by
    change expo 0 1 ∈ (MvPolynomial.weightedHomogeneousComponent (wt ρ σ)
      (vDeg ρ σ T) (symbol T)).support at hgen
    rw [MvPolynomial.support_weightedHomogeneousComponent] at hgen
    exact (Finset.mem_filter.mp hgen).2
  have hdFilter : Finsupp.weight (wt ρ σ) d = vDeg ρ σ T := by
    change d ∈ (MvPolynomial.weightedHomogeneousComponent (wt ρ σ)
      (vDeg ρ σ T) (symbol T)).support at hd
    rw [MvPolynomial.support_weightedHomogeneousComponent] at hd
    exact (Finset.mem_filter.mp hd).2
  have hweight : ρ * (i : ℤ) + σ * (j : ℤ) = σ := by
    rw [← hde, expo_weight] at hdFilter
    rw [expo_weight] at hgenFilter
    simp at hgenFilter
    nlinarith [hdFilter, hgenFilter]
  obtain ⟨hρ, hσ, hgap⟩ :=
    oneSided_two_point_normal_sign ρ σ (i,j) hsum hpoint hpairNe hweight
  refine ⟨hρ, hσ, ?_⟩
  rw [← hde]
  simpa [expo] using hgap

/-- The remaining exact-pair branch has the actual strict/horizontal Newton
normal: positive first coordinate, nonpositive second coordinate, and positive
sum. No restriction is placed on the mate's mass or differential order. -/
theorem oneSided_exact_pair_strict_negative_face (P Q : A1 ℂ)
    (hpair : Q * P - P * Q = 1)
    (hPside : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d ≤ 0)
    (hPnonconstant : ∃ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, d ≠ 0)
    (hQnonconstant : ∃ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, d ≠ 0)
    (hPscalarFree : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (P : Module.End ℂ ℂ[X])).support)
    (hQscalarFree : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (Q : Module.End ℂ ℂ[X])).support)
    (hPother : ∃ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support,
      d ≠ expo 0 1) :
    ∃ ρ σ : ℤ, 0 < ρ ∧ σ ≤ 0 ∧ 0 < ρ + σ ∧
      expo 0 1 ∈ (leadingForm ρ σ (P : Module.End ℂ ℂ[X])).support ∧
      ∃ d ∈ (leadingForm ρ σ (P : Module.End ℂ ℂ[X])).support,
        d ≠ expo 0 1 ∧ d 0 + 1 < d 1 := by
  obtain ⟨ρ, σ, hsum, hgen, d, hd, hne⟩ :=
    oneSided_exact_pair_strict_face P Q hpair hPside hPnonconstant
      hQnonconstant hPscalarFree hQscalarFree hPother
  have hQpositive : ∃ e ∈ (symbol (Q : Module.End ℂ ℂ[X])).support,
      0 < grade e := by
    by_contra hn
    have hQside : ∀ e ∈ (symbol (Q : Module.End ℂ ℂ[X])).support,
        grade e ≤ 0 := by
      intro e he
      by_contra hnot
      exact hn ⟨e, he, lt_of_not_ge hnot⟩
    exact (no_exact_pair_both_nonpositive P Q hPside hQside) hpair
  have hstrict := oneSided_exact_pair_strict_grade P Q hpair hPside
    hPscalarFree hQpositive
  obtain ⟨hρ, hσ, hgap⟩ := oneSided_symbol_face_normal_sign
    (P : Module.End ℂ ℂ[X]) hstrict ρ σ hsum hgen d hd hne
  exact ⟨ρ, σ, hρ, hσ, hsum, hgen, d, hd, hne, hgap⟩

/-- The native strict/horizontal face selected from a scalar-free
one-sided exact pair must have zero leading Poisson bracket. The bracket-one
alternative is eliminated by the complete primitive crossing argument. -/
theorem oneSided_exact_pair_selected_face_bracket_zero (P Q : A1 ℂ)
    (hpair : Q * P - P * Q = 1)
    (hPside : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d ≤ 0)
    (hPnonconstant : ∃ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, d ≠ 0)
    (hQnonconstant : ∃ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, d ≠ 0)
    (hPscalarFree : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (P : Module.End ℂ ℂ[X])).support)
    (hQscalarFree : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (Q : Module.End ℂ ℂ[X])).support)
    (hPother : ∃ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support,
      d ≠ expo 0 1) :
    ∃ ρ σ : ℤ, 0 < ρ ∧ σ ≤ 0 ∧ 0 < ρ + σ ∧
      expo 0 1 ∈ (leadingForm ρ σ (P : Module.End ℂ ℂ[X])).support ∧
      1 < (leadingForm ρ σ (P : Module.End ℂ ℂ[X])).support.card ∧
      poisson (leadingForm ρ σ (Q : Module.End ℂ ℂ[X]))
        (leadingForm ρ σ (P : Module.End ℂ ℂ[X])) = 0 := by
  obtain ⟨ρ, σ, hρ, hσ, hsum, hY, d, hd, hne, _⟩ :=
    oneSided_exact_pair_strict_negative_face P Q hpair hPside
      hPnonconstant hQnonconstant hPscalarFree hQscalarFree hPother
  have hcard : 1 < (leadingForm ρ σ (P : Module.End ℂ ℂ[X])).support.card :=
    Finset.one_lt_card.mpr ⟨expo 0 1, hY, d, hd, Ne.symm hne⟩
  have hscalar : MvPolynomial.coeff (expo 0 0)
      (leadingForm ρ σ (P : Module.End ℂ ℂ[X])) = 0 := by
    have hnot : expo 0 0 ∉ (leadingForm ρ σ (P : Module.End ℂ ℂ[X])).support := by
      intro hmem
      have hfull := leadingForm_support_subset_symbol_support
        (P : Module.End ℂ ℂ[X]) ρ σ hmem
      exact hPscalarFree (by simpa [expo] using hfull)
    simpa [MvPolynomial.mem_support_iff] using hnot
  have hsplit := exactPair_leadingPoisson_zero_or_one P Q ρ σ hsum hpair
  have hzero : poisson (leadingForm ρ σ (Q : Module.End ℂ ℂ[X]))
      (leadingForm ρ σ (P : Module.End ℂ ℂ[X])) = 0 := by
    rcases hsplit with hz | hone
    · exact hz
    · exact False.elim (crossing_pair_bracket_one_impossible
        (P : Module.End ℂ ℂ[X]) (Q : Module.End ℂ ℂ[X]) ρ σ
        hρ hσ hsum hY hscalar hcard hone)
  exact ⟨ρ, σ, hρ, hσ, hsum, hY, hcard, hzero⟩

/-- A nonzero exponent of nonpositive weight cannot lie on the same
nonnegative ray as an exponent of positive weight. -/
theorem collinear_exponents_nonpositive_vs_positive_weight
    (w : Fin 2 → ℤ) (a b : Fin 2 →₀ ℕ)
    (hane : a ≠ 0)
    (hcol : a 1 * b 0 = a 0 * b 1)
    (ha : Finsupp.weight w a ≤ 0)
    (hb : 0 < Finsupp.weight w b) : False := by
  have hcolZ : (a 1 : ℤ) * b 0 = (a 0 : ℤ) * b 1 := by exact_mod_cast hcol
  have haw : (a 0 : ℤ) * w 0 + (a 1 : ℤ) * w 1 ≤ 0 := by
    simpa [Finsupp.weight_eq_sum, Fin.sum_univ_succ] using ha
  have hbw : 0 < (b 0 : ℤ) * w 0 + (b 1 : ℤ) * w 1 := by
    simpa [Finsupp.weight_eq_sum, Fin.sum_univ_succ] using hb
  by_cases ha0 : a 0 = 0
  · have ha1 : 0 < a 1 := by
      by_contra hn
      have hz : a 1 = 0 := by omega
      apply hane
      ext i
      fin_cases i <;> simp [ha0, hz]
    have hmul := congrArg (fun z : ℤ => w 0 * z) hcolZ
    have hrel :
        ((b 0 : ℤ) * w 0 + (b 1 : ℤ) * w 1) * a 1 =
          ((a 0 : ℤ) * w 0 + (a 1 : ℤ) * w 1) * b 1 := by
      nlinarith [hmul]
    have hleft : 0 <
        ((b 0 : ℤ) * w 0 + (b 1 : ℤ) * w 1) * a 1 :=
      mul_pos hbw (by exact_mod_cast ha1)
    have hright :
        ((a 0 : ℤ) * w 0 + (a 1 : ℤ) * w 1) * b 1 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg haw (by positivity)
    omega

  · have ha0pos : 0 < a 0 := Nat.pos_of_ne_zero ha0
    have hmul := congrArg (fun z : ℤ => w 1 * z) hcolZ
    have hrel :
        ((b 0 : ℤ) * w 0 + (b 1 : ℤ) * w 1) * a 0 =
          ((a 0 : ℤ) * w 0 + (a 1 : ℤ) * w 1) * b 0 := by
      nlinarith [hmul]
    have hleft : 0 <
        ((b 0 : ℤ) * w 0 + (b 1 : ℤ) * w 1) * a 0 :=
      mul_pos hbw (by exact_mod_cast ha0pos)
    have hright :
        ((a 0 : ℤ) * w 0 + (a 1 : ℤ) * w 1) * b 0 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg haw (by positivity)
    omega

/-- The zero Poisson bracket forces collinear endpoint exponents. In the
nonnegative exponent quadrant, that is incompatible with nonpositive weight
on a scalar-free first face and positive weight on the mate face. -/
theorem poisson_ne_zero_of_opposite_face_weight_signs
    (w : Fin 2 → ℤ) (m n : ℤ)
    (R F : MvPolynomial (Fin 2) ℂ)
    (hwnz : w 0 ≠ 0 ∨ w 1 ≠ 0)
    (hRhom : ∀ a ∈ R.support, Finsupp.weight w a = m)
    (hFhom : ∀ b ∈ F.support, Finsupp.weight w b = n)
    (hRscalarFree : (0 : Fin 2 →₀ ℕ) ∉ R.support)
    (hRne : R ≠ 0) (hFne : F ≠ 0)
    (hm : m ≤ 0) (hn : 0 < n) : poisson R F ≠ 0 := by
  intro hzero
  obtain ⟨a, _, b, _, ha, _, hb, _, _, _, _, _, hcol, _⟩ :=
    poisson_homogeneous_support_endpoints_collinear w m n R F hwnz
      hRhom hFhom hRne hFne hzero
  have hcolNat : a 1 * b 0 = a 0 * b 1 := by
    have h := sub_eq_zero.mp hcol
    exact_mod_cast h
  exact collinear_exponents_nonpositive_vs_positive_weight w a b
    (by exact fun hz => hRscalarFree (hz ▸ ha)) hcolNat
    ((hRhom a ha).trans_le hm) (hn.trans_eq (hFhom b hb).symm)

/-- A positive PBW grade has positive weight in every strict/horizontal
normal with positive first coordinate and positive coordinate sum. -/
theorem positive_grade_positive_crossing_weight
    (ρ σ : ℤ) (a : Fin 2 →₀ ℕ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ) (hgrade : 0 < grade a) :
    0 < Finsupp.weight (wt ρ σ) a := by
  have hgap : 0 < (a 0 : ℤ) - a 1 := by simpa [grade] using hgrade
  have hgapmul : 0 < ρ * ((a 0 : ℤ) - a 1) := mul_pos hρ hgap
  have hrest : 0 ≤ (ρ + σ) * (a 1 : ℤ) :=
    mul_nonneg (le_of_lt hsum) (by positivity)
  have hweight : Finsupp.weight (wt ρ σ) a =
      ρ * ((a 0 : ℤ) - a 1) + (ρ + σ) * (a 1 : ℤ) := by
    simp [Finsupp.weight_eq_sum, Fin.sum_univ_succ, wt]
    ring
  omega

private theorem weightedDegree_eq_vDeg_of_mem_symbol_support_local
    (ρ σ : ℤ) (T : Module.End ℂ ℂ[X]) {a : Fin 2 →₀ ℕ}
    (ha : a ∈ (symbol T).support) :
    MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol T) =
      (vDeg ρ σ T : WithBot ℤ) := by
  have hsymbol : symbol T ≠ 0 := by
    intro hz
    have hsupport : (symbol T).support = ∅ := by simp [hz]
    rw [hsupport] at ha
    exact Finset.notMem_empty a ha
  have hnotbot : MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol T) ≠ ⊥ := by
    intro hbot
    exact hsymbol ((MvPolynomial.weightedTotalDegree'_eq_bot_iff _ _).mp hbot)
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hnotbot
  rw [← hm]
  simp [vDeg, ← hm]

/-- A positive-grade monomial anywhere in the mate's full support makes
its selected leading weight positive in every crossing normal. This does
not claim that the positive-grade monomial itself lies on the selected face. -/
theorem positive_grade_forces_positive_crossing_vDeg
    (T : Module.End ℂ ℂ[X]) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ + σ)
    (hpositive : ∃ a ∈ (symbol T).support, 0 < grade a) :
    0 < vDeg ρ σ T := by
  obtain ⟨a, ha, hgrade⟩ := hpositive
  have hweight := positive_grade_positive_crossing_weight ρ σ a hρ hsum hgrade
  have hleBot : (Finsupp.weight (wt ρ σ) a : WithBot ℤ) ≤
      MvPolynomial.weightedTotalDegree' (wt ρ σ) (symbol T) := by
    rw [MvPolynomial.weightedTotalDegree']
    exact Finset.le_sup
      (f := fun e => (Finsupp.weight (wt ρ σ) e : WithBot ℤ)) ha
  rw [weightedDegree_eq_vDeg_of_mem_symbol_support_local ρ σ T ha] at hleBot
  have hle : Finsupp.weight (wt ρ σ) a ≤ vDeg ρ σ T :=
    WithBot.coe_le_coe.mp hleBot
  exact lt_of_lt_of_le hweight hle

/-- At a selected scalar-free face through `Y`, a full-support positive
grade on the mate already contradicts zero Poisson bracket. No assertion
about the grade of the mate's selected face is needed. -/
theorem crossing_zero_bracket_impossible_of_mate_positive_grade
    (P Q : A1 ℂ) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hσ : σ ≤ 0) (hsum : 0 < ρ + σ)
    (hY : expo 0 1 ∈ (leadingForm ρ σ (P : Module.End ℂ ℂ[X])).support)
    (hPscalarFree : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (P : Module.End ℂ ℂ[X])).support)
    (hQpositive : ∃ a ∈ (symbol (Q : Module.End ℂ ℂ[X])).support,
      0 < grade a)
    (hzero : poisson (leadingForm ρ σ (Q : Module.End ℂ ℂ[X]))
      (leadingForm ρ σ (P : Module.End ℂ ℂ[X])) = 0) : False := by
  let R := leadingForm ρ σ (P : Module.End ℂ ℂ[X])
  let F := leadingForm ρ σ (Q : Module.End ℂ ℂ[X])
  have hRdeg : vDeg ρ σ (P : Module.End ℂ ℂ[X]) = σ := by
    have h := (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol (P : Module.End ℂ ℂ[X])) (w := wt ρ σ)
      (n := vDeg ρ σ (P : Module.End ℂ ℂ[X])))
      (MvPolynomial.mem_support_iff.mp hY)
    simpa [expo_weight] using h.symm
  have hFpos : 0 < vDeg ρ σ (Q : Module.End ℂ ℂ[X]) :=
    positive_grade_forces_positive_crossing_vDeg
      (Q : Module.End ℂ ℂ[X]) ρ σ hρ hsum hQpositive
  have hRhom : ∀ a ∈ R.support,
      Finsupp.weight (wt ρ σ) a = vDeg ρ σ (P : Module.End ℂ ℂ[X]) := by
    intro a ha
    exact (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol (P : Module.End ℂ ℂ[X])) (w := wt ρ σ)
      (n := vDeg ρ σ (P : Module.End ℂ ℂ[X])))
      (MvPolynomial.mem_support_iff.mp ha)
  have hFhom : ∀ b ∈ F.support,
      Finsupp.weight (wt ρ σ) b = vDeg ρ σ (Q : Module.End ℂ ℂ[X]) := by
    intro b hb
    exact (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol (Q : Module.End ℂ ℂ[X])) (w := wt ρ σ)
      (n := vDeg ρ σ (Q : Module.End ℂ ℂ[X])))
      (MvPolynomial.mem_support_iff.mp hb)
  have hRscalar : (0 : Fin 2 →₀ ℕ) ∉ R.support := by
    intro ha
    exact hPscalarFree (leadingForm_support_subset_symbol_support
      (P : Module.End ℂ ℂ[X]) ρ σ ha)
  have hRne : R ≠ 0 := by
    intro hz
    have hy : expo 0 1 ∈ R.support := hY
    simp [hz] at hy
  have hFne : F ≠ 0 := leadingForm_ne_zero_of_vDeg_pos Q ρ σ hFpos
  have hwnz : (wt ρ σ) 0 ≠ 0 ∨ (wt ρ σ) 1 ≠ 0 := by
    left
    simpa [wt] using ne_of_gt hρ
  have hanti : poisson R F = -poisson F R := by unfold poisson; ring
  have hzero' : poisson R F = 0 := by rw [hanti, hzero]; simp
  exact (poisson_ne_zero_of_opposite_face_weight_signs (wt ρ σ)
    (vDeg ρ σ (P : Module.End ℂ ℂ[X]))
    (vDeg ρ σ (Q : Module.End ℂ ℂ[X])) R F
    hwnz hRhom hFhom hRscalar hRne hFne
    (hRdeg.le.trans hσ) hFpos) hzero'

/-- A scalar-free one-sided exact pair cannot have a nonmonomial first
member. The selected face's bracket-one branch is excluded by crossing
rigidity, and its zero branch by opposite leading-weight signs. -/
theorem oneSided_exact_pair_nonmonomial_impossible (P Q : A1 ℂ)
    (hpair : Q * P - P * Q = 1)
    (hPside : ∀ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, grade d ≤ 0)
    (hPnonconstant : ∃ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support, d ≠ 0)
    (hQnonconstant : ∃ d ∈ (symbol (Q : Module.End ℂ ℂ[X])).support, d ≠ 0)
    (hPscalarFree : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (P : Module.End ℂ ℂ[X])).support)
    (hQscalarFree : (0 : Fin 2 →₀ ℕ) ∉
      (symbol (Q : Module.End ℂ ℂ[X])).support)
    (hPother : ∃ d ∈ (symbol (P : Module.End ℂ ℂ[X])).support,
      d ≠ expo 0 1) : False := by
  obtain ⟨ρ, σ, hρ, hσ, hsum, hY, _, hzero⟩ :=
    oneSided_exact_pair_selected_face_bracket_zero P Q hpair hPside
      hPnonconstant hQnonconstant hPscalarFree hQscalarFree hPother
  have hQpositive : ∃ a ∈ (symbol (Q : Module.End ℂ ℂ[X])).support,
      0 < grade a := by
    by_contra hn
    have hQside : ∀ a ∈ (symbol (Q : Module.End ℂ ℂ[X])).support,
        grade a ≤ 0 := by
      intro a ha
      by_contra hnot
      exact hn ⟨a, ha, lt_of_not_ge hnot⟩
    exact (no_exact_pair_both_nonpositive P Q hPside hQside) hpair
  exact crossing_zero_bracket_impossible_of_mate_positive_grade P Q ρ σ
    hρ hσ hsum hY hPscalarFree hQpositive hzero

end Dixmier.Weyl
