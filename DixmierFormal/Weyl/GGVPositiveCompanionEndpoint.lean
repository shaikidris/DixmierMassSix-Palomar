/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.OneSidedScalarNormalize
public import DixmierFormal.Weyl.GGVFaceFirstDownwardTilt
public import DixmierFormal.Weyl.PoissonDiagonalStart
public import DixmierFormal.Weyl.PureGradeCompanion
public import DixmierFormal.Weyl.PoissonFixedPointDivision
public import DixmierFormal.Weyl.GGVRationalFace
public import DixmierFormal.Weyl.GGVCompanionAdapter
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Positive-slope support of a homogeneous Poisson companion

This proves the lattice restriction used in G13 Lemma 6.4(1), then
extracts its first arithmetic consequence: a nonmonomial positive-slope
face with an exact homogeneous companion must have first weight one.
The remaining endpoint statement for the face itself is separated below.
-/

namespace Dixmier.Weyl

open MvPolynomial

/-- For `0 < ρ < σ`, a monomial of companion weight `ρ + σ` is either
on the `x`-axis or is exactly `xy`. -/
theorem positive_companion_support_restrict
    (ρ σ : ℕ) (hρ : 0 < ρ) (hρσ : ρ < σ)
    (F : MvPolynomial (Fin 2) ℂ)
    (hFhom : F.IsWeightedHomogeneous (wt (ρ : ℤ) (σ : ℤ))
      ((ρ : ℤ) + σ))
    (e : Fin 2 →₀ ℕ) (he : e ∈ F.support) :
    e 1 = 0 ∨ e = expo 1 1 := by
  have hw' : (e 0 : ℤ) * (ρ : ℤ) + (e 1 : ℤ) * (σ : ℤ) =
      (ρ : ℤ) + σ := by
    simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two] using
      hFhom (MvPolynomial.mem_support_iff.mp he)
  have hw : (ρ : ℤ) * (e 0 : ℤ) + (σ : ℤ) * (e 1 : ℤ) =
      (ρ : ℤ) + σ := by nlinarith [hw']
  by_cases hzero : e 1 = 0
  · exact Or.inl hzero
  · by_cases hone : e 1 = 1
    · have hiw : (ρ : ℤ) * (e 0 : ℤ) = ρ := by
        rw [hone] at hw
        nlinarith
      have hiwNat : ρ * e 0 = ρ := by exact_mod_cast hiw
      have hi : e 0 = 1 :=
        Nat.eq_of_mul_eq_mul_left hρ (by simpa using hiwNat)
      right
      ext i
      fin_cases i <;> simp [expo, hi, hone]
    · have htwo : 2 ≤ e 1 := by omega
      have hσ : 0 < (σ : ℤ) := by exact_mod_cast (lt_trans hρ hρσ)
      have htwoZ : (2 : ℤ) ≤ e 1 := by exact_mod_cast htwo
      have hlarge : 2 * (σ : ℤ) ≤ (σ : ℤ) * (e 1 : ℤ) :=
        by simpa [mul_comm] using
          mul_le_mul_of_nonneg_left htwoZ (le_of_lt hσ)
      have hwtLower : (σ : ℤ) * (e 1 : ℤ) ≤ (ρ : ℤ) + σ := by
        nlinarith [hw, mul_nonneg (show (0 : ℤ) ≤ ρ by omega)
          (show (0 : ℤ) ≤ (e 0 : ℤ) by exact_mod_cast Nat.zero_le (e 0))]
      have : σ ≤ ρ := by nlinarith
      omega

/-- If a nonzero weighted-homogeneous polynomial has at least two support
points, its exact companion cannot be supported only at `xy`. Thus the
companion has an occupied `x`-axis monomial. -/
theorem positive_companion_has_axis_term
    (ρ σ : ℕ) (hρ : 0 < ρ) (hρσ : ρ < σ)
    (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ)
    (hRhom : R.IsWeightedHomogeneous (wt (ρ : ℤ) (σ : ℤ)) m)
    (hFhom : F.IsWeightedHomogeneous (wt (ρ : ℤ) (σ : ℤ))
      ((ρ : ℤ) + σ))
    (hRface : 1 < R.support.card)
    (hcomp : poisson R F = R) :
    ∃ e ∈ F.support, e 1 = 0 := by
  by_contra haxis
  have hFsubset : F.support ⊆ {expo 1 1} := by
    intro e he
    rcases positive_companion_support_restrict ρ σ hρ hρσ F hFhom e he with h | h
    · exact False.elim (haxis ⟨e, he, h⟩)
    · simp [h]
  let c : ℂ := MvPolynomial.coeff (expo 1 1) F
  have hmono : F = monomial (expo 1 1) c :=
    eq_monomial_of_support_subset_singleton (by
      intro e he
      exact Finset.mem_singleton.mp (hFsubset he))
  have hexpo : expo 1 1 = Finsupp.single 0 1 + Finsupp.single 1 1 := by
    ext i
    fin_cases i <;> simp [expo]
  have hFxy : F = C c * X 0 * X 1 := by
    calc
      F = monomial (expo 1 1) c := hmono
      _ = monomial (Finsupp.single 0 1 + Finsupp.single 1 1) c := by rw [hexpo]
      _ = monomial (Finsupp.single 0 1) c * X 1 := by
        rw [monomial_add_single]
        simp
      _ = C c * X 0 * X 1 := by rw [C_mul_X_eq_monomial]
  have hlinear : poisson R (C c * X 0 * X 1) =
      C c * poisson R (X 0 * X 1) := by
    calc
      poisson R (C c * X 0 * X 1) = poisson R (C c * (X 0 * X 1)) := by
        rw [mul_assoc]
      _ = C c * poisson R (X 0 * X 1) := by
        unfold poisson
        simp only [MvPolynomial.pderiv_C_mul]
        ring
  rw [hFxy, hlinear] at hcomp
  have hcoeff (e : Fin 2 →₀ ℕ) (he : e ∈ R.support) :
      c * ((e 1 : ℂ) - (e 0 : ℂ)) = 1 := by
    have heCoeff : MvPolynomial.coeff e R ≠ 0 := MvPolynomial.mem_support_iff.mp he
    have h := congrArg (MvPolynomial.coeff e) hcomp
    rw [MvPolynomial.coeff_C_mul, poisson_xy_coeff] at h
    apply mul_right_cancel₀ heCoeff
    calc
      (c * ((e 1 : ℂ) - (e 0 : ℂ))) * MvPolynomial.coeff e R =
          c * (((e 1 : ℂ) - (e 0 : ℂ)) * MvPolynomial.coeff e R) := by ring
      _ = MvPolynomial.coeff e R := h
      _ = 1 * MvPolynomial.coeff e R := by ring
  obtain ⟨d, hd, e, he, hde⟩ := Finset.one_lt_card_iff.mp hRface
  have hc : c ≠ 0 := by
    intro hz
    have h := hcoeff d e
    rw [hz] at h
    norm_num at h
  have hcoeffEq : c * ((d 1 : ℂ) - d 0) =
      c * ((hd 1 : ℂ) - hd 0) :=
    (hcoeff d e).trans (hcoeff hd he).symm
  have hdiff := mul_left_cancel₀ hc hcoeffEq
  have hgrade : grade d = grade hd := by
    have hz' : (d 1 : ℤ) - d 0 = (hd 1 : ℤ) - hd 0 := by
      exact_mod_cast hdiff
    have hz : (d 0 : ℤ) - d 1 = (hd 0 : ℤ) - hd 1 := by omega
    simpa [grade] using hz
  have hweight : Finsupp.weight (wt (ρ : ℤ) (σ : ℤ)) d =
      Finsupp.weight (wt (ρ : ℤ) (σ : ℤ)) hd := by
    exact (hRhom (MvPolynomial.mem_support_iff.mp e)).trans
      (hRhom (MvPolynomial.mem_support_iff.mp he)).symm
  have hsum : (ρ : ℤ) + σ ≠ 0 := by
    have hsumPos : (0 : ℤ) < (ρ : ℤ) + σ := by
      have hn : 0 < ρ + σ := by omega
      exact_mod_cast hn
    omega
  exact hde (exponent_eq_of_grade_and_weight (ρ : ℤ) (σ : ℤ)
    hsum d hd hgrade hweight)

/-- The primitive direction condition forces `ρ = 1` once the companion
has an `x`-axis monomial. -/
theorem positive_companion_first_weight_one
    (ρ σ : ℕ) (hρ : 0 < ρ) (hρσ : ρ < σ)
    (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ)
    (hcop : Nat.Coprime ρ σ)
    (hRhom : R.IsWeightedHomogeneous (wt (ρ : ℤ) (σ : ℤ)) m)
    (hFhom : F.IsWeightedHomogeneous (wt (ρ : ℤ) (σ : ℤ))
      ((ρ : ℤ) + σ))
    (hRface : 1 < R.support.card)
    (hcomp : poisson R F = R) :
    ρ = 1 ∧ ∃ e ∈ F.support, e 1 = 0 := by
  obtain ⟨e, he, he0⟩ := positive_companion_has_axis_term
    ρ σ hρ hρσ R F m hRhom hFhom hRface hcomp
  have hw := hFhom (MvPolynomial.mem_support_iff.mp he)
  have hmulZ : (ρ : ℤ) * (e 0 : ℤ) = (ρ : ℤ) + σ := by
    have hweight : (e 0 : ℤ) * (ρ : ℤ) = (ρ : ℤ) + σ := by
      simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two, he0] using hw
    nlinarith [hweight]
  have hmul : ρ * e 0 = ρ + σ := by exact_mod_cast hmulZ
  have hmod : σ % ρ = 0 := by
    have h := congrArg (fun n : ℕ => n % ρ) hmul
    have hleft : (ρ * e 0) % ρ = 0 := Nat.mul_mod_right ρ (e 0)
    have hright : (ρ + σ) % ρ = σ % ρ := by
      rw [Nat.add_mod]
      simp
    rw [hleft, hright] at h
    exact h.symm
  have hdiv : ρ ∣ σ := Nat.dvd_of_mod_eq_zero hmod
  have hone : ρ = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdiv
  exact ⟨hone, ⟨e, he, he0⟩⟩

/-- If the homogeneous companion has a nonzero `x^(σ+1)` term and its only
other possible term is `xy`, then the exact equation `{R,F}=R` forces `R`
to meet the `x`-axis. The proof reads the coefficient one step below the
least `y`-exponent of `R`; the `x^(σ+1)` bracket shifts that coefficient
downward, while the `xy` bracket preserves its exponent. -/
theorem positive_companion_root_has_axis_term_of_shape
    (σ : ℕ) (R : MvPolynomial (Fin 2) ℂ) (c d : ℂ)
    (hc : c ≠ 0) (hR : R ≠ 0)
    (hcomp : poisson R (C c * X 0 ^ (σ+1) + C d * X 0 * X 1) = R) :
    ∃ e ∈ R.support, e 1 = 0 := by
  classical
  by_contra hno
  have hsupport : R.support.Nonempty := MvPolynomial.support_nonempty.mpr hR
  obtain ⟨e, he, hmin⟩ := Finset.exists_min_image R.support (fun x => x 1) hsupport
  have hepos : 0 < e 1 := by
    by_contra hn
    have hz : e 1 = 0 := by omega
    exact hno ⟨e, he, hz⟩
  let z := expo (e 0 + σ) (e 1 - 1)
  have hznot : z ∉ R.support := by
    intro hz
    have hminz := hmin z hz
    have hz1 : z 1 = e 1 - 1 := by simp [z, expo]
    rw [hz1] at hminz
    omega
  have hcoeffR : MvPolynomial.coeff z R = 0 := by
    by_contra hn
    exact hznot (MvPolynomial.mem_support_iff.mpr hn)
  have hsplit : poisson R (C c * X 0 ^ (σ+1) + C d * X 0 * X 1) =
      poisson R (C c * X 0 ^ (σ+1)) + poisson R (C d * X 0 * X 1) := by
    unfold poisson
    rw [map_add, map_add]
    ring
  have hcoeffEq := congrArg (MvPolynomial.coeff z) (hsplit.symm.trans hcomp)
  rw [MvPolynomial.coeff_add, hcoeffR] at hcoeffEq
  have haxis : MvPolynomial.coeff z (poisson R (C c * X 0 ^ (σ+1))) =
      ((σ+1 : ℕ) : ℂ) * c * (e 1 : ℂ) * MvPolynomial.coeff e R := by
    rw [poisson_mul_right]
    have hc0 : poisson R (C c) = 0 := by simp [poisson]
    rw [hc0, zero_mul, zero_add]
    have hp0 : MvPolynomial.pderiv 0 (X 0 ^ (σ+1) : MvPolynomial (Fin 2) ℂ) =
        C (((σ+1 : ℕ) : ℂ)) * X 0 ^ σ := by
      rw [MvPolynomial.pderiv_pow]
      simp
    have hp1 : MvPolynomial.pderiv 1 (X 0 ^ (σ+1) : MvPolynomial (Fin 2) ℂ) = 0 := by
      rw [MvPolynomial.pderiv_pow]
      simp
    have hpoisson : poisson R (X 0 ^ (σ+1) : MvPolynomial (Fin 2) ℂ) =
        C (((σ+1 : ℕ) : ℂ)) *
          (MvPolynomial.pderiv 1 R * X 0 ^ σ) := by
      unfold poisson
      rw [hp0, hp1]
      simp only [mul_zero, sub_zero]
      simp [mul_assoc, mul_comm, mul_left_comm]
    rw [MvPolynomial.coeff_C_mul, hpoisson, MvPolynomial.coeff_C_mul]
    rw [show (X 0 : MvPolynomial (Fin 2) ℂ) ^ σ =
      MvPolynomial.monomial (Finsupp.single 0 σ) (1 : ℂ) by simp [X_pow_eq_monomial]]
    have hm : expo (e 0) (e 1 - 1) + Finsupp.single 0 σ = z := by
      ext i
      fin_cases i <;> simp [z, expo]
    have hm1 : expo (e 0) (e 1 - 1) + Finsupp.single 1 1 = e := by
      have h1 : 1 ≤ e 1 := by omega
      ext i
      fin_cases i
      · simp [expo]
      · simp [expo, Nat.sub_add_cancel h1]
    rw [← hm, coeff_mul_monomial, coeff_pderiv, hm1]
    simp [expo, hepos]
    ring
  have hxy : MvPolynomial.coeff z (poisson R (C d * X 0 * X 1)) =
      d * ((z 1 : ℂ) - (z 0 : ℂ)) * MvPolynomial.coeff z R := by
    have hlin : poisson R (C d * X 0 * X 1) = C d * poisson R (X 0 * X 1) := by
      calc
        poisson R (C d * X 0 * X 1) = poisson R (C d * (X 0 * X 1)) := by ring
        _ = poisson R (C d) * (X 0 * X 1) + C d * poisson R (X 0 * X 1) :=
          poisson_mul_right R (C d) (X 0 * X 1)
        _ = C d * poisson R (X 0 * X 1) := by simp [poisson]
    rw [hlin, coeff_C_mul, poisson_xy_coeff]
    ring
  have heqaxis : ((σ+1 : ℕ) : ℂ) * c * (e 1 : ℂ) * MvPolynomial.coeff e R = 0 := by
    rw [haxis, hxy, hcoeffR] at hcoeffEq
    simpa using hcoeffEq
  have heCoeff : MvPolynomial.coeff e R ≠ 0 := MvPolynomial.mem_support_iff.mp he
  have heposC : (e 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hepos)
  have hsigma : (((σ+1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show σ+1 ≠ 0 by omega)
  have hbad : ((σ+1 : ℕ) : ℂ) * c * (e 1 : ℂ) * MvPolynomial.coeff e R ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hsigma hc) heposC) heCoeff
  exact hbad heqaxis

/-- Under a primitive positive-slope exact companion, the homogeneous root
has a unique total-degree leading point on the `x`-axis. This is the root
level endpoint restriction behind G13 Lemma 6.4(1); it remains conditional
on the supplied companion relation. -/
theorem positive_companion_root_has_total_degree_endpoint
    (ρ σ : ℕ) (hρ : 0 < ρ) (hρσ : ρ < σ)
    (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ)
    (hcop : Nat.Coprime ρ σ)
    (hRhom : R.IsWeightedHomogeneous (wt (ρ : ℤ) (σ : ℤ)) m)
    (hFhom : F.IsWeightedHomogeneous (wt (ρ : ℤ) (σ : ℤ)) ((ρ : ℤ) + σ))
    (hRface : 1 < R.support.card)
    (hcomp : poisson R F = R) :
    ρ = 1 ∧ (∃ e ∈ R.support, e = expo (m.toNat) 0) ∧
      (∀ e ∈ R.support, e 0 + e 1 ≤ m.toNat) ∧
      (∀ e ∈ R.support, e 0 + e 1 = m.toNat → e = expo (m.toNat) 0) := by
  have hfirst := positive_companion_first_weight_one
    ρ σ hρ hρσ R F m hcop hRhom hFhom hRface hcomp
  rcases hfirst with ⟨hρone, hFaxis⟩
  have hρanswer : ρ = 1 := hρone
  subst ρ
  have hσ : 1 < σ := by omega
  obtain ⟨f, hf, hfaxis⟩ := hFaxis
  have hfw := hFhom (MvPolynomial.mem_support_iff.mp hf)
  have hfwt : (f 0 : ℤ) + (f 1 : ℤ) * (σ : ℤ) = 1 + σ := by
    simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two] using hfw
  have hfx : f 0 = σ + 1 := by
    have hz : (f 0 : ℤ) = (σ : ℤ) + 1 := by rw [hfaxis] at hfwt; omega
    exact_mod_cast hz
  let u : Fin 2 →₀ ℕ := Finsupp.single 0 (σ + 1)
  let v := expo 1 1
  have hvShape : v = Finsupp.single 0 1 + Finsupp.single 1 1 := by
    ext i
    fin_cases i <;> simp [v, expo]
  have hu : u ∈ F.support := by
    have hfu : f = u := by
      ext i
      fin_cases i
      · simpa [u, expo] using hfx
      · simpa [u, expo] using hfaxis
    simpa [hfu] using hf
  have huv : u ≠ v := by
    intro h
    have hzero := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
    simp [u, v, expo] at hzero
  have hsubset : ∀ e ∈ F.support, e = u ∨ e = v := by
    intro e he
    rcases positive_companion_support_restrict 1 σ (by omega) hσ F hFhom e he with hz | hv
    · have hw := hFhom (MvPolynomial.mem_support_iff.mp he)
      have he0 : e 0 = σ + 1 := by
        have hz' : (e 0 : ℤ) + (e 1 : ℤ) * (σ : ℤ) = 1 + σ := by
          simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two] using hw
        rw [hz] at hz'
        have hz'' : (e 0 : ℤ) = (σ : ℤ) + 1 := by omega
        exact_mod_cast hz''
      have heq : e = u := by
        ext i
        fin_cases i
        · simpa [u, expo] using he0
        · simpa [u, expo] using hz
      exact Or.inl heq
    · exact Or.inr (by simpa [v] using hv)
  let c : ℂ := MvPolynomial.coeff u F
  let d : ℂ := MvPolynomial.coeff v F
  have hc : c ≠ 0 := by
    exact MvPolynomial.mem_support_iff.mp (by simpa [c] using hu)
  have hshapeMono : F = monomial u c + monomial v d := by
    apply MvPolynomial.ext
    intro e
    simp only [MvPolynomial.coeff_add, coeff_monomial]
    by_cases heU : e = u
    · subst e
      simp [c, d, huv.symm]
    · by_cases heV : e = v
      · subst e
        simp [c, d, huv]
      · have hcoeff : MvPolynomial.coeff e F = 0 := by
          by_contra hn
          have he : e ∈ F.support := MvPolynomial.mem_support_iff.mpr hn
          rcases hsubset e he with he | he <;> contradiction
        simp [Ne.symm heU, Ne.symm heV, hcoeff]
  have hmonoU : monomial u c = C c * X 0 ^ (σ + 1) := by
    change monomial (Finsupp.single 0 (σ + 1)) c = C c * X 0 ^ (σ + 1)
    exact (C_mul_X_pow_eq_monomial (s := (0 : Fin 2)) (a := c)
      (n := σ + 1)).symm
  have hmonoV : monomial v d = C d * X 0 * X 1 := by
    rw [hvShape]
    calc
      monomial (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1) d =
          monomial (Finsupp.single (0 : Fin 2) 1) d * X 1 := by
        rw [monomial_add_single]
        simp
      _ = C d * X 0 * X 1 := by rw [C_mul_X_eq_monomial]
  have hshape : F = C c * X 0 ^ (σ + 1) + C d * X 0 * X 1 := by
    rw [hshapeMono, hmonoU, hmonoV]
  have hRne : R ≠ 0 := by
    intro h
    subst R
    simp at hRface
  obtain ⟨e, he, heAxis⟩ :=
    positive_companion_root_has_axis_term_of_shape σ R c d hc hRne
      (by rw [← hshape]; exact hcomp)
  have hewt := hRhom (MvPolynomial.mem_support_iff.mp he)
  have heX : (e 0 : ℤ) = m := by
    have hwt : (e 0 : ℤ) * 1 + (e 1 : ℤ) * (σ : ℤ) = m := by
      simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two] using hewt
    rw [heAxis] at hwt
    simpa using hwt
  have hmnonneg : 0 ≤ m := by omega
  have hmn : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hmnonneg
  have heXnat : e 0 = m.toNat := by
    rw [← hmn] at heX
    exact_mod_cast heX
  have heq : e = expo (m.toNat) 0 := by
    ext i
    fin_cases i
    · simpa [expo] using heXnat
    · simpa [expo] using heAxis
  refine ⟨hρanswer, ⟨e, he, heq⟩, ?_, ?_⟩
  · intro z hz
    have hzw := hRhom (MvPolynomial.mem_support_iff.mp hz)
    have hwt : (z 0 : ℤ) + (z 1 : ℤ) * (σ : ℤ) = m := by
      simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two] using hzw
    have hz1 : (z 0 : ℤ) + z 1 ≤ (m.toNat : ℤ) := by
      rw [hmn]
      nlinarith [Nat.zero_le (z 1)]
    exact_mod_cast hz1
  · intro z hz hdeg
    have hzw := hRhom (MvPolynomial.mem_support_iff.mp hz)
    have hwt : (z 0 : ℤ) + (z 1 : ℤ) * (σ : ℤ) = m := by
      simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two] using hzw
    have hdeg' : (z 0 : ℤ) + z 1 = m := by
      have hcast : ((z 0 + z 1 : ℕ) : ℤ) = (m.toNat : ℤ) := by
        exact_mod_cast hdeg
      rw [hmn] at hcast
      simpa using hcast
    have hzero : z 1 = 0 := by
      have hσ2 : 1 < (σ : ℤ) := by exact_mod_cast hσ
      nlinarith [Nat.zero_le (z 1)]
    have hx : z 0 = m.toNat := by
      have hz0 : (z 0 : ℤ) = m := by omega
      rw [← hmn] at hz0
      exact_mod_cast hz0
    ext i
    fin_cases i
    · simpa [expo] using hx
    · simpa [expo] using hzero

/-- The distinguished `x`-axis endpoint of a positive-slope homogeneous
companion root survives in every power.  This is the support-transfer step
needed before applying the root endpoint geometry to a proper-power leading
face. -/
theorem positive_companion_root_power_has_axis_endpoint
    (ρ σ : ℕ) (hρ : 0 < ρ) (hρσ : ρ < σ)
    (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ) (k : ℕ)
    (hcop : Nat.Coprime ρ σ)
    (hRhom : R.IsWeightedHomogeneous (wt (ρ : ℤ) (σ : ℤ)) m)
    (hFhom : F.IsWeightedHomogeneous (wt (ρ : ℤ) (σ : ℤ)) ((ρ : ℤ) + σ))
    (hRface : 1 < R.support.card)
    (hcomp : poisson R F = R) :
    expo (k * m.toNat) 0 ∈ (R ^ k).support := by
  classical
  obtain ⟨hρone, ⟨e, he, heq⟩, htotal, _⟩ :=
    positive_companion_root_has_total_degree_endpoint
      ρ σ hρ hρσ R F m hcop hRhom hFhom hRface hcomp
  subst ρ
  let M := m.toNat
  have hRne : R ≠ 0 := by
    intro hzero
    subst R
    simp at he
  have hmax : ∀ d ∈ R.support, d 0 ≤ M := by
    intro d hd
    exact le_trans (Nat.le_add_right (d 0) (d 1)) (htotal d hd)
  have hdegR : R.degreeOf 0 = M := by
    apply Nat.le_antisymm
    · rw [MvPolynomial.degreeOf_eq_sup]
      exact Finset.sup_le fun d hd => hmax d hd
    · simpa [M, heq, expo] using MvPolynomial.le_degreeOf_of_mem_support 0 he
  have hpowne : R ^ k ≠ 0 := pow_ne_zero k hRne
  have hsupport : (R ^ k).support.Nonempty :=
    MvPolynomial.support_nonempty.mpr hpowne
  obtain ⟨d, hd, hdmax⟩ :=
    Finset.exists_max_image (R ^ k).support (fun z => z 0) hsupport
  have hd0 : d 0 = k * M := by
    have hmaxdeg : (R ^ k).degreeOf 0 = d 0 := by
      apply Nat.le_antisymm
      · rw [MvPolynomial.degreeOf_eq_sup]
        exact Finset.sup_le fun z hz => hdmax z hz
      · exact MvPolynomial.le_degreeOf_of_mem_support 0 hd
    rw [MvPolynomial.degreeOf_pow_eq 0 R k hRne, hdegR] at hmaxdeg
    exact hmaxdeg.symm
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
  have hi : i = k * M := by simpa [expo] using hd0
  have hmnonneg : 0 ≤ m := by
    have hm := hRhom (MvPolynomial.mem_support_iff.mp he)
    have hm' : (e 0 : ℤ) + (e 1 : ℤ) * (σ : ℤ) = m := by
      simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two] using hm
    rw [heq] at hm'
    simp [expo] at hm'
    omega
  have hmn : (M : ℤ) = m := by
    dsimp [M]
    exact Int.toNat_of_nonneg hmnonneg
  have hpow := (hRhom.pow k) (MvPolynomial.mem_support_iff.mp hd)
  have hpowWeight : (i : ℤ) + (σ : ℤ) * (j : ℤ) = m * k := by
    simpa [expo, wt, Finsupp.weight_eq_sum, Fin.sum_univ_two, nsmul_eq_mul,
      mul_comm, mul_left_comm] using hpow
  have hiZ : (i : ℤ) = (k : ℤ) * M := by
    rw [hi]
    push_cast
    ring
  have hjzero : j = 0 := by
    have hσpos : 0 < (σ : ℤ) := by exact_mod_cast (lt_trans (by omega : 0 < 1) hρσ)
    have hjnonneg : 0 ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j
    rw [hiZ, ← hmn] at hpowWeight
    have : (σ : ℤ) * (j : ℤ) = 0 := by nlinarith [hpowWeight]
    have hjZ : (j : ℤ) = 0 :=
      (mul_eq_zero.mp this).resolve_left (ne_of_gt hσpos)
    exact_mod_cast hjZ
  subst i
  subst j
  simpa [M, expo] using hd

/-- A proper-power leading face with a positive-slope homogeneous companion
therefore has its predicted occupied `x`-axis endpoint.  This is the direct
operator-face consumer of the root-power endpoint theorem. -/
theorem positive_companion_leadingFace_has_axis_endpoint
    (P : A1 ℂ) (ρ σ : ℕ) (hρ : 0 < ρ) (hρσ : ρ < σ)
    (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ) (k : ℕ) (μ : ℂ)
    (hμ : μ ≠ 0) (hcop : Nat.Coprime ρ σ)
    (hRhom : R.IsWeightedHomogeneous (wt (ρ : ℤ) (σ : ℤ)) m)
    (hFhom : F.IsWeightedHomogeneous (wt (ρ : ℤ) (σ : ℤ)) ((ρ : ℤ) + σ))
    (hRface : 1 < R.support.card)
    (hface : leadingForm (ρ : ℤ) (σ : ℤ) P.1 = C μ * R ^ k)
    (hcomp : poisson R F = R) :
    ρ = 1 ∧ expo (k * m.toNat) 0 ∈
      (leadingForm (ρ : ℤ) (σ : ℤ) P.1).support := by
  have hroot := positive_companion_root_has_total_degree_endpoint
    ρ σ hρ hρσ R F m hcop hRhom hFhom hRface hcomp
  obtain ⟨hρone, -, -, -⟩ := hroot
  refine ⟨hρone, ?_⟩
  have hpower := positive_companion_root_power_has_axis_endpoint
    ρ σ hρ hρσ R F m k hcop hRhom hFhom hRface hcomp
  rw [hface, MvPolynomial.C_mul', MvPolynomial.support_smul_eq hμ]
  exact hpower

/-- The positive-slope endpoint is also a global total-degree endpoint of
the operator symbol.  Once the companion forces first weight one, every
support exponent lies below the positive supporting line, and hence below
its `x`-axis intercept in total degree. -/
theorem positive_companion_symbol_totalDegree_bound
    (P : A1 ℂ) (ρ σ : ℕ) (hρ : 0 < ρ) (hρσ : ρ < σ)
    (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ) (k : ℕ) (μ : ℂ)
    (hμ : μ ≠ 0) (hcop : Nat.Coprime ρ σ)
    (hRhom : R.IsWeightedHomogeneous (wt (ρ : ℤ) (σ : ℤ)) m)
    (hFhom : F.IsWeightedHomogeneous (wt (ρ : ℤ) (σ : ℤ)) ((ρ : ℤ) + σ))
    (hRface : 1 < R.support.card)
    (hface : leadingForm (ρ : ℤ) (σ : ℤ) P.1 = C μ * R ^ k)
    (hcomp : poisson R F = R) :
    ρ = 1 ∧ expo (k * m.toNat) 0 ∈ (symbol P.1).support ∧
      ∀ e ∈ (symbol P.1).support, e 0 + e 1 ≤ k * m.toNat := by
  obtain ⟨hρone, hend⟩ := positive_companion_leadingFace_has_axis_endpoint
    P ρ σ hρ hρσ R F m k μ hμ hcop hRhom hFhom hRface hface hcomp
  subst ρ
  let M := m.toNat
  have hfaceData :=
    (leadingForm_mem_iff_rational_slope P 1 (σ : ℤ) (by omega)
      (expo (k * M) 0)).mp (by simpa [M] using hend)
  refine ⟨rfl, hfaceData.1, ?_⟩
  intro e he
  have hweight := hfaceData.2 e he
  have hσ : (1 : ℚ) ≤ σ := by
    exact_mod_cast (Nat.succ_le_iff.mpr (by omega : 0 < σ))
  have heNonneg : (0 : ℚ) ≤ e 1 := by exact_mod_cast Nat.zero_le (e 1)
  have hsmall : (e 0 : ℚ) + e 1 ≤ (e 0 : ℚ) + (σ : ℚ) * e 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hσ heNonneg]
  dsimp [rationalNewtonWeight] at hweight
  have htop : (e 0 : ℚ) + (σ : ℚ) * e 1 ≤ k * M := by
    norm_num [expo] at hweight ⊢
    exact hweight
  have hanswer : (e 0 : ℚ) + e 1 ≤ k * M := hsmall.trans htop
  exact_mod_cast hanswer

/-- In the positive-slope companion situation, the intercept of the forced
axis endpoint is exactly the operator's total PBW degree. -/
theorem positive_companion_totalDeg_eq_axis_intercept
    (P : A1 ℂ) (ρ σ : ℕ) (hρ : 0 < ρ) (hρσ : ρ < σ)
    (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ) (k : ℕ) (μ : ℂ)
    (hμ : μ ≠ 0) (hcop : Nat.Coprime ρ σ)
    (hRhom : R.IsWeightedHomogeneous (wt (ρ : ℤ) (σ : ℤ)) m)
    (hFhom : F.IsWeightedHomogeneous (wt (ρ : ℤ) (σ : ℤ)) ((ρ : ℤ) + σ))
    (hRface : 1 < R.support.card)
    (hface : leadingForm (ρ : ℤ) (σ : ℤ) P.1 = C μ * R ^ k)
    (hcomp : poisson R F = R) :
    ρ = 1 ∧ totalDeg P.1 = k * m.toNat := by
  obtain ⟨hρone, hend, hbound⟩ := positive_companion_symbol_totalDegree_bound
    P ρ σ hρ hρσ R F m k μ hμ hcop hRhom hFhom hRface hface hcomp
  refine ⟨hρone, ?_⟩
  apply Nat.le_antisymm
  · change (symbol P.1).support.sup (fun e => e.sum (fun _ n => n)) ≤ k * m.toNat
    apply Finset.sup_le
    intro e he
    rw [Finsupp.sum_fintype e (fun _ n => n) (by simp)]
    simpa [Fin.sum_univ_two] using hbound e he
  · have hlow := MvPolynomial.le_totalDegree hend
    rw [Finsupp.sum_fintype (expo (k * m.toNat) 0) (fun _ n => n) (by simp)] at hlow
    simpa [totalDeg, expo, Fin.sum_univ_two] using hlow

/-- A positive-slope companion face cannot share a positive-`y` diagonal
endpoint.  This is the local contradiction used when a successor of the
diagonal face is assumed to lie strictly below the vertical direction. -/
theorem positive_companion_shared_diagonal_point_y_eq_zero
    (P : A1 ℂ) (ρ σ : ℕ) (hρ : 0 < ρ) (hρσ : ρ < σ)
    (R F : MvPolynomial (Fin 2) ℂ) (m : ℤ) (k : ℕ) (μ : ℂ)
    (hμ : μ ≠ 0) (hcop : Nat.Coprime ρ σ)
    (hRhom : R.IsWeightedHomogeneous (wt (ρ : ℤ) (σ : ℤ)) m)
    (hFhom : F.IsWeightedHomogeneous (wt (ρ : ℤ) (σ : ℤ)) ((ρ : ℤ) + σ))
    (hRface : 1 < R.support.card)
    (hface : leadingForm (ρ : ℤ) (σ : ℤ) P.1 = C μ * R ^ k)
    (hcomp : poisson R F = R)
    (a b : ℕ) (hdiag : totalDeg P.1 = a + b)
    (hshared : expo a b ∈ (leadingForm (ρ : ℤ) (σ : ℤ) P.1).support) :
    b = 0 := by
  have hendpoint := positive_companion_leadingFace_has_axis_endpoint
    P ρ σ hρ hρσ R F m k μ hμ hcop hRhom hFhom hRface hface hcomp
  obtain ⟨hρone, hend⟩ := hendpoint
  subst ρ
  have hdegree := positive_companion_totalDeg_eq_axis_intercept
    P 1 σ (by omega) hρσ R F m k μ hμ hcop hRhom hFhom hRface hface hcomp
  obtain ⟨-, htotal⟩ := hdegree
  have hweight (d : Fin 2 →₀ ℕ)
      (hd : d ∈ (leadingForm 1 (σ : ℤ) P.1).support) :
      Finsupp.weight (wt 1 (σ : ℤ)) d = vDeg 1 (σ : ℤ) P.1 := by
    change d ∈ (MvPolynomial.weightedHomogeneousComponent
      (wt 1 (σ : ℤ)) (vDeg 1 (σ : ℤ) P.1) (symbol P.1)).support at hd
    rw [MvPolynomial.support_weightedHomogeneousComponent] at hd
    exact (Finset.mem_filter.mp hd).2
  have hwshared := hweight (expo a b) hshared
  have hwend := hweight (expo (k * m.toNat) 0) hend
  rw [expo_weight] at hwshared hwend
  have hweights : (a : ℤ) + (σ : ℤ) * b = (k * m.toNat : ℤ) := by
    push_cast at hwend
    nlinarith [hwshared, hwend]
  have hdiagZ : (k * m.toNat : ℤ) = (a : ℤ) + b := by
    exact_mod_cast htotal.symm.trans hdiag
  have hσ : 1 < (σ : ℤ) := by exact_mod_cast hρσ
  have hbnonneg : 0 ≤ (b : ℤ) := by exact_mod_cast Nat.zero_le b
  have hbZ : (b : ℤ) = 0 := by nlinarith [hweights, hdiagZ]
  exact_mod_cast hbZ

/-- The shared-diagonal contradiction only needs the preliminary companion
for the actual face.  It does not require a prior proper-power
factorization: instantiate the root in the preceding theorem by the face
itself. -/
theorem preliminary_positive_face_shared_diagonal_point_y_eq_zero
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℕ) (hρ : 0 < ρ) (hρσ : ρ < σ)
    (hcop : Nat.Coprime ρ σ)
    (hdir : IsDirection (ρ : ℤ) (σ : ℤ))
    (hfaceDir : InDir (ρ : ℤ) (σ : ℤ) P.1)
    (a b : ℕ) (hdiag : totalDeg P.1 = a + b)
    (hshared : expo a b ∈ (leadingForm (ρ : ℤ) (σ : ℤ) P.1).support) :
    b = 0 := by
  obtain ⟨F, hFhom, hcomp⟩ := hsource P Q hpair (ρ : ℤ) (σ : ℤ) hdir
  have hRhom : (leadingForm (ρ : ℤ) (σ : ℤ) P.1).IsWeightedHomogeneous
      (wt (ρ : ℤ) (σ : ℤ)) (vDeg (ρ : ℤ) (σ : ℤ) P.1) := by
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt (ρ : ℤ) (σ : ℤ))
      (n := vDeg (ρ : ℤ) (σ : ℤ) P.1)
  exact positive_companion_shared_diagonal_point_y_eq_zero
    P ρ σ hρ hρσ (leadingForm (ρ : ℤ) (σ : ℤ) P.1) F
    (vDeg (ρ : ℤ) (σ : ℤ) P.1) 1 1 (by norm_num) hcop hRhom hFhom
    hfaceDir (by simp) hcomp a b hdiag hshared

private theorem positive_rational_direction
    (t : ℚ) (hone : 1 < t) :
    IsDirection (t.den : ℤ) t.num ∧
      0 < (t.den : ℤ) ∧ (t.den : ℤ) < t.num ∧
      (t.num : ℚ) / (t.den : ℚ) = t := by
  have hdenQ : (0 : ℚ) < t.den := by
    exact_mod_cast Rat.den_pos t
  have hdenZ : (0 : ℤ) < t.den := by
    exact_mod_cast Rat.den_pos t
  have hnum : t * (t.den : ℚ) = (t.num : ℚ) := by
    calc
      t * (t.den : ℚ) =
          ((t.num : ℚ) / (t.den : ℚ)) * (t.den : ℚ) := by
            rw [Rat.num_div_den]
      _ = (t.num : ℚ) := by field_simp
  have hltQ : (t.den : ℚ) < t.num := by
    have hmul := mul_lt_mul_of_pos_right hone hdenQ
    rw [hnum] at hmul
    simpa using hmul
  have hlt : (t.den : ℤ) < t.num := by
    exact_mod_cast hltQ
  have hsum : (0 : ℤ) < (t.den : ℤ) + t.num := by omega
  have hcop : Int.gcd (t.den : ℤ) t.num = 1 := by
    simpa [Int.gcd_def, Nat.gcd_comm, Nat.Coprime] using t.reduced.symm
  exact ⟨⟨hcop, hsum⟩, hdenZ, hlt, Rat.num_div_den t⟩

private theorem rational_numDen_natCoprime (t : ℚ) :
    Nat.Coprime t.den t.num.natAbs := by
  exact t.reduced.symm

/-- Under the source-shaped preliminary companion, a singleton diagonal
leading face at `(a,b)` bounds the second coordinate of every PBW support
point by `b`.  A hypothetical higher point gives a first rational upward
tilt; its primitive positive integer face shares the diagonal endpoint and
contradicts `preliminary_positive_face_shared_diagonal_point_y_eq_zero`. -/
theorem preliminary_companion_support_second_coord_le
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b : ℕ) (hdiag : totalDeg P.1 = a + b)
    (hdiagMem : expo a b ∈ (leadingForm 1 1 P.1).support)
    (hdiagUnique : ∀ d ∈ (leadingForm 1 1 P.1).support, d = expo a b)
    (hb : 0 < b) :
    ∀ d ∈ (symbol P.1).support, d 1 ≤ b := by
  intro d hd
  by_contra hnot
  have habove : ∃ d ∈ (symbol P.1).support, b < d 1 :=
    ⟨d, hd, Nat.lt_of_not_ge hnot⟩
  have hlast : ∀ d ∈ (leadingForm 1 1 P.1).support,
      d 1 ≤ (expo a b) 1 := by
    intro d hd
    rw [hdiagUnique d hd]
  obtain ⟨t, ht, hmax, c, hc, hcb, htie⟩ :=
    leadingFace_exists_first_upward_tilt P 1 1 (by norm_num) (expo a b)
      hdiagMem hlast (by simpa [expo] using habove)
  obtain ⟨htdir, htden, htlt, hratio⟩ :=
    positive_rational_direction t (by simpa using ht)
  have hnumNonneg : 0 ≤ t.num := by omega
  have hnumCast : (t.num.natAbs : ℤ) = t.num := by omega
  have htltNat : t.den < t.num.natAbs := by
    have hltZ : (t.den : ℤ) < (t.num.natAbs : ℤ) := by
      rw [hnumCast]
      exact htlt
    exact_mod_cast hltZ
  have hdir : IsDirection (t.den : ℤ) (t.num.natAbs : ℤ) := by
    rw [hnumCast]
    exact htdir
  have hratioNat : ((t.num.natAbs : ℤ) : ℚ) / ((t.den : ℤ) : ℚ) = t := by
    rw [hnumCast]
    simpa only [Int.cast_natCast] using hratio
  have haSupport := (leadingForm_mem_iff_rational_slope P 1 1 (by norm_num)
    (expo a b)).mp hdiagMem |>.1
  have haFace : expo a b ∈
      (leadingForm (t.den : ℤ) (t.num.natAbs : ℤ) P.1).support := by
    apply (leadingForm_mem_iff_rational_slope P (t.den : ℤ)
      (t.num.natAbs : ℤ) (by exact_mod_cast Rat.den_pos t) (expo a b)).mpr
    rw [hratioNat]
    exact ⟨haSupport, hmax⟩
  have hcMax : ∀ d ∈ (symbol P.1).support,
      rationalNewtonWeight t d ≤ rationalNewtonWeight t c := by
    intro d hd
    exact (hmax d hd).trans_eq htie.symm
  have hcFace : c ∈
      (leadingForm (t.den : ℤ) (t.num.natAbs : ℤ) P.1).support := by
    apply (leadingForm_mem_iff_rational_slope P (t.den : ℤ)
      (t.num.natAbs : ℤ) (by exact_mod_cast Rat.den_pos t) c).mpr
    rw [hratioNat]
    exact ⟨hc, hcMax⟩
  have hne : expo a b ≠ c := by
    intro heq
    rw [← heq] at hcb
    simpa [expo] using hcb
  have hfaceDir : InDir (t.den : ℤ) (t.num.natAbs : ℤ) P.1 :=
    Finset.one_lt_card_iff.mpr ⟨expo a b, c, haFace, hcFace, hne⟩
  have hzero := preliminary_positive_face_shared_diagonal_point_y_eq_zero
    hsource P Q hpair t.den t.num.natAbs
    (Rat.den_pos t) htltNat (rational_numDen_natCoprime t)
    hdir hfaceDir a b hdiag haFace
  exact (Nat.ne_of_gt hb) hzero

/-- The preliminary companion forces the native positive-slope face's
first weight and its actual total-degree axis endpoint. -/
theorem preliminary_positive_face_total_degree_axis_endpoint
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℕ) (hρ : 0 < ρ) (hρσ : ρ < σ)
    (hcop : Nat.Coprime ρ σ)
    (hdir : IsDirection (ρ : ℤ) (σ : ℤ))
    (hfaceDir : InDir (ρ : ℤ) (σ : ℤ) P.1) :
    ρ = 1 ∧ totalDeg P.1 = (vDeg (ρ : ℤ) (σ : ℤ) P.1).toNat ∧
      expo (totalDeg P.1) 0 ∈
        (leadingForm (ρ : ℤ) (σ : ℤ) P.1).support := by
  obtain ⟨F, hFhom, hcomp⟩ := hsource P Q hpair (ρ : ℤ) (σ : ℤ) hdir
  have hRhom : (leadingForm (ρ : ℤ) (σ : ℤ) P.1).IsWeightedHomogeneous
      (wt (ρ : ℤ) (σ : ℤ)) (vDeg (ρ : ℤ) (σ : ℤ) P.1) := by
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt (ρ : ℤ) (σ : ℤ))
      (n := vDeg (ρ : ℤ) (σ : ℤ) P.1)
  have ht := positive_companion_totalDeg_eq_axis_intercept
    P ρ σ hρ hρσ (leadingForm (ρ : ℤ) (σ : ℤ) P.1) F
    (vDeg (ρ : ℤ) (σ : ℤ) P.1) 1 1 (by norm_num) hcop hRhom hFhom
    hfaceDir (by simp) hcomp
  have he := positive_companion_leadingFace_has_axis_endpoint
    P ρ σ hρ hρσ (leadingForm (ρ : ℤ) (σ : ℤ) P.1) F
    (vDeg (ρ : ℤ) (σ : ℤ) P.1) 1 1 (by norm_num) hcop hRhom hFhom
    hfaceDir (by simp) hcomp
  have hd : totalDeg P.1 = (vDeg (ρ : ℤ) (σ : ℤ) P.1).toNat := by
    simpa using ht.2
  refine ⟨ht.1, hd, ?_⟩
  rw [hd]
  simpa using he.2

/-- A last positive-slope face point with positive Y-coordinate bounds
all Y-exponents; no total-degree or rectangle hypothesis is needed. -/
theorem preliminary_positive_last_point_y_bound
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ a b : ℕ) (hσ : 1 ≤ σ)
    (hmem : expo a b ∈ (leadingForm 1 (σ : ℤ) P.1).support)
    (hlast : ∀ d ∈ (leadingForm 1 (σ : ℤ) P.1).support, d 1 ≤ (expo a b) 1)
    (hb : 0 < b) :
    ∀ d ∈ (symbol P.1).support, d 1 ≤ b := by
  intro d hd
  by_contra hnot
  have habove : ∃ d ∈ (symbol P.1).support, b < d 1 :=
    ⟨d, hd, Nat.lt_of_not_ge hnot⟩
  obtain ⟨t, ht, hmax, c, hc, hcb, htie⟩ :=
    leadingFace_exists_first_upward_tilt P 1 (σ : ℤ) (by norm_num) (expo a b)
      hmem hlast (by simpa [expo] using habove)
  obtain ⟨htdir, htden, htlt, hratio⟩ :=
    positive_rational_direction t (by
      have hσQ : (1 : ℚ) ≤ σ := by exact_mod_cast hσ
      have htσ : (σ : ℚ) < t := by simpa using ht
      exact lt_of_le_of_lt hσQ htσ)
  have hnumNonneg : 0 ≤ t.num := by omega
  have hnumCast : (t.num.natAbs : ℤ) = t.num := by omega
  have htltNat : t.den < t.num.natAbs := by
    have hltZ : (t.den : ℤ) < (t.num.natAbs : ℤ) := by
      rw [hnumCast]
      exact htlt
    exact_mod_cast hltZ
  have hdir : IsDirection (t.den : ℤ) (t.num.natAbs : ℤ) := by
    rw [hnumCast]
    exact htdir
  have hratioNat : ((t.num.natAbs : ℤ) : ℚ) / ((t.den : ℤ) : ℚ) = t := by
    rw [hnumCast]
    simpa only [Int.cast_natCast] using hratio
  have haSupport := (leadingForm_mem_iff_rational_slope P 1 (σ : ℤ) (by norm_num)
    (expo a b)).mp hmem |>.1
  have haFace : expo a b ∈
      (leadingForm (t.den : ℤ) (t.num.natAbs : ℤ) P.1).support := by
    apply (leadingForm_mem_iff_rational_slope P (t.den : ℤ)
      (t.num.natAbs : ℤ) (by exact_mod_cast Rat.den_pos t) (expo a b)).mpr
    rw [hratioNat]
    exact ⟨haSupport, hmax⟩
  have hcMax : ∀ d ∈ (symbol P.1).support,
      rationalNewtonWeight t d ≤ rationalNewtonWeight t c := by
    intro d hd
    exact (hmax d hd).trans_eq htie.symm
  have hcFace : c ∈
      (leadingForm (t.den : ℤ) (t.num.natAbs : ℤ) P.1).support := by
    apply (leadingForm_mem_iff_rational_slope P (t.den : ℤ)
      (t.num.natAbs : ℤ) (by exact_mod_cast Rat.den_pos t) c).mpr
    rw [hratioNat]
    exact ⟨hc, hcMax⟩
  have hne : expo a b ≠ c := by
    intro heq
    rw [← heq] at hcb
    simpa [expo] using hcb
  have hfaceDir : InDir (t.den : ℤ) (t.num.natAbs : ℤ) P.1 :=
    Finset.one_lt_card_iff.mpr ⟨expo a b, c, haFace, hcFace, hne⟩
  obtain ⟨hρone, hdegree, haxisFace⟩ :=
    preliminary_positive_face_total_degree_axis_endpoint hsource P Q hpair
      t.den t.num.natAbs (Rat.den_pos t) htltNat
      (rational_numDen_natCoprime t) hdir hfaceDir
  have haxisData := (leadingForm_mem_iff_rational_slope P (t.den : ℤ)
    (t.num.natAbs : ℤ) (by exact_mod_cast Rat.den_pos t)
      (expo (totalDeg P.1) 0)).mp haxisFace
  rw [hratioNat] at haxisData
  have haxisOld := (leadingForm_mem_iff_rational_slope P 1 (σ : ℤ)
    (by norm_num) (expo a b)).mp hmem
  have haxisLe := haxisOld.2 (expo (totalDeg P.1) 0) haxisData.1
  have hforward := hmax (expo (totalDeg P.1) 0) haxisData.1
  have hback := haxisData.2 (expo a b) haSupport
  have htσ : (σ : ℚ) < t := by simpa using ht
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  norm_num [rationalNewtonWeight, expo] at haxisLe hforward hback
  nlinarith

/-- If a positive singleton face is not yet a total-degree bound, its
next downward face has a strictly smaller positive integer slope. -/
theorem preliminary_positive_singleton_next_integer_face
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (σ a b : ℕ) (hσ : 1 ≤ σ) (hb : 0 < b)
    (hmem : expo a b ∈ (leadingForm 1 (σ : ℤ) P.1).support)
    (hunique : ∀ d ∈ (leadingForm 1 (σ : ℤ) P.1).support, d = expo a b)
    (hbad : ∃ d ∈ (symbol P.1).support, a+b < d 0 + d 1) :
    ∃ τ : ℕ, 1 < τ ∧ τ < σ ∧ InDir 1 (τ : ℤ) P.1 ∧
      expo a b ∈ (leadingForm 1 (τ : ℤ) P.1).support := by
  classical
  have hy := preliminary_positive_last_point_y_bound hsource P Q hpair σ a b hσ hmem
    (by intro d hd; rw [hunique d hd]) hb
  have hold := (leadingForm_mem_iff_rational_slope P 1 (σ : ℤ)
    (by norm_num) (expo a b)).mp hmem
  obtain ⟨d,hd,hdsum⟩ := hbad
  have hdle := hy d hd
  have hdlower : d 1 < b := by
    by_contra hn
    have he : d 1 = b := by omega
    have hw := hold.2 d hd
    simp [rationalNewtonWeight,expo,he] at hw
    have hsumQ : (a : ℚ)+b < (d 0 : ℚ)+d 1 := by exact_mod_cast hdsum
    rw [he] at hsumQ
    linarith
  obtain ⟨t,ht,hmax,c,hc,hcb,htie⟩ :=
    leadingFace_exists_first_downward_tilt P 1 (σ : ℤ) (by norm_num) (expo a b) hmem
      (by intro p hp; rw [hunique p hp]) ⟨d,hd,by simpa [expo] using hdlower⟩
  have htone : 1 < t := by
    by_contra hn
    have hw := hmax d hd
    have hsumQ : (a : ℚ)+b < (d 0 : ℚ)+d 1 := by exact_mod_cast hdsum
    have hyQ : (d 1 : ℚ) ≤ b := by exact_mod_cast hdle
    have hprod : 0 ≤ (1-t)*((b : ℚ)-d 1) := mul_nonneg (by linarith) (by linarith)
    norm_num [rationalNewtonWeight,expo] at hw
    nlinarith
  obtain ⟨htdir,htden,htlt,hratio⟩ := positive_rational_direction t htone
  have hnumCast : (t.num.natAbs : ℤ) = t.num := by omega
  have htltNat : t.den < t.num.natAbs := by
    have hz : (t.den : ℤ) < t.num.natAbs := by rw [hnumCast]; exact htlt
    exact_mod_cast hz
  have hdir : IsDirection (t.den : ℤ) (t.num.natAbs : ℤ) := by
    rw [hnumCast]; exact htdir
  have hratioNat : ((t.num.natAbs : ℤ) : ℚ) / ((t.den : ℤ) : ℚ) = t := by
    rw [hnumCast]; simpa only [Int.cast_natCast] using hratio
  have haFace : expo a b ∈ (leadingForm (t.den : ℤ) (t.num.natAbs : ℤ) P.1).support := by
    apply (leadingForm_mem_iff_rational_slope P (t.den : ℤ) (t.num.natAbs : ℤ)
      (by exact_mod_cast Rat.den_pos t) (expo a b)).mpr
    rw [hratioNat]
    exact ⟨hold.1,hmax⟩
  have hcFace : c ∈ (leadingForm (t.den : ℤ) (t.num.natAbs : ℤ) P.1).support := by
    apply (leadingForm_mem_iff_rational_slope P (t.den : ℤ) (t.num.natAbs : ℤ)
      (by exact_mod_cast Rat.den_pos t) c).mpr
    rw [hratioNat]
    exact ⟨hc,fun p hp => (hmax p hp).trans_eq htie.symm⟩
  have hne : expo a b ≠ c := by
    intro heq
    rw [← heq] at hcb
    simpa [expo] using hcb
  have hface : InDir (t.den : ℤ) (t.num.natAbs : ℤ) P.1 :=
    Finset.one_lt_card_iff.mpr ⟨expo a b,c,haFace,hcFace,hne⟩
  have hdenOne := (preliminary_positive_face_total_degree_axis_endpoint hsource P Q hpair
    t.den t.num.natAbs (Rat.den_pos t) htltNat
    (rational_numDen_natCoprime t) hdir hface).1
  have htEq : (t.num.natAbs : ℚ) = t := by simpa [hdenOne] using hratioNat
  have hsmall : t.num.natAbs < σ := by
    have hq : (t.num.natAbs : ℚ) < σ := by rw [htEq]; simpa using ht
    exact_mod_cast hq
  exact ⟨t.num.natAbs,by simpa [hdenOne] using htltNat,hsmall,
    by simpa [hdenOne] using hface,by simpa [hdenOne] using haFace⟩

/-- A singleton diagonal axis face and a positive-Y support point determine
an actual positive integer face. -/
theorem preliminary_axis_diagonal_first_positive_face
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) (a : ℕ)
    (hmem : expo a 0 ∈ (leadingForm 1 1 P.1).support)
    (hunique : ∀ d ∈ (leadingForm 1 1 P.1).support, d = expo a 0)
    (habove : ∃ d ∈ (symbol P.1).support, 0 < d 1) :
    ∃ σ : ℕ, 1 < σ ∧ InDir 1 (σ : ℤ) P.1 ∧
      expo a 0 ∈ (leadingForm 1 (σ : ℤ) P.1).support := by
  classical
  obtain ⟨t, ht, hmax, c, hc, hcb, htie⟩ :=
    leadingFace_exists_first_upward_tilt P 1 1 (by norm_num) (expo a 0)
      hmem (by intro d hd; rw [hunique d hd]) (by simpa [expo] using habove)
  obtain ⟨htdir, htden, htlt, hratio⟩ :=
    positive_rational_direction t (by simpa using ht)
  have hnumNonneg : 0 ≤ t.num := by omega
  have hnumCast : (t.num.natAbs : ℤ) = t.num := by omega
  have htltNat : t.den < t.num.natAbs := by
    have hltZ : (t.den : ℤ) < (t.num.natAbs : ℤ) := by
      rw [hnumCast]
      exact htlt
    exact_mod_cast hltZ
  have hdir : IsDirection (t.den : ℤ) (t.num.natAbs : ℤ) := by
    rw [hnumCast]
    exact htdir
  have hratioNat : ((t.num.natAbs : ℤ) : ℚ) / ((t.den : ℤ) : ℚ) = t := by
    rw [hnumCast]
    simpa only [Int.cast_natCast] using hratio
  have haSupport := (leadingForm_mem_iff_rational_slope P 1 1 (by norm_num)
    (expo a 0)).mp hmem |>.1
  have haFace : expo a 0 ∈
      (leadingForm (t.den : ℤ) (t.num.natAbs : ℤ) P.1).support := by
    apply (leadingForm_mem_iff_rational_slope P (t.den : ℤ)
      (t.num.natAbs : ℤ) (by exact_mod_cast Rat.den_pos t) (expo a 0)).mpr
    rw [hratioNat]
    exact ⟨haSupport, hmax⟩
  have hcMax : ∀ d ∈ (symbol P.1).support,
      rationalNewtonWeight t d ≤ rationalNewtonWeight t c := by
    intro d hd
    exact (hmax d hd).trans_eq htie.symm
  have hcFace : c ∈
      (leadingForm (t.den : ℤ) (t.num.natAbs : ℤ) P.1).support := by
    apply (leadingForm_mem_iff_rational_slope P (t.den : ℤ)
      (t.num.natAbs : ℤ) (by exact_mod_cast Rat.den_pos t) c).mpr
    rw [hratioNat]
    exact ⟨hc, hcMax⟩
  have hne : expo a 0 ≠ c := by
    intro heq
    rw [← heq] at hcb
    simpa [expo] using hcb
  have hfaceDir : InDir (t.den : ℤ) (t.num.natAbs : ℤ) P.1 :=
    Finset.one_lt_card_iff.mpr ⟨expo a 0, c, haFace, hcFace, hne⟩
  have hden := (preliminary_positive_face_total_degree_axis_endpoint hsource P Q hpair
    t.den t.num.natAbs (Rat.den_pos t) htltNat (rational_numDen_natCoprime t)
    hdir hfaceDir).1
  refine ⟨t.num.natAbs, ?_, ?_, ?_⟩
  · simpa [hden] using htltNat
  · simpa [hden] using hfaceDir
  · simpa [hden] using haFace

/-- An exact counterexample with an axis-only diagonal has a nontrivial
positive integer face, without an extra support-existence premise. -/
theorem preliminary_axis_diagonal_positive_face
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q) (a : ℕ)
    (hmem : expo a 0 ∈ (leadingForm 1 1 P.1).support)
    (hunique : ∀ d ∈ (leadingForm 1 1 P.1).support, d = expo a 0) :
    ∃ σ : ℕ, 1 < σ ∧ InDir 1 (σ : ℤ) P.1 ∧
      expo a 0 ∈ (leadingForm 1 (σ : ℤ) P.1).support := by
  obtain ⟨d,hd,hnegative⟩ := (ggv_grades_opposite_proved P Q hpair).2
  have hy : 0 < d 1 := by
    dsimp [grade] at hnegative
    omega
  exact preliminary_axis_diagonal_first_positive_face hsource P Q hpair a hmem hunique
    ⟨d,hd,hy⟩

end Dixmier.Weyl
